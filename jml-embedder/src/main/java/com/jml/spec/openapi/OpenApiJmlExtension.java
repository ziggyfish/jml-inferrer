package com.jml.spec.openapi;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.jml.spec.SignalsClause;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * Read/write helpers for the OpenAPI {@code x-jml-*} extension family
 * defined in {@code journal/rq2_embedding_design.md} §6.
 *
 * <p>This implementation operates on JSON-shaped OpenAPI documents (the
 * native serialisation format for both OpenAPI 3.x and a common output of
 * springdoc-openapi). YAML inputs can be converted to JSON via any
 * standard YAML library before invoking the reader; the writer emits JSON
 * because it is unambiguous on the wire.</p>
 *
 * <p>The reader is permissive — extension keys present on operations that
 * do not declare them are skipped silently. The writer is strict — emitted
 * arrays preserve order for {@code requires} and emit unordered for
 * {@code ensures}, {@code assignable}, {@code loop-invariant},
 * {@code invariant}.</p>
 */
public final class OpenApiJmlExtension {

    private static final Gson GSON = new GsonBuilder()
            .setPrettyPrinting()
            .disableHtmlEscaping()
            .create();
    private static final String EXT_REQUIRES = "x-jml-requires";
    private static final String EXT_ENSURES = "x-jml-ensures";
    private static final String EXT_ASSIGNABLE = "x-jml-assignable";
    private static final String EXT_LOOP_INVARIANT = "x-jml-loop-invariant";
    private static final String EXT_SIGNALS = "x-jml-signals";

    private OpenApiJmlExtension() {
    }

    /**
     * Read every operation's JML extensions from an OpenAPI JSON document.
     *
     * @param openapiJson OpenAPI 3.x document as JSON.
     * @return per-operation specifications keyed by route + HTTP verb.
     */
    public static Map<OperationKey, OperationSpec> read(String openapiJson) {
        Map<OperationKey, OperationSpec> result = new LinkedHashMap<>();
        JsonObject doc = GSON.fromJson(openapiJson, JsonObject.class);
        if (doc == null || !doc.has("paths")) return result;
        JsonObject paths = doc.getAsJsonObject("paths");
        for (Map.Entry<String, JsonElement> pathEntry : paths.entrySet()) {
            String route = pathEntry.getKey();
            if (!pathEntry.getValue().isJsonObject()) continue;
            JsonObject pathItem = pathEntry.getValue().getAsJsonObject();
            for (Map.Entry<String, JsonElement> verbEntry : pathItem.entrySet()) {
                String verb = verbEntry.getKey();
                if (!isHttpVerb(verb)) continue;
                if (!verbEntry.getValue().isJsonObject()) continue;
                OperationSpec spec = readOperation(verbEntry.getValue().getAsJsonObject());
                if (!isEmpty(spec)) {
                    result.put(new OperationKey(route, verb.toUpperCase()), spec);
                }
            }
        }
        return result;
    }

    public static Map<OperationKey, OperationSpec> readFile(Path jsonFile) throws IOException {
        return read(Files.readString(jsonFile));
    }

    /**
     * Write the given operation specs into an OpenAPI document, returning
     * the modified JSON string. The input document is not mutated; existing
     * extension keys are overwritten where the spec contributes a key, and
     * preserved otherwise.
     */
    public static String write(String openapiJson, Map<OperationKey, OperationSpec> specs) {
        JsonObject doc = openapiJson == null || openapiJson.isBlank()
                ? minimalOpenApiSkeleton()
                : GSON.fromJson(openapiJson, JsonObject.class);
        if (doc == null) doc = minimalOpenApiSkeleton();
        JsonObject paths = doc.has("paths") ? doc.getAsJsonObject("paths") : new JsonObject();
        if (!doc.has("paths")) doc.add("paths", paths);

        for (Map.Entry<OperationKey, OperationSpec> e : specs.entrySet()) {
            String route = e.getKey().route();
            String verb = e.getKey().method().toLowerCase();
            JsonObject pathItem = paths.has(route) && paths.get(route).isJsonObject()
                    ? paths.getAsJsonObject(route) : new JsonObject();
            if (!paths.has(route)) paths.add(route, pathItem);
            JsonObject operation = pathItem.has(verb) && pathItem.get(verb).isJsonObject()
                    ? pathItem.getAsJsonObject(verb) : new JsonObject();
            if (!pathItem.has(verb)) pathItem.add(verb, operation);
            writeOperation(operation, e.getValue());
        }
        return GSON.toJson(doc);
    }

    public static void writeFile(Path jsonFile, String openapiJson, Map<OperationKey, OperationSpec> specs)
            throws IOException {
        Files.writeString(jsonFile, write(openapiJson, specs));
    }

    /**
     * Sidecar JSON form, per design doc §6.4. Use when the OpenAPI document
     * is auto-generated and not editable. Keyed by {@code "<verb> <route>"}.
     */
    public static String writeSidecar(Map<OperationKey, OperationSpec> specs) {
        JsonObject root = new JsonObject();
        root.addProperty("version", "1.0");
        JsonObject ops = new JsonObject();
        // Use a TreeMap to make the output ordering deterministic so test
        // diffs and downstream consumers see stable strings.
        Map<String, OperationSpec> sorted = new TreeMap<>();
        for (Map.Entry<OperationKey, OperationSpec> e : specs.entrySet()) {
            sorted.put(e.getKey().method() + " " + e.getKey().route(), e.getValue());
        }
        for (Map.Entry<String, OperationSpec> e : sorted.entrySet()) {
            JsonObject opJson = new JsonObject();
            writeOperation(opJson, e.getValue());
            ops.add(e.getKey(), opJson);
        }
        root.add("operations", ops);
        return GSON.toJson(root);
    }

    public static Map<OperationKey, OperationSpec> readSidecar(String json) {
        Map<OperationKey, OperationSpec> result = new LinkedHashMap<>();
        JsonObject doc = GSON.fromJson(json, JsonObject.class);
        if (doc == null || !doc.has("operations")) return result;
        JsonObject ops = doc.getAsJsonObject("operations");
        for (Map.Entry<String, JsonElement> e : ops.entrySet()) {
            String key = e.getKey();
            int sp = key.indexOf(' ');
            if (sp < 0) continue;
            String verb = key.substring(0, sp);
            String route = key.substring(sp + 1);
            OperationSpec spec = readOperation(e.getValue().getAsJsonObject());
            result.put(new OperationKey(route, verb), spec);
        }
        return result;
    }

    // --- helpers ---

    private static OperationSpec readOperation(JsonObject op) {
        return new OperationSpec(
                readStringArray(op, EXT_REQUIRES),
                readStringArray(op, EXT_ENSURES),
                readStringArray(op, EXT_ASSIGNABLE),
                readStringArray(op, EXT_LOOP_INVARIANT),
                readSignals(op),
                "1.0");
    }

    private static void writeOperation(JsonObject op, OperationSpec spec) {
        if (!spec.requires().isEmpty()) op.add(EXT_REQUIRES, jsonArray(spec.requires()));
        if (!spec.ensures().isEmpty()) op.add(EXT_ENSURES, jsonArray(spec.ensures()));
        if (!spec.assignable().isEmpty()) op.add(EXT_ASSIGNABLE, jsonArray(spec.assignable()));
        if (!spec.loopInvariant().isEmpty()) op.add(EXT_LOOP_INVARIANT, jsonArray(spec.loopInvariant()));
        if (!spec.signals().isEmpty()) {
            com.google.gson.JsonArray arr = new com.google.gson.JsonArray();
            for (SignalsClause s : spec.signals()) {
                JsonObject obj = new JsonObject();
                obj.addProperty("exception", s.exceptionType());
                obj.addProperty("condition", s.condition());
                arr.add(obj);
            }
            op.add(EXT_SIGNALS, arr);
        }
    }

    private static List<String> readStringArray(JsonObject op, String key) {
        if (!op.has(key) || !op.get(key).isJsonArray()) return List.of();
        com.google.gson.JsonArray arr = op.getAsJsonArray(key);
        List<String> out = new ArrayList<>(arr.size());
        for (JsonElement el : arr) {
            if (el.isJsonPrimitive()) out.add(el.getAsString());
        }
        return out;
    }

    private static List<SignalsClause> readSignals(JsonObject op) {
        if (!op.has(EXT_SIGNALS) || !op.get(EXT_SIGNALS).isJsonArray()) return List.of();
        com.google.gson.JsonArray arr = op.getAsJsonArray(EXT_SIGNALS);
        List<SignalsClause> out = new ArrayList<>(arr.size());
        for (JsonElement el : arr) {
            if (!el.isJsonObject()) continue;
            JsonObject o = el.getAsJsonObject();
            if (!o.has("exception") || !o.has("condition")) continue;
            out.add(new SignalsClause(o.get("exception").getAsString(),
                    o.get("condition").getAsString()));
        }
        return out;
    }

    private static com.google.gson.JsonArray jsonArray(List<String> items) {
        com.google.gson.JsonArray arr = new com.google.gson.JsonArray();
        for (String s : items) arr.add(s);
        return arr;
    }

    private static boolean isHttpVerb(String s) {
        return switch (s.toLowerCase()) {
            case "get", "post", "put", "delete", "patch", "options", "head", "trace" -> true;
            default -> false;
        };
    }

    private static boolean isEmpty(OperationSpec spec) {
        return spec.requires().isEmpty() && spec.ensures().isEmpty()
                && spec.assignable().isEmpty() && spec.loopInvariant().isEmpty()
                && spec.signals().isEmpty();
    }

    private static JsonObject minimalOpenApiSkeleton() {
        JsonObject doc = new JsonObject();
        doc.addProperty("openapi", "3.0.3");
        JsonObject info = new JsonObject();
        info.addProperty("title", "Generated");
        info.addProperty("version", "1.0.0");
        doc.add("info", info);
        doc.add("paths", new JsonObject());
        return doc;
    }
}
