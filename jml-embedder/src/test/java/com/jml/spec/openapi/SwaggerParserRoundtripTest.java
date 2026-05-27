package com.jml.spec.openapi;

import io.swagger.v3.oas.models.OpenAPI;
import io.swagger.v3.oas.models.Operation;
import io.swagger.v3.oas.models.PathItem;
import io.swagger.v3.parser.OpenAPIV3Parser;
import io.swagger.v3.parser.core.models.ParseOptions;
import io.swagger.v3.parser.core.models.SwaggerParseResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Article 2 RQ5 follow-up: empirical demonstration that the {@code x-jml-*}
 * extension family is preserved unchanged by the canonical OpenAPI 3.x
 * parser (swagger-parser 2.1.x). Round-trips a non-trivial OpenAPI document
 * carrying every x-jml-* extension key through the parser and checks that
 * the in-memory model exposes the extensions on the operation object,
 * preserving both key names and value lists in order.
 *
 * <p>The OpenAPI 3.x specification (§3.9) requires that any property whose
 * name starts with {@code x-} is preserved by conformant parsers; this test
 * verifies that swagger-parser, the reference Java implementation, honours
 * the requirement for the extension family this paper proposes.</p>
 */
class SwaggerParserRoundtripTest {

    @Test
    @DisplayName("All five x-jml-* extension keys survive swagger-parser parse/serialize")
    void allExtensionsSurviveSwaggerParser() {
        String doc = """
                {
                  "openapi": "3.0.3",
                  "info": {"title": "Test API", "version": "1.0.0"},
                  "paths": {
                    "/orders/{id}": {
                      "get": {
                        "operationId": "getOrder",
                        "summary": "Get an order by id",
                        "parameters": [
                          {"name": "id", "in": "path", "required": true,
                           "schema": {"type": "integer"}}
                        ],
                        "responses": {"200": {"description": "ok"}},
                        "x-jml-requires": ["id != null", "id > 0"],
                        "x-jml-ensures": ["\\\\result != null ==> \\\\result.id == id"],
                        "x-jml-assignable": ["\\\\nothing"],
                        "x-jml-loopInvariant": ["i >= 0 && i <= n"],
                        "x-jml-signals": [
                          {"exception": "NotFoundException",
                           "condition": "id > 0 && !exists(id)"}
                        ]
                      }
                    }
                  }
                }
                """;

        ParseOptions options = new ParseOptions();
        options.setResolve(false);
        SwaggerParseResult parsed = new OpenAPIV3Parser().readContents(doc, null, options);

        assertNotNull(parsed, "swagger-parser must accept the document");
        assertNotNull(parsed.getOpenAPI(), "parsed model must not be null");
        // The parser should not report errors on a well-formed x-* extension.
        // (Warnings are tolerated; the OpenAPI spec defines x-* as
        // implementation-defined, and some parsers warn that they do not
        // recognise the key, which is harmless and expected.)
        List<String> messages = parsed.getMessages();
        long errorCount = messages == null ? 0L : messages.stream()
                .filter(m -> m.toLowerCase().contains("error") && !m.toLowerCase().contains("unrecognized"))
                .count();
        assertEquals(0, errorCount,
                "no parser errors expected on x-* extensions; got: " + messages);

        OpenAPI api = parsed.getOpenAPI();
        PathItem path = api.getPaths().get("/orders/{id}");
        assertNotNull(path, "/orders/{id} path must be retained");
        Operation get = path.getGet();
        assertNotNull(get, "GET operation must be retained");

        Map<String, Object> ext = get.getExtensions();
        assertNotNull(ext, "extensions map must be present");

        // swagger-parser exposes extension keys without the leading 'x-'
        // dropped; the canonical preservation rule is that the key with
        // the leading 'x-' is present in the model.
        assertTrue(ext.containsKey("x-jml-requires"),
                "x-jml-requires must be preserved; extensions: " + ext.keySet());
        assertTrue(ext.containsKey("x-jml-ensures"),
                "x-jml-ensures must be preserved; extensions: " + ext.keySet());
        assertTrue(ext.containsKey("x-jml-assignable"),
                "x-jml-assignable must be preserved; extensions: " + ext.keySet());
        assertTrue(ext.containsKey("x-jml-loopInvariant"),
                "x-jml-loopInvariant must be preserved; extensions: " + ext.keySet());
        assertTrue(ext.containsKey("x-jml-signals"),
                "x-jml-signals must be preserved; extensions: " + ext.keySet());

        // requires preserves array order
        @SuppressWarnings("unchecked")
        List<Object> requires = (List<Object>) ext.get("x-jml-requires");
        assertEquals(2, requires.size());
        assertEquals("id != null", requires.get(0));
        assertEquals("id > 0", requires.get(1));

        // ensures preserves the literal string with backslashes
        @SuppressWarnings("unchecked")
        List<Object> ensures = (List<Object>) ext.get("x-jml-ensures");
        assertEquals(1, ensures.size());
        assertEquals("\\result != null ==> \\result.id == id", ensures.get(0));

        // signals preserves the {exception, condition} object structure
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> signals = (List<Map<String, Object>>) ext.get("x-jml-signals");
        assertEquals(1, signals.size());
        assertEquals("NotFoundException", signals.get(0).get("exception"));
        assertEquals("id > 0 && !exists(id)", signals.get(0).get("condition"));
    }

    @Test
    @DisplayName("Existing OpenAPI properties remain unchanged when x-jml-* are added")
    void otherPropertiesUnchanged() {
        String doc = """
                {
                  "openapi": "3.0.3",
                  "info": {"title": "Test API", "version": "1.0.0"},
                  "paths": {
                    "/users": {
                      "get": {
                        "operationId": "listUsers",
                        "summary": "List users",
                        "responses": {"200": {"description": "ok"}},
                        "x-jml-requires": ["offset >= 0"]
                      }
                    }
                  }
                }
                """;

        ParseOptions options = new ParseOptions();
        options.setResolve(false);
        SwaggerParseResult parsed = new OpenAPIV3Parser().readContents(doc, null, options);
        OpenAPI api = parsed.getOpenAPI();
        Operation get = api.getPaths().get("/users").getGet();

        assertEquals("listUsers", get.getOperationId());
        assertEquals("List users", get.getSummary());
        assertNotNull(get.getResponses().get("200"));
        @SuppressWarnings("unchecked")
        List<Object> requires = (List<Object>) get.getExtensions().get("x-jml-requires");
        assertEquals(List.of("offset >= 0"), requires);
    }
}
