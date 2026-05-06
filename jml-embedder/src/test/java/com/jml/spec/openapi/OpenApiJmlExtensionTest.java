package com.jml.spec.openapi;

import com.jml.spec.SignalsClause;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class OpenApiJmlExtensionTest {

    @Test
    @DisplayName("Reading an operation with x-jml-* yields the corresponding OperationSpec")
    void readOperation() {
        String doc = """
                {
                  "openapi": "3.0.3",
                  "paths": {
                    "/orders/{id}": {
                      "get": {
                        "x-jml-requires": ["id != null", "id > 0"],
                        "x-jml-ensures": ["\\\\result != null ==> \\\\result.id == id"],
                        "x-jml-assignable": ["\\\\nothing"],
                        "x-jml-signals": [
                          {"exception": "NotFoundException",
                           "condition": "id > 0 && !exists(id)"}
                        ]
                      }
                    }
                  }
                }
                """;
        Map<OperationKey, OperationSpec> specs = OpenApiJmlExtension.read(doc);
        assertEquals(1, specs.size());
        OperationSpec spec = specs.get(new OperationKey("/orders/{id}", "GET"));
        assertNotNull(spec);
        assertEquals(List.of("id != null", "id > 0"), spec.requires());
        assertEquals(List.of("\\result != null ==> \\result.id == id"), spec.ensures());
        assertEquals(List.of("\\nothing"), spec.assignable());
        assertEquals(1, spec.signals().size());
        assertEquals("NotFoundException", spec.signals().get(0).exceptionType());
        assertEquals("id > 0 && !exists(id)", spec.signals().get(0).condition());
    }

    @Test
    @DisplayName("Writing into an empty document produces a minimal OpenAPI skeleton")
    void writeEmptyDocument() {
        OperationSpec spec = new OperationSpec(
                List.of("p != null"), List.of("\\result == p"),
                List.of("\\nothing"), List.of(), List.of(), "1.0");
        String result = OpenApiJmlExtension.write(null,
                Map.of(new OperationKey("/foo", "GET"), spec));
        assertTrue(result.contains("\"openapi\""), result);
        assertTrue(result.contains("\"x-jml-requires\""), result);
        assertTrue(result.contains("p != null"), result);
        assertTrue(result.contains("\"/foo\""), result);
    }

    @Test
    @DisplayName("Writing into existing document preserves existing operation properties")
    void writePreservesExistingProperties() {
        String input = """
                {
                  "openapi": "3.0.3",
                  "paths": {
                    "/users": {
                      "get": {
                        "summary": "List users",
                        "operationId": "listUsers"
                      }
                    }
                  }
                }
                """;
        OperationSpec spec = new OperationSpec(
                List.of("offset >= 0"), List.of(), List.of("\\nothing"),
                List.of(), List.of(), "1.0");
        String out = OpenApiJmlExtension.write(input,
                Map.of(new OperationKey("/users", "GET"), spec));
        assertTrue(out.contains("List users"), out);
        assertTrue(out.contains("listUsers"), out);
        assertTrue(out.contains("offset >= 0"), out);
    }

    @Test
    @DisplayName("Roundtrip: write then read returns equal specs")
    void roundtrip() {
        OperationSpec original = new OperationSpec(
                List.of("a != null", "a.length > 0"),
                List.of("\\result == 42"),
                List.of("\\nothing"),
                List.of("0 <= i && i <= n"),
                List.of(new SignalsClause("IllegalStateException", "broken")),
                "1.0");
        String written = OpenApiJmlExtension.write(null,
                Map.of(new OperationKey("/x", "POST"), original));
        Map<OperationKey, OperationSpec> read = OpenApiJmlExtension.read(written);
        OperationSpec back = read.get(new OperationKey("/x", "POST"));
        assertNotNull(back);
        assertEquals(original.requires(), back.requires());
        assertEquals(original.ensures(), back.ensures());
        assertEquals(original.assignable(), back.assignable());
        assertEquals(original.loopInvariant(), back.loopInvariant());
        assertEquals(original.signals(), back.signals());
    }

    @Test
    @DisplayName("Sidecar JSON form: write and read are inverse")
    void sidecarRoundtrip() {
        OperationSpec spec = new OperationSpec(
                List.of("id > 0"), List.of("\\result != null"),
                List.of(), List.of(), List.of(), "1.0");
        String sidecar = OpenApiJmlExtension.writeSidecar(
                Map.of(new OperationKey("/orders/{id}", "GET"), spec));
        assertTrue(sidecar.contains("\"GET /orders/{id}\""), sidecar);
        Map<OperationKey, OperationSpec> back = OpenApiJmlExtension.readSidecar(sidecar);
        assertEquals(spec.requires(),
                back.get(new OperationKey("/orders/{id}", "GET")).requires());
    }

    @Test
    @DisplayName("Non-HTTP-verb keys are ignored when reading")
    void nonVerbsIgnored() {
        String doc = """
                {
                  "paths": {
                    "/foo": {
                      "summary": "ignored",
                      "parameters": [],
                      "x-jml-requires": ["this should not be picked up"],
                      "get": {"x-jml-requires": ["real one"]}
                    }
                  }
                }
                """;
        Map<OperationKey, OperationSpec> specs = OpenApiJmlExtension.read(doc);
        assertEquals(1, specs.size());
        OperationSpec spec = specs.get(new OperationKey("/foo", "GET"));
        assertNotNull(spec);
        assertEquals(List.of("real one"), spec.requires());
    }
}
