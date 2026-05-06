package com.jml.inferrer.rest;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.jml.spec.openapi.OpenApiJmlExtension;
import com.jml.spec.openapi.OperationKey;
import com.jml.spec.openapi.OperationSpec;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class RestEndpointInferrerTest {

    @Test
    @DisplayName("@GetMapping handler infers a precondition and ends up at the right route")
    void getMappingProducesExtension() {
        CompilationUnit cu = parse("""
                import org.springframework.web.bind.annotation.*;

                @RestController
                public class OrderController {
                    @GetMapping("/orders/{id}")
                    public Order get(String id) {
                        return new Order(id.length());
                    }
                }

                class Order {
                    int n;
                    Order(int n) { this.n = n; }
                }
                """);

        Map<OperationKey, OperationSpec> specs = new RestEndpointInferrer().inferEndpoints(cu);
        OperationSpec spec = specs.get(new OperationKey("/orders/{id}", "GET"));
        assertNotNull(spec, "expected /orders/{id} GET endpoint; got: " + specs.keySet());
        assertTrue(spec.requires().stream().anyMatch(p -> p.contains("id != null")),
                "expected id != null precondition; got: " + spec.requires());
    }

    @Test
    @DisplayName("Class-level @RequestMapping prefix combines with method-level mapping")
    void requestMappingPrefixCombines() {
        CompilationUnit cu = parse("""
                import org.springframework.web.bind.annotation.*;

                @RestController
                @RequestMapping("/api")
                public class V1Controller {
                    @GetMapping("/items")
                    public String list() {
                        return "all";
                    }
                }
                """);

        Map<OperationKey, OperationSpec> specs = new RestEndpointInferrer().inferEndpoints(cu);
        assertTrue(specs.containsKey(new OperationKey("/api/items", "GET")),
                "expected combined route /api/items; got: " + specs.keySet());
    }

    @Test
    @DisplayName("PostMapping is recognised and produces POST verb")
    void postMappingRecognised() {
        CompilationUnit cu = parse("""
                import org.springframework.web.bind.annotation.*;

                @RestController
                public class CreateController {
                    @PostMapping("/users")
                    public String create(String body) {
                        return body.trim();
                    }
                }
                """);

        Map<OperationKey, OperationSpec> specs = new RestEndpointInferrer().inferEndpoints(cu);
        OperationSpec spec = specs.get(new OperationKey("/users", "POST"));
        assertNotNull(spec, "expected POST /users; got: " + specs.keySet());
    }

    @Test
    @DisplayName("Multiple verbs and routes produce a complete OpenAPI document")
    void multipleEndpointsProduceOpenApi() {
        CompilationUnit cu = parse("""
                import org.springframework.web.bind.annotation.*;

                @RestController
                @RequestMapping("/v1")
                public class CrudController {
                    @GetMapping("/items/{id}")
                    public String get(String id) { return id.length() > 0 ? id : ""; }

                    @PostMapping("/items")
                    public String create(String body) { return body.trim(); }

                    @DeleteMapping("/items/{id}")
                    public void delete(String id) { }
                }
                """);

        String openApi = new RestEndpointInferrer().inferToOpenApi(cu);
        assertTrue(openApi.contains("/v1/items/{id}"), openApi);
        assertTrue(openApi.contains("/v1/items"), openApi);
        assertTrue(openApi.contains("\"x-jml-requires\""), "OpenAPI should contain x-jml-requires");
        // Roundtrip via the OpenAPI reader.
        Map<OperationKey, OperationSpec> readBack = OpenApiJmlExtension.read(openApi);
        assertEquals(3, readBack.size(),
                "expected three operations on the roundtripped OpenAPI; got: " + readBack.keySet());
    }

    @Test
    @DisplayName("Sidecar JSON form contains the same operations as the OpenAPI form")
    void sidecarMatchesOpenApi() {
        CompilationUnit cu = parse("""
                import org.springframework.web.bind.annotation.*;

                @RestController
                public class EndpointsController {
                    @GetMapping("/foo")
                    public String foo(String x) { return x.toUpperCase(); }
                }
                """);

        RestEndpointInferrer rei = new RestEndpointInferrer();
        Map<OperationKey, OperationSpec> direct = rei.inferEndpoints(cu);
        String sidecar = rei.inferToSidecar(cu);
        Map<OperationKey, OperationSpec> readBack = OpenApiJmlExtension.readSidecar(sidecar);
        assertEquals(direct.keySet(), readBack.keySet());
        assertEquals(direct.get(new OperationKey("/foo", "GET")).requires(),
                readBack.get(new OperationKey("/foo", "GET")).requires());
    }

    @Test
    @DisplayName("Non-controller classes are ignored")
    void nonControllersIgnored() {
        CompilationUnit cu = parse("""
                public class PlainClass {
                    public String hello(String name) {
                        return "Hello " + name;
                    }
                }
                """);

        Map<OperationKey, OperationSpec> specs = new RestEndpointInferrer().inferEndpoints(cu);
        assertTrue(specs.isEmpty(), "non-controller classes should produce no specs; got: " + specs);
    }

    @Test
    @DisplayName("Methods without a mapping annotation are ignored")
    void unmappedMethodsIgnored() {
        CompilationUnit cu = parse("""
                import org.springframework.web.bind.annotation.*;

                @RestController
                public class MixedController {
                    @GetMapping("/exposed")
                    public String exposed() { return ""; }

                    public String internal() { return ""; }
                }
                """);

        Map<OperationKey, OperationSpec> specs = new RestEndpointInferrer().inferEndpoints(cu);
        assertEquals(1, specs.size());
        assertTrue(specs.containsKey(new OperationKey("/exposed", "GET")));
    }

    private static CompilationUnit parse(String source) {
        return new JavaParser().parse(source).getResult().orElseThrow();
    }
}
