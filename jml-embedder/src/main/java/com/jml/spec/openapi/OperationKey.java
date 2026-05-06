package com.jml.spec.openapi;

/**
 * Identifies an OpenAPI operation by route and HTTP verb.
 *
 * <p>The verb is upper-case ({@code "GET"}, {@code "POST"}, etc.); the route
 * is exact as it appears in the OpenAPI document, including curly-brace
 * parameter placeholders like {@code "/orders/{id}"}.</p>
 */
public record OperationKey(String route, String method) {
}
