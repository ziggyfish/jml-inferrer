package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ReturnStmt;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

/**
 * Analyzes Java Stream API operations to infer specifications.
 *
 * Handles:
 * - filter(): Cardinality constraints (result size <= source size)
 * - map(): Element transformation (same cardinality)
 * - flatMap(): Cardinality relationships
 * - collect(): Collection type constraints
 * - reduce(): Result type constraints
 * - distinct(): Uniqueness guarantees
 * - sorted(): Ordering guarantees
 * - findFirst()/findAny(): Optional result constraints
 * - anyMatch()/allMatch()/noneMatch(): Boolean result constraints
 * - count(): Non-negative result
 */
public class StreamOperationAnalyzer {

    private static final Logger logger = LoggerFactory.getLogger(StreamOperationAnalyzer.class);

    /**
     * Represents a chain of stream operations.
     */
    public static class StreamChain {
        private final String sourceExpression;
        private final List<StreamOperation> operations = new ArrayList<>();
        private String terminalOperation;

        public StreamChain(String source) {
            this.sourceExpression = source;
        }

        public void addOperation(StreamOperation op) {
            operations.add(op);
        }

        public void setTerminalOperation(String terminal) {
            this.terminalOperation = terminal;
        }

        public String getSourceExpression() {
            return sourceExpression;
        }

        public List<StreamOperation> getOperations() {
            return operations;
        }

        public String getTerminalOperation() {
            return terminalOperation;
        }

        public boolean hasFilter() {
            return operations.stream().anyMatch(op -> op.type == OperationType.FILTER);
        }

        public boolean hasMap() {
            return operations.stream().anyMatch(op -> op.type == OperationType.MAP);
        }

        public boolean hasFlatMap() {
            return operations.stream().anyMatch(op -> op.type == OperationType.FLAT_MAP);
        }

        public boolean hasDistinct() {
            return operations.stream().anyMatch(op -> op.type == OperationType.DISTINCT);
        }

        public boolean hasSorted() {
            return operations.stream().anyMatch(op -> op.type == OperationType.SORTED);
        }

        public int getFilterCount() {
            return (int) operations.stream().filter(op -> op.type == OperationType.FILTER).count();
        }
    }

    /**
     * Represents a single stream operation.
     */
    public static class StreamOperation {
        public final OperationType type;
        public final String predicateOrMapper;

        public StreamOperation(OperationType type, String predicateOrMapper) {
            this.type = type;
            this.predicateOrMapper = predicateOrMapper;
        }
    }

    /**
     * Types of stream operations.
     */
    public enum OperationType {
        FILTER, MAP, FLAT_MAP, DISTINCT, SORTED, LIMIT, SKIP,
        PEEK, TAKE_WHILE, DROP_WHILE
    }

    /**
     * Terminal operation types.
     */
    public enum TerminalType {
        COLLECT, REDUCE, FOR_EACH, COUNT, FIND_FIRST, FIND_ANY,
        ANY_MATCH, ALL_MATCH, NONE_MATCH, TO_ARRAY, TO_LIST, MIN, MAX, SUM, AVERAGE
    }

    /**
     * Analyzes stream operations in a method and returns inferred specifications.
     */
    public List<String> analyzeStreamOperations(MethodDeclaration methodDecl) {
        List<String> specifications = new ArrayList<>();

        // Find all method call expressions that might be stream operations
        List<MethodCallExpr> methodCalls = methodDecl.findAll(MethodCallExpr.class);

        // Look for stream() calls or Stream.of() patterns
        for (MethodCallExpr call : methodCalls) {
            if (isStreamStart(call)) {
                StreamChain chain = analyzeStreamChain(call);
                if (chain != null) {
                    specifications.addAll(inferChainSpecifications(chain, methodDecl));
                }
            }
        }

        return specifications;
    }

    /**
     * Checks if a method call starts a stream.
     */
    private boolean isStreamStart(MethodCallExpr call) {
        String methodName = call.getNameAsString();
        return methodName.equals("stream") ||
               methodName.equals("parallelStream") ||
               methodName.equals("of") ||
               methodName.equals("generate") ||
               methodName.equals("iterate") ||
               methodName.equals("range") ||
               methodName.equals("rangeClosed") ||
               methodName.equals("empty") ||
               methodName.equals("concat");
    }

    /**
     * Analyzes a stream chain starting from the initial stream call.
     */
    private StreamChain analyzeStreamChain(MethodCallExpr streamStart) {
        String source = getStreamSource(streamStart);
        StreamChain chain = new StreamChain(source);

        // Walk up the AST to find the full chain
        MethodCallExpr current = streamStart;

        // Find the parent chain by looking at what calls use this expression
        while (current.getParentNode().isPresent() &&
               current.getParentNode().get() instanceof MethodCallExpr) {
            // Actually, we need to look at method calls ON this expression
            // Stream operations chain like: source.stream().filter().map()
            break;
        }

        // Instead, trace forward through the chain
        // This is done by finding method calls that have `current` as their scope
        traceStreamChain(streamStart, chain);

        return chain;
    }

    /**
     * Traces a stream chain by following method calls.
     */
    private void traceStreamChain(MethodCallExpr start, StreamChain chain) {
        // Find all method calls in the same statement
        // that could be part of this chain
        start.findAncestor(com.github.javaparser.ast.stmt.Statement.class).ifPresent(stmt -> {
            List<MethodCallExpr> calls = stmt.findAll(MethodCallExpr.class);

            // Sort by position (source order)
            // Then trace the chain from the stream start
            for (MethodCallExpr call : calls) {
                String name = call.getNameAsString();

                // Skip the stream start itself
                if (call == start) continue;

                // Intermediate operations
                switch (name) {
                    case "filter":
                        String predicate = call.getArguments().isEmpty() ? "" :
                                call.getArguments().get(0).toString();
                        chain.addOperation(new StreamOperation(OperationType.FILTER, predicate));
                        break;
                    case "map":
                    case "mapToInt":
                    case "mapToLong":
                    case "mapToDouble":
                        String mapper = call.getArguments().isEmpty() ? "" :
                                call.getArguments().get(0).toString();
                        chain.addOperation(new StreamOperation(OperationType.MAP, mapper));
                        break;
                    case "flatMap":
                    case "flatMapToInt":
                    case "flatMapToLong":
                    case "flatMapToDouble":
                        String flatMapper = call.getArguments().isEmpty() ? "" :
                                call.getArguments().get(0).toString();
                        chain.addOperation(new StreamOperation(OperationType.FLAT_MAP, flatMapper));
                        break;
                    case "distinct":
                        chain.addOperation(new StreamOperation(OperationType.DISTINCT, ""));
                        break;
                    case "sorted":
                        chain.addOperation(new StreamOperation(OperationType.SORTED, ""));
                        break;
                    case "limit":
                        String limit = call.getArguments().isEmpty() ? "" :
                                call.getArguments().get(0).toString();
                        chain.addOperation(new StreamOperation(OperationType.LIMIT, limit));
                        break;
                    case "skip":
                        String skip = call.getArguments().isEmpty() ? "" :
                                call.getArguments().get(0).toString();
                        chain.addOperation(new StreamOperation(OperationType.SKIP, skip));
                        break;
                    case "takeWhile":
                        chain.addOperation(new StreamOperation(OperationType.TAKE_WHILE, ""));
                        break;
                    case "dropWhile":
                        chain.addOperation(new StreamOperation(OperationType.DROP_WHILE, ""));
                        break;

                    // Terminal operations
                    case "collect":
                    case "toList":
                    case "toArray":
                    case "forEach":
                    case "forEachOrdered":
                    case "reduce":
                    case "count":
                    case "findFirst":
                    case "findAny":
                    case "anyMatch":
                    case "allMatch":
                    case "noneMatch":
                    case "min":
                    case "max":
                    case "sum":
                    case "average":
                        chain.setTerminalOperation(name);
                        break;
                }
            }
        });
    }

    /**
     * Gets the source expression for a stream.
     */
    private String getStreamSource(MethodCallExpr streamStart) {
        return streamStart.getScope().map(Expression::toString).orElse("unknown");
    }

    /**
     * Infers specifications from a stream chain.
     */
    private List<String> inferChainSpecifications(StreamChain chain, MethodDeclaration methodDecl) {
        List<String> specs = new ArrayList<>();
        String source = chain.getSourceExpression();
        String terminal = chain.getTerminalOperation();

        // Cardinality constraints from filter operations
        if (chain.hasFilter()) {
            int filterCount = chain.getFilterCount();
            if (filterCount > 0) {
                specs.add("\\result.size() <= " + source + ".size()");
            }
        }

        // Map preserves cardinality (without filter)
        if (chain.hasMap() && !chain.hasFilter() && !chain.hasFlatMap()) {
            specs.add("\\result.size() == " + source + ".size()");
        }

        // flatMap can increase or decrease cardinality
        if (chain.hasFlatMap()) {
            // No specific size guarantee, but result is non-null
            specs.add("\\result != null");
        }

        // distinct reduces or preserves size
        if (chain.hasDistinct()) {
            specs.add("\\result.size() <= " + source + ".size()");
            specs.add("\\result contains no duplicates");
        }

        // sorted preserves size
        if (chain.hasSorted() && !chain.hasFilter()) {
            specs.add("\\result.size() == " + source + ".size()");
            specs.add("\\result is sorted");
        }

        // Terminal operation specific specs
        if (terminal != null) {
            switch (terminal) {
                case "collect":
                case "toList":
                    specs.add("\\result != null");
                    break;
                case "count":
                    specs.add("\\result >= 0");
                    if (!chain.hasFilter() && !chain.hasFlatMap()) {
                        specs.add("\\result == " + source + ".size()");
                    }
                    break;
                case "findFirst":
                case "findAny":
                    specs.add("\\result != null"); // Optional is never null
                    if (!chain.hasFilter()) {
                        specs.add("\\result.isPresent() == !" + source + ".isEmpty()");
                    }
                    break;
                case "anyMatch":
                case "allMatch":
                case "noneMatch":
                    // Boolean result, no size constraints
                    break;
                case "min":
                case "max":
                    specs.add("\\result != null"); // Optional
                    break;
                case "sum":
                    specs.add("\\result >= 0"); // For positive elements
                    break;
                case "average":
                    specs.add("\\result != null"); // OptionalDouble
                    break;
                case "reduce":
                    // Depends on the reduction operation
                    specs.add("\\result != null");
                    break;
            }
        }

        // Check for null-filtering pattern
        for (StreamOperation op : chain.getOperations()) {
            if (op.type == OperationType.FILTER) {
                String predicate = op.predicateOrMapper;
                if (predicate.contains("!= null") || predicate.contains("nonNull") ||
                    predicate.contains("Objects::nonNull")) {
                    specs.add("\\result contains no null elements");
                }
            }
        }

        // Check for limit operation
        for (StreamOperation op : chain.getOperations()) {
            if (op.type == OperationType.LIMIT) {
                try {
                    long limit = Long.parseLong(op.predicateOrMapper);
                    specs.add("\\result.size() <= " + limit);
                } catch (NumberFormatException e) {
                    specs.add("\\result.size() <= " + op.predicateOrMapper);
                }
            }
        }

        return specs;
    }

    /**
     * Analyzes a method and returns stream-related postconditions.
     */
    public Set<String> inferStreamPostconditions(MethodDeclaration methodDecl) {
        Set<String> postconditions = new LinkedHashSet<>();
        postconditions.addAll(analyzeStreamOperations(methodDecl));
        return postconditions;
    }
}
