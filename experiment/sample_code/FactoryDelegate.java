package experiment.sample_code;

import java.util.ArrayList;
import java.util.List;

/**
 * Sample class demonstrating Factory and Delegate patterns.
 */
@com.jml.inferrer.annotations.Invariant("items != null")
@com.jml.inferrer.annotations.Invariant("builder != null")
@com.jml.inferrer.annotations.Invariant("items != null")
@com.jml.inferrer.annotations.Invariant("builder != null")
public class FactoryDelegate {

    @com.jml.inferrer.annotations.Nullable
    @com.jml.inferrer.annotations.Nullable
    private List<String> items;

    @com.jml.inferrer.annotations.Nullable
    @com.jml.inferrer.annotations.Nullable
    private StringBuilder builder;

    public FactoryDelegate() {
        this.items = new ArrayList<>();
        this.builder = new StringBuilder();
    }

    // Factory method - creates new instance
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Ensures("\result instanceof FactoryDelegate")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public static FactoryDelegate create() {
        return new FactoryDelegate();
    }

    // Factory method with parameter
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Assignable("fd.items")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(n)")
    public static FactoryDelegate createWithCapacity(int capacity) {
        FactoryDelegate fd = new FactoryDelegate();
        fd.items = new ArrayList<>(capacity);
        return fd;
    }

    // Factory for creating list
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Ensures("\result.size() >= 0")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(n)")
    public static List<String> createEmptyList() {
        return new ArrayList<>();
    }

    // Factory with initial value
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.LoopInvariant("i >= 0")
    @com.jml.inferrer.annotations.LoopInvariant("i <= end")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(n)")
    public static List<Integer> createRangeList(int start, int end) {
        List<Integer> list = new ArrayList<>();
        for (int i = start; i <= end; i++) {
            list.add(i);
        }
        return list;
    }

    // Delegate to list
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(2^n)", space = "O(log n)")
    public boolean add(String item) {
        return items.add(item);
    }

    // Delegate to list
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(2^n)", space = "O(log n)")
    public String get(int index) {
        return items.get(index);
    }

    // Delegate to list
    @com.jml.inferrer.annotations.Ensures("\result >= 1")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(2^n)", space = "O(log n)")
    public int size() {
        return items.size();
    }

    // Delegate to list
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(2^n)", space = "O(log n)")
    public boolean isEmpty() {
        return items.isEmpty();
    }

    // Delegate to StringBuilder
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(2^n)", space = "O(log n)")
    public void append(String s) {
        builder.append(s);
    }

    // Delegate to StringBuilder
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public String build() {
        return builder.toString();
    }

    // Delegate with transformation
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(2^n)", space = "O(log n)")
    public boolean contains(String item) {
        return items.contains(item);
    }

    // Factory creating array
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.LoopInvariant("i >= 0")
    @com.jml.inferrer.annotations.LoopInvariant("i < size")
    @com.jml.inferrer.annotations.LoopInvariant("(\forall int k; 0 <= k < i; arr[k] == defaultValue)")
    @com.jml.inferrer.annotations.Assignable("arr[*]")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(n)")
    public static int[] createIntArray(int size, int defaultValue) {
        int[] arr = new int[size];
        for (int i = 0; i < size; i++) {
            arr[i] = defaultValue;
        }
        return arr;
    }
}
