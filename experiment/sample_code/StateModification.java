package experiment.sample_code;

/**
 * Sample class demonstrating State Modification methods.
 */
@com.jml.inferrer.annotations.Invariant("counter >= 0")
@com.jml.inferrer.annotations.Invariant("status != null")
@com.jml.inferrer.annotations.Invariant("data != null")
public class StateModification {

    private int counter;

    private double balance;

    @com.jml.inferrer.annotations.Nullable
    private String status;

    @com.jml.inferrer.annotations.Nullable
    private int[] data;

    private boolean locked;

    public StateModification() {
        this.counter = 0;
        this.balance = 0.0;
        this.status = "INITIAL";
        this.data = new int[10];
        this.locked = false;
    }

    // Increment with logic
    @com.jml.inferrer.annotations.Ensures("this.counter == \old(this.counter) + 1")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void increment() {
        if (!locked) {
            counter++;
        }
    }

    // Decrement with constraint
    @com.jml.inferrer.annotations.Ensures("this.counter == \old(this.counter) - 1")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void decrement() {
        if (!locked && counter > 0) {
            counter--;
        }
    }

    // State modification with validation
    @com.jml.inferrer.annotations.Requires("amount > 0")
    @com.jml.inferrer.annotations.Ensures("this.balance == \old(this.balance) + amount")
    @com.jml.inferrer.annotations.Assignable("this.balance")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public boolean deposit(double amount) {
        if (amount > 0 && !locked) {
            balance += amount;
            return true;
        }
        return false;
    }

    // State modification with constraint
    @com.jml.inferrer.annotations.Requires("amount > 0")
    @com.jml.inferrer.annotations.Requires("amount <= balance")
    @com.jml.inferrer.annotations.Ensures("this.balance == \old(this.balance) - amount")
    @com.jml.inferrer.annotations.Assignable("this.balance")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public boolean withdraw(double amount) {
        if (amount > 0 && amount <= balance && !locked) {
            balance -= amount;
            return true;
        }
        return false;
    }

    // Apply discount with percentage
    @com.jml.inferrer.annotations.Requires("percentage > 0")
    @com.jml.inferrer.annotations.Requires("percentage <= 100")
    @com.jml.inferrer.annotations.Ensures("this.balance == \old(this.balance) * (1 - percentage / 100)")
    @com.jml.inferrer.annotations.Assignable("this.balance")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void applyDiscount(double percentage) {
        if (percentage > 0 && percentage <= 100) {
            balance = balance * (1 - percentage / 100);
        }
    }

    // State transition
    @com.jml.inferrer.annotations.Assignable("this.status")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void activate() {
        if (status.equals("INITIAL") || status.equals("SUSPENDED")) {
            status = "ACTIVE";
        }
    }

    // State transition
    @com.jml.inferrer.annotations.Assignable("this.status")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void suspend() {
        if (status.equals("ACTIVE")) {
            status = "SUSPENDED";
        }
    }

    // State transition
    @com.jml.inferrer.annotations.Assignable("this.status")
    @com.jml.inferrer.annotations.Assignable("this.locked")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void terminate() {
        status = "TERMINATED";
        locked = true;
    }

    // Array modification
    @com.jml.inferrer.annotations.Requires("index >= 0")
    @com.jml.inferrer.annotations.Requires("index < data.length")
    @com.jml.inferrer.annotations.Assignable("data[*]")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void setElement(int index, int value) {
        if (index >= 0 && index < data.length) {
            data[index] = value;
        }
    }

    // Reset state
    @com.jml.inferrer.annotations.LoopInvariant("i >= 0")
    @com.jml.inferrer.annotations.LoopInvariant("i < data.length")
    @com.jml.inferrer.annotations.LoopInvariant("(\forall int k; 0 <= k < i; data[k] == 0)")
    @com.jml.inferrer.annotations.Assignable("this.counter")
    @com.jml.inferrer.annotations.Assignable("this.balance")
    @com.jml.inferrer.annotations.Assignable("this.status")
    @com.jml.inferrer.annotations.Assignable("this.locked")
    @com.jml.inferrer.annotations.Assignable("data[*]")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(1)")
    public void reset() {
        counter = 0;
        balance = 0.0;
        status = "INITIAL";
        locked = false;
        for (int i = 0; i < data.length; i++) {
            data[i] = 0;
        }
    }

    // Lock/unlock
    @com.jml.inferrer.annotations.Assignable("this.locked")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void lock() {
        locked = true;
    }

    @com.jml.inferrer.annotations.Assignable("this.locked")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void unlock() {
        locked = false;
    }

    // Getters for verification
    @com.jml.inferrer.annotations.Ensures("\result == this.counter")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public int getCounter() {
        return counter;
    }

    @com.jml.inferrer.annotations.Ensures("\result == this.balance")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public double getBalance() {
        return balance;
    }

    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Ensures("\result == this.status")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public String getStatus() {
        return status;
    }

    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public boolean isLocked() {
        return locked;
    }
}
