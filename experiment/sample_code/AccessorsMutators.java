package experiment.sample_code;

/**
 * Sample class demonstrating Accessor and Mutator methods.
 */
@com.jml.inferrer.annotations.Invariant("name != null")
@com.jml.inferrer.annotations.Invariant("tags != null")
public class AccessorsMutators {

    @com.jml.inferrer.annotations.Nullable
    private String name;

    private int age;

    private double balance;

    private boolean active;

    @com.jml.inferrer.annotations.Nullable
    private String[] tags;

    public AccessorsMutators() {
        this.name = "";
        this.age = 0;
        this.balance = 0.0;
        this.active = false;
        this.tags = new String[0];
    }

    // Simple getter
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Ensures("\result == this.name")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public String getName() {
        return name;
    }

    // Simple setter
    @com.jml.inferrer.annotations.Ensures("this.name == name")
    @com.jml.inferrer.annotations.Assignable("this.name")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void setName(String name) {
        this.name = name;
    }

    // Getter with primitive type
    @com.jml.inferrer.annotations.Ensures("\result == this.age")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public int getAge() {
        return age;
    }

    // Setter with validation potential
    @com.jml.inferrer.annotations.Ensures("this.age == age")
    @com.jml.inferrer.annotations.Assignable("this.age")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void setAge(int age) {
        this.age = age;
    }

    // Getter for double
    @com.jml.inferrer.annotations.Ensures("\result == this.balance")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public double getBalance() {
        return balance;
    }

    // Setter for double
    @com.jml.inferrer.annotations.Ensures("this.balance == balance")
    @com.jml.inferrer.annotations.Assignable("this.balance")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void setBalance(double balance) {
        this.balance = balance;
    }

    // Boolean getter
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public boolean isActive() {
        return active;
    }

    // Boolean setter
    @com.jml.inferrer.annotations.Ensures("this.active == active")
    @com.jml.inferrer.annotations.Assignable("this.active")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void setActive(boolean active) {
        this.active = active;
    }

    // Array getter
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Ensures("\result == this.tags")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public String[] getTags() {
        return tags;
    }

    // Array setter
    @com.jml.inferrer.annotations.Ensures("this.tags == tags")
    @com.jml.inferrer.annotations.Assignable("this.tags")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void setTags(String[] tags) {
        this.tags = tags;
    }
}
