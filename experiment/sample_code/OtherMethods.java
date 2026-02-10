package experiment.sample_code;

import java.io.PrintStream;

/**
 * Sample class demonstrating Other/Miscellaneous methods.
 */
@com.jml.inferrer.annotations.Invariant("output != null")
@com.jml.inferrer.annotations.Invariant("lastMessage != null")
public class OtherMethods {

    @com.jml.inferrer.annotations.Nullable
    private PrintStream output;

    @com.jml.inferrer.annotations.Nullable
    private Runnable callback;

    @com.jml.inferrer.annotations.Nullable
    private String lastMessage;

    public OtherMethods() {
        this.output = System.out;
        this.lastMessage = "";
    }

    // Event handler style
    @com.jml.inferrer.annotations.Requires("output != null")
    @com.jml.inferrer.annotations.Ensures("this.lastMessage is modified")
    @com.jml.inferrer.annotations.Assignable("this.lastMessage")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void handleClick(String buttonId) {
        lastMessage = "Button clicked: " + buttonId;
        if (output != null) {
            output.println(lastMessage);
        }
    }

    // Callback registration
    @com.jml.inferrer.annotations.Ensures("this.callback == callback")
    @com.jml.inferrer.annotations.Assignable("this.callback")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void setCallback(Runnable callback) {
        this.callback = callback;
    }

    // Invoke callback
    @com.jml.inferrer.annotations.Requires("callback != null")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void invokeCallback() {
        if (callback != null) {
            callback.run();
        }
    }

    // Logging method
    @com.jml.inferrer.annotations.Requires("output != null")
    @com.jml.inferrer.annotations.Ensures("this.lastMessage == message")
    @com.jml.inferrer.annotations.Assignable("this.lastMessage")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void log(String message) {
        lastMessage = message;
        if (output != null) {
            output.println("[LOG] " + message);
        }
    }

    // Debug method
    @com.jml.inferrer.annotations.Requires("output != null")
    @com.jml.inferrer.annotations.Assignable("this.lastMessage")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void debug(String message, Object... args) {
        String formatted = String.format(message, args);
        lastMessage = formatted;
        if (output != null) {
            output.println("[DEBUG] " + formatted);
        }
    }

    // Notification
    @com.jml.inferrer.annotations.Ensures("this.lastMessage is modified")
    @com.jml.inferrer.annotations.Assignable("this.lastMessage")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void notify(String event) {
        lastMessage = "Event: " + event;
    }

    // toString override
    @Override
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public String toString() {
        return "OtherMethods{lastMessage='" + lastMessage + "'}";
    }

    // equals override
    @Override
    @com.jml.inferrer.annotations.Requires("obj != null")
    @com.jml.inferrer.annotations.Ensures("(this.equals(obj) ==> obj.equals(this))")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(2^n)", space = "O(log n)")
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null || getClass() != obj.getClass())
            return false;
        OtherMethods that = (OtherMethods) obj;
        return lastMessage != null ? lastMessage.equals(that.lastMessage) : that.lastMessage == null;
    }

    // hashCode override
    @Override
    @com.jml.inferrer.annotations.Ensures("\result == \result")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(2^n)", space = "O(log n)")
    public int hashCode() {
        return lastMessage != null ? lastMessage.hashCode() : 0;
    }

    // Getter for testing
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Ensures("\result == this.lastMessage")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public String getLastMessage() {
        return lastMessage;
    }

    // Set output stream
    @com.jml.inferrer.annotations.Ensures("this.output == output")
    @com.jml.inferrer.annotations.Assignable("this.output")
    @com.jml.inferrer.annotations.Mutator
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public void setOutput(PrintStream output) {
        this.output = output;
    }
}
