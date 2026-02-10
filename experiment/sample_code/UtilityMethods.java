package experiment.sample_code;

/**
 * Sample class demonstrating Utility/Helper methods.
 */
@com.jml.inferrer.annotations.ThreadSafe
@com.jml.inferrer.annotations.ThreadSafe
public class UtilityMethods {

    // String utility
    @com.jml.inferrer.annotations.Requires("input != null")
    @com.jml.inferrer.annotations.Requires("!input.isEmpty()")
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public static String capitalize(String input) {
        if (input == null || input.isEmpty()) {
            return input;
        }
        return input.substring(0, 1).toUpperCase() + input.substring(1);
    }

    // Math utility
    @com.jml.inferrer.annotations.Requires("value < 0")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public static int abs(int value) {
        return value < 0 ? -value : value;
    }

    // Computation utility
    @com.jml.inferrer.annotations.Requires("numbers != null")
    @com.jml.inferrer.annotations.Requires("numbers.length == 0")
    @com.jml.inferrer.annotations.Ensures("\result >= 0")
    @com.jml.inferrer.annotations.LoopInvariant("n != null")
    @com.jml.inferrer.annotations.LoopInvariant("n is element of numbers")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(1)")
    public static double average(int[] numbers) {
        if (numbers == null || numbers.length == 0) {
            return 0.0;
        }
        int sum = 0;
        for (int n : numbers) {
            sum += n;
        }
        return (double) sum / numbers.length;
    }

    // String utility
    @com.jml.inferrer.annotations.Requires("s != null")
    @com.jml.inferrer.annotations.Requires("!s.isEmpty()")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public static boolean isNullOrEmpty(String s) {
        return s == null || s.isEmpty();
    }

    // Array utility
    @com.jml.inferrer.annotations.Requires("arr != null")
    @com.jml.inferrer.annotations.Requires("arr.length > 0")
    @com.jml.inferrer.annotations.Requires("arr.length > i")
    @com.jml.inferrer.annotations.LoopInvariant("i >= 0")
    @com.jml.inferrer.annotations.LoopInvariant("i < arr.length")
    @com.jml.inferrer.annotations.LoopInvariant("(\forall int k; 0 <= k < i; result[k] == arr[arr.length - 1 - i])")
    @com.jml.inferrer.annotations.Assignable("result[*]")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(n)")
    public static int[] reverse(int[] arr) {
        if (arr == null) {
            return null;
        }
        int[] result = new int[arr.length];
        for (int i = 0; i < arr.length; i++) {
            result[i] = arr[arr.length - 1 - i];
        }
        return result;
    }

    // Math utility
    @com.jml.inferrer.annotations.Ensures("\result == a")
    @com.jml.inferrer.annotations.LoopInvariant("b != 0")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(1)")
    public static int gcd(int a, int b) {
        a = Math.abs(a);
        b = Math.abs(b);
        while (b != 0) {
            int temp = b;
            b = a % b;
            a = temp;
        }
        return a;
    }

    // Validation utility
    @com.jml.inferrer.annotations.Requires("email != null")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public static boolean isValidEmail(String email) {
        if (email == null) {
            return false;
        }
        int atIndex = email.indexOf('@');
        int dotIndex = email.lastIndexOf('.');
        return atIndex > 0 && dotIndex > atIndex + 1 && dotIndex < email.length() - 1;
    }

    // Conversion utility
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public static String intToHex(int value) {
        return Integer.toHexString(value);
    }

    // String manipulation
    @com.jml.inferrer.annotations.Requires("s != null")
    @com.jml.inferrer.annotations.Requires("times <= 0")
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Ensures("\result.isEmpty() || \result.length() > 0")
    @com.jml.inferrer.annotations.LoopInvariant("i >= 0")
    @com.jml.inferrer.annotations.LoopInvariant("i < times")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(1)")
    public static String repeat(String s, int times) {
        if (s == null || times <= 0) {
            return "";
        }
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < times; i++) {
            sb.append(s);
        }
        return sb.toString();
    }

    // Range check utility
    @com.jml.inferrer.annotations.Requires("value >= min")
    @com.jml.inferrer.annotations.Requires("value <= max")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public static boolean isInRange(int value, int min, int max) {
        return value >= min && value <= max;
    }
}
