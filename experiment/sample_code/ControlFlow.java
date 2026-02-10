package experiment.sample_code;

/**
 * Sample class demonstrating Control Flow methods.
 */
public class ControlFlow {

    // Simple conditional
    @com.jml.inferrer.annotations.Requires("a > b")
    @com.jml.inferrer.annotations.Ensures("\result == a")
    @com.jml.inferrer.annotations.Ensures("\result == b")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public int max(int a, int b) {
        if (a > b) {
            return a;
        } else {
            return b;
        }
    }

    // Multiple conditions
    @com.jml.inferrer.annotations.Requires("score >= 90")
    @com.jml.inferrer.annotations.Requires("score >= 80")
    @com.jml.inferrer.annotations.Requires("score >= 70")
    @com.jml.inferrer.annotations.Requires("score >= 60")
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public String classify(int score) {
        if (score >= 90) {
            return "A";
        } else if (score >= 80) {
            return "B";
        } else if (score >= 70) {
            return "C";
        } else if (score >= 60) {
            return "D";
        } else {
            return "F";
        }
    }

    // Loop with accumulator
    @com.jml.inferrer.annotations.Requires("numbers != null")
    @com.jml.inferrer.annotations.Requires("numbers.length > 0")
    @com.jml.inferrer.annotations.Requires("numbers.length > i")
    @com.jml.inferrer.annotations.LoopInvariant("i >= 0")
    @com.jml.inferrer.annotations.LoopInvariant("i < numbers.length")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(1)")
    public int sum(int[] numbers) {
        int total = 0;
        for (int i = 0; i < numbers.length; i++) {
            total += numbers[i];
        }
        return total;
    }

    // Loop with early exit
    @com.jml.inferrer.annotations.Requires("arr != null")
    @com.jml.inferrer.annotations.Requires("arr.length > 0")
    @com.jml.inferrer.annotations.Requires("arr.length > i")
    @com.jml.inferrer.annotations.LoopInvariant("i >= 0")
    @com.jml.inferrer.annotations.LoopInvariant("i < arr.length")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Observer
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(1)")
    public int findFirst(int[] arr, int target) {
        for (int i = 0; i < arr.length; i++) {
            if (arr[i] == target) {
                return i;
            }
        }
        return -1;
    }

    // Nested conditions
    @com.jml.inferrer.annotations.Requires("value < min")
    @com.jml.inferrer.annotations.Requires("value > max")
    @com.jml.inferrer.annotations.Ensures("\result == min")
    @com.jml.inferrer.annotations.Ensures("\result == max")
    @com.jml.inferrer.annotations.Ensures("\result == value")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public int clamp(int value, int min, int max) {
        if (value < min) {
            return min;
        } else if (value > max) {
            return max;
        } else {
            return value;
        }
    }

    // While loop
    @com.jml.inferrer.annotations.LoopInvariant("num > 0")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(n)", space = "O(1)")
    public int countDigits(int n) {
        if (n == 0)
            return 1;
        int count = 0;
        int num = Math.abs(n);
        while (num > 0) {
            count++;
            num /= 10;
        }
        return count;
    }

    // Switch statement
    @com.jml.inferrer.annotations.Ensures("\result != null")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public String dayName(int day) {
        switch(day) {
            case 1:
                return "Monday";
            case 2:
                return "Tuesday";
            case 3:
                return "Wednesday";
            case 4:
                return "Thursday";
            case 5:
                return "Friday";
            case 6:
                return "Saturday";
            case 7:
                return "Sunday";
            default:
                return "Invalid";
        }
    }

    // Complex boolean logic
    @com.jml.inferrer.annotations.Requires("a > 0")
    @com.jml.inferrer.annotations.Requires("b > 0")
    @com.jml.inferrer.annotations.Requires("c > 0")
    @com.jml.inferrer.annotations.Assignable("\nothing")
    @com.jml.inferrer.annotations.Pure
    @com.jml.inferrer.annotations.ThreadSafe
    @com.jml.inferrer.annotations.Complexity(time = "O(1)", space = "O(1)")
    public boolean isValidTriangle(int a, int b, int c) {
        return a > 0 && b > 0 && c > 0 && a + b > c && b + c > a && a + c > b;
    }
}
