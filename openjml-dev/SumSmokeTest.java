// Smoke test for the \sum / \num_of / \product extension.
// After building the fork, run:
//   openjml --esc --code-math=safe --spec-math=bigint \
//           --arithmetic-failure=hard --nullable-by-default SumSmokeTest.java
//
// Expected: all three methods verify clean (no "Not yet supported" warnings,
// no verification failures).
public class SumSmokeTest {

    //@ requires 0 < n && n < 100;
    //@ ensures \result == (\sum int k; 0 <= k && k < n; k);
    public static int sumTo(int n) {
        int total = 0;
        //@ loop_invariant 0 <= j && j <= n;
        //@ loop_invariant total == (\sum int k; 0 <= k && k < j; k);
        //@ decreases n - j;
        for (int j = 0; j < n; j++) {
            //@ assume Integer.MIN_VALUE <= total + j && total + j <= Integer.MAX_VALUE;
            total += j;
        }
        return total;
    }

    //@ requires arr != null;
    //@ requires 0 < arr.length && arr.length < 50;
    //@ ensures \result == (\num_of int k; 0 <= k && k < arr.length; arr[k] > 0);
    public static int countPositive(int[] arr) {
        int c = 0;
        //@ loop_invariant 0 <= i && i <= arr.length;
        //@ loop_invariant c == (\num_of int k; 0 <= k && k < i; arr[k] > 0);
        for (int i = 0; i < arr.length; i++) {
            if (arr[i] > 0) c++;
        }
        return c;
    }

    //@ requires 0 < n && n < 10;
    //@ ensures \result == (\product int k; 1 <= k && k <= n; k);
    public static int factorial(int n) {
        int p = 1;
        //@ loop_invariant 1 <= j && j <= n + 1;
        //@ loop_invariant p == (\product int k; 1 <= k && k < j; k);
        for (int j = 1; j <= n; j++) {
            //@ assume Integer.MIN_VALUE <= p * j && p * j <= Integer.MAX_VALUE;
            p *= j;
        }
        return p;
    }
}
