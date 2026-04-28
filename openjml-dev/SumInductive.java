// Simpler smoke test: just the \sum with loop_invariant guidance.
// Skip overflow/arithmetic checks to isolate the \sum translation.
public class SumInductive {

    //@ requires 0 <= n && n < 100;
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
}
