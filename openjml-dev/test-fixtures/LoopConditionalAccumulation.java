// SOLVER_UNKNOWN Group D fixture - conditional accumulator with ternary inside \sum
public class LoopConditionalAccumulation {

    //@ requires arr != null;
    //@ ensures 0 >= arr.length ==> \result == 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int sumPositives(int[] arr) {
        int sum = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= arr.length;
        //@ loop_invariant sum == (\sum int k; 0 <= k && k < i; (arr[k] > 0) ? (arr[k]) : 0);
        for (int i = 0; i < arr.length; i++) {
            if (arr[i] > 0)
                sum += arr[i];
        }
        return sum;
    }
}
