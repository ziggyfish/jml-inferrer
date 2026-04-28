// SOLVER_UNKNOWN Group A fixture (basic sum)
public class AccumulatorInvariant {

    //@ requires arr != null;
    //@ ensures 0 >= arr.length ==> \result == 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int sum(int[] arr) {
        int sum = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= arr.length;
        //@ loop_invariant sum == (\sum int k; 0 <= k && k < i; arr[k]);
        for (int i = 0; i < arr.length; i++) {
            sum += arr[i];
        }
        return sum;
    }
}
