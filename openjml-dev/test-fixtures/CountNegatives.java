// SOLVER_UNKNOWN Group C fixture from inferred-spec-completed.log
public class CountNegatives {

    //@ requires arr != null;
    //@ ensures \result >= 0;
    //@ ensures \result <= arr.length;
    //@ assignable \nothing;
    /*@ pure @*/
    public int countNeg(int[] arr) {
        int count = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= arr.length;
        //@ loop_invariant count >= 0;
        //@ loop_invariant count <= i;
        //@ loop_invariant count == (\num_of int k; 0 <= k && k < i; arr[k] < 0);
        for (int i = 0; i < arr.length; i++) {
            if (arr[i] < 0) {
                count++;
            }
        }
        return count;
    }
}
