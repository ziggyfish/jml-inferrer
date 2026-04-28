// SOLVER_UNKNOWN Group C fixture - exercises a compound predicate
public class CountInRange {

    //@ requires arr != null;
    //@ ensures \result >= 0;
    //@ ensures \result <= arr.length;
    //@ assignable \nothing;
    /*@ pure @*/
    public int countInRange(int[] arr, int lo, int hi) {
        int count = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= arr.length;
        //@ loop_invariant count >= 0;
        //@ loop_invariant count <= i;
        //@ loop_invariant count == (\num_of int k; 0 <= k && k < i; arr[k] >= lo && arr[k] <= hi);
        for (int i = 0; i < arr.length; i++) {
            if (arr[i] >= lo && arr[i] <= hi) {
                count++;
            }
        }
        return count;
    }
}
