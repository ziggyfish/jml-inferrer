// SOLVER_UNKNOWN Group C fixture
public class GuardLoop1 {

    //@ requires arr != null;
    //@ ensures \result >= 0;
    //@ ensures \result <= arr.length;
    //@ assignable \nothing;
    //@ signals (IllegalArgumentException e) arr == null;
    /*@ pure @*/
    public int countMatches(int[] arr, int target) {
        if (arr == null)
            throw new IllegalArgumentException();
        int count = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= arr.length;
        //@ loop_invariant count >= 0;
        //@ loop_invariant count <= i;
        //@ loop_invariant count == (\num_of int k; 0 <= k && k < i; arr[k] == target);
        for (int i = 0; i < arr.length; i++) {
            if (arr[i] == target)
                count++;
        }
        return count;
    }
}
