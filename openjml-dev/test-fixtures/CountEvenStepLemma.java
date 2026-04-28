// Targets the SOLVER_UNKNOWN Group C fixture: \num_of loop invariant.
public class CountEvenStepLemma {

    //@ requires arr != null;
    //@ ensures \result >= 0;
    //@ ensures \result <= arr.length;
    //@ assignable \nothing;
    /*@ pure @*/
    public int countEven(int[] arr) {
        int count = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= arr.length;
        //@ loop_invariant count >= 0;
        //@ loop_invariant count <= i;
        //@ loop_invariant count == (\num_of int k; 0 <= k && k < i; arr[k] % 2 == 0);
        for (int i = 0; i < arr.length; i++) {
            if (arr[i] % 2 == 0)
                count++;
        }
        return count;
    }
}
