// SOLVER_UNKNOWN Group C fixture
public class ArrFilter2 {

    //@ requires arr != null;
    //@ ensures \result >= 0;
    //@ ensures \result <= arr.length;
    //@ assignable \nothing;
    /*@ pure @*/
    public int countAbove(int[] arr, int threshold) {
        if (arr == null)
            throw new IllegalArgumentException();
        int count = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= arr.length;
        //@ loop_invariant count >= 0;
        //@ loop_invariant count <= i;
        //@ loop_invariant count == (\num_of int k; 0 <= k && k < i; arr[k] > threshold);
        for (int i = 0; i < arr.length; i++) {
            if (arr[i] > threshold)
                count++;
        }
        return count;
    }
}
