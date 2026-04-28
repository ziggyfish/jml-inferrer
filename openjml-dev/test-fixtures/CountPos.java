// SOLVER_UNKNOWN Group C fixture
class CountPos {

    //@ requires items != null;
    //@ ensures \result >= 0;
    //@ ensures \result <= items.length;
    //@ assignable \nothing;
    /*@ pure @*/
    int countPositive(int[] items) {
        int count = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= items.length;
        //@ loop_invariant count >= 0;
        //@ loop_invariant count <= i;
        //@ loop_invariant count == (\num_of int k; 0 <= k && k < i; items[k] > 0);
        for (int i = 0; i < items.length; i++) {
            if (items[i] > 0) {
                count++;
            }
        }
        return count;
    }
}
