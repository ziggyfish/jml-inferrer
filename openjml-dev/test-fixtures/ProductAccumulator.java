// SOLVER_UNKNOWN Group B fixture
public class ProductAccumulator {

    //@ requires arr != null;
    //@ ensures 0 >= arr.length ==> \result == 1;
    //@ assignable \nothing;
    /*@ pure @*/
    public int product(int[] arr) {
        int prod = 1;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= arr.length;
        //@ loop_invariant prod == (\product int k; 0 <= k && k < i; arr[k]);
        for (int i = 0; i < arr.length; i++) {
            prod *= arr[i];
        }
        return prod;
    }
}
