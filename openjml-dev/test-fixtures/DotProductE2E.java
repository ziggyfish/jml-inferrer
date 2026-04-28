// SOLVER_UNKNOWN Group A fixture (sum with multiplicative element function)
public class DotProductE2E {

    //@ requires a != null;
    //@ requires b != null;
    //@ requires b.length >= a.length;
    //@ ensures 0 >= a.length ==> \result == 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int dotProduct(int[] a, int[] b) {
        int result = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= a.length;
        //@ loop_invariant result == (\sum int k; 0 <= k && k < i; a[k] * b[k]);
        for (int i = 0; i < a.length; i++) {
            result += a[i] * b[i];
        }
        return result;
    }
}
