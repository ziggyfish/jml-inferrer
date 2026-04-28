// SOLVER_UNKNOWN Group B fixture (constant-base product over range)
public class PowerPrecondition {

    //@ requires 0 <= exp;
    //@ ensures 0 >= exp ==> \result == 1;
    //@ assignable \nothing;
    /*@ pure @*/
    public int power(int base, int exp) {
        int result = 1;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= exp;
        //@ loop_invariant result == (\product int k; 0 <= k && k < i; base);
        for (int i = 0; i < exp; i++) {
            result *= base;
        }
        return result;
    }
}
