// SOLVER_UNKNOWN Group B fixture
public class FactorialPrecondition {

    //@ requires 1 <= (n + 1);
    //@ ensures 1 > n ==> \result == 1;
    //@ assignable \nothing;
    /*@ pure @*/
    public int factorial(int n) {
        int result = 1;
        //@ loop_invariant i >= 1;
        //@ loop_invariant i <= (n + 1);
        //@ loop_invariant result == (\product int k; 1 <= k && k < i; k);
        for (int i = 1; i <= n; i++) {
            result *= i;
        }
        return result;
    }
}
