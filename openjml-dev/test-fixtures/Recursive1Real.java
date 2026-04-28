// SOLVER_UNKNOWN Group E fixture - exactly as inferred
public class Recursive1Real {

    //@ requires n >= 0;
    //@ requires ((\bigint) n - (\bigint) 1) >= Integer.MIN_VALUE;
    //@ ensures \result > 0;
    //@ ensures (n >= 0) && (n <= 1) ==> \result == 1;
    //@ ensures (n >= 0) && (n > 1) ==> \result == n * factorial(n - 1);
    //@ assignable \nothing;
    //@ signals (IllegalArgumentException e) n < 0;
    /*@ pure @*/
    public int factorial(int n) {
        if (n < 0)
            throw new IllegalArgumentException();
        if (n <= 1)
            return 1;
        return n * factorial(n - 1);
    }
}
