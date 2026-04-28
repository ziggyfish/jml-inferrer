// SOLVER_UNKNOWN Group E fixture - recursive power with double-recursion in even branch
public class Recursive5 {

    //@ requires exp >= 0;
    //@ requires ((\bigint) exp - (\bigint) 1) >= Integer.MIN_VALUE;
    //@ ensures exp == 0 ==> \result == 1;
    //@ ensures ((exp >= 0) && (exp != 0)) && (exp % 2 == 0) ==> \result == power(base, exp / 2) * power(base, exp / 2);
    //@ ensures ((exp >= 0) && (exp != 0)) && (exp % 2 != 0) ==> \result == base * power(base, exp - 1);
    //@ assignable \nothing;
    //@ signals (IllegalArgumentException e) exp < 0;
    /*@ pure @*/
    public long power(int base, int exp) {
        if (exp < 0)
            throw new IllegalArgumentException();
        if (exp == 0)
            return 1;
        if (exp % 2 == 0) {
            long half = power(base, exp / 2);
            return half * half;
        }
        return base * power(base, exp - 1);
    }
}
