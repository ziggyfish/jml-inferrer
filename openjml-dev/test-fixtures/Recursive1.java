// SOLVER_UNKNOWN Group E fixture: recursive pure method with self-referential postcondition
public class Recursive1 {

    //@ requires n >= 0;
    //@ requires n <= 12;
    //@ ensures \result >= 1;
    /*@ pure @*/
    public int factorial(int n) {
        if (n <= 1) return 1;
        return n * factorial(n - 1);
    }
}
