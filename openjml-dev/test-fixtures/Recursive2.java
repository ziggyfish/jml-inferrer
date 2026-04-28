// Variant: recursive postcondition that references self
public class Recursive2 {

    //@ requires n >= 0;
    //@ requires n <= 12;
    //@ ensures n <= 1 ==> \result == 1;
    //@ ensures n > 1 ==> \result == n * factorial(n - 1);
    /*@ pure @*/
    public int factorial(int n) {
        if (n <= 1) return 1;
        return n * factorial(n - 1);
    }
}
