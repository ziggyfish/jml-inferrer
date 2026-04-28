// SOLVER_UNKNOWN Group B fixture (sum identity)
class SumToN {

    //@ requires 0 <= n;
    //@ ensures 0 >= n ==> \result == 0;
    //@ assignable \nothing;
    /*@ pure @*/
    int sumTo(int n) {
        int total = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= n;
        //@ loop_invariant total == (\sum int k; 0 <= k && k < i; k);
        for (int i = 0; i < n; i++) {
            total += i;
        }
        return total;
    }
}
