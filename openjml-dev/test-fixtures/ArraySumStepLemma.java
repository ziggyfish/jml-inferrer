// Targets the SOLVER_UNKNOWN Group A fixture: \sum loop invariant whose
// inductive step the upstream `define-fun-rec` recursion direction cannot
// hand to z3 via E-matching. After the step-lemma patch is in place, this
// should verify cleanly.
public class ArraySumStepLemma {

    //@ requires arr != null;
    //@ ensures 0 >= arr.length ==> \result == 0;
    //@ assignable \nothing;
    /*@ pure @*/
    public int sum(int[] arr) {
        int total = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= arr.length;
        //@ loop_invariant total == (\sum int k; 0 <= k && k < i; arr[k]);
        for (int i = 0; i < arr.length; i++) {
            total += arr[i];
        }
        return total;
    }
}
