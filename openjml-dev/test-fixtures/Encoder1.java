// SOLVER_UNKNOWN Group C fixture - \num_of with predicate involving k-1
public class Encoder1 {

    //@ requires data != null;
    //@ requires data != null && data.length != 0;
    //@ requires 1 <= data.length;
    //@ ensures \result > 0;
    //@ assignable \nothing;
    //@ signals (IllegalArgumentException e) data == null || data.length == 0;
    /*@ pure @*/
    public int countRuns(int[] data) {
        if (data == null || data.length == 0)
            throw new IllegalArgumentException();
        int runs = 1;
        //@ loop_invariant i >= 1;
        //@ loop_invariant i <= data.length;
        //@ loop_invariant runs >= 0;
        //@ loop_invariant runs <= i;
        //@ loop_invariant runs == (\num_of int k; 1 <= k && k < i; data[k] != data[k - 1]);
        for (int i = 1; i < data.length; i++) {
            if (data[i] != data[i - 1])
                runs++;
        }
        return runs;
    }
}
