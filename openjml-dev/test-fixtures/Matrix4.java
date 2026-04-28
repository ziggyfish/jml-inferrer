// SOLVER_UNKNOWN Group A fixture (sum with nested 2D array indexing)
public class Matrix4 {

    //@ public invariant size >= 0;
    /*@ spec_public @*/ private int[][] data;

    /*@ spec_public @*/ private int size;

    //@ requires this.data != null;
    //@ requires 0 <= size;
    //@ ensures 0 >= size ==> \result == 0;
    //@ assignable \nothing;
    public int trace() {
        int sum = 0;
        //@ loop_invariant i >= 0;
        //@ loop_invariant i <= size;
        //@ loop_invariant sum == (\sum int k; 0 <= k && k < i; data[k][k]);
        for (int i = 0; i < size; i++) {
            sum += data[i][i];
        }
        return sum;
    }
}
