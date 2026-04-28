// SOLVER_UNKNOWN Group A fixture - 2D nested array indexing in sum
public class Matrix3 {

    //@ public invariant cols >= 0;
    /*@ spec_public @*/ private int[][] data;

    /*@ spec_public @*/ private int cols;

    //@ requires row >= 0;
    //@ requires row < this.data.length;
    //@ requires data != null;
    //@ requires (row >= 0 && row < this.data.length) ==> this.data[row] != null;
    //@ requires this.data != null;
    //@ requires 0 <= cols;
    //@ ensures 0 >= cols ==> \result == 0;
    //@ assignable \nothing;
    //@ signals (IllegalStateException e) data == null;
    public int rowSum(int row) {
        if (data == null)
            throw new IllegalStateException();
        int sum = 0;
        //@ loop_invariant j >= 0;
        //@ loop_invariant j <= cols;
        //@ loop_invariant sum == (\sum int k; 0 <= k && k < j; data[row][k]);
        for (int j = 0; j < cols; j++) {
            sum += data[row][j];
        }
        return sum;
    }
}
