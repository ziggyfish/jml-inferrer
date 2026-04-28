import java.util.Arrays;

public class ArrayCongruenceTest {

    /*@ requires arr != null && arr.length > 0;
      @ ensures \result.length == arr.length;
      @*/
    public int[] copyArr(int[] arr) {
        return Arrays.copyOf(arr, arr.length);
    }
}
