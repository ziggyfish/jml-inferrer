public class MaxArrayBAD {

    //@ requires array != null && array.length > 0;
    //@ ensures (\forall int k; 0 <= k && k < array.length; \result > array[k]);
    //@ ensures (\exists int k; 0 <= k && k < array.length; \result == array[k]);
    //@ assignable \nothing;
    public static int max(final int[] array) {
        if (array == null || array.length == 0) {
            throw new IllegalArgumentException("array");
        }
        int max = array[0];
        //@ maintaining 1 <= j && j <= array.length;
        //@ maintaining (\forall int k; 0 <= k && k < j; max >= array[k]);
        //@ maintaining (\exists int k; 0 <= k && k < j; max == array[k]);
        //@ decreases array.length - j;
        for (int j = 1; j < array.length; j++) {
            if (array[j] > max) {
                max = array[j];
            }
        }
        return max;
    }
}
