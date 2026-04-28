public class SumMinimal {
    //@ requires 0 < n && n < 100;
    //@ ensures \result == (\sum int k; 0 <= k && k < n; k);
    public static int sumTo(int n) {
        int total = 0;
        for (int j = 0; j < n; j++) {
            total += j;
        }
        return total;
    }
}
