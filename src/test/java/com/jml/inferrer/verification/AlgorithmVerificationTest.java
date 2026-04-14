package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for algorithmic patterns: sorting, searching,
 * mathematical computations, and classic algorithms.
 */
class AlgorithmVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Sorting algorithms
    // =========================================================================

    @Test
    @DisplayName("Bubble sort: swap adjacent elements")
    void bubbleSort() throws IOException {
        String source = """
                public class BubbleSort {
                    public void sort(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length - 1; i++) {
                            for (int j = 0; j < arr.length - 1 - i; j++) {
                                if (arr[j] > arr[j + 1]) {
                                    int temp = arr[j];
                                    arr[j] = arr[j + 1];
                                    arr[j + 1] = temp;
                                }
                            }
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BubbleSort", "sort"));
    }

    @Test
    @DisplayName("Insertion sort: shift and insert")
    void insertionSort() throws IOException {
        String source = """
                public class InsertionSort {
                    public void sort(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 1; i < arr.length; i++) {
                            int key = arr[i];
                            int j = i - 1;
                            while (j >= 0 && arr[j] > key) {
                                arr[j + 1] = arr[j];
                                j--;
                            }
                            arr[j + 1] = key;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "InsertionSort", "sort"));
    }

    @Test
    @DisplayName("Selection sort: find minimum and swap")
    void selectionSort() throws IOException {
        String source = """
                public class SelectionSort {
                    public void sort(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length - 1; i++) {
                            int minIdx = i;
                            for (int j = i + 1; j < arr.length; j++) {
                                if (arr[j] < arr[minIdx]) {
                                    minIdx = j;
                                }
                            }
                            int temp = arr[i];
                            arr[i] = arr[minIdx];
                            arr[minIdx] = temp;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SelectionSort", "sort"));
    }

    // =========================================================================
    // Searching algorithms
    // =========================================================================

    @Test
    @DisplayName("Binary search: iterative")
    void binarySearchIterative() throws IOException {
        String source = """
                public class BinarySearch {
                    public int search(int[] arr, int target) {
                        if (arr == null) throw new IllegalArgumentException();
                        int lo = 0;
                        int hi = arr.length - 1;
                        while (lo <= hi) {
                            int mid = lo + (hi - lo) / 2;
                            if (arr[mid] == target) return mid;
                            if (arr[mid] < target) lo = mid + 1;
                            else hi = mid - 1;
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BinarySearch", "search"));
    }

    @Test
    @DisplayName("Linear search: find first occurrence")
    void linearSearch() throws IOException {
        String source = """
                public class LinearSearch {
                    public int search(int[] arr, int target) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] == target) return i;
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LinearSearch", "search"));
    }

    @Test
    @DisplayName("Find minimum element in array")
    void findMin() throws IOException {
        String source = """
                public class FindMin {
                    public int findMin(int[] arr) {
                        if (arr == null || arr.length == 0) throw new IllegalArgumentException();
                        int min = arr[0];
                        for (int i = 1; i < arr.length; i++) {
                            if (arr[i] < min) min = arr[i];
                        }
                        return min;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FindMin", "findMin"));
    }

    @Test
    @DisplayName("Find maximum element in array")
    void findMax() throws IOException {
        String source = """
                public class FindMax {
                    public int findMax(int[] arr) {
                        if (arr == null || arr.length == 0) throw new IllegalArgumentException();
                        int max = arr[0];
                        for (int i = 1; i < arr.length; i++) {
                            if (arr[i] > max) max = arr[i];
                        }
                        return max;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FindMax", "findMax"));
    }

    // =========================================================================
    // Mathematical algorithms
    // =========================================================================

    @Test
    @DisplayName("Fibonacci iterative")
    void fibonacciIterative() throws IOException {
        String source = """
                public class Fibonacci {
                    public int fib(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        if (n <= 1) return n;
                        int prev = 0;
                        int curr = 1;
                        for (int i = 2; i <= n; i++) {
                            int next = prev + curr;
                            prev = curr;
                            curr = next;
                        }
                        return curr;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Fibonacci", "fib"));
    }

    @Test
    @DisplayName("Power computation: iterative x^n")
    void powerIterative() throws IOException {
        String source = """
                public class Power {
                    public long power(int base, int exp) {
                        if (exp < 0) throw new IllegalArgumentException();
                        long result = 1;
                        for (int i = 0; i < exp; i++) {
                            result *= base;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Power", "power"));
    }

    @Test
    @DisplayName("Fast power: binary exponentiation")
    void fastPower() throws IOException {
        String source = """
                public class FastPower {
                    public long power(long base, int exp) {
                        if (exp < 0) throw new IllegalArgumentException();
                        long result = 1;
                        long b = base;
                        int e = exp;
                        while (e > 0) {
                            if (e % 2 == 1) {
                                result *= b;
                            }
                            b *= b;
                            e /= 2;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FastPower", "power"));
    }

    @Test
    @DisplayName("Euclidean distance squared")
    void distanceSquared() throws IOException {
        String source = """
                public class Geometry {
                    public double distanceSquared(double x1, double y1, double x2, double y2) {
                        double dx = x2 - x1;
                        double dy = y2 - y1;
                        return dx * dx + dy * dy;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Geometry", "distanceSquared"));
    }

    @Test
    @DisplayName("Is prime: trial division")
    void isPrime() throws IOException {
        String source = """
                public class PrimeCheck {
                    public boolean isPrime(int n) {
                        if (n < 2) return false;
                        for (int i = 2; i * i <= n; i++) {
                            if (n % i == 0) return false;
                        }
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PrimeCheck", "isPrime"));
    }

    @Test
    @DisplayName("LCM via GCD")
    void lcm() throws IOException {
        String source = """
                public class LCM {
                    public int gcd(int a, int b) {
                        while (b != 0) {
                            int temp = b;
                            b = a % b;
                            a = temp;
                        }
                        return a;
                    }
                    public int lcm(int a, int b) {
                        if (a == 0 || b == 0) throw new IllegalArgumentException();
                        return Math.abs(a / gcd(a, b) * b);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LCM", "lcm"));
    }

    @Test
    @DisplayName("Sum of digits")
    void sumOfDigits() throws IOException {
        String source = """
                public class DigitSum {
                    public int sumOfDigits(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        int sum = 0;
                        int num = n;
                        while (num > 0) {
                            sum += num % 10;
                            num /= 10;
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DigitSum", "sumOfDigits"));
    }

    @Test
    @DisplayName("Reverse integer digits")
    void reverseDigits() throws IOException {
        String source = """
                public class ReverseInt {
                    public int reverse(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        int result = 0;
                        int num = n;
                        while (num > 0) {
                            result = result * 10 + num % 10;
                            num /= 10;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ReverseInt", "reverse"));
    }

    // =========================================================================
    // Array manipulation algorithms
    // =========================================================================

    @Test
    @DisplayName("Array rotation: left rotate by one")
    void leftRotateByOne() throws IOException {
        String source = """
                public class ArrayRotation {
                    public void leftRotateByOne(int[] arr) {
                        if (arr == null || arr.length == 0) throw new IllegalArgumentException();
                        int first = arr[0];
                        for (int i = 0; i < arr.length - 1; i++) {
                            arr[i] = arr[i + 1];
                        }
                        arr[arr.length - 1] = first;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayRotation", "leftRotateByOne"));
    }

    @Test
    @DisplayName("Dutch national flag: 3-way partition")
    void dutchNationalFlag() throws IOException {
        String source = """
                public class DutchFlag {
                    public void partition(int[] arr, int pivot) {
                        if (arr == null) throw new IllegalArgumentException();
                        int lo = 0;
                        int mid = 0;
                        int hi = arr.length - 1;
                        while (mid <= hi) {
                            if (arr[mid] < pivot) {
                                int temp = arr[lo];
                                arr[lo] = arr[mid];
                                arr[mid] = temp;
                                lo++;
                                mid++;
                            } else if (arr[mid] > pivot) {
                                int temp = arr[mid];
                                arr[mid] = arr[hi];
                                arr[hi] = temp;
                                hi--;
                            } else {
                                mid++;
                            }
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DutchFlag", "partition"));
    }

    @Test
    @DisplayName("Kadane's algorithm: maximum subarray sum")
    void kadaneMaxSubarraySum() throws IOException {
        String source = """
                public class Kadane {
                    public int maxSubarraySum(int[] arr) {
                        if (arr == null || arr.length == 0) throw new IllegalArgumentException();
                        int maxSoFar = arr[0];
                        int maxEndingHere = arr[0];
                        for (int i = 1; i < arr.length; i++) {
                            maxEndingHere = Math.max(arr[i], maxEndingHere + arr[i]);
                            maxSoFar = Math.max(maxSoFar, maxEndingHere);
                        }
                        return maxSoFar;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Kadane", "maxSubarraySum"));
    }

    @Test
    @DisplayName("Remove duplicates from sorted array in-place")
    void removeDuplicates() throws IOException {
        String source = """
                public class RemoveDuplicates {
                    public int removeDups(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (arr.length == 0) return 0;
                        int writeIdx = 1;
                        for (int i = 1; i < arr.length; i++) {
                            if (arr[i] != arr[i - 1]) {
                                arr[writeIdx] = arr[i];
                                writeIdx++;
                            }
                        }
                        return writeIdx;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "RemoveDuplicates", "removeDups"));
    }

    @Test
    @DisplayName("Two-pointer: move zeroes to end")
    void moveZeroes() throws IOException {
        String source = """
                public class MoveZeroes {
                    public void moveZeroes(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int writeIdx = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] != 0) {
                                arr[writeIdx] = arr[i];
                                writeIdx++;
                            }
                        }
                        for (int i = writeIdx; i < arr.length; i++) {
                            arr[i] = 0;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MoveZeroes", "moveZeroes"));
    }

    @Test
    @DisplayName("Prefix sum array computation")
    void prefixSum() throws IOException {
        String source = """
                public class PrefixSum {
                    public int[] computePrefixSum(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int[] prefix = new int[arr.length];
                        if (arr.length == 0) return prefix;
                        prefix[0] = arr[0];
                        for (int i = 1; i < arr.length; i++) {
                            prefix[i] = prefix[i - 1] + arr[i];
                        }
                        return prefix;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PrefixSum", "computePrefixSum"));
    }

    // =========================================================================
    // String algorithms
    // =========================================================================

    @Test
    @DisplayName("String reverse via char array")
    void stringReverse() throws IOException {
        String source = """
                public class StringReverse {
                    public String reverse(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        char[] chars = s.toCharArray();
                        int left = 0;
                        int right = chars.length - 1;
                        while (left < right) {
                            char temp = chars[left];
                            chars[left] = chars[right];
                            chars[right] = temp;
                            left++;
                            right--;
                        }
                        return new String(chars);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StringReverse", "reverse"));
    }

    @Test
    @DisplayName("Count character occurrences in string")
    void countChar() throws IOException {
        String source = """
                public class CharCounter {
                    public int countChar(String s, char c) {
                        if (s == null) throw new IllegalArgumentException();
                        int count = 0;
                        for (int i = 0; i < s.length(); i++) {
                            if (s.charAt(i) == c) count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CharCounter", "countChar"));
    }

    @Test
    @DisplayName("Is palindrome check")
    void isPalindrome() throws IOException {
        String source = """
                public class Palindrome {
                    public boolean isPalindrome(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        int left = 0;
                        int right = s.length() - 1;
                        while (left < right) {
                            if (s.charAt(left) != s.charAt(right)) return false;
                            left++;
                            right--;
                        }
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Palindrome", "isPalindrome"));
    }
}
