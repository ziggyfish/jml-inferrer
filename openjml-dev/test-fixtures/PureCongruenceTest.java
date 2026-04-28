public class PureCongruenceTest {

    /*@ requires s != null && s.length() >= 3;
      @ ensures \result.equals(s.substring(0, 3));
      @*/
    public String foo(String s) {
        return s.substring(0, 3);
    }

    /*@ requires s != null;
      @ ensures \result.equals(s.toLowerCase());
      @*/
    public String lower(String s) {
        return s.toLowerCase();
    }
}
