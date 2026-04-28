public class PureCongruenceTest2 {

    /*@ requires s != null && s.length() >= 3 && t != null && t.length() >= 3;
      @ ensures \result.equals(s.substring(0, 3));
      @*/
    public String fooDifferent(String s, String t) {
        // Body call uses s, spec call uses s — but t is unused. Should still verify.
        return s.substring(0, 3);
    }

    /*@ requires s != null && s.length() >= 3;
      @ ensures \result.length() == 3;
      @*/
    public String onlyLength(String s) {
        return s.substring(0, 3);
    }

    /*@ requires s != null;
      @ ensures \result == s.toLowerCase().toUpperCase();
      @*/
    public String chained(String s) {
        return s.toLowerCase().toUpperCase();
    }
}
