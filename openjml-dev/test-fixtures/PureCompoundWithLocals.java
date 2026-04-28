// SOLVER_UNKNOWN Group F fixture
public class PureCompoundWithLocals {

    //@ requires ((\bigint) x2 - (\bigint) x1) >= Integer.MIN_VALUE;
    //@ requires ((\bigint) x2 - (\bigint) x1) <= Integer.MAX_VALUE;
    //@ requires ((\bigint) y2 - (\bigint) y1) >= Integer.MIN_VALUE;
    //@ requires ((\bigint) y2 - (\bigint) y1) <= Integer.MAX_VALUE;
    //@ requires ((((\bigint) x2 - (\bigint) x1) * ((\bigint) x2 - (\bigint) x1)) + (((\bigint) y2 - (\bigint) y1) * ((\bigint) y2 - (\bigint) y1))) >= Integer.MIN_VALUE;
    //@ requires ((((\bigint) x2 - (\bigint) x1) * ((\bigint) x2 - (\bigint) x1)) + (((\bigint) y2 - (\bigint) y1) * ((\bigint) y2 - (\bigint) y1))) <= Integer.MAX_VALUE;
    //@ requires (((\bigint) x2 - (\bigint) x1) * ((\bigint) x2 - (\bigint) x1)) >= Integer.MIN_VALUE;
    //@ requires (((\bigint) x2 - (\bigint) x1) * ((\bigint) x2 - (\bigint) x1)) <= Integer.MAX_VALUE;
    //@ requires (((\bigint) y2 - (\bigint) y1) * ((\bigint) y2 - (\bigint) y1)) >= Integer.MIN_VALUE;
    //@ requires (((\bigint) y2 - (\bigint) y1) * ((\bigint) y2 - (\bigint) y1)) <= Integer.MAX_VALUE;
    //@ ensures \result == (x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1);
    //@ assignable \nothing;
    /*@ pure @*/
    public int distSquared(int x1, int y1, int x2, int y2) {
        int dx = x2 - x1;
        int dy = y2 - y1;
        return dx * dx + dy * dy;
    }
}
