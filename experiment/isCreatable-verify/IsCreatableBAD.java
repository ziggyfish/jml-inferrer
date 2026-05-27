public class IsCreatableBAD {

    //@ requires true;
    //@ ensures (str == null || str.length() == 0) ==> \result;
    //@ ensures \result ==> (str != null && str.length() > 0);
    //@ assignable \nothing;
    public static boolean isCreatable(final String str) {
        if (str == null || str.length() == 0) {
            return false;
        }
        final char[] chars = str.toCharArray();
        int sz = chars.length;
        boolean hasExp = false;
        boolean hasDecPoint = false;
        boolean allowSigns = false;
        boolean foundDigit = false;
        final int start = chars[0] == '-' || chars[0] == '+' ? 1 : 0;
        if (sz > start + 1 && chars[start] == '0' && str.indexOf('.') < 0) {
            if (chars[start + 1] == 'x' || chars[start + 1] == 'X') {
                int i = start + 2;
                if (i == sz) {
                    return false;
                }
                //@ maintaining start + 2 <= i && i <= chars.length;
                for (; i < chars.length; i++) {
                    if ((chars[i] < '0' || chars[i] > '9') && (chars[i] < 'a' || chars[i] > 'f') && (chars[i] < 'A' || chars[i] > 'F')) {
                        return false;
                    }
                }
                return true;
            }
            if (Character.isDigit(chars[start + 1])) {
                int i = start + 1;
                //@ maintaining start + 1 <= i && i <= chars.length;
                for (; i < chars.length; i++) {
                    if (chars[i] < '0' || chars[i] > '7') {
                        return false;
                    }
                }
                return true;
            }
        }
        sz--;
        int i = start;
        //@ maintaining start <= i && i <= sz + 1;
        //@ maintaining sz == chars.length - 1;
        while (i < sz || i < sz + 1 && allowSigns && !foundDigit) {
            if (chars[i] >= '0' && chars[i] <= '9') {
                foundDigit = true;
                allowSigns = false;
            } else if (chars[i] == '.') {
                if (hasDecPoint || hasExp) {
                    return false;
                }
                hasDecPoint = true;
            } else if (chars[i] == 'e' || chars[i] == 'E') {
                if (hasExp) {
                    return false;
                }
                if (!foundDigit) {
                    return false;
                }
                hasExp = true;
                allowSigns = true;
            } else if (chars[i] == '+' || chars[i] == '-') {
                if (!allowSigns) {
                    return false;
                }
                allowSigns = false;
                foundDigit = false;
            } else {
                return false;
            }
            i++;
        }
        if (i < chars.length) {
            if (chars[i] >= '0' && chars[i] <= '9') {
                return true;
            }
            if (chars[i] == 'e' || chars[i] == 'E') {
                return false;
            }
            if (chars[i] == '.') {
                if (hasDecPoint || hasExp) {
                    return false;
                }
                return foundDigit;
            }
            if (!allowSigns && (chars[i] == 'd' || chars[i] == 'D' || chars[i] == 'f' || chars[i] == 'F')) {
                return foundDigit;
            }
            if (chars[i] == 'l' || chars[i] == 'L') {
                return foundDigit && !hasExp && !hasDecPoint;
            }
            return false;
        }
        return !allowSigns && foundDigit;
    }
}
