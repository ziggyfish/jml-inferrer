# Daikon vs JML-Inferrer — all observed methods

Daikon 5.8.24 (dynamic, hand-written workload) vs JML-Inferrer (static).
Daikon invariants filtered to drop unchanged-field `== orig()` equalities,
`getClass().getName()` noise, and constant-only class fields. Methods are
those Daikon's workload exercised; JML-Inferrer clauses are from its
annotated source. Matching is by simple-class + method + arity (overloads
may occasionally mis-pair).

## `BooleanUtils.and/1`

**Source:**
```java
public static boolean and(final boolean... array) {
    ObjectUtils.requireNonEmpty(array, "array");
    for (final boolean element : array) {
        if (!element) {
            return false;
        }
    }
    return true;
}
public static Boolean and(final Boolean... array) {
    ObjectUtils.requireNonEmpty(array, "array");
    return and(ArrayUtils.toPrimitive(array)) ? Boolean.TRUE : Boolean.FALSE;
}
```

**Daikon:**
  - [ENTER] array != null
  - [ENTER] size(org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[]) == size(array[])
  - [EXIT] (array[] == [1, 1])  <==>  (return == true)
  - [EXIT] (array[] == [1, 1])  ==>  (array[] elements == return)
  - [EXIT] (array[] == [1, 1])  ==>  (array[] elements == true)
  - [EXIT] (array[] one of { [0, 0], [0, 1], [1, 0] })  <==>  (return == false)
  - [EXIT] array[] == [1, 1]
  - [EXIT] array[] elements == return
  - [EXIT] array[] elements == true
  - [EXIT] array[] one of { [0, 0], [0, 1], [1, 0] }
  - [EXIT] return == false
  - [EXIT] return == true
  - [EXIT] return in array[]

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("true")
  - LoopInvariant("array != null")

## `BooleanUtils.compare/2`

**Source:**
```java
public static int compare(final boolean x, final boolean y) {
    if (x == y) {
        return 0;
    }
    return x ? 1 : -1;
}
```

**Daikon:**
  - [ENTER] x == false
  - [EXIT] (return == -1)  <==>  (orig(y) == true)
  - [EXIT] (return == 0)  <==>  (orig(y) == false)
  - [EXIT] orig(y) == true
  - [EXIT] return == -1
  - [EXIT] return == 0
  - [EXIT] return one of { -1, 0 }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("(x != y) && (!(x)) ==> \\result == -1")
  - Ensures("(x != y) && (x) ==> \\result == 1")
  - Ensures("\\result == 1 || \\result == -1")
  - Ensures("x == y ==> \\result == 0")

## `BooleanUtils.isFalse/1`

**Source:**
```java
public static boolean isFalse(final Boolean bool) {
    return Boolean.FALSE.equals(bool);
}
```

**Daikon:**
  - [EXIT] (return == true)  ==>  (orig(bool) in org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[])
  - [EXIT] orig(bool) in org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[]
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Boolean.FALSE.equals(bool)")

## `BooleanUtils.isTrue/1`

**Source:**
```java
public static boolean isTrue(final Boolean bool) {
    return Boolean.TRUE.equals(bool);
}
```

**Daikon:**
  - [EXIT] (return == true)  ==>  (orig(bool) in org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[])
  - [EXIT] orig(bool) in org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[]
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Boolean.TRUE.equals(bool)")

## `BooleanUtils.negate/1`

**Source:**
```java
public static Boolean negate(final Boolean bool) {
    if (bool == null) {
        return null;
    }
    return bool.booleanValue() ? Boolean.FALSE : Boolean.TRUE;
}
```

**Daikon:**
  - [EXIT] (return == null)  <==>  (orig(bool) == null)
  - [EXIT] orig(bool) in org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[]
  - [EXIT] return == null
  - [EXIT] return in org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[]

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("(bool != null) && (!(bool.booleanValue())) ==> \\result == Boolean.TRUE")
  - Ensures("(bool != null) && (bool.booleanValue()) ==> \\result == Boolean.FALSE")
  - Ensures("bool == null ==> \\result == null")
  - Requires("bool != null")

## `BooleanUtils.or/1`

**Source:**
```java
public static boolean or(final boolean... array) {
    ObjectUtils.requireNonEmpty(array, "array");
    for (final boolean element : array) {
        if (element) {
            return true;
        }
    }
    return false;
}
public static Boolean or(final Boolean... array) {
    ObjectUtils.requireNonEmpty(array, "array");
    return or(ArrayUtils.toPrimitive(array)) ? Boolean.TRUE : Boolean.FALSE;
}
```

**Daikon:**
  - [ENTER] array != null
  - [ENTER] size(org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[]) == size(array[])
  - [EXIT] (array[] == [0, 0])  <==>  (return == false)
  - [EXIT] (array[] == [0, 0])  ==>  (array[] elements == false)
  - [EXIT] (array[] == [0, 0])  ==>  (array[] elements == return)
  - [EXIT] (array[] one of { [0, 1], [1, 0], [1, 1] })  <==>  (return == true)
  - [EXIT] array[] == [0, 0]
  - [EXIT] array[] elements == false
  - [EXIT] array[] elements == return
  - [EXIT] array[] one of { [0, 1], [1, 0], [1, 1] }
  - [EXIT] return == false
  - [EXIT] return == true
  - [EXIT] return in array[]

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("true")
  - LoopInvariant("array != null")

## `BooleanUtils.toInteger/1`

**Source:**
```java
public static int toInteger(final boolean bool) {
    return bool ? 1 : 0;
}
```

**Daikon:**
  - [EXIT] return <= size(org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[])-1
  - [EXIT] return one of { 0, 1 }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("!(bool) ==> \\result == 0")
  - Ensures("\\result == 1 || \\result == 0")
  - Ensures("bool ==> \\result == 1")

## `BooleanUtils.toString/3`

**Source:**
```java
public static String toString(final boolean bool, final String trueString, final String falseString) {
    return bool ? trueString : falseString;
}
```

**Daikon:**
  - [ENTER] falseString != null
  - [ENTER] falseString.toString one of { "false", "no" }
  - [ENTER] org.apache.commons.lang3.BooleanUtils.FALSE.toString < trueString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.FALSE.toString <= falseString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.NO.toString < trueString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.NO.toString >= falseString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.OFF.toString < trueString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.OFF.toString > falseString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.ON.toString < trueString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.ON.toString > falseString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.TRUE.toString <= trueString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.TRUE.toString > falseString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.YES.toString > falseString.toString
  - [ENTER] org.apache.commons.lang3.BooleanUtils.YES.toString >= trueString.toString
  - [ENTER] trueString != null
  - [ENTER] trueString.toString > falseString.toString
  - [ENTER] trueString.toString one of { "true", "yes" }
  - [EXIT] falseString.toString <= return.toString
  - [EXIT] falseString.toString one of { "false", "no" }
  - [EXIT] org.apache.commons.lang3.BooleanUtils.FALSE.toString < trueString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.FALSE.toString <= falseString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.FALSE.toString <= return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.NO.toString < trueString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.NO.toString >= falseString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.OFF.toString != return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.OFF.toString < trueString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.OFF.toString > falseString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.ON.toString != return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.ON.toString < trueString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.ON.toString > falseString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.TRUE.toString <= trueString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.TRUE.toString > falseString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.YES.toString > falseString.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.YES.toString >= return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.YES.toString >= trueString.toString
  - [EXIT] return != null
  - [EXIT] trueString.toString > falseString.toString
  - [EXIT] trueString.toString >= return.toString
  - [EXIT] trueString.toString one of { "true", "yes" }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("!(bool) ==> \\result.equals(falseString)")
  - Ensures("\\result != null")
  - Ensures("bool ==> \\result.equals(trueString)")

## `BooleanUtils.toStringTrueFalse/1`

**Source:**
```java
public static String toStringTrueFalse(final boolean bool) {
    return toString(bool, TRUE, FALSE);
}
public static String toStringTrueFalse(final Boolean bool) {
    return toString(bool, TRUE, FALSE, null);
}
```

**Daikon:**
  - [EXIT] org.apache.commons.lang3.BooleanUtils.FALSE.toString <= return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.NO.toString != return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.OFF.toString != return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.ON.toString != return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.TRUE.toString >= return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.YES.toString > return.toString
  - [EXIT] return.toString one of { "false", "true" }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("(bool != null) && (!(bool.booleanValue())) ==> \\result.equals(FALSE)")
  - Ensures("(bool != null) && (!(bool.booleanValue())) ==> \\result.equals(falseString)")
  - Ensures("(bool != null) && (bool.booleanValue()) ==> \\result.equals(TRUE)")
  - Ensures("(bool != null) && (bool.booleanValue()) ==> \\result.equals(trueString)")
  - Ensures("\\result != null")
  - Ensures("\\result.equals(toString(bool, TRUE, FALSE))")
  - Ensures("\\result.equals(toString(bool, TRUE, FALSE, null))")
  - Ensures("bool == null ==> \\result.equals(nullString)")
  - Requires("bool != null")

## `BooleanUtils.toStringYesNo/1`

**Source:**
```java
public static String toStringYesNo(final boolean bool) {
    return toString(bool, YES, NO);
}
public static String toStringYesNo(final Boolean bool) {
    return toString(bool, YES, NO, null);
}
```

**Daikon:**
  - [EXIT] org.apache.commons.lang3.BooleanUtils.FALSE.toString < return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.NO.toString <= return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.OFF.toString != return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.ON.toString != return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.TRUE.toString != return.toString
  - [EXIT] org.apache.commons.lang3.BooleanUtils.YES.toString >= return.toString
  - [EXIT] return.toString one of { "no", "yes" }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("(bool != null) && (!(bool.booleanValue())) ==> \\result.equals(NO)")
  - Ensures("(bool != null) && (!(bool.booleanValue())) ==> \\result.equals(falseString)")
  - Ensures("(bool != null) && (bool.booleanValue()) ==> \\result.equals(YES)")
  - Ensures("(bool != null) && (bool.booleanValue()) ==> \\result.equals(trueString)")
  - Ensures("\\result != null")
  - Ensures("\\result.equals(toString(bool, YES, NO))")
  - Ensures("\\result.equals(toString(bool, YES, NO, null))")
  - Ensures("bool == null ==> \\result.equals(nullString)")
  - Requires("bool != null")

## `BooleanUtils.xor/1`

**Source:**
```java
public static boolean xor(final boolean... array) {
    ObjectUtils.requireNonEmpty(array, "array");
    boolean result = false;
    for (final boolean element : array) {
        result ^= element;
    }
    return result;
}
public static Boolean xor(final Boolean... array) {
    ObjectUtils.requireNonEmpty(array, "array");
    return xor(ArrayUtils.toPrimitive(array)) ? Boolean.TRUE : Boolean.FALSE;
}
```

**Daikon:**
  - [ENTER] array != null
  - [ENTER] size(org.apache.commons.lang3.BooleanUtils.BOOLEAN_LIST[]) == size(array[])
  - [EXIT] (array[] one of { [0, 0], [1, 1] })  <==>  (return == false)
  - [EXIT] (array[] one of { [0, 0], [1, 1] })  ==>  (array[] elements are equal)
  - [EXIT] (array[] one of { [0, 1], [1, 0] })  <==>  (return == true)
  - [EXIT] (array[] one of { [0, 1], [1, 0] })  ==>  (return in array[])
  - [EXIT] array[] elements are equal
  - [EXIT] array[] one of { [0, 0], [1, 1] }
  - [EXIT] array[] one of { [0, 1], [1, 0] }
  - [EXIT] return == false
  - [EXIT] return == true
  - [EXIT] return in array[]

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("true")
  - LoopInvariant("array != null")

## `CharUtils.isAscii/1`

**Source:**
```java
public static boolean isAscii(final char ch) {
    return ch < 128;
}
```

**Daikon:**
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [ENTER] org.apache.commons.lang3.CharUtils.CR != ch
  - [ENTER] org.apache.commons.lang3.CharUtils.LF <= ch
  - [ENTER] org.apache.commons.lang3.CharUtils.NUL < ch
  - [EXIT] (return == false)  <==>  (orig(ch) == 200)
  - [EXIT] (return == true)  <==>  (orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1)
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [EXIT] orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) == 200
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (ch < 128)")

## `CharUtils.isAsciiAlpha/1`

**Source:**
```java
public static boolean isAsciiAlpha(final char ch) {
    return isAsciiAlphaUpper(ch) || isAsciiAlphaLower(ch);
}
```

**Daikon:**
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [ENTER] org.apache.commons.lang3.CharUtils.CR != ch
  - [ENTER] org.apache.commons.lang3.CharUtils.LF <= ch
  - [ENTER] org.apache.commons.lang3.CharUtils.NUL < ch
  - [EXIT] (return == false)  ==>  (orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF])
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.CR < orig(ch))
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.LF < orig(ch))
  - [EXIT] (return == true)  ==>  (orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1])
  - [EXIT] (return == true)  ==>  (orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR])
  - [EXIT] (return == true)  ==>  (orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1)
  - [EXIT] (return == true)  ==>  (orig(ch) <= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF])
  - [EXIT] (return == true)  ==>  (orig(ch) > org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF-1])
  - [EXIT] (return == true)  ==>  (orig(ch) > org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL])
  - [EXIT] (return == true)  ==>  (orig(ch) > size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[]))
  - [EXIT] (return == true)  ==>  (orig(ch) one of { 90, 97 })
  - [EXIT] org.apache.commons.lang3.CharUtils.CR < orig(ch)
  - [EXIT] org.apache.commons.lang3.CharUtils.LF < orig(ch)
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF]
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [EXIT] orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) <= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF]
  - [EXIT] orig(ch) > org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF-1]
  - [EXIT] orig(ch) > org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL]
  - [EXIT] orig(ch) > size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) one of { 90, 97 }
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (isAsciiAlphaUpper(ch) || isAsciiAlphaLower(ch))")

## `CharUtils.isAsciiAlphaLower/1`

**Source:**
```java
public static boolean isAsciiAlphaLower(final char ch) {
    return ch >= 'a' && ch <= 'z';
}
```

**Daikon:**
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [ENTER] org.apache.commons.lang3.CharUtils.CR != ch
  - [ENTER] org.apache.commons.lang3.CharUtils.LF <= ch
  - [ENTER] org.apache.commons.lang3.CharUtils.NUL < ch
  - [EXIT] (return == false)  <==>  (orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF])
  - [EXIT] (return == true)  <==>  (orig(ch) == org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF])
  - [EXIT] (return == true)  ==>  (orig(ch) == 97)
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF]
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [EXIT] orig(ch) == 97
  - [EXIT] orig(ch) == org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF]
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (ch >= 'a' && ch <= 'z')")

## `CharUtils.isAsciiAlphaUpper/1`

**Source:**
```java
public static boolean isAsciiAlphaUpper(final char ch) {
    return ch >= 'A' && ch <= 'Z';
}
```

**Daikon:**
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [ENTER] org.apache.commons.lang3.CharUtils.CR != ch
  - [ENTER] org.apache.commons.lang3.CharUtils.LF <= ch
  - [ENTER] org.apache.commons.lang3.CharUtils.NUL < ch
  - [EXIT] (return == true)  ==>  (orig(ch) == 90)
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [EXIT] orig(ch) == 90
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (ch >= 'A' && ch <= 'Z')")

## `CharUtils.isAsciiAlphanumeric/1`

**Source:**
```java
public static boolean isAsciiAlphanumeric(final char ch) {
    return isAsciiAlpha(ch) || isAsciiNumeric(ch);
}
```

**Daikon:**
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [ENTER] org.apache.commons.lang3.CharUtils.CR != ch
  - [ENTER] org.apache.commons.lang3.CharUtils.LF <= ch
  - [ENTER] org.apache.commons.lang3.CharUtils.NUL < ch
  - [EXIT] (return == false)  ==>  (orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF-1])
  - [EXIT] (return == false)  ==>  (orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF])
  - [EXIT] (return == false)  ==>  (orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL])
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.CR < orig(ch))
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.LF < orig(ch))
  - [EXIT] (return == true)  ==>  (orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1])
  - [EXIT] (return == true)  ==>  (orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR])
  - [EXIT] (return == true)  ==>  (orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1)
  - [EXIT] (return == true)  ==>  (orig(ch) <= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF])
  - [EXIT] (return == true)  ==>  (orig(ch) > size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[]))
  - [EXIT] (return == true)  ==>  (orig(ch) >= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL])
  - [EXIT] org.apache.commons.lang3.CharUtils.CR < orig(ch)
  - [EXIT] org.apache.commons.lang3.CharUtils.LF < orig(ch)
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL]
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [EXIT] orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) <= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF]
  - [EXIT] orig(ch) > size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) >= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL]
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (isAsciiAlpha(ch) || isAsciiNumeric(ch))")

## `CharUtils.isAsciiControl/1`

**Source:**
```java
public static boolean isAsciiControl(final char ch) {
    return ch < 32 || ch == 127;
}
```

**Daikon:**
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [ENTER] org.apache.commons.lang3.CharUtils.CR != ch
  - [ENTER] org.apache.commons.lang3.CharUtils.LF <= ch
  - [ENTER] org.apache.commons.lang3.CharUtils.NUL < ch
  - [EXIT] (return == false)  <==>  (org.apache.commons.lang3.CharUtils.CR < orig(ch))
  - [EXIT] (return == false)  <==>  (org.apache.commons.lang3.CharUtils.LF < orig(ch))
  - [EXIT] (return == false)  <==>  (orig(ch) > size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[]))
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.HEX_DIGITS[ch-1] == 57)
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.HEX_DIGITS[ch] == 97)
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.HEX_DIGITS[orig(ch)-1] == 57)
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.HEX_DIGITS[orig(ch)] == 97)
  - [EXIT] (return == true)  ==>  (orig(org.apache.commons.lang3.CharUtils.HEX_DIGITS[ch-1]) == 57)
  - [EXIT] (return == true)  ==>  (orig(org.apache.commons.lang3.CharUtils.HEX_DIGITS[ch]) == 97)
  - [EXIT] (return == true)  ==>  (orig(org.apache.commons.lang3.CharUtils.HEX_DIGITS[post(ch)-1]) == 57)
  - [EXIT] (return == true)  ==>  (orig(org.apache.commons.lang3.CharUtils.HEX_DIGITS[post(ch)]) == 97)
  - [EXIT] org.apache.commons.lang3.CharUtils.CR < orig(ch)
  - [EXIT] org.apache.commons.lang3.CharUtils.LF < orig(ch)
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [EXIT] orig(ch) > size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (ch < 32 || ch == 127)")

## `CharUtils.isAsciiNumeric/1`

**Source:**
```java
public static boolean isAsciiNumeric(final char ch) {
    return ch >= '0' && ch <= '9';
}
```

**Daikon:**
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [ENTER] org.apache.commons.lang3.CharUtils.CR != ch
  - [ENTER] org.apache.commons.lang3.CharUtils.LF <= ch
  - [ENTER] org.apache.commons.lang3.CharUtils.NUL < ch
  - [EXIT] (return == false)  ==>  (orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF-1])
  - [EXIT] (return == false)  ==>  (orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL])
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.CR < orig(ch))
  - [EXIT] (return == true)  ==>  (org.apache.commons.lang3.CharUtils.LF < orig(ch))
  - [EXIT] (return == true)  ==>  (orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1])
  - [EXIT] (return == true)  ==>  (orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR])
  - [EXIT] (return == true)  ==>  (orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF])
  - [EXIT] (return == true)  ==>  (orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1)
  - [EXIT] (return == true)  ==>  (orig(ch) <= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF-1])
  - [EXIT] (return == true)  ==>  (orig(ch) > size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[]))
  - [EXIT] (return == true)  ==>  (orig(ch) >= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL])
  - [EXIT] (return == true)  ==>  (orig(ch) in org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] org.apache.commons.lang3.CharUtils.CR < orig(ch)
  - [EXIT] org.apache.commons.lang3.CharUtils.LF < orig(ch)
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL]
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [EXIT] orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) < org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF]
  - [EXIT] orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) <= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.LF-1]
  - [EXIT] orig(ch) > size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) >= org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.NUL]
  - [EXIT] orig(ch) in org.apache.commons.lang3.CharUtils.HEX_DIGITS[]
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (ch >= '0' && ch <= '9')")

## `CharUtils.toIntValue/1`

**Source:**
```java
public static int toIntValue(final char ch) {
    if (!isAsciiNumeric(ch)) {
        throw new IllegalArgumentException("The character " + ch + " is not in the range '0' - '9'");
    }
    return ch - 48;
}
public static int toIntValue(final Character ch) {
    return toIntValue(toChar(ch));
}
```

**Daikon:**
  - [ENTER] ch in org.apache.commons.lang3.CharUtils.HEX_DIGITS[]
  - [ENTER] ch one of { 48, 57 }
  - [EXIT] orig(ch) == org.apache.commons.lang3.CharUtils.HEX_DIGITS[return]
  - [EXIT] return one of { 0, 9 }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("!(isAsciiNumeric(toChar(ch))) ==> \\result == defaultValue")
  - Ensures("\\result < ch")
  - Ensures("\\result == ch - 48")
  - Ensures("\\result == toIntValue(toChar(ch))")
  - Ensures("isAsciiNumeric(toChar(ch)) ==> \\result == toChar(ch) - 48")
  - Requires("((\\bigint) ch - (\\bigint) 48) >= Integer.MIN_VALUE")
  - Requires("((\\bigint) toChar(ch) - (\\bigint) 48) >= Integer.MIN_VALUE")
  - Requires("ch != null")
  - Requires("ch.length() > 0")
  - Requires("isAsciiNumeric(ch)")
  - Signals("IllegalArgumentException when !isAsciiNumeric(ch)")

## `CharUtils.toString/1`

**Source:**
```java
public static String toString(final char ch) {
    if (ch < CHAR_STRING_ARRAY.length) {
        return CHAR_STRING_ARRAY[ch];
    }
    return String.valueOf(ch);
}
public static String toString(final Character ch) {
    return ch != null ? toString(ch.charValue()) : null;
}
```

**Daikon:**
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [ENTER] ch != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [ENTER] ch != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [ENTER] org.apache.commons.lang3.CharUtils.CR != ch
  - [ENTER] org.apache.commons.lang3.CharUtils.LF <= ch
  - [ENTER] org.apache.commons.lang3.CharUtils.NUL < ch
  - [EXIT] (orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1)  ==>  (return == org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[ch])
  - [EXIT] (orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1)  ==>  (return == org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[orig(ch)])
  - [EXIT] (orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1)  ==>  (return.toString in org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[].toString)
  - [EXIT] (orig(ch) == 200)  ==>  (return.toString == "\310")
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR-1]
  - [EXIT] orig(ch) != org.apache.commons.lang3.CharUtils.HEX_DIGITS[org.apache.commons.lang3.CharUtils.CR]
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])
  - [EXIT] orig(ch) != size(org.apache.commons.lang3.CharUtils.HEX_DIGITS[])-1
  - [EXIT] orig(ch) < size(org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[])-1
  - [EXIT] orig(ch) == 200
  - [EXIT] return != null
  - [EXIT] return == org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[orig(ch)]
  - [EXIT] return.toString == "\310"
  - [EXIT] return.toString in org.apache.commons.lang3.CharUtils.CHAR_STRING_ARRAY[].toString

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("ch != null ==> \\result != null")
  - Ensures("ch < CHAR_STRING_ARRAY.length ==> \\result.equals(CHAR_STRING_ARRAY[ch])")
  - Ensures("ch == null ==> \\result.equals(null)")
  - Ensures("ch >= CHAR_STRING_ARRAY.length ==> \\result.equals(String.valueOf(ch))")
  - Requires("ch != null")
  - Requires("this.CHAR_STRING_ARRAY != null")

## `ImmutablePair.getLeft/0`

**Source:**
```java
@Override
public L getLeft() {
    return left;
}
```

**Daikon:**
  - [ENTER] this.left != null
  - [ENTER] this.right != null
  - [EXIT] return != null
  - [EXIT] this.left == return
  - [EXIT] this.right != null

**JML-Inferrer:**
  - (no matching clause found)

## `ImmutablePair.getRight/0`

**Source:**
```java
@Override
public R getRight() {
    return right;
}
```

**Daikon:**
  - [ENTER] this.left != null
  - [ENTER] this.right != null
  - [EXIT] return != null
  - [EXIT] this.left != null
  - [EXIT] this.right == return

**JML-Inferrer:**
  - (no matching clause found)

## `ImmutablePair.of/2`

**Source:**
```java
public static <L, R> ImmutablePair<L, R> of(final L left, final R right) {
    return left != null || right != null ? new ImmutablePair<>(left, right) : nullPair();
}
```

**Daikon:**
  - [ENTER] left != null
  - [ENTER] right != null
  - [EXIT] return != null
  - [EXIT] return.left != null
  - [EXIT] return.right != null

**JML-Inferrer:**
  - (no matching clause found)

## `MutableBoolean.booleanValue/0`

**Source:**
```java
public boolean booleanValue() {
    return value;
}
```

**Daikon:**
  - [EXIT] return == false
  - [EXIT] return == true
  - [EXIT] this.value == return

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == this.value")

## `MutableBoolean.compareTo/1`

**Source:**
```java
@Override
public int compareTo(final MutableBoolean other) {
    return BooleanUtils.compare(this.value, other.value);
}
```

**Daikon:**
  - [ENTER] this.value == false
  - [EXIT] return one of { -1, 0 }
  - [EXIT] this.value == false

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result >= -1 && \\result <= 1 || \\result < -1 || \\result > 1")
  - Requires("other != null")

## `MutableBoolean.isFalse/0`

**Source:**
```java
public boolean isFalse() {
    return !value;
}
```

**Daikon:**
  - [EXIT] (this.value == false)  <==>  (return == true)
  - [EXIT] (this.value == true)  <==>  (return == false)
  - [EXIT] return == false
  - [EXIT] return == true
  - [EXIT] this.value == false
  - [EXIT] this.value == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == !value")

## `MutableBoolean.isTrue/0`

**Source:**
```java
public boolean isTrue() {
    return value;
}
```

**Daikon:**
  - [EXIT] return == false
  - [EXIT] return == true
  - [EXIT] this.value == return

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == this.value")

## `MutableBoolean.setFalse/0`

**Source:**
```java
public void setFalse() {
    this.value = false;
}
```

**Daikon:**
  - [ENTER] this.value == true
  - [EXIT] this.value == false

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == false")

## `MutableBoolean.setTrue/0`

**Source:**
```java
public void setTrue() {
    this.value = true;
}
```

**Daikon:**
  - [EXIT] this.value == true

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == true")

## `MutableDouble.add/1`

**Source:**
```java
public void add(final double operand) {
    this.value += operand;
}
public void add(final Number operand) {
    this.value += operand.doubleValue();
}
```

**Daikon:**
  - [ENTER] operand == 2.0
  - [ENTER] this.value != operand
  - [EXIT] this.value - orig(this.value) - 2 == 0

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == \\old(this.value) + operand")
  - Ensures("this.value == \\old(this.value) + operand.doubleValue()")
  - Requires("operand != null")

## `MutableDouble.compareTo/1`

**Source:**
```java
@Override
public int compareTo(final MutableDouble other) {
    return Double.compare(this.value, other.value);
}
```

**Daikon:**
  - [ENTER] other != null
  - [ENTER] this.value - other.value - 1 == 0
  - [EXIT] return == 1
  - [EXIT] this.value - other.value - 1 == 0

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Double.compare(this.value, other.value)")
  - Ensures("\\result >= -1 && \\result <= 1 || \\result < -1 || \\result > 1")
  - Requires("other != null")

## `MutableDouble.doubleValue/0`

**Source:**
```java
@Override
public double doubleValue() {
    return value;
}
```

**Daikon:**
  - [EXIT] this.value == return

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == this.value")

## `MutableDouble.increment/0`

**Source:**
```java
public void increment() {
    value++;
}
```

**Daikon:**
  - [EXIT] this.value - orig(this.value) - 1 == 0

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == \\old(this.value) + 1")

## `MutableDouble.intValue/0`

**Source:**
```java
@Override
public int intValue() {
    return (int) value;
}
```

**Daikon:**
  - [EXIT] org.apache.commons.lang3.mutable.MutableDouble.serialVersionUID > return
  - [EXIT] return >= 0

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (int) value")

## `MutableDouble.isNaN/0`

**Source:**
```java
public boolean isNaN() {
    return Double.isNaN(value);
}
```

**Daikon:**
  - [EXIT] return == false

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Double.isNaN(value)")

## `MutableDouble.setValue/1`

**Source:**
```java
public void setValue(final double value) {
    this.value = value;
}
@Override
public void setValue(final Number value) {
    this.value = value.doubleValue();
}
```

**Daikon:**
  - [ENTER] this.value - value - 1 == 0
  - [EXIT] this.value - orig(this.value) + 1 == 0

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == value")
  - Requires("value != null")

## `MutableDouble.subtract/1`

**Source:**
```java
public void subtract(final double operand) {
    this.value -= operand;
}
public void subtract(final Number operand) {
    this.value -= operand.doubleValue();
}
```

**Daikon:**
  - [ENTER] operand == 1.0
  - [ENTER] this.value != operand
  - [EXIT] this.value - orig(this.value) + 1 == 0

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == \\old(this.value) - operand")
  - Ensures("this.value == \\old(this.value) - operand.doubleValue()")
  - Requires("operand != null")

## `MutableInt.add/1`

**Source:**
```java
public void add(final int operand) {
    this.value += operand;
}
public void add(final Number operand) {
    this.value += operand.intValue();
}
```

**Daikon:**
  - [ENTER] operand == 5
  - [ENTER] this.value != operand
  - [EXIT] this.value - orig(this.value) - 5 == 0

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == \\old(this.value) + operand")
  - Ensures("this.value == \\old(this.value) + operand.intValue()")
  - Requires("((\\bigint) this.value + (\\bigint) operand) <= Integer.MAX_VALUE")
  - Requires("((\\bigint) this.value + (\\bigint) operand) >= Integer.MIN_VALUE")
  - Requires("operand != null")

## `MutableInt.compareTo/1`

**Source:**
```java
@Override
public int compareTo(final MutableInt other) {
    return NumberUtils.compare(this.value, other.value);
}
```

**Daikon:**
  - [ENTER] org.apache.commons.lang3.mutable.MutableInt.serialVersionUID > other.value
  - [ENTER] other != null
  - [ENTER] this.value - 2 * other.value == 0
  - [EXIT] org.apache.commons.lang3.mutable.MutableInt.serialVersionUID > other.value
  - [EXIT] org.apache.commons.lang3.mutable.MutableInt.serialVersionUID > return
  - [EXIT] return one of { -1, 0, 1 }
  - [EXIT] this.value - 2 * other.value == 0

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Integer.compare(this.value, other.value)")
  - Ensures("\\result >= -1 && \\result <= 1 || \\result < -1 || \\result > 1")
  - Requires("other != null")

## `MutableInt.decrement/0`

**Source:**
```java
public void decrement() {
    value--;
}
```

**Daikon:**
  - [EXIT] this.value - orig(this.value) + 1 == 0

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == \\old(this.value) - 1")
  - Requires("this.value > Integer.MIN_VALUE")

## `MutableInt.getValue/0`

**Source:**
```java
@Override
public Integer getValue() {
    return Integer.valueOf(this.value);
}
```

**Daikon:**
  - [EXIT] return != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result == Integer.valueOf(this.value)")

## `MutableInt.increment/0`

**Source:**
```java
public void increment() {
    value++;
}
```

**Daikon:**
  - [EXIT] this.value - orig(this.value) - 1 == 0

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == \\old(this.value) + 1")
  - Requires("this.value < Integer.MAX_VALUE")

## `MutableInt.intValue/0`

**Source:**
```java
@Override
public int intValue() {
    return value;
}
```

**Daikon:**
  - [EXIT] org.apache.commons.lang3.mutable.MutableInt.serialVersionUID > return
  - [EXIT] this.value == return

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (int) value")
  - Ensures("\\result == this.value")

## `MutableInt.setValue/1`

**Source:**
```java
public void setValue(final int value) {
    this.value = value;
}
@Override
public void setValue(final Number value) {
    this.value = value.intValue();
}
```

**Daikon:**
  - [ENTER] 2 * this.value - 2 * value - 4 == 0
  - [ENTER] org.apache.commons.lang3.mutable.MutableInt.serialVersionUID > value
  - [ENTER] this.value != value
  - [EXIT] this.value != orig(this.value)
  - [EXIT] this.value - 2 * orig(this.value) + 4 == 0

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == value")
  - Requires("value != null")

## `MutableInt.subtract/1`

**Source:**
```java
public void subtract(final int operand) {
    this.value -= operand;
}
public void subtract(final Number operand) {
    this.value -= operand.intValue();
}
```

**Daikon:**
  - [ENTER] operand == 3
  - [ENTER] this.value != operand
  - [EXIT] this.value - orig(this.value) + 3 == 0

**JML-Inferrer:**
  - Assignable("this.value")
  - Ensures("this.value == \\old(this.value) - operand")
  - Ensures("this.value == \\old(this.value) - operand.intValue()")
  - Requires("((\\bigint) this.value - (\\bigint) operand) <= Integer.MAX_VALUE")
  - Requires("((\\bigint) this.value - (\\bigint) operand) >= Integer.MIN_VALUE")
  - Requires("operand != null")

## `MutableInt.toInteger/0`

**Source:**
```java
public Integer toInteger() {
    return Integer.valueOf(intValue());
}
```

**Daikon:**
  - [EXIT] return != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result == Integer.valueOf(intValue())")

## `MutablePair.MutablePair/2`

**Daikon:**
  - [ENTER] left != null
  - [ENTER] right != null

**JML-Inferrer:**
  - (no matching clause found)

## `MutablePair.getLeft/0`

**Source:**
```java
@Override
public L getLeft() {
    return left;
}
```

**Daikon:**
  - [EXIT] return != null
  - [EXIT] this.left == return

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == this.left")

## `MutablePair.getRight/0`

**Source:**
```java
@Override
public R getRight() {
    return right;
}
```

**Daikon:**
  - [EXIT] return != null
  - [EXIT] this.right == return

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == this.right")

## `MutablePair.of/2`

**Source:**
```java
public static <L, R> MutablePair<L, R> of(final L left, final R right) {
    return new MutablePair<>(left, right);
}
```

**Daikon:**
  - [ENTER] left != null
  - [ENTER] right != null
  - [EXIT] return != null
  - [EXIT] return.left != null
  - [EXIT] return.right != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Requires("pair != null")

## `MutablePair.setLeft/1`

**Source:**
```java
public void setLeft(final L left) {
    this.left = left;
}
```

**Daikon:**
  - [ENTER] left != null

**JML-Inferrer:**
  - Assignable("this.left")
  - Ensures("this.left == left")

## `MutablePair.setRight/1`

**Source:**
```java
public void setRight(final R right) {
    this.right = right;
}
```

**Daikon:**
  - [ENTER] right != null

**JML-Inferrer:**
  - Assignable("this.right")
  - Ensures("this.right == right")

## `MutablePair.setValue/1`

**Source:**
```java
@Override
public R setValue(final R value) {
    final R result = getRight();
    setRight(value);
    return result;
}
```

**Daikon:**
  - [ENTER] value != null
  - [EXIT] return != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result == getRight()")

## `NumberUtils.compare/2`

**Source:**
```java
public static int compare(final byte x, final byte y) {
    return x - y;
}
public static int compare(final int x, final int y) {
    if (x == y) {
        return 0;
    }
    return x < y ? -1 : 1;
}
public static int compare(final long x, final long y) {
    if (x == y) {
        return 0;
    }
    return x < y ? -1 : 1;
}
public static int compare(final short x, final short y) {
    if (x == y) {
        return 0;
    }
    return x < y ? -1 : 1;
}
```

**Daikon:**
  - [ENTER] y >= -1
  - [EXIT] return one of { -1, 0, 1 }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Byte.compare(x, y)")
  - Ensures("\\result == Integer.compare(x, y)")
  - Ensures("\\result == Long.compare(x, y)")
  - Ensures("\\result == Short.compare(x, y)")

## `NumberUtils.isCreatable/1`

**Source:**
```java
public static boolean isCreatable(final String str) {
    if (StringUtils.isEmpty(str)) {
        return false;
    }
    final char[] chars = str.toCharArray();
    int sz = chars.length;
    boolean hasExp = false;
    boolean hasDecPoint = false;
    boolean allowSigns = false;
    boolean foundDigit = false;
    final int start = chars[0] == '-' || chars[0] == '+' ? 1 : 0;
    if (sz > start + 1 && chars[start] == '0' && !StringUtils.contains(str, '.')) {
        if (chars[start + 1] == 'x' || chars[start + 1] == 'X') {
            int i = start + 2;
            if (i == sz) {
                return false;
            }
            for (; i < chars.length; i++) {
                if ((chars[i] < '0' || chars[i] > '9') && (chars[i] < 'a' || chars[i] > 'f') && (chars[i] < 'A' || chars[i] > 'F')) {
                    return false;
                }
            }
            return true;
        }
        if (Character.isDigit(chars[start + 1])) {
            int i = start + 1;
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
```

**Daikon:**
  - [EXIT] (return == false)  ==>  (str.toString one of { "", "  9 ", "abc" })
  - [EXIT] (return == true)  ==>  (orig(str) != null)
  - [EXIT] orig(str) != null
  - [EXIT] return == false
  - [EXIT] return == true
  - [EXIT] str.toString == ""
  - [EXIT] str.toString one of { "  9 ", "abc" }
  - [EXIT] str.toString one of { "", "  9 ", "abc" }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("true")
  - LoopInvariant("str != null")
  - Requires("str != null")

## `NumberUtils.isDigits/1`

**Source:**
```java
public static boolean isDigits(final String str) {
    return StringUtils.isNumeric(str);
}
```

**Daikon:**
  - [EXIT] (return == true)  ==>  (orig(str) != null)
  - [EXIT] orig(str) != null
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("true")

## `NumberUtils.isParsable/1`

**Source:**
```java
public static boolean isParsable(final String str) {
    if (StringUtils.isEmpty(str)) {
        return false;
    }
    if (str.charAt(str.length() - 1) == '.') {
        return false;
    }
    if (str.charAt(0) == '-') {
        if (str.length() == 1) {
            return false;
        }
        return withDecimalsParsing(str, 1);
    }
    return withDecimalsParsing(str, 0);
}
```

**Daikon:**
  - [EXIT] (return == false)  ==>  (str.toString one of { "  9 ", "abc" })
  - [EXIT] (return == false)  ==>  (str.toString one of { "", "  9 ", "abc" })
  - [EXIT] (return == true)  ==>  (orig(str) != null)
  - [EXIT] orig(str) != null
  - [EXIT] return == false
  - [EXIT] return == true
  - [EXIT] str.toString == ""
  - [EXIT] str.toString == "-1"
  - [EXIT] str.toString one of { "  9 ", "abc" }
  - [EXIT] str.toString one of { "", "  9 ", "abc" }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("true")
  - Requires("str != null")

## `NumberUtils.isSign/1`

**Daikon:**
  - [EXIT] (return == true)  ==>  (orig(ch) == 45)
  - [EXIT] orig(ch) == 45
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == (ch == '-' || ch == '+')")

## `NumberUtils.max/1`

**Source:**
```java
public static byte max(final byte... array) {
    validateArray(array);
    byte max = array[0];
    for (int i = 1; i < array.length; i++) {
        if (array[i] > max) {
            max = array[i];
        }
    }
    return max;
}
public static double max(final double... array) {
    validateArray(array);
    double max = array[0];
    for (int j = 1; j < array.length; j++) {
        if (Double.isNaN(array[j])) {
            return Double.NaN;
        }
        if (array[j] > max) {
            max = array[j];
        }
    }
    return max;
}
public static float max(final float... array) {
    validateArray(array);
    float max = array[0];
    for (int j = 1; j < array.length; j++) {
        if (Float.isNaN(array[j])) {
            return Float.NaN;
        }
        if (array[j] > max) {
            max = array[j];
        }
    }
    return max;
}
public static int max(final int... array) {
    validateArray(array);
    int max = array[0];
    for (int j = 1; j < array.length; j++) {
        if (array[j] > max) {
            max = array[j];
        }
    }
    return max;
}
public static long max(final long... array) {
    validateArray(array);
    long max = array[0];
    for (int j = 1; j < array.length; j++) {
        if (array[j] > max) {
            max = array[j];
        }
    }
    return max;
}
public static short max(final short... array) {
    validateArray(array);
    short max = array[0];
    for (int i = 1; i < array.length; i++) {
        if (array[i] > max) {
            max = array[i];
        }
    }
    return max;
}
```

**Daikon:**
  - [ENTER] array != null
  - [ENTER] size(array[]) == 2
  - [EXIT] array[] elements <= return
  - [EXIT] return != orig(size(array[]))
  - [EXIT] return >= -1
  - [EXIT] return in array[]

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("(\\exists int k; 0 <= k && k < array.length; \\result == array[k])")
  - Ensures("(\\forall int k; 0 <= k && k < array.length; \\result >= array[k])")
  - Ensures("true")
  - LoopInvariant("i <= array.length")
  - LoopInvariant("i >= 1")
  - LoopInvariant("j <= array.length")
  - LoopInvariant("j >= 1")
  - LoopInvariant(value = "(\\exists int k; 0 <= k && k < i; max == array[k])", loopLine = 1056)
  - LoopInvariant(value = "(\\exists int k; 0 <= k && k < i; max == array[k])", loopLine = 815)
  - LoopInvariant(value = "(\\exists int k; 0 <= k && k < j; max == array[k])", loopLine = 1015)
  - LoopInvariant(value = "(\\exists int k; 0 <= k && k < j; max == array[k])", loopLine = 975)
  - LoopInvariant(value = "(\\forall int k; 0 <= k && k < i; max >= array[k])", loopLine = 1056)
  - LoopInvariant(value = "(\\forall int k; 0 <= k && k < i; max >= array[k])", loopLine = 815)
  - LoopInvariant(value = "(\\forall int k; 0 <= k && k < j; max >= array[k])", loopLine = 1015)
  - LoopInvariant(value = "(\\forall int k; 0 <= k && k < j; max >= array[k])", loopLine = 975)
  - Requires("1 <= array.length")

## `NumberUtils.max/3`

**Source:**
```java
public static byte max(byte a, final byte b, final byte c) {
    if (b > a) {
        a = b;
    }
    if (c > a) {
        a = c;
    }
    return a;
}
public static double max(final double a, final double b, final double c) {
    return Math.max(Math.max(a, b), c);
}
public static float max(final float a, final float b, final float c) {
    return Math.max(Math.max(a, b), c);
}
public static int max(int a, final int b, final int c) {
    if (b > a) {
        a = b;
    }
    if (c > a) {
        a = c;
    }
    return a;
}
public static long max(long a, final long b, final long c) {
    if (b > a) {
        a = b;
    }
    if (c > a) {
        a = c;
    }
    return a;
}
public static short max(short a, final short b, final short c) {
    if (b > a) {
        a = b;
    }
    if (c > a) {
        a = c;
    }
    return a;
}
```

**Daikon:**
  - [ENTER] a != c
  - [ENTER] b != c
  - [ENTER] b >= -1
  - [ENTER] c == 5
  - [EXIT] return >= orig(a)
  - [EXIT] return >= orig(b)
  - [EXIT] return >= orig(c)

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Math.max(Math.max(a, b), c)")
  - Ensures("true")
  - Requires("b > a")
  - Requires("c > a")

## `NumberUtils.min/1`

**Source:**
```java
public static byte min(final byte... array) {
    validateArray(array);
    byte min = array[0];
    for (int i = 1; i < array.length; i++) {
        if (array[i] < min) {
            min = array[i];
        }
    }
    return min;
}
public static double min(final double... array) {
    validateArray(array);
    double min = array[0];
    for (int i = 1; i < array.length; i++) {
        if (Double.isNaN(array[i])) {
            return Double.NaN;
        }
        if (array[i] < min) {
            min = array[i];
        }
    }
    return min;
}
public static float min(final float... array) {
    validateArray(array);
    float min = array[0];
    for (int i = 1; i < array.length; i++) {
        if (Float.isNaN(array[i])) {
            return Float.NaN;
        }
        if (array[i] < min) {
            min = array[i];
        }
    }
    return min;
}
public static int min(final int... array) {
    validateArray(array);
    int min = array[0];
    for (int j = 1; j < array.length; j++) {
        if (array[j] < min) {
            min = array[j];
        }
    }
    return min;
}
public static long min(final long... array) {
    validateArray(array);
    long min = array[0];
    for (int i = 1; i < array.length; i++) {
        if (array[i] < min) {
            min = array[i];
        }
    }
    return min;
}
public static short min(final short... array) {
    validateArray(array);
    short min = array[0];
    for (int i = 1; i < array.length; i++) {
        if (array[i] < min) {
            min = array[i];
        }
    }
    return min;
}
```

**Daikon:**
  - [ENTER] array != null
  - [ENTER] size(array[]) == 2
  - [EXIT] array[] elements >= return
  - [EXIT] return != orig(size(array[]))
  - [EXIT] return in array[]

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("(\\exists int k; 0 <= k && k < array.length; \\result == array[k])")
  - Ensures("(\\forall int k; 0 <= k && k < array.length; \\result <= array[k])")
  - Ensures("true")
  - LoopInvariant("i <= array.length")
  - LoopInvariant("i >= 1")
  - LoopInvariant("j <= array.length")
  - LoopInvariant("j >= 1")
  - LoopInvariant(value = "(\\exists int k; 0 <= k && k < i; min == array[k])", loopLine = 1096)
  - LoopInvariant(value = "(\\exists int k; 0 <= k && k < i; min == array[k])", loopLine = 1262)
  - LoopInvariant(value = "(\\exists int k; 0 <= k && k < i; min == array[k])", loopLine = 1303)
  - LoopInvariant(value = "(\\exists int k; 0 <= k && k < j; min == array[k])", loopLine = 1222)
  - LoopInvariant(value = "(\\forall int k; 0 <= k && k < i; min <= array[k])", loopLine = 1096)
  - LoopInvariant(value = "(\\forall int k; 0 <= k && k < i; min <= array[k])", loopLine = 1262)
  - LoopInvariant(value = "(\\forall int k; 0 <= k && k < i; min <= array[k])", loopLine = 1303)
  - LoopInvariant(value = "(\\forall int k; 0 <= k && k < j; min <= array[k])", loopLine = 1222)
  - Requires("1 <= array.length")

## `NumberUtils.min/3`

**Source:**
```java
public static byte min(byte a, final byte b, final byte c) {
    if (b < a) {
        a = b;
    }
    if (c < a) {
        a = c;
    }
    return a;
}
public static double min(final double a, final double b, final double c) {
    return Math.min(Math.min(a, b), c);
}
public static float min(final float a, final float b, final float c) {
    return Math.min(Math.min(a, b), c);
}
public static int min(int a, final int b, final int c) {
    if (b < a) {
        a = b;
    }
    if (c < a) {
        a = c;
    }
    return a;
}
public static long min(long a, final long b, final long c) {
    if (b < a) {
        a = b;
    }
    if (c < a) {
        a = c;
    }
    return a;
}
public static short min(short a, final short b, final short c) {
    if (b < a) {
        a = b;
    }
    if (c < a) {
        a = c;
    }
    return a;
}
```

**Daikon:**
  - [ENTER] a != c
  - [ENTER] b != c
  - [ENTER] b >= -1
  - [ENTER] c == 5
  - [EXIT] return <= orig(a)
  - [EXIT] return <= orig(b)
  - [EXIT] return <= orig(c)

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Math.min(Math.min(a, b), c)")
  - Ensures("true")
  - Requires("b < a")
  - Requires("c < a")

## `NumberUtils.toDouble/1`

**Source:**
```java
public static double toDouble(final BigDecimal value) {
    return toDouble(value, 0.0d);
}
public static double toDouble(final String str) {
    return toDouble(str, 0.0d);
}
```

**Daikon:**
  - [EXIT] return >= -1.0

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("true")
  - Ensures("value != null ==> \\result != null")
  - Ensures("value != null ==> \\result == value.doubleValue()")
  - Ensures("value == null ==> \\result == defaultValue")
  - Requires("str != null")

## `NumberUtils.toDouble/2`

**Source:**
```java
public static double toDouble(final BigDecimal value, final double defaultValue) {
    return value == null ? defaultValue : value.doubleValue();
}
public static double toDouble(final String str, final double defaultValue) {
    if (str == null) {
        return defaultValue;
    }
    try {
        return Double.parseDouble(str);
    } catch (final NumberFormatException nfe) {
        return defaultValue;
    }
}
```

**Daikon:**
  - [ENTER] defaultValue == 0.0
  - [EXIT] orig(str) != null
  - [EXIT] return == 0.0
  - [EXIT] return >= -1.0
  - [EXIT] str.toString one of { "", "abc" }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Double.parseDouble(str)")
  - Ensures("value != null ==> \\result != null")
  - Ensures("value != null ==> \\result == value.doubleValue()")
  - Ensures("value == null ==> \\result == defaultValue")
  - Requires("value != null")
  - Signals("on RuntimeException returns defaultValue")

## `NumberUtils.toInt/1`

**Source:**
```java
public static int toInt(final String str) {
    return toInt(str, 0);
}
```

**Daikon:**
  - [EXIT] return >= -1

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == toInt(str, 0)")

## `NumberUtils.toInt/2`

**Source:**
```java
public static int toInt(final String str, final int defaultValue) {
    if (str == null) {
        return defaultValue;
    }
    try {
        return Integer.parseInt(str);
    } catch (final NumberFormatException nfe) {
        return defaultValue;
    }
}
```

**Daikon:**
  - [ENTER] defaultValue one of { 0, 99 }
  - [EXIT] orig(str) != null
  - [EXIT] return >= -1
  - [EXIT] return one of { 0, 99 }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Integer.parseInt(str)")
  - Signals("on RuntimeException returns defaultValue")

## `NumberUtils.toLong/1`

**Source:**
```java
public static long toLong(final String str) {
    return toLong(str, 0L);
}
```

**Daikon:**
  - [EXIT] return >= -1

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("true")

## `NumberUtils.toLong/2`

**Source:**
```java
public static long toLong(final String str, final long defaultValue) {
    if (str == null) {
        return defaultValue;
    }
    try {
        return Long.parseLong(str);
    } catch (final NumberFormatException nfe) {
        return defaultValue;
    }
}
```

**Daikon:**
  - [ENTER] defaultValue == 0
  - [EXIT] orig(str) != null
  - [EXIT] return == 0
  - [EXIT] return >= -1

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == Long.parseLong(str)")
  - Signals("on RuntimeException returns defaultValue")

## `NumberUtils.validateArray/1`

**Source:**
```java
private static void validateArray(final Object array) {
    Objects.requireNonNull(array, "array");
    Validate.isTrue(Array.getLength(array) != 0, "Array cannot be empty.");
}
```

**Daikon:**
  - [ENTER] array != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Requires("array != null")

## `NumberUtils.withDecimalsParsing/2`

**Source:**
```java
private static boolean withDecimalsParsing(final String str, final int beginIdx) {
    int decimalPoints = 0;
    for (int i = beginIdx; i < str.length(); i++) {
        final boolean isDecimalPoint = str.charAt(i) == '.';
        if (isDecimalPoint) {
            decimalPoints++;
        }
        if (decimalPoints > 1) {
            return false;
        }
        if (!isDecimalPoint && !Character.isDigit(str.charAt(i))) {
            return false;
        }
    }
    return true;
}
```

**Daikon:**
  - [ENTER] beginIdx one of { 0, 1 }
  - [ENTER] str != null
  - [EXIT] (return == false)  ==>  (orig(beginIdx) == 0)
  - [EXIT] (return == false)  ==>  (str.toString one of { "  9 ", "abc" })
  - [EXIT] (return == true)  ==>  (orig(beginIdx) one of { 0, 1 })
  - [EXIT] orig(beginIdx) == 0
  - [EXIT] return == false
  - [EXIT] return == true
  - [EXIT] str.toString one of { "  9 ", "abc" }

**JML-Inferrer:**
  - (no matching clause found)

## `ObjectUtils.isArray/1`

**Source:**
```java
public static boolean isArray(final Object object) {
    return object != null && object.getClass().isArray();
}
```

**Daikon:**
  - [ENTER] object != null
  - [EXIT] return == true

**JML-Inferrer:**
  - (no matching clause found)

## `ObjectUtils.isEmpty/1`

**Source:**
```java
public static boolean isEmpty(final Object object) {
    if (object == null) {
        return true;
    }
    if (object instanceof CharSequence) {
        return ((CharSequence) object).length() == 0;
    }
    if (isArray(object)) {
        return Array.getLength(object) == 0;
    }
    if (object instanceof Collection<?>) {
        return ((Collection<?>) object).isEmpty();
    }
    if (object instanceof Map<?, ?>) {
        return ((Map<?, ?>) object).isEmpty();
    }
    if (object instanceof Optional<?>) {
        return !((Optional<?>) object).isPresent();
    }
    return false;
}
```

**Daikon:**
  - [ENTER] object != null
  - [EXIT] return == false

**JML-Inferrer:**
  - (no matching clause found)

## `ObjectUtils.requireNonEmpty/2`

**Source:**
```java
public static <T> T requireNonEmpty(final T obj, final String message) {
    Objects.requireNonNull(obj, message);
    if (isEmpty(obj)) {
        throw new IllegalArgumentException(message);
    }
    return obj;
}
```

**Daikon:**
  - [ENTER] message != null
  - [ENTER] message.toString == "array"
  - [ENTER] obj != null
  - [EXIT] message.toString == "array"
  - [EXIT] return != null

**JML-Inferrer:**
  - (no matching clause found)

## `Pair.getKey/0`

**Source:**
```java
@Override
public final L getKey() {
    return getLeft();
}
```

**Daikon:**
  - [EXIT] return != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result == getLeft()")

## `Pair.getValue/0`

**Source:**
```java
@Override
public R getValue() {
    return getRight();
}
```

**Daikon:**
  - [EXIT] return != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result == Boolean.valueOf(this.value)")
  - Ensures("\\result == getRight()")

## `Pair.of/2`

**Source:**
```java
public static <L, R> Pair<L, R> of(final L left, final R right) {
    return ImmutablePair.of(left, right);
}
```

**Daikon:**
  - [ENTER] left != null
  - [ENTER] right != null
  - [EXIT] return != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")

## `Pair.toString/0`

**Source:**
```java
@Override
public String toString() {
    return "(" + getLeft() + ',' + getRight() + ')';
}
```

**Daikon:**
  - [EXIT] return != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result.equals(\"(\" + getLeft() + ',' + getRight() + ')')")

## `Range$ComparableComparator.ComparableComparator/2`

**Daikon:**
  - [ENTER] $hidden$1.toString == "INSTANCE"
  - [ENTER] $hidden$2 == 0
  - [EXIT] $hidden$1.toString == "INSTANCE"

**JML-Inferrer:**
  - (no matching clause found)

## `Range$ComparableComparator.compare/2`

**Daikon:**
  - [ENTER] obj1 != null
  - [ENTER] obj2 != null
  - [EXIT] orig(this) in org.apache.commons.lang3.Range$ComparableComparator.$VALUES[]
  - [EXIT] return <= size(org.apache.commons.lang3.Range$ComparableComparator.$VALUES[])
  - [EXIT] return one of { -1, 0, 1 }

**JML-Inferrer:**
  - (no matching clause found)

## `Range.Range/3`

**Daikon:**
  - [ENTER] comp == null

**JML-Inferrer:**
  - (no matching clause found)

## `Range.between/2`

**Source:**
```java
@Deprecated
public static <T extends Comparable<? super T>> Range<T> between(final T fromInclusive, final T toInclusive) {
    return of(fromInclusive, toInclusive, null);
}
```

**Daikon:**
  - [EXIT] return.hashCode == 0
  - [EXIT] return.toString == null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result == of(fromInclusive, toInclusive, null)")
  - Requires("fromInclusive instanceof Comparable<? super T>")
  - Requires("toInclusive instanceof Comparable<? super T>")

## `Range.contains/1`

**Source:**
```java
public boolean contains(final T element) {
    if (element == null) {
        return false;
    }
    return comparator.compare(element, minimum) > -1 && comparator.compare(element, maximum) < 1;
}
```

**Daikon:**
  - [ENTER] element != null
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("element != null ==> \\result == (comparator.compare(element, minimum) > -1 && comparator.compare(element, maximum) < 1)")
  - Requires("element != null")
  - Requires("this.comparator != null")

## `Range.containsRange/1`

**Source:**
```java
public boolean containsRange(final Range<T> otherRange) {
    if (otherRange == null) {
        return false;
    }
    return contains(otherRange.minimum) && contains(otherRange.maximum);
}
```

**Daikon:**
  - [ENTER] this.comparator == otherRange.comparator
  - [ENTER] this.hashCode == otherRange.hashCode
  - [ENTER] this.toString == otherRange.toString
  - [EXIT] return == true
  - [EXIT] this.comparator == otherRange.comparator
  - [EXIT] this.hashCode == otherRange.hashCode
  - [EXIT] this.toString == otherRange.toString

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("otherRange != null ==> \\result == (contains(otherRange.minimum) && contains(otherRange.maximum))")
  - Requires("otherRange != null")
  - Requires("otherRange.maximum != null")
  - Requires("otherRange.minimum != null")
  - Requires("this.comparator != null")

## `Range.getMaximum/0`

**Source:**
```java
public T getMaximum() {
    return maximum;
}
```

**Daikon:**
  - [EXIT] this.maximum == return

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == this.maximum")

## `Range.getMinimum/0`

**Source:**
```java
public T getMinimum() {
    return minimum;
}
```

**Daikon:**
  - [EXIT] this.minimum == return

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result == this.minimum")

## `Range.isAfter/1`

**Source:**
```java
public boolean isAfter(final T element) {
    if (element == null) {
        return false;
    }
    return comparator.compare(element, minimum) < 0;
}
```

**Daikon:**
  - [ENTER] element != null
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("element != null ==> \\result == (comparator.compare(element, minimum) < 0)")
  - Requires("element != null")
  - Requires("this.comparator != null")

## `Range.isBefore/1`

**Source:**
```java
public boolean isBefore(final T element) {
    if (element == null) {
        return false;
    }
    return comparator.compare(element, maximum) > 0;
}
```

**Daikon:**
  - [ENTER] element != null
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("element != null ==> \\result == (comparator.compare(element, maximum) > 0)")
  - Requires("element != null")
  - Requires("this.comparator != null")

## `Range.isEndedBy/1`

**Source:**
```java
public boolean isEndedBy(final T element) {
    if (element == null) {
        return false;
    }
    return comparator.compare(element, maximum) == 0;
}
```

**Daikon:**
  - [ENTER] element != null
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("element != null ==> \\result == (comparator.compare(element, maximum) == 0)")
  - Requires("element != null")
  - Requires("this.comparator != null")

## `Range.isStartedBy/1`

**Source:**
```java
public boolean isStartedBy(final T element) {
    if (element == null) {
        return false;
    }
    return comparator.compare(element, minimum) == 0;
}
```

**Daikon:**
  - [ENTER] element != null
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("element != null ==> \\result == (comparator.compare(element, minimum) == 0)")
  - Requires("element != null")
  - Requires("this.comparator != null")

## `Range.of/3`

**Source:**
```java
public static <T> Range<T> of(final T fromInclusive, final T toInclusive, final Comparator<T> comparator) {
    return new Range<>(fromInclusive, toInclusive, comparator);
}
```

**Daikon:**
  - [ENTER] comparator == null
  - [EXIT] return.hashCode == 0
  - [EXIT] return.toString == null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")

## `StringUtils.isEmpty/1`

**Source:**
```java
public static boolean isEmpty(final CharSequence cs) {
    return cs == null || cs.length() == 0;
}
```

**Daikon:**
  - [EXIT] (return == false)  ==>  (orig(cs) != null)
  - [EXIT] orig(cs) != null
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - (no matching clause found)

## `StringUtils.isNumeric/1`

**Source:**
```java
public static boolean isNumeric(final CharSequence cs) {
    if (isEmpty(cs)) {
        return false;
    }
    final int sz = cs.length();
    for (int i = 0; i < sz; i++) {
        if (!Character.isDigit(cs.charAt(i))) {
            return false;
        }
    }
    return true;
}
```

**Daikon:**
  - [EXIT] (return == true)  ==>  (orig(cs) != null)
  - [EXIT] orig(cs) != null
  - [EXIT] return == false
  - [EXIT] return == true

**JML-Inferrer:**
  - (no matching clause found)

## `Validate.exclusiveBetween/3`

**Source:**
```java
@SuppressWarnings("boxing")
public static void exclusiveBetween(final double start, final double end, final double value) {
    if (value <= start || value >= end) {
        throw new IllegalArgumentException(String.format(DEFAULT_EXCLUSIVE_BETWEEN_EX_MESSAGE, value, start, end));
    }
}
@SuppressWarnings("boxing")
public static void exclusiveBetween(final long start, final long end, final long value) {
    if (value <= start || value >= end) {
        throw new IllegalArgumentException(String.format(DEFAULT_EXCLUSIVE_BETWEEN_EX_MESSAGE, value, start, end));
    }
}
public static <T> void exclusiveBetween(final T start, final T end, final Comparable<T> value) {
    if (value.compareTo(start) <= 0 || value.compareTo(end) >= 0) {
        throw new IllegalArgumentException(String.format(DEFAULT_EXCLUSIVE_BETWEEN_EX_MESSAGE, value, start, end));
    }
}
```

**Daikon:**
  - [ENTER] end == 5
  - [ENTER] end > value
  - [ENTER] start < value
  - [ENTER] start == 0
  - [ENTER] value one of { 1, 2, 3 }

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Requires("value != null")
  - Requires("value < end")
  - Requires("value > start && value < end")
  - Requires("value > start")
  - Requires("value instanceof Comparable")
  - Requires("value.compareTo(start) > 0 && value.compareTo(end) < 0")
  - Signals("IllegalArgumentException when value <= start || value >= end")
  - Signals("IllegalArgumentException when value.compareTo(start) <= 0 || value.compareTo(end) >= 0")

## `Validate.getMessage/2`

**Source:**
```java
private static String getMessage(final String message, final Object... values) {
    return ArrayUtils.isEmpty(values) ? message : String.format(message, values);
}
```

**Daikon:**
  - [ENTER] message != null
  - [ENTER] message.toString one of { "The validated object is null", "msg" }
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_EXCLUSIVE_BETWEEN_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_FINITE_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_INCLUSIVE_BETWEEN_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_ASSIGNABLE_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_INSTANCE_OF_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE.toString <= message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_TRUE_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_MATCHES_PATTERN_EX.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_BLANK_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_ARRAY_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_CHAR_SEQUENCE_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_COLLECTION_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_MAP_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_NAN_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NO_NULL_ELEMENTS_ARRAY_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NO_NULL_ELEMENTS_COLLECTION_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_ARRAY_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_CHAR_SEQUENCE_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_COLLECTION_EX_MESSAGE.toString < message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_VALID_STATE_EX_MESSAGE.toString != message.toString
  - [ENTER] values != null
  - [ENTER] values[] == []
  - [EXIT] message.toString == return.toString
  - [EXIT] message.toString one of { "The validated object is null", "msg" }
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_EXCLUSIVE_BETWEEN_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_FINITE_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_INCLUSIVE_BETWEEN_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_ASSIGNABLE_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_INSTANCE_OF_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE.toString <= message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_TRUE_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_MATCHES_PATTERN_EX.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_BLANK_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_ARRAY_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_CHAR_SEQUENCE_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_COLLECTION_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_MAP_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_NAN_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NO_NULL_ELEMENTS_ARRAY_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NO_NULL_ELEMENTS_COLLECTION_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_ARRAY_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_CHAR_SEQUENCE_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_COLLECTION_EX_MESSAGE.toString < message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_VALID_STATE_EX_MESSAGE.toString != message.toString
  - [EXIT] return != null
  - [EXIT] values[] == []

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")

## `Validate.inclusiveBetween/3`

**Source:**
```java
@SuppressWarnings("boxing")
public static void inclusiveBetween(final double start, final double end, final double value) {
    if (value < start || value > end) {
        throw new IllegalArgumentException(String.format(DEFAULT_INCLUSIVE_BETWEEN_EX_MESSAGE, value, start, end));
    }
}
@SuppressWarnings("boxing")
public static void inclusiveBetween(final long start, final long end, final long value) {
    if (value < start || value > end) {
        throw new IllegalArgumentException(String.format(DEFAULT_INCLUSIVE_BETWEEN_EX_MESSAGE, value, start, end));
    }
}
public static <T> void inclusiveBetween(final T start, final T end, final Comparable<T> value) {
    if (value.compareTo(start) < 0 || value.compareTo(end) > 0) {
        throw new IllegalArgumentException(String.format(DEFAULT_INCLUSIVE_BETWEEN_EX_MESSAGE, value, start, end));
    }
}
```

**Daikon:**
  - [ENTER] end == 5
  - [ENTER] end > value
  - [ENTER] start <= value
  - [ENTER] start == 0
  - [ENTER] value >= 0

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Requires("value != null")
  - Requires("value <= end")
  - Requires("value >= start && value <= end")
  - Requires("value >= start")
  - Requires("value instanceof Comparable")
  - Requires("value.compareTo(start) >= 0 && value.compareTo(end) <= 0")
  - Signals("IllegalArgumentException when value < start || value > end")
  - Signals("IllegalArgumentException when value.compareTo(start) < 0 || value.compareTo(end) > 0")

## `Validate.isTrue/1`

**Source:**
```java
public static void isTrue(final boolean expression) {
    if (!expression) {
        throw new IllegalArgumentException(DEFAULT_IS_TRUE_EX_MESSAGE);
    }
}
```

**Daikon:**
  - [ENTER] expression == true

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Requires("expression")
  - Signals("IllegalArgumentException when !expression")

## `Validate.isTrue/3`

**Source:**
```java
public static void isTrue(final boolean expression, final String message, final double value) {
    if (!expression) {
        throw new IllegalArgumentException(String.format(message, Double.valueOf(value)));
    }
}
public static void isTrue(final boolean expression, final String message, final long value) {
    if (!expression) {
        throw new IllegalArgumentException(String.format(message, Long.valueOf(value)));
    }
}
public static void isTrue(final boolean expression, final String message, final Object... values) {
    if (!expression) {
        throw new IllegalArgumentException(getMessage(message, values));
    }
}
```

**Daikon:**
  - [ENTER] expression == true
  - [ENTER] message != null
  - [ENTER] message.toString one of { "Array cannot be empty.", "msg" }
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_EXCLUSIVE_BETWEEN_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_FINITE_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_INCLUSIVE_BETWEEN_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_ASSIGNABLE_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_INSTANCE_OF_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_TRUE_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_MATCHES_PATTERN_EX.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_BLANK_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_ARRAY_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_CHAR_SEQUENCE_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_COLLECTION_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_MAP_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NOT_NAN_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NO_NULL_ELEMENTS_ARRAY_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_NO_NULL_ELEMENTS_COLLECTION_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_ARRAY_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_CHAR_SEQUENCE_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_COLLECTION_EX_MESSAGE.toString != message.toString
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_VALID_STATE_EX_MESSAGE.toString != message.toString
  - [ENTER] values != null
  - [ENTER] values[] == []
  - [EXIT] message.toString one of { "Array cannot be empty.", "msg" }
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_EXCLUSIVE_BETWEEN_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_FINITE_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_INCLUSIVE_BETWEEN_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_ASSIGNABLE_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_INSTANCE_OF_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_TRUE_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_MATCHES_PATTERN_EX.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_BLANK_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_ARRAY_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_CHAR_SEQUENCE_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_COLLECTION_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_EMPTY_MAP_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NOT_NAN_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NO_NULL_ELEMENTS_ARRAY_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_NO_NULL_ELEMENTS_COLLECTION_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_ARRAY_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_CHAR_SEQUENCE_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_VALID_INDEX_COLLECTION_EX_MESSAGE.toString != message.toString
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_VALID_STATE_EX_MESSAGE.toString != message.toString
  - [EXIT] values[] == []

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Requires("expression")
  - Signals("IllegalArgumentException when !expression")

## `Validate.notNull/1`

**Source:**
```java
@Deprecated
public static <T> T notNull(final T object) {
    return notNull(object, DEFAULT_IS_NULL_EX_MESSAGE);
}
```

**Daikon:**
  - [ENTER] object != null
  - [EXIT] return != null

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result == notNull(object, DEFAULT_IS_NULL_EX_MESSAGE)")

## `Validate.notNull/3`

**Source:**
```java
public static <T> T notNull(final T object, final String message, final Object... values) {
    return Objects.requireNonNull(object, toSupplier(message, values));
}
```

**Daikon:**
  - [ENTER] object != null
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE == message
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE.toString == message.toString
  - [ENTER] values != null
  - [ENTER] values[] == []
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE.toString == message.toString
  - [EXIT] return != null
  - [EXIT] values[] == []

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result == Objects.requireNonNull(object, toSupplier(message, values))")
  - Ensures("\\result == object")
  - Requires("object != null")

## `Validate.toSupplier/2`

**Source:**
```java
private static Supplier<String> toSupplier(final String message, final Object... values) {
    return () -> getMessage(message, values);
}
```

**Daikon:**
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE == message
  - [ENTER] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE.toString == message.toString
  - [ENTER] values != null
  - [ENTER] values[] == []
  - [EXIT] org.apache.commons.lang3.Validate.DEFAULT_IS_NULL_EX_MESSAGE.toString == message.toString
  - [EXIT] return != null
  - [EXIT] values[] == []

**JML-Inferrer:**
  - Assignable("\\nothing")
  - Ensures("\\result != null")
  - Ensures("\\result == (() -> getMessage(message, values))")

