#!/usr/bin/env python3
"""
Patches OpenJML's java/lang/String.jml + Integer.jml to expose
length-preservation / length-monotonicity / non-null / range postconditions
that the upstream specs hide inside `-RAC@` (RAC-only) or FIXME comment blocks.

Without these, ESC mode sees no useful postcondition for many of the most
common String/Integer methods. Inferred specs for callers cannot discharge.

Each block is replaced with an ESC-visible spec that uses only `length()`,
`equals()`, and arithmetic --- no internal `chars` model field references ---
so the proofs go through the length()-as-uninterpreted-function machinery
that OpenJML already supports.

Idempotent: each file is checked for a marker comment before being touched.
"""
import sys
from pathlib import Path

PATCH_MARKER = "// jml-string-transform-patch"

# Allow callers to pass a Specs/ root, or the path to String.jml directly
# (back-compat with earlier versions of this script).
_arg = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("Specs")
if _arg.is_file() and _arg.name == "String.jml":
    SPECS_ROOT = _arg.parent.parent.parent
else:
    SPECS_ROOT = _arg


# -----------------------------------------------------------------------------
# String.jml
# -----------------------------------------------------------------------------

STRING_REPLACEMENTS = [
    # ---- toLowerCase(Locale) -----------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
      @   requires locale != null;
      @   ensures \\result != null && \\result.chars.length == chars.length;
      @   ensures (* \\result == a lower case conversion of this using the 
      @                          rules of the given locale *);
      @*/
    public /*@ pure @*/
        String toLowerCase(/*@ non_null @*/ Locale locale);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires locale != null;
      @   ensures \\result != null;
      @   ensures \\result.length() == length();
      @ also public exceptional_behavior
      @   requires locale == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ pure @*/
        String toLowerCase(/*@ non_null @*/ Locale locale);""",
    ),
    # ---- toLowerCase() -----------------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
          {
             return toLowerCase(Locale.getDefault());
          }
      @*/
    public /*@ pure @*/ String toLowerCase();""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() == length();
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String toLowerCase();""",
    ),
    # ---- toUpperCase(Locale) -----------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
      @   requires locale != null;
      @   ensures \\result != null && \\result.length() == length();
      @   ensures (* \\result == an upper case conversion of this using the 
      @                          rules of the given locale *);
      @*/
    public /*@ pure @*/ /*@ non_null @*/
        String toUpperCase(/*@ non_null @*/ Locale locale);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires locale != null;
      @   ensures \\result != null;
      @   ensures \\result.length() == length();
      @ also public exceptional_behavior
      @   requires locale == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ pure @*/ /*@ non_null @*/
        String toUpperCase(/*@ non_null @*/ Locale locale);""",
    ),
    # ---- toUpperCase() -----------------------------------------------------
    (
        """    /* FIXME @  public normal_behavior
      @   { return toUpperCase(Locale.getDefault())); }
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String toUpperCase();""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() == length();
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String toUpperCase();""",
    ),
    # ---- trim() / strip family --------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
      @   ensures \\result != null
      @            && \\result.chars.length <= chars.length
      @            && \\result.chars[0] > ' '
      @            && \\result.chars[\\result.chars.length - 1] > ' ';
      @*/
    // FIXME - be more precise about what is omitted; also avoid recursion
    public /*@ pure @*/ /*@ non_null @*/ String trim();""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() <= length();
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String trim();

    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() <= length();
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String strip();

    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() <= length();
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String stripLeading();

    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() <= length();
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String stripTrailing();

    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires count >= 0;
      @   ensures \\result != null;
      @   ensures \\result.length() == length() * count;
      @ also public exceptional_behavior
      @   requires count < 0;
      @   signals_only IllegalArgumentException;
      @*/
    public /*@ pure @*/ String repeat(int count);""",
    ),
    # ---- indexOf(int) ------------------------------------------------------
    (
        """    /*@  public normal_behavior
      @   ensures \\result == indexOf(ch, 0);
      @*/
    public /*@ pure @*/ int indexOf(int ch);""",
        """    /*@  public normal_behavior  // jml-string-transform-patch
      @   ensures \\result == indexOf(ch, 0);
      @   ensures -1 <= \\result && \\result < length();
      @*/
    public /*@ pure @*/ int indexOf(int ch);""",
    ),
    # ---- indexOf(int, int) -------------------------------------------------
    (
        """    /* FIXME @  public normal_behavior
      @   requires fromIndex >= length();
      @   ensures \\result == -1;
      @  //also
      @  // requires fromIndex < 0;
      @  // ensures \\result == indexOf(ch, 0); // Note - can't use recursive
      @  also
      @   requires fromIndex < length();
      @   {|
      @     requires charAt((fromIndex < 0 ? 0 : fromIndex)) == ch;
      @     ensures \\result == (fromIndex < 0 ? 0 : fromIndex);
      @   also
      @     //-RAC@ ensures \\result == -1 <==> (\\forall int i; (fromIndex < 0 ? 0 : fromIndex) <= i < chars.length; chars[i] != ch);
      @     //-RAC@ ensures \\result != -1 <==> ((fromIndex < 0 ? 0 : fromIndex) <= \\result < chars.length);
      @     //-RAC@ ensures \\result != -1  ==> (
      @     //-RAC@            chars[\\result] == ch &&
      @     //-RAC@            (\\forall int i; (fromIndex < 0 ? 0 : fromIndex) <= i < \\result;
      @     //-RAC@                 chars[i] != ch));
      @   |}
      @*/
    public /*@ pure @*/ int indexOf(int ch, int fromIndex);""",
        """    /*@  public normal_behavior  // jml-string-transform-patch
      @   ensures -1 <= \\result && \\result < length();
      @*/
    public /*@ pure @*/ int indexOf(int ch, int fromIndex);""",
    ),
    # ---- lastIndexOf(int) --------------------------------------------------
    (
        """    /* FIXME @  public normal_behavior
      @   ensures \\result == lastIndexOf(ch, length() - 1);
      @*/
    public /*@ pure @*/ int lastIndexOf(int ch);""",
        """    /*@  public normal_behavior  // jml-string-transform-patch
      @   ensures -1 <= \\result && \\result < length();
      @*/
    public /*@ pure @*/ int lastIndexOf(int ch);""",
    ),
    # ---- indexOf(String) ---------------------------------------------------
    (
        """    /*@ public normal_behavior
      @  requires str != null;
      @  ensures \\result == indexOf(str, 0);
      @*/
    public /*@ pure @*/ int indexOf(String str);""",
        """    /*@  public normal_behavior  // jml-string-transform-patch
      @   requires str != null;
      @   ensures -1 <= \\result && \\result < length();
      @ also public exceptional_behavior
      @   requires str == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ pure @*/ int indexOf(String str);""",
    ),
    # ---- substring(int) ----------------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
      @   requires 0 <= beginIndex <= chars.length;
      @   //-RAC@ ensures \\result.chars.length == this.chars.length - beginIndex
      @   //-RAC@      && (\\result.chars == chars.tail(beginIndex));
      @   ensures beginIndex == 0 ==> (this.chars == \\result.chars);
      @ also
      @  public exceptional_behavior
      @   requires beginIndex < 0 || beginIndex > length();
      @   signals_only StringIndexOutOfBoundsException;
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String substring(int beginIndex)
      throws StringIndexOutOfBoundsException;""",
        """    /*@  public normal_behavior  // jml-string-transform-patch
      @   requires 0 <= beginIndex && beginIndex <= length();
      @   ensures \\result != null;
      @   ensures \\result.length() == length() - beginIndex;
      @ also
      @  public exceptional_behavior
      @   requires beginIndex < 0 || beginIndex > length();
      @   signals_only StringIndexOutOfBoundsException;
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String substring(int beginIndex)
      throws StringIndexOutOfBoundsException;""",
    ),
    # ---- substring(int, int) -----------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
      @   requires 0 <= beginIndex <= endIndex <= chars.length;
      @   //-RAC@ ensures \\result.chars.length == endIndex - beginIndex
      @   //-RAC@      && \\result.chars == chars.substring(beginIndex, endIndex);
      @   //-RAC@ ensures beginIndex == 0 && endIndex == chars.length ==> this.chars == \\result.chars;
      @ also
      @  public exceptional_behavior
      @   requires 0 > beginIndex
      @             || beginIndex > endIndex
      @             || (endIndex > length());
      @   signals_only StringIndexOutOfBoundsException;
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String substring(int beginIndex,
                                                            int endIndex)
      throws StringIndexOutOfBoundsException;""",
        """    /*@  public normal_behavior  // jml-string-transform-patch
      @   requires 0 <= beginIndex && beginIndex <= endIndex && endIndex <= length();
      @   ensures \\result != null;
      @   ensures \\result.length() == endIndex - beginIndex;
      @ also
      @  public exceptional_behavior
      @   requires 0 > beginIndex
      @             || beginIndex > endIndex
      @             || (endIndex > length());
      @   signals_only StringIndexOutOfBoundsException;
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String substring(int beginIndex,
                                                            int endIndex)
      throws StringIndexOutOfBoundsException;""",
    ),
    # ---- valueOf(int) ------------------------------------------------------
    (
        """    /* FIXME @  public normal_behavior
      @   ensures \\result == Integer.toString(i,10);
      @   //ensures String.equals(\\result, Integer.toString(i,10)); // FIXME - feasibility probloem with gitbug467
      @   //-RAC@ ensures \\result.chars.length <= 11;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ String valueOf(int i);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() >= 1;
      @   ensures \\result.length() <= 11;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ String valueOf(int i);""",
    ),
    # ---- valueOf(long) -----------------------------------------------------
    (
        """    /* FIXME @  public normal_behavior
      @   ensures \\result == Long.toString(l);
      @   ensures \\result.length() <= 22;
      @*/
    public static /*@ pure helper non_null @*/ String valueOf(long l);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() >= 1;
      @   ensures \\result.length() <= 22;
      @*/
    public static /*@ pure helper non_null @*/ String valueOf(long l);""",
    ),
    # ---- valueOf(float) ----------------------------------------------------
    (
        """    /* FIXME @  public normal_behavior
      @   ensures \\result == Float.toString(f);
      @   ensures \\result.length() < 100; // FIXME - make this tighter
      @*/
    public static /*@ pure helper non_null @*/ String valueOf(float f);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() >= 1;
      @*/
    public static /*@ pure helper non_null @*/ String valueOf(float f);""",
    ),
    # ---- valueOf(double) ---------------------------------------------------
    (
        """    /* FIXME @  public normal_behavior
      @   ensures \\result == Double.toString(d);
      @   ensures \\result.length() < 100; // FIXME - make this tighter
      @*/
    public static /*@ pure helper non_null @*/ String valueOf(double d);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() >= 1;
      @*/
    public static /*@ pure helper non_null @*/ String valueOf(double d);""",
    ),
    # === EXTENSION-V2: contains/startsWith/endsWith/replace/matches ============
    # ---- startsWith(String) ------------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
      @   requires prefix != null && prefix.chars.length <= this.chars.length;
      @   ensures \\result <==> prefix.chars == this.chars.substring(0, prefix.chars.length);
      @   ensures \\result <==> this.chars.startsWith(prefix.chars);
      @ also
      @   requires prefix != null && prefix.chars.length > this.chars.length;
      @   ensures !\\result;
      @*/
    public /*@ spec_pure @*/ boolean startsWith(String prefix);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires prefix != null;
      @   requires prefix.length() > length();
      @   ensures !\\result;
      @ also public normal_behavior
      @   requires prefix != null;
      @   requires prefix.length() <= length();
      @   // truth value undetermined for short prefix; we just commit to total
      @ also public exceptional_behavior
      @   requires prefix == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ spec_pure @*/ boolean startsWith(String prefix);""",
    ),
    # ---- startsWith(String, int) -------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
      @   requires prefix != null && 0 <= toffset && toffset + prefix.chars.length <= this.chars.length;
      @   ensures \\result <==> prefix.chars == this.chars.substring(toffset, toffset+prefix.chars.length);
      @ also
      @   requires prefix != null && toffset + prefix.chars.length > this.chars.length;
      @   ensures !\\result;
      @*/
    public /*@ spec_pure @*/ boolean startsWith(String prefix, int toffset);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires prefix != null;
      @   requires toffset < 0 || toffset + prefix.length() > length();
      @   ensures !\\result;
      @ also public normal_behavior
      @   requires prefix != null;
      @   requires 0 <= toffset && toffset + prefix.length() <= length();
      @ also public exceptional_behavior
      @   requires prefix == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ spec_pure @*/ boolean startsWith(String prefix, int toffset);""",
    ),
    # ---- endsWith(String) --------------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
      @   requires suffix != null && suffix.chars.length <= chars.length;
      @   ensures \\result == (chars.tail(length() - suffix.length()) == suffix.chars);
      @  also
      @   requires suffix != null && suffix.chars.length > chars.length;
      @   ensures !\\result;
      @*/
    public /*@ pure @*/ boolean endsWith(String suffix);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires suffix != null;
      @   requires suffix.length() > length();
      @   ensures !\\result;
      @ also public normal_behavior
      @   requires suffix != null;
      @   requires suffix.length() <= length();
      @ also public exceptional_behavior
      @   requires suffix == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ pure @*/ boolean endsWith(String suffix);""",
    ),
    # ---- replace(char, char) -----------------------------------------------
    (
        """    /*-RAC@  public normal_behavior
      @   ensures \\result.chars.length == chars.length
      @            && (\\forall int i; 0 <= i < chars.length;
      @                  \\result.chars[i] 
      @                     == ((this.chars[i] == oldChar) ? newChar : this.chars[i]));
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String replace(char oldChar,
                                                        char newChar);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() == length();
      @*/
    public /*@ pure @*/ /*@ non_null @*/ String replace(char oldChar,
                                                        char newChar);""",
    ),
    # ---- contains(CharSequence) - missing entirely from upstream! Insert
    # alongside replace(CharSequence, CharSequence) which is the closest method
    # we can anchor to in the file.
    # NOTE: the upstream lacks any `contains` method spec entirely; we inject
    # a complete spec block right after replace(CharSequence,CharSequence).
    (
        """    // FIXME
    /*@  public normal_behavior
      @    ensures \\result != null;
      @  pure
      @*/
    public String replace(CharSequence oldString, CharSequence newString);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires oldString != null && newString != null;
      @   ensures \\result != null;
      @ also public exceptional_behavior
      @   requires oldString == null || newString == null;
      @   signals_only NullPointerException;
      @*/
    public String replace(CharSequence oldString, CharSequence newString);

    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires s != null;
      @ also public exceptional_behavior
      @   requires s == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ pure @*/ boolean contains(/*@ nullable @*/ CharSequence s);""",
    ),
    # ---- matches(String) ---------------------------------------------------
    (
        """    /* FIXME @ public normal_behavior
      @     requires regex != null;
      @     assignable \\nothing;
      @     ensures \\result <==> Pattern.matches(regex, this);
      @*/
    public /*@ pure @*/ boolean matches(/*@ non_null @*/ String regex);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires regex != null;
      @ also public exceptional_behavior
      @   requires regex == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ pure @*/ boolean matches(/*@ non_null @*/ String regex);""",
    ),
    # ---- replaceFirst(String, String) --------------------------------------
    (
        """    /* FIXME @ public normal_behavior
      @     requires regex != null && replacement != null;
      @     assignable \\nothing;
      @     ensures equals(\\result,
      @               Pattern.compile(regex).matcher(this)
      @                      .replaceFirst(replacement));
      @*/
    public /*@ pure @*/ /*@ non_null @*/
        String replaceFirst(/*@ non_null @*/ String regex,
                            /*@ non_null @*/ String replacement);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires regex != null && replacement != null;
      @   ensures \\result != null;
      @ also public exceptional_behavior
      @   requires regex == null || replacement == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ pure @*/ /*@ non_null @*/
        String replaceFirst(/*@ non_null @*/ String regex,
                            /*@ non_null @*/ String replacement);""",
    ),
    # ---- replaceAll(String, String) ----------------------------------------
    (
        """    /* FIXME @ public normal_behavior
      @     requires regex != null && replacement != null;
      @     assignable \\nothing;
      @     ensures equals(\\result,
      @               Pattern.compile(regex).matcher(this)
      @                      .replaceAll(replacement));
      @*/
    public /*@ pure @*/ /*@ non_null @*/
        String replaceAll(/*@ non_null @*/ String regex,
                          /*@ non_null @*/ String replacement);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   requires regex != null && replacement != null;
      @   ensures \\result != null;
      @ also public exceptional_behavior
      @   requires regex == null || replacement == null;
      @   signals_only NullPointerException;
      @*/
    public /*@ pure @*/ /*@ non_null @*/
        String replaceAll(/*@ non_null @*/ String regex,
                          /*@ non_null @*/ String replacement);""",
    ),
]


# -----------------------------------------------------------------------------
# Integer.jml --- toString(int) needs ESC-visible non-null + length spec.
# -----------------------------------------------------------------------------

INTEGER_REPLACEMENTS = [
    (
        """    /*-RAC@ public normal_behavior
      @   ensures \\result.chars == \\string.of(i, 10);
      @   //ensures parseable(\\result, 10);
      @   //ensures i == parseInt(\\result, 10);
      @   //ensures i == 0 ==> \\result.length() == 1;
      @   //ensures i >  0 ==> \\result.length() >= 1;
      @   //ensures i <  0 ==> \\result.length() >= 2;
      @   //ensures i == 0 ==> \\result.equals(\"0\");
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ String toString(int i);""",
        """    /*@ public normal_behavior  // jml-string-transform-patch
      @   ensures \\result != null;
      @   ensures \\result.length() >= 1;
      @   ensures \\result.length() <= 11;
      @*/
    public static /*@ pure @*/ /*@ non_null @*/ String toString(int i);""",
    ),
]


def patch_file(path: Path, replacements):
    if not path.exists():
        print(f"  SKIP: {path} does not exist")
        return False
    src = path.read_text(encoding="utf-8")
    if PATCH_MARKER in src:
        print(f"  SKIP: {path} already patched (marker present)")
        return True
    patched = src
    applied = 0
    missing = 0
    for old, new in replacements:
        if old in patched:
            patched = patched.replace(old, new, 1)
            applied += 1
        else:
            missing += 1
            sys.stderr.write(f"  WARN: expected block not found in {path}\n")
    if applied == 0:
        print(f"  NOTHING APPLIED in {path}")
        return False
    path.write_text(patched, encoding="utf-8")
    print(f"  OK: applied {applied}/{len(replacements)} replacements in {path}"
          + (f" ({missing} missing)" if missing else ""))
    return True


def main():
    string_jml = SPECS_ROOT / "java" / "lang" / "String.jml"
    integer_jml = SPECS_ROOT / "java" / "lang" / "Integer.jml"

    print(f"Patching {string_jml}...")
    patch_file(string_jml, STRING_REPLACEMENTS)
    print(f"Patching {integer_jml}...")
    patch_file(integer_jml, INTEGER_REPLACEMENTS)


if __name__ == "__main__":
    main()
