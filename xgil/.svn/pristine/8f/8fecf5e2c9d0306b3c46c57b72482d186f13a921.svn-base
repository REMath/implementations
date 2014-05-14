// mlsstr.cc            see license.txt for copyright and terms of use
// code for mlsstr.h
// based on ccsstr.cc

#include "mlsstr.h"      // this module
#include "xassert.h"     // xassert
#include "exc.h"         // xformat
#include "strutil.h"     // string, replace

#include <ctype.h>       // isspace


MLSubstrate::MLSubstrate(ReportError *err)
  : EmbeddedLang(err)
{
  reset();
}

void MLSubstrate::reset(int initNest)
{
  state = ST_NORMAL;
  delims.empty();
  nestingBias = initNest;
  comNesting = 0;
  prev = 0;
  text.setlength(0);
}


MLSubstrate::~MLSubstrate()
{}


void MLSubstrate::handle(char const *str, int len, char finalDelim)
{
  text.append(str, len);

  for (; len>0; len--,str++) {
  process_char_again:
    switch (state) {
      case ST_NORMAL:
        switch (*str) {
          case '{':
          case '(':
          case '[':
            if (!inComment()) {
              delims.push(*str);
            }
            break;

          case '}':
          case ')':
          case ']':
            if (inComment()) {
              if (prev == '*' && *str == ')') {
                comNesting--;
              }
            }
            else if (nesting() == 0) {
              err->reportError(stringc
                << "unexpected closing delimiter `" << *str
                << "' -- probably due to missing `" << finalDelim << "'");
            }
            else {
              char o = delims.top();
              char c = *str;
              if (!(( o=='{' && c=='}' ) ||
                    ( o=='(' && c==')' ) ||
                    ( o=='[' && c==']' ))) {
                err->reportError(stringc
                  << "opening delimiter `" << o
                  << "' does not match closing delimiter `" << c << "'");
              }
              delims.pop();
            }
            break;

          case '\"':
            state = ST_STRING;
            break;

          case '\'':
            if (isalnum(prev) || prev=='_' || prev=='\'') {
              // this is a prime on a variable name; stay in normal mode
            }
            else {
              state = ST_APOSTROPHE1;
            }
            break;

          case '*':
            if (prev == '(') {
              if (comNesting == 0) {
                // undo 'delims.push()' from the '('
                xassert(nesting() > 0);
                delims.pop();
              }
              comNesting++;

              // if the next char is ')', i.e. input was "(*)", do
              // not allow it to use this '*' to finish the comment
              prev = 0;
              continue;
            }
            break;
        }
        break;

      case ST_APOSTROPHE1:
        // While the OCaml manual does not specify how to disambiguate
        // between character literals and type variables, the ocaml
        // lexer (parsing/lexer.mll) uses (approximately) the
        // following rules:
        //
        //   - If the input is (apostrophe, char, apostrophe), it is
        //     a character literal.
        //   - If the input is (apostrophe, backslash), it is the start
        //     of a a character literal.
        //   - Any other occurrence of apostrophe starts a type variable.
        if (*str == '\\') {
          state = ST_CHAR;
        }
        else {
          state = ST_APOSTROPHE2;
        }
        break;
        
      case ST_APOSTROPHE2:
        if (*str == '\'') {
          state = ST_NORMAL;    // finishes the character literal
        }
        else {                  
          // whole thing is a type variable; but if *str is something
          // like ')' then we need to consider its effects on nesting
          state = ST_NORMAL;
          goto process_char_again;
        }
        break;

      case ST_STRING:
      case ST_CHAR:
        if (prev != '\\') {
          if ((state == ST_STRING && *str == '\"') ||
              (state == ST_CHAR && *str == '\'')) {
            state = ST_NORMAL;
          }
          else if (*str == '\n') {
            // actually, ocaml allows unescaped newlines in string literals
            //err->reportError("unterminated string or char literal");
          }
        }
        else {
          prev = 0;      // the backslash cancels any specialness of *str
          continue;
        }
        break;

      #if 0   // old
      case ST_COMMENT:
        if (prev == '(' && *str == '*') {
          comNesting++;
          prev = 0;      // like above
          continue;
        }
        else if (prev == '*' && *str == ')') {
          xassert(comNesting >= 0);
          if (comNesting == 0) {
            // done with comment
            state = ST_NORMAL;
          }
          else {
            // decrease nesting
            comNesting--;
          }
        }
        break;
      #endif // 0

      default:
        xfailure("unknown state");
    }

    prev = *str;
  }
}


bool MLSubstrate::zeroNesting() const
{
  return state == ST_NORMAL && nesting() == 0 && !inComment();
}


string MLSubstrate::getFuncBody() const
{
  return text;
}


// 4/29/04: I have no idea if this is right or not.. this is the
// definition from ccsstr.cc.
string MLSubstrate::getDeclName() const
{
  // go with the rather inelegant heuristic that the word
  // just before the first '(' is the function's name
  char const *start = text.c_str();
  char const *p = start;
  
  // find first '('
  while (*p && *p!='(') { p++; }
  if (!*p) {
    xformat("missing '('");
  }             
  if (p == start) {
    xformat("missing name");
  }

  // skip backward past any whitespace before the '('
  p--;
  while (p>=start && isspace(*p)) { p--; }
  if (p<start) {
    xformat("missing name");
  }
  char const *nameEnd = p+1;    // char just past last
  
  // move backward through the name
  while (p>=start && 
         (isalnum(*p) || *p=='_'))
    { p--; }
  p++;    // move back to most recent legal char
  
  // done
  return substring(p, nameEnd-p);
}


// ------------------ test code -------------------
#ifdef TEST_MLSSTR

#define ML MLSubstrate
#define Test MLSubstrateTest

// test code is put into a class just so that MLSubstrate
// can grant it access to private fields
class Test {
public:
  void feed(ML &ml, char const *src, bool allowErrors = false);
  void silentFeed(ML &ml, char const *src);
  void test(char const *src, ML::State state, int nesting,
            int comNesting, char prev);
  void normal(char const *src, int nesting);
  void str(char const *src, int nesting, bool bs);
  void yes(char const *src);
  void no(char const *src);
  void name(char const *body, char const *n);
  void badname(char const *body);
  void bad(char const *body);
  int main(int argc, char *argv[]);
};


#define min(a,b) ((a)<(b)?(a):(b))

void Test::feed(ML &ml, char const *src, bool allowErrors)
{
  int origErrors = simpleReportError.errors;

  cout << "trying: " << src << endl;
  silentFeed(ml, src);

  if (!allowErrors &&
      origErrors != simpleReportError.errors) {
    xfailure(stringc << "caused error: " << src);
  }
}

void Test::silentFeed(ML &ml, char const *src)
{
  while (*src) {
    // feed it in 10 char increments, to test split processing too
    int len = min(strlen(src), 10);
    ml.handle(src, len, '}');
    src += len;
  }
}


void Test::test(char const *src, ML::State state, int nesting,
                int comNesting, char prev)
{
  ML ml;
  feed(ml, src);

  if (!( ml.state == state &&
         ml.nesting() == nesting &&
         ml.comNesting == comNesting &&
         ml.prev == prev )) {
    xfailure(stringc << "failed on src: " << src);
  }
}


void Test::normal(char const *src, int nesting)
{
  test(src, ML::ST_NORMAL, nesting, 0, src[strlen(src)-1]);
}

void Test::str(char const *src, int nesting, bool bs)
{
  char prev = (bs? '\\' : src[strlen(src)-1]);
  test(src, ML::ST_STRING, nesting, 0, prev);

  // repeat the test with single-tick
  //
  // 2005-01-25: No, OCaml's character-literal rules do not treat
  // quote and apostrophe similarly.
  //string another = replace(src, "\"", "\'");
  //test(another, ML::ST_CHAR, nesting, 0, prev);
}


void Test::yes(char const *src)
{
  ML ml;
  feed(ml, src);

  xassert(ml.zeroNesting());
}

void Test::no(char const *src)
{
  ML ml;
  feed(ml, src);

  xassert(!ml.zeroNesting());
}

void Test::name(char const *body, char const *n)
{
  ML ml;
  feed(ml, body);
  xassert(ml.getDeclName().equals(n));
}

void Test::badname(char const *body)
{
  ML ml;
  feed(ml, body);
  try {
    ml.getDeclName();
    xbase("got a name when it shoudn't have!");
  }
  catch (...)
    {}
}

void Test::bad(char const *body)
{
  int origErrors = simpleReportError.errors;

  ML ml;
  feed(ml, body, true /*allowErrors*/);

  if (origErrors == simpleReportError.errors) {
    xbase(stringc << "should have caused an error: " << body);
  }
}


int Test::main(int argc, char *argv[])
{
  if (argc >= 2) {
    // analyze the files passed as an argument, expecting them to be
    // complete caml source files, ending in normal mode with all
    // delimiters closed         
    for (int i=1; i<argc; i++) {
      string text = readStringFromFile(argv[i]);
      
      ML ml;
      silentFeed(ml, text.c_str());

      if (ml.state != ML::ST_NORMAL) {
        xbase(stringc << argv[i] << ": ended in state " << (int)ml.state);
      }
      if (ml.nesting() != 0) {
        xbase(stringc << argv[i] << ": ended with nesting " << ml.nesting());
      }
      if (ml.inComment()) {
        xbase(stringc << argv[i] << ": ended in a comment");
      }
      if (simpleReportError.errors != 0) {
        xbase(stringc << argv[i] << ": caused errors");
      }

      cout << argv[i] << ": ok\n";
    }
    return 0;
  }

  normal("int main()", 0);
  normal("int main() { hi", 1);
  normal("int main() { hi {", 2);
  normal("int main() { hi { foo[5", 3);
  normal("int main() { hi { foo[5] and ", 2);
  normal("int main() { hi { foo[5] and } bar ", 1);
  normal("int main() { hi { foo[5] and } bar } baz ", 0);

  normal("main() { printf(\"hello \\ world\"); ret", 1);

  normal("()[]{}([{}])", 0);
  normal("{ ()[]{}([{}]) } ", 0);
  normal("( ()[]{}([{}]) )", 0);
  normal("[ ()[]{}([{}]) ]", 0);
  normal("\"foo\" ()[]{}([{}])", 0);

  str("main() { printf(\"hello", 2, false);
  str("main() { printf(\"hello \\", 2, true);
  str("main() { printf(\"hello \\ world", 2, false);
  str("main() { printf(\"hello \\ world\", \"hi", 2, false);
  
  // escaped newline
  normal("main() { printf(\"hello \\\n world\"); }", 0);

  // newlines do not have to be escaped!
  normal("main() { printf(\"hello \n world\"); }", 0);

  test("\"a\" 'b' (", ML::ST_NORMAL, 1, 0, '(');
  test("\"a\" '\\n' (", ML::ST_NORMAL, 1, 0, '(');
  test("\"a\" '\\\\' (", ML::ST_NORMAL, 1, 0, '(');

  // here, the "'b" is to be treated as a type variable
  test("\"a\" 'b (", ML::ST_NORMAL, 1, 0, '(');
  test("\"a\" ('b) (", ML::ST_NORMAL, 1, 0, '(');

  // and here it is a prime ending the name of a variable
  test("\"a\" b' (", ML::ST_NORMAL, 1, 0, '(');
  test("\"a\" (b') (", ML::ST_NORMAL, 1, 0, '(');
  test("\"a\" let b=b' (", ML::ST_NORMAL, 1, 0, '(');
  test("\"a\" let b=b'' (", ML::ST_NORMAL, 1, 0, '(');
  test("\"a\" let b=b''' (", ML::ST_NORMAL, 1, 0, '(');

  // test comments, particularly testing
  test("(", ML::ST_NORMAL, 1, 0, '(');
  test("(*", ML::ST_NORMAL, 0, 1, 0);
  test("(*)", ML::ST_NORMAL, 0, 1, ')');
  test("(*)(", ML::ST_NORMAL, 0, 1, '(');
  test("(*)(*", ML::ST_NORMAL, 0, 2, 0);
  test("(*)(*)", ML::ST_NORMAL, 0, 2, ')');
  test("(*)(*)*", ML::ST_NORMAL, 0, 2, '*');
  test("(*)(*)*)", ML::ST_NORMAL, 0, 1, ')');
  test("(*)(*)*)*", ML::ST_NORMAL, 0, 1, '*');
  test("(*)(*)*)*)", ML::ST_NORMAL, 0, 0, ')');

  test("(*(*(*(*", ML::ST_NORMAL, 0, 4, 0);

  yes("main() {}");
  yes("main() { printf(\"foo\", 3, 4 (*yep{*)); }");
  yes("some (* junk {\n more*)");
  yes("'\\''");
  yes("\"\\\"\"");
  yes("[][][][][]");
  yes("\"[[[\"");
  yes("*");
  yes("(* [ / * [ *)");
  yes("(* \"(*\" *)");     // quoted open-comment ignored

  no("\"");
  no("(");
  no(" ( (* ) *) ");

  name("int main()", "main");
  name("int eval(Environment &env)", "eval");
  name("man()", "man");
  badname("(");
  badname("  (");
  badname("  ");
  badname("");
  bad(")");
  badname("main");

  cout << "\nmlsstr: all tests PASSED\n";

  return 0;
}

int main(int argc, char *argv[])
{
  //xBase::logExceptions = false;
  try {
    Test t;
    return t.main(argc, argv);
  }
  catch (xBase &x) {
    cout << endl << x << endl;
    return 10;
  }
}

#endif // TEST_MLSSTR
