/*******************************************************************************
 * The MIT License
 *
 * Copyright (c) 2008 Adam Kiezun
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ******************************************************************************/
package hampi.tests;

import hampi.Hampi;
import hampi.utils.CFG2HMP;

import java.io.*;

import junit.framework.TestCase;

//this stores the tests that currently fail
public class SolverFailingTests extends TestCase{

  //from full solver tests
  public void testRegression2() throws Exception{
    Hampi.run(new String[] { FullSolverTests.D + getName() + ".hmp", "-c", "-v" });
  }

  //Some grammars in cfganalyze data fail on Hampi. We generate tests for this
  public void generateFailingTestsFromCFGAnalyzerGrammars() throws Exception{
    String[] bugs = { "sml.cfg", "g6.cfg", "sql.4.cfg", "rna2.cfg", "059.cfg", "c-ambig.cfg", "rna5.cfg", "rna4.cfg", "04_11_047.cfg", "rna8.cfg", "058.cfg", "elsa_small.cfg", "voss-buggy.cfg",
        "068.cfg", "pascal.1.cfg", "sql.2.cfg", "067.cfg", "sql.3.cfg", "test1.cfg", "sql.5.cfg", "voss.cfg", "c.cfg", "java.0.cfg", "01_05_076.cfg", "pascal.3.cfg", "rna1.cfg", "set_exp.cfg",
        "pascal.cfg", "90_10_042.cfg", "elsa.cfg", "pascal.4.cfg", "pascal.2.cfg" };
    String dirName = "resources/othertools/ambiguity";
    File dir = new File(dirName);
    for (String fname : bugs){
      File cfgAnalyzerFile = new File(dir, fname);
      //      System.out.println(cfgAnalyzerFile);
      try{
        String hampiConstraint = CFG2HMP.convertToEmptinessConstraint(10, cfgAnalyzerFile.getAbsolutePath());
        String[] lines = hampiConstraint.split("\n");
        System.out.println("public void test_" + fname.replace('.', '_') + "() throws Exception{");
        System.out.println("StringBuilder b= new StringBuilder();");
        for (String line : lines){
          line = line.replace("\"", "\\\"");
          System.out.println("b.append(\"" + line + "\");");
        }
        System.out.println("String c = b.toString();");
        System.out.println("Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));");
        System.out.println("}");
      }catch (Exception e){
        System.err.println(e);
      }
      System.out.println();
    }
  }

  public void test_g6_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  \"a\" S \"a\" | \"b\" S \"b\" | \"a\" | \"b\" | ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_sql_4_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg y_sql :=  y_alter | y_create | y_drop | y_insert | y_select | y_update | y_delete ;");
    b.append("cfg y_alter :=  \"ALTER\" \"TABLE\" y_table \"ADD\" \"COLUMN\" y_columndef | \"ALTER\" \"TABLE\" y_table \"ADD\" y_columndef ;");
    b.append("cfg y_create :=  \"CREATE\" \"TABLE\" y_table \"(\" y_columndefs \")\" ;");
    b.append("cfg y_drop :=  \"DROP\" \"TABLE\" y_table ;");
    b
        .append("cfg y_select :=  \"SELECT\" y_columns \"FROM\" y_table | \"SELECT\" y_columns \"FROM\" y_table \"WHERE\" y_condition | \"SELECT\" y_columns \"FROM\" y_table \"ORDER\" \"BY\" y_order | \"SELECT\" y_columns \"FROM\" y_table \"WHERE\" y_condition \"ORDER\" \"BY\" y_order ;");
    b.append("cfg y_delete :=  \"DELETE\" \"FROM\" y_table | \"DELETE\" \"FROM\" y_table \"WHERE\" y_condition ;");
    b.append("cfg y_insert :=  \"INSERT\" \"INTO\" y_table y_values | \"INSERT\" \"INTO\" y_table \"(\" y_columns \")\" y_values ;");
    b.append("cfg y_update :=  \"UPDATE\" y_table \"SET\" y_assignments | \"UPDATE\" y_table \"SET\" y_assignments \"WHERE\" y_condition ;");
    b.append("cfg y_columndefs :=  y_columndef | y_columndefs \",\" y_columndef ;");
    b
        .append("cfg y_columndef :=  \"NAME\" \"VARCHAR\" \"(\" \"INTNUM\" \")\" | \"NAME\" \"INT\" | \"NAME\" \"INTEGER\" | \"NAME\" \"DOUBLE\" | \"NAME\" \"DOUBLE\" \"PRECISION\" | \"NAME\" \"DATE\" ;");
    b.append("cfg y_columns :=  \"*\" | y_column_list ;");
    b.append("cfg y_column_list :=  \"NAME\" | y_column_list \",\" \"NAME\" ;");
    b.append("cfg y_table :=  \"NAME\" ;");
    b.append("cfg y_values :=  \"VALUES\" \"(\" y_value_list \")\" ;");
    b
        .append("cfg y_value_list :=  \"NULL_VALUE\" | \"STRING\" | \"INTNUM\" | \"-\" \"INTNUM\" | \"FLOATNUM\" | \"-\" \"FLOATNUM\" | y_value_list \",\" \"NULL_VALUE\" | y_value_list \",\" \"STRING\" | y_value_list \",\" \"INTNUM\" | y_value_list \",\" \"-\" \"INTNUM\" | y_value_list \",\" \"FLOATNUM\" | y_value_list \",\" \"-\" \"FLOATNUM\" ;");
    b.append("cfg y_assignments :=  y_assignment | y_assignments \",\" y_assignment ;");
    b.append("cfg y_assignment :=  \"NAME\" \"EQUAL\" \"NULL_VALUE\" | \"NAME\" \"EQUAL\" y_expression ;");
    b.append("cfg y_condition :=  y_sub_condition ;");
    b.append("cfg y_sub_condition :=  y_sub_condition2 | y_sub_condition \"OR\" y_sub_condition2 ;");
    b.append("cfg y_sub_condition2 :=  y_boolean | y_sub_condition2 \"AND\" y_boolean ;");
    b.append("cfg y_boolean :=  y_comparison | \"(\" y_sub_condition \")\" | \"NOT\" y_boolean ;");
    b
        .append("cfg y_comparison :=  y_expression \"EQUAL\" y_expression | y_expression \"COMPARISON_OPERATOR\" y_expression | y_expression \"IS\" \"NULL_VALUE\" | y_expression \"NOT\" \"NULL_VALUE\" ;");
    b.append("cfg y_expression :=  y_product | y_expression \"+\" y_product | y_expression \"-\" y_product ;");
    b.append("cfg y_product :=  y_term | y_product \"*\" y_term | y_product \"/\" y_term ;");
    b.append("cfg y_term :=  y_atom | \"-\" y_term ;");
    b.append("cfg y_atom :=  y_value | y_column | \"(\" y_expression \")\" ;");
    b.append("cfg y_value :=  \"STRING\" | \"INTNUM\" | \"FLOATNUM\" ;");
    b.append("cfg y_column :=  \"NAME\" ;");
    b.append("cfg y_order :=  \"NAME\" ;");
    b.append("cfg y_columndef :=  \"NAME\" \"INT\" \",\" \"NAME\" \"INT\" ;");
    b.append("reg limit := fix(y_sql, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_rna2_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  \"(\" P \")\" | \".\" S | S \".\" | S S | ;");
    b.append("cfg P :=  \"(\" P \")\" | S ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_059_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  B | A ;");
    b.append("cfg A :=  | \"a\" A ;");
    b.append("cfg B :=  | \"b\" B ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_c_ambig_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg start :=  translation_unit ;");
    b.append("cfg primary_expression :=  IDENTIFIER | CONSTANT | STRING_LITERAL | \"(\" expression \")\" ;");
    b
        .append("cfg postfix_expression :=  primary_expression | postfix_expression \"[\" expression \"]\" | postfix_expression \"(\" \")\" | postfix_expression \"(\" argument_expression_list \")\" | postfix_expression \".\" IDENTIFIER | postfix_expression PTR_OP IDENTIFIER | postfix_expression INC_OP | postfix_expression DEC_OP ;");
    b.append("cfg argument_expression_list :=  assignment_expression | argument_expression_list \",\" assignment_expression ;");
    b
        .append("cfg unary_expression :=  postfix_expression | INC_OP unary_expression | DEC_OP unary_expression | unary_operator cast_expression | SIZEOF unary_expression | SIZEOF \"(\" type_name \")\" ;");
    b.append("cfg unary_operator :=  \"&\" | \"*\" | \"+\" | \"-\" | \"~\" | \"!\" ;");
    b.append("cfg cast_expression :=  unary_expression | \"(\" type_name \")\" cast_expression ;");
    b
        .append("cfg multiplicative_expression :=  cast_expression | multiplicative_expression \"*\" cast_expression | multiplicative_expression \"/\" cast_expression | multiplicative_expression \"%\" cast_expression ;");
    b.append("cfg additive_expression :=  multiplicative_expression | additive_expression \"+\" multiplicative_expression | additive_expression \"-\" multiplicative_expression ;");
    b.append("cfg shift_expression :=  additive_expression | shift_expression LEFT_OP additive_expression | shift_expression RIGHT_OP additive_expression ;");
    b
        .append("cfg relational_expression :=  shift_expression | relational_expression \"<\" shift_expression | relational_expression \">\" shift_expression | relational_expression LE_OP shift_expression | relational_expression GE_OP shift_expression ;");
    b.append("cfg equality_expression :=  relational_expression | equality_expression EQ_OP relational_expression | equality_expression NE_OP relational_expression ;");
    b.append("cfg and_expression :=  equality_expression | and_expression \"&\" equality_expression ;");
    b.append("cfg exclusive_or_expression :=  and_expression | exclusive_or_expression \"^\" and_expression ;");
    b.append("cfg inclusive_or_expression :=  exclusive_or_expression | inclusive_or_expression \":\" exclusive_or_expression ;");
    b.append("cfg logical_and_expression :=  inclusive_or_expression | logical_and_expression AND_OP inclusive_or_expression ;");
    b.append("cfg logical_or_expression :=  logical_and_expression | logical_or_expression OR_OP logical_and_expression ;");
    b.append("cfg conditional_expression :=  logical_or_expression | logical_or_expression \"?\" expression \":\" conditional_expression ;");
    b.append("cfg assignment_expression :=  conditional_expression | unary_expression assignment_operator assignment_expression ;");
    b.append("cfg assignment_operator :=  \"=\" | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN | ADD_ASSIGN | SUB_ASSIGN | LEFT_ASSIGN | RIGHT_ASSIGN | AND_ASSIGN | XOR_ASSIGN | OR_ASSIGN ;");
    b.append("cfg expression :=  assignment_expression | expression \",\" assignment_expression ;");
    b.append("cfg constant_expression :=  conditional_expression ;");
    b.append("cfg declaration :=  declaration_specifiers \";\" | declaration_specifiers init_declarator_list \";\" ;");
    b
        .append("cfg declaration_specifiers :=  storage_class_specifier | storage_class_specifier declaration_specifiers | type_specifier | type_specifier declaration_specifiers | type_qualifier | type_qualifier declaration_specifiers ;");
    b.append("cfg init_declarator_list :=  init_declarator | init_declarator_list \",\" init_declarator ;");
    b.append("cfg init_declarator :=  declarator | declarator \"=\" initializer ;");
    b.append("cfg storage_class_specifier :=  TYPEDEF | EXTERN | STATIC | AUTO | REGISTER ;");
    b.append("cfg type_specifier :=  VOID | CHAR | SHORT | INT | LONG | FLOAT | DOUBLE | SIGNED | UNSIGNED | struct_or_union_specifier | enum_specifier | typedef_name ;");
    b.append("cfg struct_or_union_specifier :=  struct_or_union IDENTIFIER \"{\" struct_declaration_list \"}\" | struct_or_union \"{\" struct_declaration_list \"}\" | struct_or_union IDENTIFIER ;");
    b.append("cfg struct_or_union :=  STRUCT | UNION ;");
    b.append("cfg struct_declaration_list :=  struct_declaration | struct_declaration_list struct_declaration ;");
    b.append("cfg struct_declaration :=  specifier_qualifier_list struct_declarator_list \";\" ;");
    b.append("cfg specifier_qualifier_list :=  type_specifier specifier_qualifier_list | type_specifier | type_qualifier specifier_qualifier_list | type_qualifier ;");
    b.append("cfg struct_declarator_list :=  struct_declarator | struct_declarator_list \",\" struct_declarator ;");
    b.append("cfg struct_declarator :=  declarator | \":\" constant_expression | declarator \":\" constant_expression ;");
    b.append("cfg enum_specifier :=  ENUM \"{\" enumerator_list \"}\" | ENUM IDENTIFIER \"{\" enumerator_list \"}\" | ENUM IDENTIFIER ;");
    b.append("cfg enumerator_list :=  enumerator | enumerator_list \",\" enumerator ;");
    b.append("cfg enumerator :=  IDENTIFIER | IDENTIFIER \"=\" constant_expression ;");
    b.append("cfg type_qualifier :=  CONST | VOLATILE ;");
    b.append("cfg declarator :=  pointer direct_declarator | direct_declarator ;");
    b
        .append("cfg direct_declarator :=  IDENTIFIER | \"(\" declarator \")\" | direct_declarator \"[\" constant_expression \"]\" | direct_declarator \"[\" \"]\" | direct_declarator \"(\" parameter_type_list \")\" | direct_declarator \"(\" identifier_list \")\" | direct_declarator \"(\" \")\" ;");
    b.append("cfg pointer :=  \"*\" | \"*\" type_qualifier_list | \"*\" pointer | \"*\" type_qualifier_list pointer ;");
    b.append("cfg type_qualifier_list :=  type_qualifier | type_qualifier_list type_qualifier ;");
    b.append("cfg parameter_type_list :=  parameter_list | parameter_list \",\" ELLIPSIS ;");
    b.append("cfg parameter_list :=  parameter_declaration | parameter_list \",\" parameter_declaration ;");
    b.append("cfg parameter_declaration :=  declaration_specifiers declarator | declaration_specifiers abstract_declarator | declaration_specifiers ;");
    b.append("cfg identifier_list :=  IDENTIFIER | identifier_list \",\" IDENTIFIER ;");
    b.append("cfg type_name :=  specifier_qualifier_list | specifier_qualifier_list abstract_declarator ;");
    b.append("cfg abstract_declarator :=  pointer | direct_abstract_declarator | pointer direct_abstract_declarator ;");
    b
        .append("cfg direct_abstract_declarator :=  \"(\" abstract_declarator \")\" | \"[\" \"]\" | \"[\" constant_expression \"]\" | direct_abstract_declarator \"[\" \"]\" | direct_abstract_declarator \"[\" constant_expression \"]\" | \"(\" \")\" | \"(\" parameter_type_list \")\" | direct_abstract_declarator \"(\" \")\" | direct_abstract_declarator \"(\" parameter_type_list \")\" ;");
    b.append("cfg initializer :=  assignment_expression | \"{\" initializer_list \"}\" | \"{\" initializer_list \",\" \"}\" ;");
    b.append("cfg initializer_list :=  initializer | initializer_list \",\" initializer ;");
    b.append("cfg typedef_name :=  IDENTIFIER ;");
    b.append("cfg statement :=  labeled_statement | compound_statement | expression_statement | selection_statement | iteration_statement | jump_statement ;");
    b.append("cfg labeled_statement :=  IDENTIFIER \":\" statement | CASE constant_expression \":\" statement | DEFAULT \":\" statement ;");
    b.append("cfg compound_statement :=  \"{\" \"}\" | \"{\" statement_list \"}\" | \"{\" declaration_list \"}\" | \"{\" declaration_list statement_list \"}\" ;");
    b.append("cfg declaration_list :=  declaration | declaration_list declaration ;");
    b.append("cfg statement_list :=  statement | statement_list statement ;");
    b.append("cfg expression_statement :=  \";\" | expression \";\" ;");
    b.append("cfg selection_statement :=  IF \"(\" expression \")\" statement | IF \"(\" expression \")\" statement ELSE statement | SWITCH \"(\" expression \")\" statement ;");
    b
        .append("cfg iteration_statement :=  WHILE \"(\" expression \")\" statement | DO statement WHILE \"(\" expression \")\" \";\" | FOR \"(\" expression_statement expression_statement \")\" statement | FOR \"(\" expression_statement expression_statement expression \")\" statement ;");
    b.append("cfg jump_statement :=  GOTO IDENTIFIER \";\" | CONTINUE \";\" | BREAK \";\" | RETURN \";\" | RETURN expression \";\" ;");
    b.append("cfg translation_unit :=  external_declaration | translation_unit external_declaration ;");
    b.append("cfg external_declaration :=  function_definition | declaration ;");
    b
        .append("cfg function_definition :=  declaration_specifiers declarator declaration_list compound_statement | declaration_specifiers declarator compound_statement | declarator declaration_list compound_statement | declarator compound_statement ;");
    b.append("cfg ADD_ASSIGN :=  \"0\" ;");
    b.append("cfg AND_ASSIGN :=  \"1\" ;");
    b.append("cfg AND_OP :=  \"2\" ;");
    b.append("cfg AUTO :=  \"3\" ;");
    b.append("cfg BREAK :=  \"4\" ;");
    b.append("cfg CASE :=  \"5\" ;");
    b.append("cfg CHAR :=  \"6\" ;");
    b.append("cfg CONST :=  \"7\" ;");
    b.append("cfg CONSTANT :=  \"8\" ;");
    b.append("cfg CONTINUE :=  \"9\" ;");
    b.append("cfg DEC_OP :=  \"a\" ;");
    b.append("cfg DEFAULT :=  \"b\" ;");
    b.append("cfg DIV_ASSIGN :=  \"c\" ;");
    b.append("cfg DO :=  \"d\" ;");
    b.append("cfg DOUBLE :=  \"e\" ;");
    b.append("ELLIPSIS: \"f\" ;");
    b.append("cfg ELSE :=  \"g\" ;");
    b.append("cfg ENUM :=  \"h\" ;");
    b.append("cfg EQ_OP :=  \"i\" ;");
    b.append("cfg EXTERN :=  \"j\" ;");
    b.append("cfg FLOAT :=  \"k\" ;");
    b.append("cfg FOR :=  \"l\" ;");
    b.append("cfg GE_OP :=  \"m\" ;");
    b.append("cfg GOTO :=  \"n\" ;");
    b.append("cfg IDENTIFIER :=  \"o\" ;");
    b.append("cfg IF :=  \"p\" ;");
    b.append("cfg INC_OP :=  \"q\" ;");
    b.append("cfg INT :=  \"r\" ;");
    b.append("cfg LEFT_ASSIGN :=  \"s\" ;");
    b.append("cfg LEFT_OP :=  \"t\" ;");
    b.append("cfg LE_OP :=  \"u\" ;");
    b.append("cfg LONG :=  \"v\" ;");
    b.append("cfg MOD_ASSIGN :=  \"w\" ;");
    b.append("cfg MUL_ASSIGN :=  \"x\" ;");
    b.append("NE_OP: \"y\" ;");
    b.append("OR_ASSIGN: \"z\" ;");
    b.append("cfg OR_OP :=  \"A\" ;");
    b.append("cfg PTR_OP :=  \"B\" ;");
    b.append("REGISTER: \"C\" ;");
    b.append("RETURN: \"D\" ;");
    b.append("cfg RIGHT_ASSIGN :=  \"E\" ;");
    b.append("cfg RIGHT_OP :=  \"F\" ;");
    b.append("cfg SHORT :=  \"G\" ;");
    b.append("cfg SIGNED :=  \"H\" ;");
    b.append("SIZEOF: \"I\" ;");
    b.append("cfg STATIC :=  \"J\" ;");
    b.append("cfg STRING_LITERAL :=  \"K\" ;");
    b.append("cfg STRUCT :=  \"L\" ;");
    b.append("cfg SUB_ASSIGN :=  \"M\" ;");
    b.append("cfg SWITCH :=  \"N\" ;");
    b.append("cfg TYPEDEF :=  \"O\" ;");
    b.append("cfg UNION :=  \"P\" ;");
    b.append("UNSIGNED: \"Q\" ;");
    b.append("VOID: \"R\" ;");
    b.append("cfg VOLATILE :=  \"S\" ;");
    b.append("cfg WHILE :=  \"T\" ;");
    b.append("cfg XOR_ASSIGN :=  \"U\" ;");
    b.append("reg limit := fix(start, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_rna5_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  \".\" S | \"(\" S \")\" S | ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_rna4_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  \".\" S | T | ;");
    b.append("cfg T :=  T \".\" | \"(\" S \")\" | T \"(\" S \")\" ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_04_11_047_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg program :=  lines | ;");
    b.append("cfg lines :=  lines line | line ;");
    b.append("cfg line :=  label statements \"n\" ;");
    b.append("cfg label :=  \"l\" | \"L\" | ;");
    b.append("cfg destination :=  \"l\" | \"L\" ;");
    b.append("cfg statements :=  statements \":\" statement | statement | ;");
    b.append("cfg statement :=  instruction ;");
    b
        .append("cfg instruction :=  \"E\" | \"G\" destination | \"g\" destination | \"i\" \"c\" \"t\" statements opt_else | \"i\" \"c\" statements else_if_list opt_else \"E\" \"i\" | \"p\" \"P\" | \"r\" ;");
    b.append("cfg else_if_list :=  else_if_list else_if | else_if ;");
    b.append("cfg else_if :=  \"e\" \"i\" \"c\" statements | ;");
    b.append("cfg opt_else :=  \"e\" statements | ;");
    b.append("reg limit := fix(program, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_rna8_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  \".\" S | T | ;");
    b.append("cfg T :=  T \".\" | \"(\" P \")\" | T \"(\" P \")\" ;");
    b.append("cfg P :=  \"(\" P \")\" | \"(\" N \")\" ;");
    b.append("cfg N :=  \".\" S | T \".\" | T \"(\" P \")\" ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_058_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  A B ;");
    b.append("cfg A :=  | \"a\" A ;");
    b.append("cfg B :=  | \"b\" B ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_voss_buggy_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg struct :=  left_dangle | noleft_dangle ;");
    b.append("cfg left_dangle :=  \".\" left_dangle | edanglel \".\" noleft_dangle | edanglel noleft_dangle_opt | edanglelr left_dangle | ;");
    b.append("cfg noleft_dangle_opt :=  noleft_dangle | ;");
    b.append("cfg noleft_dangle :=  edangler left_dangle | nodangle noleft_dangle_opt | nodangle \".\" noleft_dangle ;");
    b.append("cfg edanglel :=  \".\" initstem ;");
    b.append("cfg edangler :=  initstem \".\" ;");
    b.append("cfg edanglelr :=  \"(\" initstem \")\" ;");
    b.append("cfg nodangle :=  initstem ;");
    b.append("cfg initstem :=  closed ;");
    b.append("cfg closed :=  stack | hairpin | multiloop | leftB | rightB | iloop ;");
    b
        .append("cfg multiloop :=  \"(\" \"(\" \".\" ml_comps1 \")\" \")\" | \"(\" \"(\" \".\" ml_comps2 \")\" \")\" | \"(\" \"(\" ml_comps3 \".\" \")\" \")\" | \"(\" \"(\" ml_comps2 \".\" \")\" \")\" | \"(\" \"(\" \"(\" ml_comps4 \")\" \")\" \")\" | \"(\" \"(\" \"(\" ml_comps2 \")\" \")\" \")\" | \"(\" \"(\" \"(\" ml_comps1 \")\" \")\" \")\" | \"(\" \"(\" \"(\" ml_comps3 \")\" \")\" \")\" | \"(\" \"(\" ml_comps2 \")\" \")\" ;");
    b.append("cfg ml_comps1 :=  block_dl no_dl_no_ss_end | block_dlr dl_or_ss_left_no_ss_end | block_dl \".\" no_dl_no_ss_end ;");
    b.append("cfg ml_comps2 :=  nodangle no_dl_no_ss_end | edangler dl_or_ss_left_no_ss_end | nodangle \".\" no_dl_no_ss_end ;");
    b.append("cfg ml_comps3 :=  nodangle no_dl_ss_end | nodangle \".\" no_dl_ss_end ;");
    b.append("cfg ml_comps4 :=  block_dl no_dl_ss_end | block_dlr dl_or_ss_left_ss_end | block_dl \".\" no_dl_ss_end ;");
    b.append("cfg block_dl :=  region edanglel | edanglel ;");
    b.append("cfg block_dlr :=  region edanglelr | edanglelr ;");
    b.append("cfg no_dl_no_ss_end :=  ml_comps2 | nodangle ;");
    b.append("cfg dl_or_ss_left_no_ss_end :=  ml_comps1 | block_dl ;");
    b.append("cfg no_dl_ss_end :=  ml_comps3 | edangler | edangler region ;");
    b.append("cfg dl_or_ss_left_ss_end :=  ml_comps4 | block_dlr | block_dlr region ;");
    b.append("cfg stack :=  \"(\" closed \")\" ;");
    b.append("cfg hairpin :=  \"(\" \"(\" region \")\" \")\" ;");
    b.append("cfg leftB :=  \"(\" \"(\" region initstem \")\" \")\" ;");
    b.append("cfg rightB :=  \"(\" \"(\" initstem region \")\" \")\" ;");
    b.append("cfg iloop :=  \"(\" \"(\" region closed region \")\" \")\" ;");
    b.append("cfg region :=  \".\" | \".\" region ;");
    b.append("reg limit := fix(struct, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_068_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  \"(\" P \")\" | \".\" S | S \".\" | S S | ;");
    b.append("cfg P :=  \"(\" P \")\" | S ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_pascal_1_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg program :=  PROGRAM newident external_files \";\" block \".\" ;");
    b.append("cfg external_files :=  | \"(\" newident_list \")\" ;");
    b.append("cfg block :=  opt_declarations statement_part ;");
    b.append("opt_declarations: | declarations ;");
    b.append("cfg declarations :=  declarations declaration | declaration ;");
    b.append("cfg declaration :=  label_dcl_part | const_dcl_part | type_dcl_part | var_dcl_part | proc_dcl_part ;");
    b.append("cfg label_dcl_part :=  LABEL labels \";\" ;");
    b.append("cfg labels :=  labels \",\" label | label ;");
    b.append("cfg label :=  UNSIGNED_INT ;");
    b.append("cfg const_dcl_part :=  CONST const_defs \";\" ;");
    b.append("cfg const_defs :=  const_defs \";\" const_def | const_def ;");
    b.append("cfg const_def :=  newident \"=\" constant ;");
    b.append("cfg constant :=  unsigned_num | \"+\" unsigned_num | \"-\" unsigned_num | ident | \"+\" ident | \"-\" ident | STRING ;");
    b.append("cfg unsigned_num :=  UNSIGNED_INT | UNSIGNED_REAL ;");
    b.append("cfg type_dcl_part :=  TYPE type_defs \";\" ;");
    b.append("cfg type_defs :=  type_defs \";\" type_def | type_def ;");
    b.append("cfg type_def :=  newident \"=\" type ;");
    b.append("cfg type :=  simple_type | PACKED struct_type | struct_type | \"^\" IDENTIFIER ;");
    b.append("cfg simple_type :=  \"(\" newident_list \")\" | constant DOTDOT constant | ident ;");
    b.append("cfg struct_type :=  ARRAY \"[\" index_t_list \"]\" OF type | RECORD field_list END | SET OF simple_type | SFILE OF type ;");
    b.append("cfg index_t_list :=  index_t_list \",\" simple_type | simple_type ;");
    b.append("cfg field_list :=  fixed_part | fixed_part \";\" variant_part | variant_part ;");
    b.append("cfg fixed_part :=  fixed_part \";\" record_section | record_section ;");
    b.append("cfg record_section :=  newident_list \":\" type | ;");
    b.append("cfg variant_part :=  CASE tag_field OF variants ;");
    b.append("cfg tag_field :=  newident \":\" ident | ident ;");
    b.append("cfg variants :=  variants \";\" variant | variant ;");
    b.append("cfg variant :=  case_label_list \":\" \"(\" field_list \")\" | ;");
    b.append("cfg var_dcl_part :=  VAR variable_dcls \";\" ;");
    b.append("cfg variable_dcls :=  variable_dcls \";\" variable_dcl | variable_dcl ;");
    b.append("cfg variable_dcl :=  newident_list \":\" type ;");
    b.append("cfg newident_list :=  new_id_list ;");
    b.append("cfg new_id_list :=  new_id_list \",\" newident | newident ;");
    b.append("cfg proc_dcl_part :=  proc_or_func ;");
    b.append("cfg proc_or_func :=  proc_heading \";\" body \";\" | func_heading \";\" body \";\" ;");
    b.append("cfg proc_heading :=  PROCEDURE newident formal_params ;");
    b.append("cfg func_heading :=  FUNCTION newident function_form ;");
    b.append("cfg function_form :=  | formal_params \":\" ident ;");
    b.append("cfg body :=  block | IDENTIFIER ;");
    b.append("cfg formal_params :=  | \"(\" formal_p_sects \")\" ;");
    b.append("cfg formal_p_sects :=  formal_p_sects \";\" formal_p_sect | formal_p_sect ;");
    b.append("cfg formal_p_sect :=  param_group | VAR param_group | proc_heading | func_heading ;");
    b.append("cfg param_group :=  newident_list \":\" paramtype ;");
    b.append("cfg paramtype :=  ident | ARRAY \"[\" index_specs \"]\" OF paramtype | PACKED ARRAY \"[\" index_spec \"]\" OF ident ;");
    b.append("cfg index_specs :=  index_specs \";\" index_spec | index_spec ;");
    b.append("cfg index_spec :=  newident DOTDOT newident \":\" ident ;");
    b.append("cfg statement_part :=  compound_stmt ;");
    b.append("cfg compound_stmt :=  SBEGIN statements END ;");
    b.append("cfg statements :=  statements \";\" statement | statement ;");
    b
        .append("cfg statement :=  | label \":\" statement | compound_stmt | assignment | procedure_call | GOTO label | IF expression THEN statement | IF expression THEN statement ELSE statement | CASE expression OF case_list END | WHILE expression DO statement | REPEAT statements UNTIL expression | FOR ident BECOMES expression direction expression DO statement | WITH rec_var_list DO statement ;");
    b.append("cfg direction :=  TO | DOWNTO ;");
    b.append("cfg assignment :=  variable BECOMES expression ;");
    b.append("cfg procedure_call :=  ident actual_params ;");
    b.append("cfg actual_params :=  | \"(\" actuals_list \")\" ;");
    b.append("cfg actuals_list :=  actuals_list \",\" actual_param | actual_param ;");
    b.append("cfg actual_param :=  expression | expression colon_things ;");
    b.append("cfg colon_things :=  \":\" expression | \":\" expression \":\" expression ;");
    b.append("cfg case_list :=  case_list \";\" case_list_elem | case_list_elem ;");
    b.append("cfg case_list_elem :=  case_label_list \":\" statement | ;");
    b.append("cfg case_label_list :=  case_label_list \",\" case_label | case_label ;");
    b.append("cfg case_label :=  constant ;");
    b.append("cfg rec_var_list :=  rec_var_list \",\" record_var | record_var ;");
    b.append("cfg expression :=  simple_expr | simple_expr relational_op simple_expr ;");
    b.append("cfg relational_op :=  \"=\" | \"<\" | \">\" | LE | GE | NE | IN ;");
    b.append("cfg simple_expr :=  term | \"+\" term | \"-\" term | simple_expr add_op term ;");
    b.append("cfg add_op :=  \"+\" | \"-\" | OR ;");
    b.append("cfg term :=  factor | term mult_op factor ;");
    b.append("cfg mult_op :=  \"*\" | \"/\" | DIV | MOD | AND ;");
    b.append("cfg factor :=  variable | unsigned_lit | \"(\" expression \")\" | set | NOT factor ;");
    b.append("cfg unsigned_lit :=  unsigned_num | STRING | NIL ;");
    b.append("cfg set :=  \"[\" member_list \"]\" ;");
    b.append("cfg member_list :=  | members ;");
    b.append("cfg members :=  members \",\" member | member ;");
    b.append("cfg member :=  expression | expression DOTDOT expression ;");
    b.append("cfg variable :=  ident actual_params | variable \"[\" expressions \"]\" | variable \".\" ident | variable \"^\" ;");
    b.append("cfg expressions :=  expressions \",\" expression | expression ;");
    b.append("cfg record_var :=  variable ;");
    b.append("cfg ident :=  IDENTIFIER ;");
    b.append("cfg newident :=  IDENTIFIER ;");
    b.append("cfg AND :=  \"0\" ;");
    b.append("cfg ARRAY :=  \"1\" ;");
    b.append("cfg BECOMES :=  \"2\" ;");
    b.append("cfg CASE :=  \"3\" ;");
    b.append("cfg CONST :=  \"4\" ;");
    b.append("cfg DIV :=  \"5\" ;");
    b.append("cfg DO :=  \"6\" ;");
    b.append("DOTDOT: \"7\" ;");
    b.append("DOWNTO: \"8\" ;");
    b.append("cfg ELSE :=  \"9\" ;");
    b.append("cfg END :=  \"a\" ;");
    b.append("cfg FOR :=  \"b\" ;");
    b.append("FUNCTION: \"c\" ;");
    b.append("cfg GE :=  \"d\" ;");
    b.append("cfg GOTO :=  \"e\" ;");
    b.append("IDENTIFIER: \"f\" ;");
    b.append("cfg IF :=  \"g\" ;");
    b.append("cfg IN :=  \"h\" ;");
    b.append("cfg LABEL :=  \"i\" ;");
    b.append("cfg LE :=  \"j\" ;");
    b.append("cfg MOD :=  \"k\" ;");
    b.append("cfg NE :=  \"l\" ;");
    b.append("cfg NIL :=  \"m\" ;");
    b.append("cfg NOT :=  \"n\" ;");
    b.append("cfg OF :=  \"o\" ;");
    b.append("cfg OR :=  \"p\" ;");
    b.append("cfg PACKED :=  \"q\" ;");
    b.append("cfg PROCEDURE :=  \"r\" ;");
    b.append("PROGRAM: \"s\" ;");
    b.append("cfg RECORD :=  \"t\" ;");
    b.append("cfg REPEAT :=  \"u\" ;");
    b.append("cfg SBEGIN :=  \"v\" ;");
    b.append("cfg SET :=  \"w\" ;");
    b.append("cfg SFILE :=  \"x\" ;");
    b.append("cfg STRING :=  \"y\" ;");
    b.append("cfg THEN :=  \"z\" ;");
    b.append("cfg TO :=  \"A\" ;");
    b.append("cfg TYPE :=  \"B\" ;");
    b.append("cfg UNSIGNED_INT :=  \"C\" ;");
    b.append("cfg UNSIGNED_REAL :=  \"D\" ;");
    b.append("cfg UNTIL :=  \"E\" ;");
    b.append("cfg VAR :=  \"F\" ;");
    b.append("cfg WHILE :=  \"G\" ;");
    b.append("cfg WITH :=  \"H\" ;");
    b.append("cfg term :=  \"NOT\" term ;");
    b.append("reg limit := fix(program, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_sql_2_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg y_sql :=  y_alter | y_create | y_drop | y_insert | y_select | y_update | y_delete ;");
    b.append("cfg y_alter :=  \"ALTER\" \"TABLE\" y_table \"ADD\" \"COLUMN\" y_columndef | \"ALTER\" \"TABLE\" y_table \"ADD\" y_columndef ;");
    b.append("cfg y_create :=  \"CREATE\" \"TABLE\" y_table \"(\" y_columndefs \")\" ;");
    b.append("cfg y_drop :=  \"DROP\" \"TABLE\" y_table ;");
    b
        .append("cfg y_select :=  \"SELECT\" y_columns \"FROM\" y_table | \"SELECT\" y_columns \"FROM\" y_table \"WHERE\" y_condition | \"SELECT\" y_columns \"FROM\" y_table \"ORDER\" \"BY\" y_order | \"SELECT\" y_columns \"FROM\" y_table \"WHERE\" y_condition \"ORDER\" \"BY\" y_order ;");
    b.append("cfg y_delete :=  \"DELETE\" \"FROM\" y_table | \"DELETE\" \"FROM\" y_table \"WHERE\" y_condition ;");
    b.append("cfg y_insert :=  \"INSERT\" \"INTO\" y_table y_values | \"INSERT\" \"INTO\" y_table \"(\" y_columns \")\" y_values ;");
    b.append("cfg y_update :=  \"UPDATE\" y_table \"SET\" y_assignments | \"UPDATE\" y_table \"SET\" y_assignments \"WHERE\" y_condition ;");
    b.append("cfg y_columndefs :=  y_columndef | y_columndefs \",\" y_columndef ;");
    b
        .append("cfg y_columndef :=  \"NAME\" \"VARCHAR\" \"(\" \"INTNUM\" \")\" | \"NAME\" \"INT\" | \"NAME\" \"INTEGER\" | \"NAME\" \"DOUBLE\" | \"NAME\" \"DOUBLE\" \"PRECISION\" | \"NAME\" \"DATE\" ;");
    b.append("cfg y_columns :=  \"*\" | y_column_list ;");
    b.append("cfg y_column_list :=  \"NAME\" | y_column_list \",\" \"NAME\" ;");
    b.append("cfg y_table :=  \"NAME\" ;");
    b.append("cfg y_values :=  \"VALUES\" \"(\" y_value_list \")\" ;");
    b
        .append("cfg y_value_list :=  \"NULL_VALUE\" | \"STRING\" | \"INTNUM\" | \"-\" \"INTNUM\" | \"FLOATNUM\" | \"-\" \"FLOATNUM\" | y_value_list \",\" \"NULL_VALUE\" | y_value_list \",\" \"STRING\" | y_value_list \",\" \"INTNUM\" | y_value_list \",\" \"-\" \"INTNUM\" | y_value_list \",\" \"FLOATNUM\" | y_value_list \",\" \"-\" \"FLOATNUM\" ;");
    b.append("cfg y_assignments :=  y_assignment | y_assignments \",\" y_assignment ;");
    b.append("cfg y_assignment :=  \"NAME\" \"EQUAL\" \"NULL_VALUE\" | \"NAME\" \"EQUAL\" y_expression ;");
    b.append("cfg y_condition :=  y_sub_condition ;");
    b.append("cfg y_sub_condition :=  y_sub_condition2 | y_sub_condition \"OR\" y_sub_condition2 ;");
    b.append("cfg y_sub_condition2 :=  y_boolean | y_sub_condition2 \"AND\" y_boolean ;");
    b.append("cfg y_boolean :=  y_comparison | \"(\" y_sub_condition \")\" | \"NOT\" y_boolean ;");
    b
        .append("cfg y_comparison :=  y_expression \"EQUAL\" y_expression | y_expression \"COMPARISON_OPERATOR\" y_expression | y_expression \"IS\" \"NULL_VALUE\" | y_expression \"NOT\" \"NULL_VALUE\" ;");
    b.append("cfg y_expression :=  y_product | y_expression \"+\" y_product | y_expression \"-\" y_product ;");
    b.append("cfg y_product :=  y_term | y_product \"*\" y_term | y_product \"/\" y_term ;");
    b.append("cfg y_term :=  y_atom | \"-\" y_term ;");
    b.append("cfg y_atom :=  y_value | y_column | \"(\" y_expression \")\" ;");
    b.append("cfg y_value :=  \"STRING\" | \"INTNUM\" | \"FLOATNUM\" ;");
    b.append("cfg y_column :=  \"NAME\" ;");
    b.append("cfg y_order :=  \"NAME\" ;");
    b.append("cfg y_expression :=  \"(\" y_expression \")\" ;");
    b.append("reg limit := fix(y_sql, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_067_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  | S S | S \".\" | \".\" S | \"(\" S \")\" ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_sql_3_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg y_sql :=  y_alter | y_create | y_drop | y_insert | y_select | y_update | y_delete ;");
    b.append("cfg y_alter :=  \"ALTER\" \"TABLE\" y_table \"ADD\" \"COLUMN\" y_columndef | \"ALTER\" \"TABLE\" y_table \"ADD\" y_columndef ;");
    b.append("cfg y_create :=  \"CREATE\" \"TABLE\" y_table \"(\" y_columndefs \")\" ;");
    b.append("cfg y_drop :=  \"DROP\" \"TABLE\" y_table ;");
    b
        .append("cfg y_select :=  \"SELECT\" y_columns \"FROM\" y_table | \"SELECT\" y_columns \"FROM\" y_table \"WHERE\" y_condition | \"SELECT\" y_columns \"FROM\" y_table \"ORDER\" \"BY\" y_order | \"SELECT\" y_columns \"FROM\" y_table \"WHERE\" y_condition \"ORDER\" \"BY\" y_order ;");
    b.append("cfg y_delete :=  \"DELETE\" \"FROM\" y_table | \"DELETE\" \"FROM\" y_table \"WHERE\" y_condition ;");
    b.append("cfg y_insert :=  \"INSERT\" \"INTO\" y_table y_values | \"INSERT\" \"INTO\" y_table \"(\" y_columns \")\" y_values ;");
    b.append("cfg y_update :=  \"UPDATE\" y_table \"SET\" y_assignments | \"UPDATE\" y_table \"SET\" y_assignments \"WHERE\" y_condition ;");
    b.append("cfg y_columndefs :=  y_columndef | y_columndefs \",\" y_columndef ;");
    b
        .append("cfg y_columndef :=  \"NAME\" \"VARCHAR\" \"(\" \"INTNUM\" \")\" | \"NAME\" \"INT\" | \"NAME\" \"INTEGER\" | \"NAME\" \"DOUBLE\" | \"NAME\" \"DOUBLE\" \"PRECISION\" | \"NAME\" \"DATE\" ;");
    b.append("cfg y_columns :=  \"*\" | y_column_list ;");
    b.append("cfg y_column_list :=  \"NAME\" | y_column_list \",\" \"NAME\" ;");
    b.append("cfg y_table :=  \"NAME\" ;");
    b.append("cfg y_values :=  \"VALUES\" \"(\" y_value_list \")\" ;");
    b
        .append("cfg y_value_list :=  \"NULL_VALUE\" | \"STRING\" | \"INTNUM\" | \"-\" \"INTNUM\" | \"FLOATNUM\" | \"-\" \"FLOATNUM\" | y_value_list \",\" \"NULL_VALUE\" | y_value_list \",\" \"STRING\" | y_value_list \",\" \"INTNUM\" | y_value_list \",\" \"-\" \"INTNUM\" | y_value_list \",\" \"FLOATNUM\" | y_value_list \",\" \"-\" \"FLOATNUM\" ;");
    b.append("cfg y_assignments :=  y_assignment | y_assignments \",\" y_assignment ;");
    b.append("cfg y_assignment :=  \"NAME\" \"EQUAL\" \"NULL_VALUE\" | \"NAME\" \"EQUAL\" y_expression ;");
    b.append("cfg y_condition :=  y_sub_condition ;");
    b.append("cfg y_sub_condition :=  y_sub_condition2 | y_sub_condition \"OR\" y_sub_condition2 ;");
    b.append("cfg y_sub_condition2 :=  y_boolean | y_sub_condition2 \"AND\" y_boolean ;");
    b.append("cfg y_boolean :=  y_comparison | \"(\" y_sub_condition \")\" | \"NOT\" y_boolean ;");
    b
        .append("cfg y_comparison :=  y_expression \"EQUAL\" y_expression | y_expression \"COMPARISON_OPERATOR\" y_expression | y_expression \"IS\" \"NULL_VALUE\" | y_expression \"NOT\" \"NULL_VALUE\" ;");
    b.append("cfg y_expression :=  y_product | y_expression \"+\" y_product | y_expression \"-\" y_product ;");
    b.append("cfg y_product :=  y_term | y_product \"*\" y_term | y_product \"/\" y_term ;");
    b.append("cfg y_term :=  y_atom | \"-\" y_term ;");
    b.append("cfg y_atom :=  y_value | y_column | \"(\" y_expression \")\" ;");
    b.append("cfg y_value :=  \"STRING\" | \"INTNUM\" | \"FLOATNUM\" ;");
    b.append("cfg y_column :=  \"NAME\" ;");
    b.append("cfg y_order :=  \"NAME\" ;");
    b.append("cfg y_value :=  \"NULL_VALUE\" ;");
    b.append("reg limit := fix(y_sql, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_test1_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  S \"a\" | \"a\" S | ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_sql_5_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg y_sql :=  y_alter | y_create | y_drop | y_insert | y_select | y_update | y_delete ;");
    b.append("cfg y_alter :=  \"ALTER\" \"TABLE\" y_table \"ADD\" \"COLUMN\" y_columndef | \"ALTER\" \"TABLE\" y_table \"ADD\" y_columndef ;");
    b.append("cfg y_create :=  \"CREATE\" \"TABLE\" y_table \"(\" y_columndefs \")\" ;");
    b.append("cfg y_drop :=  \"DROP\" \"TABLE\" y_table ;");
    b
        .append("cfg y_select :=  \"SELECT\" y_columns \"FROM\" y_table | \"SELECT\" y_columns \"FROM\" y_table \"WHERE\" y_condition | \"SELECT\" y_columns \"FROM\" y_table \"ORDER\" \"BY\" y_order | \"SELECT\" y_columns \"FROM\" y_table \"WHERE\" y_condition \"ORDER\" \"BY\" y_order ;");
    b.append("cfg y_delete :=  \"DELETE\" \"FROM\" y_table | \"DELETE\" \"FROM\" y_table \"WHERE\" y_condition ;");
    b.append("cfg y_insert :=  \"INSERT\" \"INTO\" y_table y_values | \"INSERT\" \"INTO\" y_table \"(\" y_columns \")\" y_values ;");
    b.append("cfg y_update :=  \"UPDATE\" y_table \"SET\" y_assignments | \"UPDATE\" y_table \"SET\" y_assignments \"WHERE\" y_condition ;");
    b.append("cfg y_columndefs :=  y_columndef | y_columndefs \",\" y_columndef ;");
    b
        .append("cfg y_columndef :=  \"NAME\" \"VARCHAR\" \"(\" \"INTNUM\" \")\" | \"NAME\" \"INT\" | \"NAME\" \"INTEGER\" | \"NAME\" \"DOUBLE\" | \"NAME\" \"DOUBLE\" \"PRECISION\" | \"NAME\" \"DATE\" ;");
    b.append("cfg y_columns :=  \"*\" | y_column_list ;");
    b.append("cfg y_column_list :=  \"NAME\" | y_column_list \",\" \"NAME\" ;");
    b.append("cfg y_table :=  \"NAME\" ;");
    b.append("cfg y_values :=  \"VALUES\" \"(\" y_value_list \")\" ;");
    b
        .append("cfg y_value_list :=  \"NULL_VALUE\" | \"STRING\" | \"INTNUM\" | \"-\" \"INTNUM\" | \"FLOATNUM\" | \"-\" \"FLOATNUM\" | y_value_list \",\" \"NULL_VALUE\" | y_value_list \",\" \"STRING\" | y_value_list \",\" \"INTNUM\" | y_value_list \",\" \"-\" \"INTNUM\" | y_value_list \",\" \"FLOATNUM\" | y_value_list \",\" \"-\" \"FLOATNUM\" ;");
    b.append("cfg y_assignments :=  y_assignment | y_assignments \",\" y_assignment ;");
    b.append("cfg y_assignment :=  \"NAME\" \"EQUAL\" \"NULL_VALUE\" | \"NAME\" \"EQUAL\" y_expression ;");
    b.append("cfg y_condition :=  y_sub_condition ;");
    b.append("cfg y_sub_condition :=  y_sub_condition2 | y_sub_condition \"OR\" y_sub_condition2 ;");
    b.append("cfg y_sub_condition2 :=  y_boolean | y_sub_condition2 \"AND\" y_boolean ;");
    b.append("cfg y_boolean :=  y_comparison | \"(\" y_sub_condition \")\" | \"NOT\" y_boolean ;");
    b
        .append("cfg y_comparison :=  y_expression \"EQUAL\" y_expression | y_expression \"COMPARISON_OPERATOR\" y_expression | y_expression \"IS\" \"NULL_VALUE\" | y_expression \"NOT\" \"NULL_VALUE\" ;");
    b.append("cfg y_expression :=  y_product | y_expression \"+\" y_product | y_expression \"-\" y_product ;");
    b.append("cfg y_product :=  y_term | y_product \"*\" y_term | y_product \"/\" y_term ;");
    b.append("cfg y_term :=  y_atom | \"-\" y_term ;");
    b.append("cfg y_atom :=  y_value | y_column | \"(\" y_expression \")\" ;");
    b.append("cfg y_value :=  \"STRING\" | \"INTNUM\" | \"FLOATNUM\" ;");
    b.append("cfg y_column :=  \"NAME\" ;");
    b.append("cfg y_order :=  \"NAME\" ;");
    b.append("cfg y_sub_condition2 :=  y_boolean \"ORDER\" \"BY\" y_order ;");
    b.append("reg limit := fix(y_sql, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_voss_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg struct :=  left_dangle | noleft_dangle ;");
    b.append("cfg left_dangle :=  \".\" left_dangle | edanglel \".\" noleft_dangle | edanglel noleft_dangle_opt | edanglelr left_dangle | ;");
    b.append("cfg noleft_dangle_opt :=  noleft_dangle | ;");
    b.append("cfg noleft_dangle :=  edangler left_dangle | nodangle noleft_dangle_opt | nodangle \".\" noleft_dangle ;");
    b.append("cfg edanglel :=  \".\" initstem ;");
    b.append("cfg edangler :=  initstem \".\" ;");
    b.append("cfg edanglelr :=  \".\" initstem \".\" ;");
    b.append("cfg nodangle :=  initstem ;");
    b.append("cfg initstem :=  closed ;");
    b.append("cfg closed :=  stack | hairpin | multiloop | leftB | rightB | iloop ;");
    b
        .append("cfg multiloop :=  \"(\" \"(\" \".\" ml_comps1 \")\" \")\" | \"(\" \"(\" \".\" ml_comps2 \")\" \")\" | \"(\" \"(\" ml_comps3 \".\" \")\" \")\" | \"(\" \"(\" ml_comps2 \".\" \")\" \")\" | \"(\" \"(\" \".\" ml_comps4 \".\" \")\" \")\" | \"(\" \"(\" \".\" ml_comps2 \".\" \")\" \")\" | \"(\" \"(\" \".\" ml_comps1 \".\" \")\" \")\" | \"(\" \"(\" \".\" ml_comps3 \".\" \")\" \")\" | \"(\" \"(\" ml_comps2 \")\" \")\" ;");
    b.append("cfg ml_comps1 :=  block_dl no_dl_no_ss_end | block_dlr dl_or_ss_left_no_ss_end | block_dl \".\" no_dl_no_ss_end ;");
    b.append("cfg ml_comps2 :=  nodangle no_dl_no_ss_end | edangler dl_or_ss_left_no_ss_end | nodangle \".\" no_dl_no_ss_end ;");
    b.append("cfg ml_comps3 :=  nodangle no_dl_ss_end | nodangle \".\" no_dl_ss_end ;");
    b.append("cfg ml_comps4 :=  block_dl no_dl_ss_end | block_dlr dl_or_ss_left_ss_end | block_dl \".\" no_dl_ss_end ;");
    b.append("cfg block_dl :=  region edanglel | edanglel ;");
    b.append("cfg block_dlr :=  region edanglelr | edanglelr ;");
    b.append("cfg no_dl_no_ss_end :=  ml_comps2 | nodangle ;");
    b.append("cfg dl_or_ss_left_no_ss_end :=  ml_comps1 | block_dl ;");
    b.append("cfg no_dl_ss_end :=  ml_comps3 | edangler | edangler region ;");
    b.append("cfg dl_or_ss_left_ss_end :=  ml_comps4 | block_dlr | block_dlr region ;");
    b.append("cfg stack :=  \"(\" closed \")\" ;");
    b.append("cfg hairpin :=  \"(\" \"(\" region \")\" \")\" ;");
    b.append("cfg leftB :=  \"(\" \"(\" region initstem \")\" \")\" ;");
    b.append("cfg rightB :=  \"(\" \"(\" initstem region \")\" \")\" ;");
    b.append("cfg iloop :=  \"(\" \"(\" region closed region \")\" \")\" ;");
    b.append("cfg region :=  \".\" | \".\" region ;");
    b.append("reg limit := fix(struct, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_c_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg start :=  translation_unit ;");
    b.append("cfg primary_expression :=  IDENTIFIER | CONSTANT | STRING_LITERAL | \"(\" expression \")\" ;");
    b
        .append("cfg postfix_expression :=  primary_expression | postfix_expression \"[\" expression \"]\" | postfix_expression \"(\" \")\" | postfix_expression \"(\" argument_expression_list \")\" | postfix_expression \".\" IDENTIFIER | postfix_expression PTR_OP IDENTIFIER | postfix_expression INC_OP | postfix_expression DEC_OP ;");
    b.append("cfg argument_expression_list :=  assignment_expression | argument_expression_list \",\" assignment_expression ;");
    b
        .append("cfg unary_expression :=  postfix_expression | INC_OP unary_expression | DEC_OP unary_expression | unary_operator cast_expression | SIZEOF unary_expression | SIZEOF \"(\" type_name \")\" ;");
    b.append("cfg unary_operator :=  \"&\" | \"*\" | \"+\" | \"-\" | \"~\" | \"!\" ;");
    b.append("cfg cast_expression :=  unary_expression | \"(\" type_name \")\" cast_expression ;");
    b
        .append("cfg multiplicative_expression :=  cast_expression | multiplicative_expression \"*\" cast_expression | multiplicative_expression \"/\" cast_expression | multiplicative_expression \"%\" cast_expression ;");
    b.append("cfg additive_expression :=  multiplicative_expression | additive_expression \"+\" multiplicative_expression | additive_expression \"-\" multiplicative_expression ;");
    b.append("cfg shift_expression :=  additive_expression | shift_expression LEFT_OP additive_expression | shift_expression RIGHT_OP additive_expression ;");
    b
        .append("cfg relational_expression :=  shift_expression | relational_expression \"<\" shift_expression | relational_expression \">\" shift_expression | relational_expression LE_OP shift_expression | relational_expression GE_OP shift_expression ;");
    b.append("cfg equality_expression :=  relational_expression | equality_expression EQ_OP relational_expression | equality_expression NE_OP relational_expression ;");
    b.append("cfg and_expression :=  equality_expression | and_expression \"&\" equality_expression ;");
    b.append("cfg exclusive_or_expression :=  and_expression | exclusive_or_expression \"^\" and_expression ;");
    b.append("cfg inclusive_or_expression :=  exclusive_or_expression | inclusive_or_expression \":\" exclusive_or_expression ;");
    b.append("cfg logical_and_expression :=  inclusive_or_expression | logical_and_expression AND_OP inclusive_or_expression ;");
    b.append("cfg logical_or_expression :=  logical_and_expression | logical_or_expression OR_OP logical_and_expression ;");
    b.append("cfg conditional_expression :=  logical_or_expression | logical_or_expression \"?\" expression \":\" conditional_expression ;");
    b.append("cfg assignment_expression :=  conditional_expression | unary_expression assignment_operator assignment_expression ;");
    b.append("cfg assignment_operator :=  \"=\" | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN | ADD_ASSIGN | SUB_ASSIGN | LEFT_ASSIGN | RIGHT_ASSIGN | AND_ASSIGN | XOR_ASSIGN | OR_ASSIGN ;");
    b.append("cfg expression :=  assignment_expression | expression \",\" assignment_expression ;");
    b.append("cfg constant_expression :=  conditional_expression ;");
    b.append("cfg declaration :=  declaration_specifiers \";\" | declaration_specifiers init_declarator_list \";\" ;");
    b
        .append("cfg declaration_specifiers :=  storage_class_specifier | storage_class_specifier declaration_specifiers | type_specifier | type_specifier declaration_specifiers | type_qualifier | type_qualifier declaration_specifiers ;");
    b.append("cfg init_declarator_list :=  init_declarator | init_declarator_list \",\" init_declarator ;");
    b.append("cfg init_declarator :=  declarator | declarator \"=\" initializer ;");
    b.append("cfg storage_class_specifier :=  TYPEDEF | EXTERN | STATIC | AUTO | REGISTER ;");
    b.append("cfg type_specifier :=  VOID | CHAR | SHORT | INT | LONG | FLOAT | DOUBLE | SIGNED | UNSIGNED | struct_or_union_specifier | enum_specifier | TYPE_NAME ;");
    b.append("cfg struct_or_union_specifier :=  struct_or_union IDENTIFIER \"{\" struct_declaration_list \"}\" | struct_or_union \"{\" struct_declaration_list \"}\" | struct_or_union IDENTIFIER ;");
    b.append("cfg struct_or_union :=  STRUCT | UNION ;");
    b.append("cfg struct_declaration_list :=  struct_declaration | struct_declaration_list struct_declaration ;");
    b.append("cfg struct_declaration :=  specifier_qualifier_list struct_declarator_list \";\" ;");
    b.append("cfg specifier_qualifier_list :=  type_specifier specifier_qualifier_list | type_specifier | type_qualifier specifier_qualifier_list | type_qualifier ;");
    b.append("cfg struct_declarator_list :=  struct_declarator | struct_declarator_list \",\" struct_declarator ;");
    b.append("cfg struct_declarator :=  declarator | \":\" constant_expression | declarator \":\" constant_expression ;");
    b.append("cfg enum_specifier :=  ENUM \"{\" enumerator_list \"}\" | ENUM IDENTIFIER \"{\" enumerator_list \"}\" | ENUM IDENTIFIER ;");
    b.append("cfg enumerator_list :=  enumerator | enumerator_list \",\" enumerator ;");
    b.append("cfg enumerator :=  IDENTIFIER | IDENTIFIER \"=\" constant_expression ;");
    b.append("cfg type_qualifier :=  CONST | VOLATILE ;");
    b.append("cfg declarator :=  pointer direct_declarator | direct_declarator ;");
    b
        .append("cfg direct_declarator :=  IDENTIFIER | \"(\" declarator \")\" | direct_declarator \"[\" constant_expression \"]\" | direct_declarator \"[\" \"]\" | direct_declarator \"(\" parameter_type_list \")\" | direct_declarator \"(\" identifier_list \")\" | direct_declarator \"(\" \")\" ;");
    b.append("cfg pointer :=  \"*\" | \"*\" type_qualifier_list | \"*\" pointer | \"*\" type_qualifier_list pointer ;");
    b.append("cfg type_qualifier_list :=  type_qualifier | type_qualifier_list type_qualifier ;");
    b.append("cfg parameter_type_list :=  parameter_list | parameter_list \",\" ELLIPSIS ;");
    b.append("cfg parameter_list :=  parameter_declaration | parameter_list \",\" parameter_declaration ;");
    b.append("cfg parameter_declaration :=  declaration_specifiers declarator | declaration_specifiers abstract_declarator | declaration_specifiers ;");
    b.append("cfg identifier_list :=  IDENTIFIER | identifier_list \",\" IDENTIFIER ;");
    b.append("cfg type_name :=  specifier_qualifier_list | specifier_qualifier_list abstract_declarator ;");
    b.append("cfg abstract_declarator :=  pointer | direct_abstract_declarator | pointer direct_abstract_declarator ;");
    b
        .append("cfg direct_abstract_declarator :=  \"(\" abstract_declarator \")\" | \"[\" \"]\" | \"[\" constant_expression \"]\" | direct_abstract_declarator \"[\" \"]\" | direct_abstract_declarator \"[\" constant_expression \"]\" | \"(\" \")\" | \"(\" parameter_type_list \")\" | direct_abstract_declarator \"(\" \")\" | direct_abstract_declarator \"(\" parameter_type_list \")\" ;");
    b.append("cfg initializer :=  assignment_expression | \"{\" initializer_list \"}\" | \"{\" initializer_list \",\" \"}\" ;");
    b.append("cfg initializer_list :=  initializer | initializer_list \",\" initializer ;");
    b.append("cfg statement :=  labeled_statement | compound_statement | expression_statement | selection_statement | iteration_statement | jump_statement ;");
    b.append("cfg labeled_statement :=  IDENTIFIER \":\" statement | CASE constant_expression \":\" statement | DEFAULT \":\" statement ;");
    b.append("cfg compound_statement :=  \"{\" \"}\" | \"{\" statement_list \"}\" | \"{\" declaration_list \"}\" | \"{\" declaration_list statement_list \"}\" ;");
    b.append("cfg declaration_list :=  declaration | declaration_list declaration ;");
    b.append("cfg statement_list :=  statement | statement_list statement ;");
    b.append("cfg expression_statement :=  \";\" | expression \";\" ;");
    b.append("cfg selection_statement :=  IF \"(\" expression \")\" statement | IF \"(\" expression \")\" statement ELSE statement | SWITCH \"(\" expression \")\" statement ;");
    b
        .append("cfg iteration_statement :=  WHILE \"(\" expression \")\" statement | DO statement WHILE \"(\" expression \")\" \";\" | FOR \"(\" expression_statement expression_statement \")\" statement | FOR \"(\" expression_statement expression_statement expression \")\" statement ;");
    b.append("cfg jump_statement :=  GOTO IDENTIFIER \";\" | CONTINUE \";\" | BREAK \";\" | RETURN \";\" | RETURN expression \";\" ;");
    b.append("cfg translation_unit :=  external_declaration | translation_unit external_declaration ;");
    b.append("cfg external_declaration :=  function_definition | declaration ;");
    b
        .append("cfg function_definition :=  declaration_specifiers declarator declaration_list compound_statement | declaration_specifiers declarator compound_statement | declarator declaration_list compound_statement | declarator compound_statement ;");
    b.append("cfg ADD_ASSIGN :=  \"0\" ;");
    b.append("cfg AND_ASSIGN :=  \"1\" ;");
    b.append("cfg AND_OP :=  \"2\" ;");
    b.append("cfg AUTO :=  \"3\" ;");
    b.append("cfg BREAK :=  \"4\" ;");
    b.append("cfg CASE :=  \"5\" ;");
    b.append("cfg CHAR :=  \"6\" ;");
    b.append("cfg CONST :=  \"7\" ;");
    b.append("cfg CONSTANT :=  \"8\" ;");
    b.append("cfg CONTINUE :=  \"9\" ;");
    b.append("cfg DEC_OP :=  \"a\" ;");
    b.append("cfg DEFAULT :=  \"b\" ;");
    b.append("cfg DIV_ASSIGN :=  \"c\" ;");
    b.append("cfg DO :=  \"d\" ;");
    b.append("cfg DOUBLE :=  \"e\" ;");
    b.append("ELLIPSIS: \"f\" ;");
    b.append("cfg ELSE :=  \"g\" ;");
    b.append("cfg ENUM :=  \"h\" ;");
    b.append("cfg EQ_OP :=  \"i\" ;");
    b.append("cfg EXTERN :=  \"j\" ;");
    b.append("cfg FLOAT :=  \"k\" ;");
    b.append("cfg FOR :=  \"l\" ;");
    b.append("cfg GE_OP :=  \"m\" ;");
    b.append("cfg GOTO :=  \"n\" ;");
    b.append("cfg IDENTIFIER :=  \"o\" ;");
    b.append("cfg IF :=  \"p\" ;");
    b.append("cfg INC_OP :=  \"q\" ;");
    b.append("cfg INT :=  \"r\" ;");
    b.append("cfg LEFT_ASSIGN :=  \"s\" ;");
    b.append("cfg LEFT_OP :=  \"t\" ;");
    b.append("cfg LE_OP :=  \"u\" ;");
    b.append("cfg LONG :=  \"v\" ;");
    b.append("cfg MOD_ASSIGN :=  \"w\" ;");
    b.append("cfg MUL_ASSIGN :=  \"x\" ;");
    b.append("NE_OP: \"y\" ;");
    b.append("OR_ASSIGN: \"z\" ;");
    b.append("cfg OR_OP :=  \"A\" ;");
    b.append("cfg PTR_OP :=  \"B\" ;");
    b.append("REGISTER: \"C\" ;");
    b.append("RETURN: \"D\" ;");
    b.append("cfg RIGHT_ASSIGN :=  \"E\" ;");
    b.append("cfg RIGHT_OP :=  \"F\" ;");
    b.append("cfg SHORT :=  \"G\" ;");
    b.append("cfg SIGNED :=  \"H\" ;");
    b.append("SIZEOF: \"I\" ;");
    b.append("cfg STATIC :=  \"J\" ;");
    b.append("cfg STRING_LITERAL :=  \"K\" ;");
    b.append("cfg STRUCT :=  \"L\" ;");
    b.append("cfg SUB_ASSIGN :=  \"M\" ;");
    b.append("cfg SWITCH :=  \"N\" ;");
    b.append("cfg TYPEDEF :=  \"O\" ;");
    b.append("cfg UNION :=  \"P\" ;");
    b.append("UNSIGNED: \"Q\" ;");
    b.append("VOID: \"R\" ;");
    b.append("cfg VOLATILE :=  \"S\" ;");
    b.append("cfg WHILE :=  \"T\" ;");
    b.append("cfg XOR_ASSIGN :=  \"U\" ;");
    b.append("cfg TYPE_NAME :=  \"V\" ;");
    b.append("reg limit := fix(start, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_java_0_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg goal :=  compilation_unit ;");
    b.append("cfg literal :=  \"INT_LIT_TK\" | \"FP_LIT_TK\" | \"BOOL_LIT_TK\" | \"CHAR_LIT_TK\" | \"STRING_LIT_TK\" | \"NULL_TK\" ;");
    b.append("cfg type :=  primitive_type | reference_type ;");
    b.append("cfg primitive_type :=  \"INTEGRAL_TK\" | \"FP_TK\" | \"BOOLEAN_TK\" ;");
    b.append("cfg reference_type :=  class_or_interface_type | array_type ;");
    b.append("cfg class_or_interface_type :=  name ;");
    b.append("cfg class_type :=  class_or_interface_type ;");
    b.append("cfg interface_type :=  class_or_interface_type ;");
    b.append("cfg array_type :=  primitive_type dims | name dims ;");
    b.append("cfg name :=  simple_name ;");
    b.append("cfg simple_name :=  identifier ;");
    b.append("cfg qualified_name :=  name \"DOT_TK\" identifier ;");
    b.append("cfg identifier :=  \"ID_TK\" ;");
    b
        .append("cfg compilation_unit :=  package_declaration | import_declarations | type_declarations | package_declaration import_declarations | package_declaration type_declarations | import_declarations type_declarations | package_declaration import_declarations type_declarations ;");
    b.append("cfg import_declarations :=  import_declaration | import_declarations import_declaration ;");
    b.append("cfg type_declarations :=  type_declaration | type_declarations type_declaration ;");
    b.append("cfg package_declaration :=  \"PACKAGE_TK\" name \"SC_TK\" | \"PACKAGE_TK\" error | \"PACKAGE_TK\" name error ;");
    b.append("cfg import_declaration :=  single_type_import_declaration | type_import_on_demand_declaration ;");
    b.append("cfg single_type_import_declaration :=  \"IMPORT_TK\" name \"SC_TK\" | \"IMPORT_TK\" error | \"IMPORT_TK\" name error ;");
    b.append("cfg type_import_on_demand_declaration :=  \"IMPORT_TK\" name \"DOT_TK\" \"MULT_TK\" \"SC_TK\" | \"IMPORT_TK\" name \"DOT_TK\" error | \"IMPORT_TK\" name \"DOT_TK\" \"MULT_TK\" error ;");
    b.append("cfg type_declaration :=  class_declaration | interface_declaration | empty_statement | error ;");
    b.append("cfg modifiers :=  \"MODIFIER_TK\" | modifiers \"MODIFIER_TK\" ;");
    b
        .append("cfg class_declaration :=  modifiers \"CLASS_TK\" identifier super interfacesclass_body | \"CLASS_TK\" identifier super interfacesclass_body | modifiers \"CLASS_TK\" error | \"CLASS_TK\" error | \"CLASS_TK\" identifier error | modifiers \"CLASS_TK\" identifier error ;");
    b.append("cfg super :=  \"EXTENDS_TK\" class_type | \"EXTENDS_TK\" class_type error | \"EXTENDS_TK\" error ;");
    b.append("cfg interfaces :=  \"IMPLEMENTS_TK\" interface_type_list | \"IMPLEMENTS_TK\" error ;");
    b.append("cfg interface_type_list :=  interface_type | interface_type_list \"C_TK\" interface_type | interface_type_list \"C_TK\" error ;");
    b.append("cfg class_body :=  \"OCB_TK\" \"CCB_TK\" | \"OCB_TK\" class_body_declarations \"CCB_TK\" ;");
    b.append("cfg class_body_declarations :=  class_body_declaration | class_body_declarations class_body_declaration ;");
    b.append("cfg class_body_declaration :=  class_member_declaration | static_initializer | constructor_declaration | block ;");
    b.append("cfg class_member_declaration :=  field_declaration | method_declaration | class_declaration | empty_statement ;");
    b.append("cfg field_declaration :=  type variable_declarators \"SC_TK\" | modifiers type variable_declarators \"SC_TK\" ;");
    b.append("cfg variable_declarators :=  variable_declarator | variable_declarators \"C_TK\" variable_declarator | variable_declarators \"C_TK\" error ;");
    b
        .append("cfg variable_declarator :=  variable_declarator_id | variable_declarator_id \"ASSIGN_TK\" variable_initializer | variable_declarator_id \"ASSIGN_TK\" error | variable_declarator_id \"ASSIGN_TK\" variable_initializer error ;");
    b
        .append("cfg variable_declarator_id :=  identifier | variable_declarator_id \"OSB_TK\" \"CSB_TK\" | identifier error | variable_declarator_id \"OSB_TK\" error | variable_declarator_id \"CSB_TK\" error ;");
    b.append("cfg variable_initializer :=  expression | array_initializer ;");
    b.append("cfg method_declaration :=  method_headermethod_body | method_header error ;");
    b
        .append("cfg method_header :=  type method_declarator throws | \"VOID_TK\" method_declarator throws | modifiers type method_declarator throws | modifiers \"VOID_TK\" method_declarator throws | type error | modifiers type error | \"VOID_TK\" error | modifiers \"VOID_TK\" error | modifiers error ;");
    b
        .append("cfg method_declarator :=  identifier \"OP_TK\" \"CP_TK\" | identifier \"OP_TK\" formal_parameter_list \"CP_TK\" | method_declarator \"OSB_TK\" \"CSB_TK\" | identifier \"OP_TK\" error | method_declarator \"OSB_TK\" error ;");
    b.append("cfg formal_parameter_list :=  formal_parameter | formal_parameter_list \"C_TK\" formal_parameter | formal_parameter_list \"C_TK\" error ;");
    b.append("cfg formal_parameter :=  type variable_declarator_id | final type variable_declarator_id | type error | final type error ;");
    b.append("cfg final :=  modifiers ;");
    b.append("cfg throws :=  \"THROWS_TK\" class_type_list | \"THROWS_TK\" error ;");
    b.append("cfg class_type_list :=  class_type | class_type_list \"C_TK\" class_type | class_type_list \"C_TK\" error ;");
    b.append("cfg method_body :=  block | \"SC_TK\" ;");
    b.append("cfg static_initializer :=  static block ;");
    b.append("cfg static :=  modifiers ;");
    b.append("cfg constructor_declaration :=  constructor_headerconstructor_body ;");
    b.append("cfg constructor_header :=  constructor_declarator throws | modifiers constructor_declarator throws ;");
    b.append("cfg constructor_declarator :=  simple_name \"OP_TK\" \"CP_TK\" | simple_name \"OP_TK\" formal_parameter_list \"CP_TK\" ;");
    b
        .append("cfg constructor_body :=  block_begin constructor_block_end | block_begin explicit_constructor_invocation constructor_block_end | block_begin block_statements constructor_block_end | block_begin explicit_constructor_invocation block_statements constructor_block_end ;");
    b.append("cfg constructor_block_end :=  block_end ;");
    b
        .append("cfg explicit_constructor_invocation :=  this_or_super \"OP_TK\" \"CP_TK\" \"SC_TK\" | this_or_super \"OP_TK\" argument_list \"CP_TK\" \"SC_TK\" | name \"DOT_TK\" \"SUPER_TK\" \"OP_TK\" argument_list \"CP_TK\" \"SC_TK\" | name \"DOT_TK\" \"SUPER_TK\" \"OP_TK\" \"CP_TK\" \"SC_TK\" ;");
    b.append("cfg this_or_super :=  \"THIS_TK\" | \"SUPER_TK\" ;");
    b
        .append("cfg interface_declaration :=  \"INTERFACE_TK\" identifierinterface_body | modifiers \"INTERFACE_TK\" identifierinterface_body | \"INTERFACE_TK\" identifier extends_interfacesinterface_body | modifiers \"INTERFACE_TK\" identifier extends_interfacesinterface_body | \"INTERFACE_TK\" identifier error | modifiers \"INTERFACE_TK\" identifier error ;");
    b.append("cfg extends_interfaces :=  \"EXTENDS_TK\" interface_type | extends_interfaces \"C_TK\" interface_type | \"EXTENDS_TK\" error | extends_interfaces \"C_TK\" error ;");
    b.append("cfg interface_body :=  \"OCB_TK\" \"CCB_TK\" | \"OCB_TK\" interface_member_declarations \"CCB_TK\" ;");
    b.append("cfg interface_member_declarations :=  interface_member_declaration | interface_member_declarations interface_member_declaration ;");
    b.append("cfg interface_member_declaration :=  constant_declaration | abstract_method_declaration | class_declaration ;");
    b.append("cfg constant_declaration :=  field_declaration ;");
    b.append("cfg abstract_method_declaration :=  method_header \"SC_TK\" | method_header error ;");
    b.append("cfg array_initializer :=  \"OCB_TK\" \"CCB_TK\" | \"OCB_TK\" \"C_TK\" \"CCB_TK\" | \"OCB_TK\" variable_initializers \"CCB_TK\" | \"OCB_TK\" variable_initializers \"C_TK\" \"CCB_TK\" ;");
    b.append("cfg variable_initializers :=  variable_initializer | variable_initializers \"C_TK\" variable_initializer | variable_initializers \"C_TK\" error ;");
    b.append("cfg block :=  block_begin block_end | block_begin block_statements block_end ;");
    b.append("cfg block_begin :=  \"OCB_TK\" ;");
    b.append("cfg block_end :=  \"CCB_TK\" ;");
    b.append("cfg block_statements :=  block_statement | block_statements block_statement ;");
    b.append("cfg block_statement :=  local_variable_declaration_statement | statement | class_declaration ;");
    b.append("cfg local_variable_declaration_statement :=  local_variable_declaration \"SC_TK\" ;");
    b.append("cfg local_variable_declaration :=  type variable_declarators | final type variable_declarators ;");
    b.append("cfg statement :=  statement_without_trailing_substatement | labeled_statement | if_then_statement | if_then_else_statement | while_statement | for_statement ;");
    b.append("cfg statement_nsi :=  statement_without_trailing_substatement | labeled_statement_nsi | if_then_else_statement_nsi | while_statement_nsi | for_statement_nsi ;");
    b
        .append("cfg statement_without_trailing_substatement :=  block | empty_statement | expression_statement | switch_statement | do_statement | break_statement | continue_statement | return_statement | synchronized_statement | throw_statement | try_statement | assert_statement ;");
    b.append("cfg empty_statement :=  \"SC_TK\" ;");
    b.append("cfg label_decl :=  identifier \"REL_CL_TK\" ;");
    b.append("cfg labeled_statement :=  label_decl statement | identifier error ;");
    b.append("cfg labeled_statement_nsi :=  label_decl statement_nsi ;");
    b
        .append("cfg expression_statement :=  statement_expression \"SC_TK\" | error \"SC_TK\" | error \"OCB_TK\" | error \"CCB_TK\" | this_or_super \"OP_TK\" error | this_or_super \"OP_TK\" \"CP_TK\" error | this_or_super \"OP_TK\" argument_list error | this_or_super \"OP_TK\" argument_list \"CP_TK\" error | name \"DOT_TK\" \"SUPER_TK\" error | name \"DOT_TK\" \"SUPER_TK\" \"OP_TK\" error | name \"DOT_TK\" \"SUPER_TK\" \"OP_TK\" argument_list error | name \"DOT_TK\" \"SUPER_TK\" \"OP_TK\" argument_list \"CP_TK\" error | name \"DOT_TK\" \"SUPER_TK\" \"OP_TK\" \"CP_TK\" error ;");
    b
        .append("cfg statement_expression :=  assignment | pre_increment_expression | pre_decrement_expression | post_increment_expression | post_decrement_expression | method_invocation | class_instance_creation_expression ;");
    b.append("cfg if_then_statement :=  \"IF_TK\" \"OP_TK\" expression \"CP_TK\" statement | \"IF_TK\" error | \"IF_TK\" \"OP_TK\" error | \"IF_TK\" \"OP_TK\" expression error ;");
    b.append("cfg if_then_else_statement :=  \"IF_TK\" \"OP_TK\" expression \"CP_TK\" statement_nsi \"ELSE_TK\" statement ;");
    b.append("cfg if_then_else_statement_nsi :=  \"IF_TK\" \"OP_TK\" expression \"CP_TK\" statement_nsi \"ELSE_TK\" statement_nsi ;");
    b.append("cfg switch_statement :=  switch_expressionswitch_block ;");
    b.append("cfg switch_expression :=  \"SWITCH_TK\" \"OP_TK\" expression \"CP_TK\" | \"SWITCH_TK\" error | \"SWITCH_TK\" \"OP_TK\" error | \"SWITCH_TK\" \"OP_TK\" expression \"CP_TK\" error ;");
    b
        .append("cfg switch_block :=  \"OCB_TK\" \"CCB_TK\" | \"OCB_TK\" switch_labels \"CCB_TK\" | \"OCB_TK\" switch_block_statement_groups \"CCB_TK\" | \"OCB_TK\" switch_block_statement_groups switch_labels \"CCB_TK\" ;");
    b.append("cfg switch_block_statement_groups :=  switch_block_statement_group | switch_block_statement_groups switch_block_statement_group ;");
    b.append("cfg switch_block_statement_group :=  switch_labels block_statements ;");
    b.append("cfg switch_labels :=  switch_label | switch_labels switch_label ;");
    b.append("cfg switch_label :=  \"CASE_TK\" constant_expression \"REL_CL_TK\" | \"DEFAULT_TK\" \"REL_CL_TK\" | \"CASE_TK\" error | \"CASE_TK\" constant_expression error | \"DEFAULT_TK\" error ;");
    b.append("cfg while_expression :=  \"WHILE_TK\" \"OP_TK\" expression \"CP_TK\" ;");
    b.append("cfg while_statement :=  while_expression statement | \"WHILE_TK\" error | \"WHILE_TK\" \"OP_TK\" error | \"WHILE_TK\" \"OP_TK\" expression error ;");
    b.append("cfg while_statement_nsi :=  while_expression statement_nsi ;");
    b.append("cfg do_statement_begin :=  \"DO_TK\" ;");
    b.append("cfg do_statement :=  do_statement_begin statement \"WHILE_TK\" \"OP_TK\" expression \"CP_TK\" \"SC_TK\" ;");
    b
        .append("cfg for_statement :=  for_begin \"SC_TK\" expression \"SC_TK\" for_update \"CP_TK\" statement | for_begin \"SC_TK\" \"SC_TK\" for_update \"CP_TK\" statement | for_begin \"SC_TK\" error | for_begin \"SC_TK\" expression \"SC_TK\" error | for_begin \"SC_TK\" \"SC_TK\" error ;");
    b.append("cfg for_statement_nsi :=  for_begin \"SC_TK\" expression \"SC_TK\" for_update \"CP_TK\" statement_nsi | for_begin \"SC_TK\" \"SC_TK\" for_update \"CP_TK\" statement_nsi ;");
    b.append("cfg for_header :=  \"FOR_TK\" \"OP_TK\" | \"FOR_TK\" error | \"FOR_TK\" \"OP_TK\" error ;");
    b.append("cfg for_begin :=  for_header for_init ;");
    b.append("cfg for_init :=  statement_expression_list | local_variable_declaration | statement_expression_list error ;");
    b.append("cfg for_update :=  statement_expression_list ;");
    b.append("cfg statement_expression_list :=  statement_expression | statement_expression_list \"C_TK\" statement_expression | statement_expression_list \"C_TK\" error ;");
    b.append("cfg break_statement :=  \"BREAK_TK\" \"SC_TK\" | \"BREAK_TK\" identifier \"SC_TK\" | \"BREAK_TK\" error | \"BREAK_TK\" identifier error ;");
    b.append("cfg continue_statement :=  \"CONTINUE_TK\" \"SC_TK\" | \"CONTINUE_TK\" identifier \"SC_TK\" | \"CONTINUE_TK\" error | \"CONTINUE_TK\" identifier error ;");
    b.append("cfg return_statement :=  \"RETURN_TK\" \"SC_TK\" | \"RETURN_TK\" expression \"SC_TK\" | \"RETURN_TK\" error | \"RETURN_TK\" expression error ;");
    b.append("cfg throw_statement :=  \"THROW_TK\" expression \"SC_TK\" | \"THROW_TK\" error | \"THROW_TK\" expression error ;");
    b.append("cfg assert_statement :=  \"ASSERT_TK\" expression \"REL_CL_TK\" expression \"SC_TK\" | \"ASSERT_TK\" expression \"SC_TK\" | \"ASSERT_TK\" error | \"ASSERT_TK\" expression error ;");
    b
        .append("cfg synchronized_statement :=  synchronized \"OP_TK\" expression \"CP_TK\" block | synchronized \"OP_TK\" expression \"CP_TK\" error | synchronized error | synchronized \"OP_TK\" error \"CP_TK\" | synchronized \"OP_TK\" error ;");
    b.append("cfg synchronized :=  modifiers ;");
    b.append("cfg try_statement :=  \"TRY_TK\" block catches | \"TRY_TK\" block finally | \"TRY_TK\" block catches finally | \"TRY_TK\" error ;");
    b.append("cfg catches :=  catch_clause | catches catch_clause ;");
    b.append("cfg catch_clause :=  catch_clause_parameter block ;");
    b.append("cfg catch_clause_parameter :=  \"CATCH_TK\" \"OP_TK\" formal_parameter \"CP_TK\" | \"CATCH_TK\" error | \"CATCH_TK\" \"OP_TK\" error | \"CATCH_TK\" \"OP_TK\" error \"CP_TK\" ;");
    b.append("cfg finally :=  \"FINALLY_TK\" block | \"FINALLY_TK\" error ;");
    b.append("cfg primary :=  primary_no_new_array | array_creation_expression ;");
    b
        .append("cfg primary_no_new_array :=  literal | \"THIS_TK\" | \"OP_TK\" expression \"CP_TK\" | class_instance_creation_expression | field_access | method_invocation | array_access | type_literals | name \"DOT_TK\" \"THIS_TK\" | \"OP_TK\" expression error | name \"DOT_TK\" error | primitive_type \"DOT_TK\" error | \"VOID_TK\" \"DOT_TK\" error ;");
    b.append("cfg type_literals :=  name \"DOT_TK\" \"CLASS_TK\" | array_type \"DOT_TK\" \"CLASS_TK\" | primitive_type \"DOT_TK\" \"CLASS_TK\" | \"VOID_TK\" \"DOT_TK\" \"CLASS_TK\" ;");
    b
        .append("cfg class_instance_creation_expression :=  \"NEW_TK\" class_type \"OP_TK\" argument_list \"CP_TK\" | \"NEW_TK\" class_type \"OP_TK\" \"CP_TK\" | anonymous_class_creation | something_dot_new identifier \"OP_TK\" \"CP_TK\" | something_dot_new identifier \"OP_TK\" \"CP_TK\" class_body | something_dot_new identifier \"OP_TK\" argument_list \"CP_TK\" | something_dot_new identifier \"OP_TK\" argument_list \"CP_TK\" class_body | \"NEW_TK\" error \"SC_TK\" | \"NEW_TK\" class_type error | \"NEW_TK\" class_type \"OP_TK\" error | \"NEW_TK\" class_type \"OP_TK\" argument_list error | something_dot_new error | something_dot_new identifier error ;");
    b.append("cfg anonymous_class_creation :=  \"NEW_TK\" class_type \"OP_TK\" argument_list CP_TKclass_body | \"NEW_TK\" class_type \"OP_TK\" CP_TKclass_body ;");
    b.append("cfg something_dot_new :=  name \"DOT_TK\" \"NEW_TK\" | primary \"DOT_TK\" \"NEW_TK\" ;");
    b.append("cfg argument_list :=  expression | argument_list \"C_TK\" expression | argument_list \"C_TK\" error ;");
    b
        .append("cfg array_creation_expression :=  \"NEW_TK\" primitive_type dim_exprs | \"NEW_TK\" class_or_interface_type dim_exprs | \"NEW_TK\" primitive_type dim_exprs dims | \"NEW_TK\" class_or_interface_type dim_exprs dims | \"NEW_TK\" class_or_interface_type dims array_initializer | \"NEW_TK\" primitive_type dims array_initializer | \"NEW_TK\" error \"CSB_TK\" | \"NEW_TK\" error \"OSB_TK\" ;");
    b.append("cfg dim_exprs :=  dim_expr | dim_exprs dim_expr ;");
    b.append("cfg dim_expr :=  \"OSB_TK\" expression \"CSB_TK\" | \"OSB_TK\" expression error | \"OSB_TK\" error ;");
    b.append("cfg dims :=  \"OSB_TK\" \"CSB_TK\" | dims \"OSB_TK\" \"CSB_TK\" | dims \"OSB_TK\" error ;");
    b.append("cfg field_access :=  primary \"DOT_TK\" identifier | \"SUPER_TK\" \"DOT_TK\" identifier | \"SUPER_TK\" error ;");
    b
        .append("cfg method_invocation :=  name \"OP_TK\" \"CP_TK\" | name \"OP_TK\" argument_list \"CP_TK\" | primary \"DOT_TK\" identifier \"OP_TK\" \"CP_TK\" | primary \"DOT_TK\" identifier \"OP_TK\" argument_list \"CP_TK\" | \"SUPER_TK\" \"DOT_TK\" identifier \"OP_TK\" \"CP_TK\" | \"SUPER_TK\" \"DOT_TK\" identifier \"OP_TK\" argument_list \"CP_TK\" | \"SUPER_TK\" \"DOT_TK\" error \"CP_TK\" | \"SUPER_TK\" \"DOT_TK\" error \"DOT_TK\" ;");
    b
        .append("cfg array_access :=  name \"OSB_TK\" expression \"CSB_TK\" | primary_no_new_array \"OSB_TK\" expression \"CSB_TK\" | name \"OSB_TK\" error | name \"OSB_TK\" expression error | primary_no_new_array \"OSB_TK\" error | primary_no_new_array \"OSB_TK\" expression error ;");
    b.append("cfg postfix_expression :=  primary | name | post_increment_expression | post_decrement_expression ;");
    b.append("cfg post_increment_expression :=  postfix_expression \"INCR_TK\" ;");
    b.append("cfg post_decrement_expression :=  postfix_expression \"DECR_TK\" ;");
    b.append("cfg trap_overflow_corner_case :=  pre_increment_expression | pre_decrement_expression | \"PLUS_TK\" unary_expression | unary_expression_not_plus_minus | \"PLUS_TK\" error ;");
    b.append("cfg unary_expression :=  trap_overflow_corner_case | \"MINUS_TK\" trap_overflow_corner_case | \"MINUS_TK\" error ;");
    b.append("cfg pre_increment_expression :=  \"INCR_TK\" unary_expression | \"INCR_TK\" error ;");
    b.append("cfg pre_decrement_expression :=  \"DECR_TK\" unary_expression | \"DECR_TK\" error ;");
    b.append("cfg unary_expression_not_plus_minus :=  postfix_expression | \"NOT_TK\" unary_expression | \"NEG_TK\" unary_expression | cast_expression | \"NOT_TK\" error | \"NEG_TK\" error ;");
    b
        .append("cfg cast_expression :=  \"OP_TK\" primitive_type dims \"CP_TK\" unary_expression | \"OP_TK\" primitive_type \"CP_TK\" unary_expression | \"OP_TK\" expression \"CP_TK\" unary_expression_not_plus_minus | \"OP_TK\" name dims \"CP_TK\" unary_expression_not_plus_minus | \"OP_TK\" primitive_type \"OSB_TK\" error | \"OP_TK\" error | \"OP_TK\" primitive_type dims \"CP_TK\" error | \"OP_TK\" primitive_type \"CP_TK\" error | \"OP_TK\" name dims \"CP_TK\" error ;");
    b
        .append("cfg multiplicative_expression :=  unary_expression | multiplicative_expression \"MULT_TK\" unary_expression | multiplicative_expression \"DIV_TK\" unary_expression | multiplicative_expression \"REM_TK\" unary_expression | multiplicative_expression \"MULT_TK\" error | multiplicative_expression \"DIV_TK\" error | multiplicative_expression \"REM_TK\" error ;");
    b
        .append("cfg additive_expression :=  multiplicative_expression | additive_expression \"PLUS_TK\" multiplicative_expression | additive_expression \"MINUS_TK\" multiplicative_expression | additive_expression \"PLUS_TK\" error | additive_expression \"MINUS_TK\" error ;");
    b
        .append("cfg shift_expression :=  additive_expression | shift_expression \"LS_TK\" additive_expression | shift_expression \"SRS_TK\" additive_expression | shift_expression \"ZRS_TK\" additive_expression | shift_expression \"LS_TK\" error | shift_expression \"SRS_TK\" error | shift_expression \"ZRS_TK\" error ;");
    b
        .append("cfg relational_expression :=  shift_expression | relational_expression \"LT_TK\" shift_expression | relational_expression \"GT_TK\" shift_expression | relational_expression \"LTE_TK\" shift_expression | relational_expression \"GTE_TK\" shift_expression | relational_expression \"INSTANCEOF_TK\" reference_type | relational_expression \"LT_TK\" error | relational_expression \"GT_TK\" error | relational_expression \"LTE_TK\" error | relational_expression \"GTE_TK\" error | relational_expression \"INSTANCEOF_TK\" error ;");
    b
        .append("cfg equality_expression :=  relational_expression | equality_expression \"EQ_TK\" relational_expression | equality_expression \"NEQ_TK\" relational_expression | equality_expression \"EQ_TK\" error | equality_expression \"NEQ_TK\" error ;");
    b.append("cfg and_expression :=  equality_expression | and_expression \"AND_TK\" equality_expression | and_expression \"AND_TK\" error ;");
    b.append("cfg exclusive_or_expression :=  and_expression | exclusive_or_expression \"XOR_TK\" and_expression | exclusive_or_expression \"XOR_TK\" error ;");
    b.append("cfg inclusive_or_expression :=  exclusive_or_expression | inclusive_or_expression \"OR_TK\" exclusive_or_expression | inclusive_or_expression \"OR_TK\" error ;");
    b.append("cfg conditional_and_expression :=  inclusive_or_expression | conditional_and_expression \"BOOL_AND_TK\" inclusive_or_expression | conditional_and_expression \"BOOL_AND_TK\" error ;");
    b.append("cfg conditional_or_expression :=  conditional_and_expression | conditional_or_expression \"BOOL_OR_TK\" conditional_and_expression | conditional_or_expression \"BOOL_OR_TK\" error ;");
    b
        .append("cfg conditional_expression :=  conditional_or_expression | conditional_or_expression \"REL_QM_TK\" expression \"REL_CL_TK\" conditional_expression | conditional_or_expression \"REL_QM_TK\" \"REL_CL_TK\" error | conditional_or_expression \"REL_QM_TK\" error | conditional_or_expression \"REL_QM_TK\" expression \"REL_CL_TK\" error ;");
    b.append("cfg assignment_expression :=  conditional_expression | assignment ;");
    b.append("cfg assignment :=  left_hand_side assignment_operator assignment_expression | left_hand_side assignment_operator error ;");
    b.append("cfg left_hand_side :=  name | field_access | array_access ;");
    b.append("cfg assignment_operator :=  \"ASSIGN_ANY_TK\" | \"ASSIGN_TK\" ;");
    b.append("cfg expression :=  assignment_expression ;");
    b.append("cfg constant_expression :=  expression ;");
    b.append("reg limit := fix(goal, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_01_05_076_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg text :=  | text textElement ;");
    b.append("cfg textElement :=  inlineElement | paragraph ;");
    b.append("cfg inlineElement :=  \"t\" | \"b\" inlineText \"B\" ;");
    b.append("cfg paragraph :=  \"p\" inlineText optParaEnd ;");
    b.append("cfg optParaEnd :=  | \"P\" ;");
    b.append("cfg inlineText :=  | inlineText inlineElement ;");
    b.append("reg limit := fix(text, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_pascal_3_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg program :=  PROGRAM newident external_files \";\" block \".\" ;");
    b.append("cfg external_files :=  | \"(\" newident_list \")\" ;");
    b.append("cfg block :=  opt_declarations statement_part ;");
    b.append("opt_declarations: | declarations ;");
    b.append("cfg declarations :=  declarations declaration | declaration ;");
    b.append("cfg declaration :=  label_dcl_part | const_dcl_part | type_dcl_part | var_dcl_part | proc_dcl_part ;");
    b.append("cfg label_dcl_part :=  LABEL labels \";\" ;");
    b.append("cfg labels :=  labels \",\" label | label ;");
    b.append("cfg label :=  UNSIGNED_INT ;");
    b.append("cfg const_dcl_part :=  CONST const_defs \";\" ;");
    b.append("cfg const_defs :=  const_defs \";\" const_def | const_def ;");
    b.append("cfg const_def :=  newident \"=\" constant ;");
    b.append("cfg constant :=  unsigned_num | \"+\" unsigned_num | \"-\" unsigned_num | ident | \"+\" ident | \"-\" ident | STRING ;");
    b.append("cfg unsigned_num :=  UNSIGNED_INT | UNSIGNED_REAL ;");
    b.append("cfg type_dcl_part :=  TYPE type_defs \";\" ;");
    b.append("cfg type_defs :=  type_defs \";\" type_def | type_def ;");
    b.append("cfg type_def :=  newident \"=\" type ;");
    b.append("cfg type :=  simple_type | PACKED struct_type | struct_type | \"^\" IDENTIFIER ;");
    b.append("cfg simple_type :=  \"(\" newident_list \")\" | constant DOTDOT constant | ident ;");
    b.append("cfg struct_type :=  ARRAY \"[\" index_t_list \"]\" OF type | RECORD field_list END | SET OF simple_type | SFILE OF type ;");
    b.append("cfg index_t_list :=  index_t_list \",\" simple_type | simple_type ;");
    b.append("cfg field_list :=  fixed_part | fixed_part \";\" variant_part | variant_part ;");
    b.append("cfg fixed_part :=  fixed_part \";\" record_section | record_section ;");
    b.append("cfg record_section :=  newident_list \":\" type | ;");
    b.append("cfg variant_part :=  CASE tag_field OF variants ;");
    b.append("cfg tag_field :=  newident \":\" ident | ident ;");
    b.append("cfg variants :=  variants \";\" variant | variant ;");
    b.append("cfg variant :=  case_label_list \":\" \"(\" field_list \")\" | ;");
    b.append("cfg var_dcl_part :=  VAR variable_dcls \";\" ;");
    b.append("cfg variable_dcls :=  variable_dcls \";\" variable_dcl | variable_dcl ;");
    b.append("cfg variable_dcl :=  newident_list \":\" type ;");
    b.append("cfg newident_list :=  new_id_list ;");
    b.append("cfg new_id_list :=  new_id_list \",\" newident | newident ;");
    b.append("cfg proc_dcl_part :=  proc_or_func ;");
    b.append("cfg proc_or_func :=  proc_heading \";\" body \";\" | func_heading \";\" body \";\" ;");
    b.append("cfg proc_heading :=  PROCEDURE newident formal_params ;");
    b.append("cfg func_heading :=  FUNCTION newident function_form ;");
    b.append("cfg function_form :=  | formal_params \":\" ident ;");
    b.append("cfg body :=  block | IDENTIFIER ;");
    b.append("cfg formal_params :=  | \"(\" formal_p_sects \")\" ;");
    b.append("cfg formal_p_sects :=  formal_p_sects \";\" formal_p_sect | formal_p_sect ;");
    b.append("cfg formal_p_sect :=  param_group | VAR param_group | proc_heading | func_heading ;");
    b.append("cfg param_group :=  newident_list \":\" paramtype ;");
    b.append("cfg paramtype :=  ident | ARRAY \"[\" index_specs \"]\" OF paramtype | PACKED ARRAY \"[\" index_spec \"]\" OF ident ;");
    b.append("cfg index_specs :=  index_specs \";\" index_spec | index_spec ;");
    b.append("cfg index_spec :=  newident DOTDOT newident \":\" ident ;");
    b.append("cfg statement_part :=  compound_stmt ;");
    b.append("cfg compound_stmt :=  SBEGIN statements END ;");
    b.append("cfg statements :=  statements \";\" statement | statement ;");
    b
        .append("cfg statement :=  | label \":\" statement | compound_stmt | assignment | procedure_call | GOTO label | IF expression THEN statement | IF expression THEN statement ELSE statement | CASE expression OF case_list END | WHILE expression DO statement | REPEAT statements UNTIL expression | FOR ident BECOMES expression direction expression DO statement | WITH rec_var_list DO statement ;");
    b.append("cfg direction :=  TO | DOWNTO ;");
    b.append("cfg assignment :=  variable BECOMES expression ;");
    b.append("cfg procedure_call :=  ident actual_params ;");
    b.append("cfg actual_params :=  | \"(\" actuals_list \")\" ;");
    b.append("cfg actuals_list :=  actuals_list \",\" actual_param | actual_param ;");
    b.append("cfg actual_param :=  expression | expression colon_things ;");
    b.append("cfg colon_things :=  \":\" expression | \":\" expression \":\" expression ;");
    b.append("cfg case_list :=  case_list \";\" case_list_elem | case_list_elem ;");
    b.append("cfg case_list_elem :=  case_label_list \":\" statement | ;");
    b.append("cfg case_label_list :=  case_label_list \",\" case_label | case_label ;");
    b.append("cfg case_label :=  constant ;");
    b.append("cfg rec_var_list :=  rec_var_list \",\" record_var | record_var ;");
    b.append("cfg expression :=  simple_expr | simple_expr relational_op simple_expr ;");
    b.append("cfg relational_op :=  \"=\" | \"<\" | \">\" | LE | GE | NE | IN ;");
    b.append("cfg simple_expr :=  term | \"+\" term | \"-\" term | simple_expr add_op term ;");
    b.append("cfg add_op :=  \"+\" | \"-\" | OR ;");
    b.append("cfg term :=  factor | term mult_op factor ;");
    b.append("cfg mult_op :=  \"*\" | \"/\" | DIV | MOD | AND ;");
    b.append("cfg factor :=  variable | unsigned_lit | \"(\" expression \")\" | set | NOT factor ;");
    b.append("cfg unsigned_lit :=  unsigned_num | STRING | NIL ;");
    b.append("cfg set :=  \"[\" member_list \"]\" ;");
    b.append("cfg member_list :=  | members ;");
    b.append("cfg members :=  members \",\" member | member ;");
    b.append("cfg member :=  expression | expression DOTDOT expression ;");
    b.append("cfg variable :=  ident actual_params | variable \"[\" expressions \"]\" | variable \".\" ident | variable \"^\" ;");
    b.append("cfg expressions :=  expressions \",\" expression | expression ;");
    b.append("cfg record_var :=  variable ;");
    b.append("cfg ident :=  IDENTIFIER ;");
    b.append("cfg newident :=  IDENTIFIER ;");
    b.append("cfg AND :=  \"0\" ;");
    b.append("cfg ARRAY :=  \"1\" ;");
    b.append("cfg BECOMES :=  \"2\" ;");
    b.append("cfg CASE :=  \"3\" ;");
    b.append("cfg CONST :=  \"4\" ;");
    b.append("cfg DIV :=  \"5\" ;");
    b.append("cfg DO :=  \"6\" ;");
    b.append("DOTDOT: \"7\" ;");
    b.append("DOWNTO: \"8\" ;");
    b.append("cfg ELSE :=  \"9\" ;");
    b.append("cfg END :=  \"a\" ;");
    b.append("cfg FOR :=  \"b\" ;");
    b.append("FUNCTION: \"c\" ;");
    b.append("cfg GE :=  \"d\" ;");
    b.append("cfg GOTO :=  \"e\" ;");
    b.append("IDENTIFIER: \"f\" ;");
    b.append("cfg IF :=  \"g\" ;");
    b.append("cfg IN :=  \"h\" ;");
    b.append("cfg LABEL :=  \"i\" ;");
    b.append("cfg LE :=  \"j\" ;");
    b.append("cfg MOD :=  \"k\" ;");
    b.append("cfg NE :=  \"l\" ;");
    b.append("cfg NIL :=  \"m\" ;");
    b.append("cfg NOT :=  \"n\" ;");
    b.append("cfg OF :=  \"o\" ;");
    b.append("cfg OR :=  \"p\" ;");
    b.append("cfg PACKED :=  \"q\" ;");
    b.append("cfg PROCEDURE :=  \"r\" ;");
    b.append("PROGRAM: \"s\" ;");
    b.append("cfg RECORD :=  \"t\" ;");
    b.append("cfg REPEAT :=  \"u\" ;");
    b.append("cfg SBEGIN :=  \"v\" ;");
    b.append("cfg SET :=  \"w\" ;");
    b.append("cfg SFILE :=  \"x\" ;");
    b.append("cfg STRING :=  \"y\" ;");
    b.append("cfg THEN :=  \"z\" ;");
    b.append("cfg TO :=  \"A\" ;");
    b.append("cfg TYPE :=  \"B\" ;");
    b.append("cfg UNSIGNED_INT :=  \"C\" ;");
    b.append("cfg UNSIGNED_REAL :=  \"D\" ;");
    b.append("cfg UNTIL :=  \"E\" ;");
    b.append("cfg VAR :=  \"F\" ;");
    b.append("cfg WHILE :=  \"G\" ;");
    b.append("cfg WITH :=  \"H\" ;");
    b.append("cfg add_op :=  \"<\" ;");
    b.append("reg limit := fix(program, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_rna1_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg S :=  \"(\" S \")\" | \".\" S | S \".\" | S S | ;");
    b.append("reg limit := fix(S, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_set_exp_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg program :=  statement | program \";\" statement ;");
    b.append("cfg statement :=  assign_stat | jump | ident \":\" statement ;");
    b.append("cfg assign_stat :=  ident \"=\" arith_exp | ident \"~\" set_exp ;");
    b.append("cfg jump :=  \"i\" relation \"t\" \"g\" ident ;");
    b.append("cfg relation :=  arith_exp \"=\" arith_exp | set_exp \"~\" set_exp ;");
    b.append("cfg arith_exp :=  arith_exp \"+\" arith_term | arith_exp \"-\" arith_term | arith_term ;");
    b.append("cfg arith_term :=  arith_term \"*\" arith_primary | arith_primary ;");
    b.append("cfg arith_primary :=  \"(\" arith_exp \")\" | ident | const ;");
    b.append("cfg set_exp :=  set_exp \"+\" set_term | set_term ;");
    b.append("cfg set_term :=  set_term \"*\" set_factor | set_factor ;");
    b.append("cfg set_factor :=  set_factor \"-\" set_primary | set_primary ;");
    b.append("cfg set_primary :=  \"(\" set_exp \")\" | ident | const ;");
    b.append("cfg ident :=  ident letter | letter ;");
    b.append("cfg const :=  const digit | digit ;");
    b.append("cfg letter :=  \"a\" | \"b\" ;");
    b.append("cfg digit :=  \"0\" | \"1\" ;");
    b.append("reg limit := fix(program, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_pascal_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg program :=  PROGRAM newident external_files \";\" block \".\" ;");
    b.append("cfg external_files :=  | \"(\" newident_list \")\" ;");
    b.append("cfg block :=  opt_declarations statement_part ;");
    b.append("opt_declarations: | declarations ;");
    b.append("cfg declarations :=  declarations declaration | declaration ;");
    b.append("cfg declaration :=  label_dcl_part | const_dcl_part | type_dcl_part | var_dcl_part | proc_dcl_part ;");
    b.append("cfg label_dcl_part :=  LABEL labels \";\" ;");
    b.append("cfg labels :=  labels \",\" label | label ;");
    b.append("cfg label :=  UNSIGNED_INT ;");
    b.append("cfg const_dcl_part :=  CONST const_defs \";\" ;");
    b.append("cfg const_defs :=  const_defs \";\" const_def | const_def ;");
    b.append("cfg const_def :=  newident \"=\" constant ;");
    b.append("cfg constant :=  unsigned_num | \"+\" unsigned_num | \"-\" unsigned_num | ident | \"+\" ident | \"-\" ident | STRING ;");
    b.append("cfg unsigned_num :=  UNSIGNED_INT | UNSIGNED_REAL ;");
    b.append("cfg type_dcl_part :=  TYPE type_defs \";\" ;");
    b.append("cfg type_defs :=  type_defs \";\" type_def | type_def ;");
    b.append("cfg type_def :=  newident \"=\" type ;");
    b.append("cfg type :=  simple_type | PACKED struct_type | struct_type | \"^\" IDENTIFIER ;");
    b.append("cfg simple_type :=  \"(\" newident_list \")\" | constant DOTDOT constant | ident ;");
    b.append("cfg struct_type :=  ARRAY \"[\" index_t_list \"]\" OF type | RECORD field_list END | SET OF simple_type | SFILE OF type ;");
    b.append("cfg index_t_list :=  index_t_list \",\" simple_type | simple_type ;");
    b.append("cfg field_list :=  fixed_part | fixed_part \";\" variant_part | variant_part ;");
    b.append("cfg fixed_part :=  fixed_part \";\" record_section | record_section ;");
    b.append("cfg record_section :=  newident_list \":\" type | ;");
    b.append("cfg variant_part :=  CASE tag_field OF variants ;");
    b.append("cfg tag_field :=  newident \":\" ident | ident ;");
    b.append("cfg variants :=  variants \";\" variant | variant ;");
    b.append("cfg variant :=  case_label_list \":\" \"(\" field_list \")\" | ;");
    b.append("cfg var_dcl_part :=  VAR variable_dcls \";\" ;");
    b.append("cfg variable_dcls :=  variable_dcls \";\" variable_dcl | variable_dcl ;");
    b.append("cfg variable_dcl :=  newident_list \":\" type ;");
    b.append("cfg newident_list :=  new_id_list ;");
    b.append("cfg new_id_list :=  new_id_list \",\" newident | newident ;");
    b.append("cfg proc_dcl_part :=  proc_or_func ;");
    b.append("cfg proc_or_func :=  proc_heading \";\" body \";\" | func_heading \";\" body \";\" ;");
    b.append("cfg proc_heading :=  PROCEDURE newident formal_params ;");
    b.append("cfg func_heading :=  FUNCTION newident function_form ;");
    b.append("cfg function_form :=  | formal_params \":\" ident ;");
    b.append("cfg body :=  block | IDENTIFIER ;");
    b.append("cfg formal_params :=  | \"(\" formal_p_sects \")\" ;");
    b.append("cfg formal_p_sects :=  formal_p_sects \";\" formal_p_sect | formal_p_sect ;");
    b.append("cfg formal_p_sect :=  param_group | VAR param_group | proc_heading | func_heading ;");
    b.append("cfg param_group :=  newident_list \":\" paramtype ;");
    b.append("cfg paramtype :=  ident | ARRAY \"[\" index_specs \"]\" OF paramtype | PACKED ARRAY \"[\" index_spec \"]\" OF ident ;");
    b.append("cfg index_specs :=  index_specs \";\" index_spec | index_spec ;");
    b.append("cfg index_spec :=  newident DOTDOT newident \":\" ident ;");
    b.append("cfg statement_part :=  compound_stmt ;");
    b.append("cfg compound_stmt :=  SBEGIN statements END ;");
    b.append("cfg statements :=  statements \";\" statement | statement ;");
    b
        .append("cfg statement :=  | label \":\" statement | compound_stmt | assignment | procedure_call | GOTO label | IF expression THEN statement | IF expression THEN statement ELSE statement | CASE expression OF case_list END | WHILE expression DO statement | REPEAT statements UNTIL expression | FOR ident BECOMES expression direction expression DO statement | WITH rec_var_list DO statement ;");
    b.append("cfg direction :=  TO | DOWNTO ;");
    b.append("cfg assignment :=  variable BECOMES expression ;");
    b.append("cfg procedure_call :=  ident actual_params ;");
    b.append("cfg actual_params :=  | \"(\" actuals_list \")\" ;");
    b.append("cfg actuals_list :=  actuals_list \",\" actual_param | actual_param ;");
    b.append("cfg actual_param :=  expression | expression colon_things ;");
    b.append("cfg colon_things :=  \":\" expression | \":\" expression \":\" expression ;");
    b.append("cfg case_list :=  case_list \";\" case_list_elem | case_list_elem ;");
    b.append("cfg case_list_elem :=  case_label_list \":\" statement | ;");
    b.append("cfg case_label_list :=  case_label_list \",\" case_label | case_label ;");
    b.append("cfg case_label :=  constant ;");
    b.append("cfg rec_var_list :=  rec_var_list \",\" record_var | record_var ;");
    b.append("cfg expression :=  simple_expr | simple_expr relational_op simple_expr ;");
    b.append("cfg relational_op :=  \"=\" | \"<\" | \">\" | LE | GE | NE | IN ;");
    b.append("cfg simple_expr :=  term | \"+\" term | \"-\" term | simple_expr add_op term ;");
    b.append("cfg add_op :=  \"+\" | \"-\" | OR ;");
    b.append("cfg term :=  factor | term mult_op factor ;");
    b.append("cfg mult_op :=  \"*\" | \"/\" | DIV | MOD | AND ;");
    b.append("cfg factor :=  variable | unsigned_lit | \"(\" expression \")\" | set | NOT factor ;");
    b.append("cfg unsigned_lit :=  unsigned_num | STRING | NIL ;");
    b.append("cfg set :=  \"[\" member_list \"]\" ;");
    b.append("cfg member_list :=  | members ;");
    b.append("cfg members :=  members \",\" member | member ;");
    b.append("cfg member :=  expression | expression DOTDOT expression ;");
    b.append("cfg variable :=  ident actual_params | variable \"[\" expressions \"]\" | variable \".\" ident | variable \"^\" ;");
    b.append("cfg expressions :=  expressions \",\" expression | expression ;");
    b.append("cfg record_var :=  variable ;");
    b.append("cfg ident :=  IDENTIFIER ;");
    b.append("cfg newident :=  IDENTIFIER ;");
    b.append("cfg AND :=  \"0\" ;");
    b.append("cfg ARRAY :=  \"1\" ;");
    b.append("cfg BECOMES :=  \"2\" ;");
    b.append("cfg CASE :=  \"3\" ;");
    b.append("cfg CONST :=  \"4\" ;");
    b.append("cfg DIV :=  \"5\" ;");
    b.append("cfg DO :=  \"6\" ;");
    b.append("DOTDOT: \"7\" ;");
    b.append("DOWNTO: \"8\" ;");
    b.append("cfg ELSE :=  \"9\" ;");
    b.append("cfg END :=  \"a\" ;");
    b.append("cfg FOR :=  \"b\" ;");
    b.append("FUNCTION: \"c\" ;");
    b.append("cfg GE :=  \"d\" ;");
    b.append("cfg GOTO :=  \"e\" ;");
    b.append("IDENTIFIER: \"f\" ;");
    b.append("cfg IF :=  \"g\" ;");
    b.append("cfg IN :=  \"h\" ;");
    b.append("cfg LABEL :=  \"i\" ;");
    b.append("cfg LE :=  \"j\" ;");
    b.append("cfg MOD :=  \"k\" ;");
    b.append("cfg NE :=  \"l\" ;");
    b.append("cfg NIL :=  \"m\" ;");
    b.append("cfg NOT :=  \"n\" ;");
    b.append("cfg OF :=  \"o\" ;");
    b.append("cfg OR :=  \"p\" ;");
    b.append("cfg PACKED :=  \"q\" ;");
    b.append("cfg PROCEDURE :=  \"r\" ;");
    b.append("PROGRAM: \"s\" ;");
    b.append("cfg RECORD :=  \"t\" ;");
    b.append("cfg REPEAT :=  \"u\" ;");
    b.append("cfg SBEGIN :=  \"v\" ;");
    b.append("cfg SET :=  \"w\" ;");
    b.append("cfg SFILE :=  \"x\" ;");
    b.append("cfg STRING :=  \"y\" ;");
    b.append("cfg THEN :=  \"z\" ;");
    b.append("cfg TO :=  \"A\" ;");
    b.append("cfg TYPE :=  \"B\" ;");
    b.append("cfg UNSIGNED_INT :=  \"C\" ;");
    b.append("cfg UNSIGNED_REAL :=  \"D\" ;");
    b.append("cfg UNTIL :=  \"E\" ;");
    b.append("cfg VAR :=  \"F\" ;");
    b.append("cfg WHILE :=  \"G\" ;");
    b.append("cfg WITH :=  \"H\" ;");
    b.append("reg limit := fix(program, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_90_10_042_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg grammar :=  rule grammar | rule \";\" grammar | ;");
    b.append("cfg rule :=  SYMBOL \":\" symbols ;");
    b.append("cfg symbols :=  SYMBOL symbols | ;");
    b.append("cfg SYMBOL :=  \"s\" ;");
    b.append("reg limit := fix(grammar, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_pascal_4_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg program :=  PROGRAM newident external_files \";\" block \".\" ;");
    b.append("cfg external_files :=  | \"(\" newident_list \")\" ;");
    b.append("cfg block :=  opt_declarations statement_part ;");
    b.append("opt_declarations: | declarations ;");
    b.append("cfg declarations :=  declarations declaration | declaration ;");
    b.append("cfg declaration :=  label_dcl_part | const_dcl_part | type_dcl_part | var_dcl_part | proc_dcl_part ;");
    b.append("cfg label_dcl_part :=  LABEL labels \";\" ;");
    b.append("cfg labels :=  labels \",\" label | label ;");
    b.append("cfg label :=  UNSIGNED_INT ;");
    b.append("cfg const_dcl_part :=  CONST const_defs \";\" ;");
    b.append("cfg const_defs :=  const_defs \";\" const_def | const_def ;");
    b.append("cfg const_def :=  newident \"=\" constant ;");
    b.append("cfg constant :=  unsigned_num | \"+\" unsigned_num | \"-\" unsigned_num | ident | \"+\" ident | \"-\" ident | STRING ;");
    b.append("cfg unsigned_num :=  UNSIGNED_INT | UNSIGNED_REAL ;");
    b.append("cfg type_dcl_part :=  TYPE type_defs \";\" ;");
    b.append("cfg type_defs :=  type_defs \";\" type_def | type_def ;");
    b.append("cfg type_def :=  newident \"=\" type ;");
    b.append("cfg type :=  simple_type | PACKED struct_type | struct_type | \"^\" IDENTIFIER ;");
    b.append("cfg simple_type :=  \"(\" newident_list \")\" | constant DOTDOT constant | ident ;");
    b.append("cfg struct_type :=  ARRAY \"[\" index_t_list \"]\" OF type | RECORD field_list END | SET OF simple_type | SFILE OF type ;");
    b.append("cfg index_t_list :=  index_t_list \",\" simple_type | simple_type ;");
    b.append("cfg field_list :=  fixed_part | fixed_part \";\" variant_part | variant_part ;");
    b.append("cfg fixed_part :=  fixed_part \";\" record_section | record_section ;");
    b.append("cfg record_section :=  newident_list \":\" type | ;");
    b.append("cfg variant_part :=  CASE tag_field OF variants ;");
    b.append("cfg tag_field :=  newident \":\" ident | ident ;");
    b.append("cfg variants :=  variants \";\" variant | variant ;");
    b.append("cfg variant :=  case_label_list \":\" \"(\" field_list \")\" | ;");
    b.append("cfg var_dcl_part :=  VAR variable_dcls \";\" ;");
    b.append("cfg variable_dcls :=  variable_dcls \";\" variable_dcl | variable_dcl ;");
    b.append("cfg variable_dcl :=  newident_list \":\" type ;");
    b.append("cfg newident_list :=  new_id_list ;");
    b.append("cfg new_id_list :=  new_id_list \",\" newident | newident ;");
    b.append("cfg proc_dcl_part :=  proc_or_func ;");
    b.append("cfg proc_or_func :=  proc_heading \";\" body \";\" | func_heading \";\" body \";\" ;");
    b.append("cfg proc_heading :=  PROCEDURE newident formal_params ;");
    b.append("cfg func_heading :=  FUNCTION newident function_form ;");
    b.append("cfg function_form :=  | formal_params \":\" ident ;");
    b.append("cfg body :=  block | IDENTIFIER ;");
    b.append("cfg formal_params :=  | \"(\" formal_p_sects \")\" ;");
    b.append("cfg formal_p_sects :=  formal_p_sects \";\" formal_p_sect | formal_p_sect ;");
    b.append("cfg formal_p_sect :=  param_group | VAR param_group | proc_heading | func_heading ;");
    b.append("cfg param_group :=  newident_list \":\" paramtype ;");
    b.append("cfg paramtype :=  ident | ARRAY \"[\" index_specs \"]\" OF paramtype | PACKED ARRAY \"[\" index_spec \"]\" OF ident ;");
    b.append("cfg index_specs :=  index_specs \";\" index_spec | index_spec ;");
    b.append("cfg index_spec :=  newident DOTDOT newident \":\" ident ;");
    b.append("cfg statement_part :=  compound_stmt ;");
    b.append("cfg compound_stmt :=  SBEGIN statements END ;");
    b.append("cfg statements :=  statements \";\" statement | statement ;");
    b
        .append("cfg statement :=  | label \":\" statement | compound_stmt | assignment | procedure_call | GOTO label | IF expression THEN statement | IF expression THEN statement ELSE statement | CASE expression OF case_list END | WHILE expression DO statement | REPEAT statements UNTIL expression | FOR ident BECOMES expression direction expression DO statement | WITH rec_var_list DO statement ;");
    b.append("cfg direction :=  TO | DOWNTO ;");
    b.append("cfg assignment :=  variable BECOMES expression ;");
    b.append("cfg procedure_call :=  ident actual_params ;");
    b.append("cfg actual_params :=  | \"(\" actuals_list \")\" ;");
    b.append("cfg actuals_list :=  actuals_list \",\" actual_param | actual_param ;");
    b.append("cfg actual_param :=  expression | expression colon_things ;");
    b.append("cfg colon_things :=  \":\" expression | \":\" expression \":\" expression ;");
    b.append("cfg case_list :=  case_list \";\" case_list_elem | case_list_elem ;");
    b.append("cfg case_list_elem :=  case_label_list \":\" statement | ;");
    b.append("cfg case_label_list :=  case_label_list \",\" case_label | case_label ;");
    b.append("cfg case_label :=  constant ;");
    b.append("cfg rec_var_list :=  rec_var_list \",\" record_var | record_var ;");
    b.append("cfg expression :=  simple_expr | simple_expr relational_op simple_expr ;");
    b.append("cfg relational_op :=  \"=\" | \"<\" | \">\" | LE | GE | NE | IN ;");
    b.append("cfg simple_expr :=  term | \"+\" term | \"-\" term | simple_expr add_op term ;");
    b.append("cfg add_op :=  \"+\" | \"-\" | OR ;");
    b.append("cfg term :=  factor | term mult_op factor ;");
    b.append("cfg mult_op :=  \"*\" | \"/\" | DIV | MOD | AND ;");
    b.append("cfg factor :=  variable | unsigned_lit | \"(\" expression \")\" | set | NOT factor ;");
    b.append("cfg unsigned_lit :=  unsigned_num | STRING | NIL ;");
    b.append("cfg set :=  \"[\" member_list \"]\" ;");
    b.append("cfg member_list :=  | members ;");
    b.append("cfg members :=  members \",\" member | member ;");
    b.append("cfg member :=  expression | expression DOTDOT expression ;");
    b.append("cfg variable :=  ident actual_params | variable \"[\" expressions \"]\" | variable \".\" ident | variable \"^\" ;");
    b.append("cfg expressions :=  expressions \",\" expression | expression ;");
    b.append("cfg record_var :=  variable ;");
    b.append("cfg ident :=  IDENTIFIER ;");
    b.append("cfg newident :=  IDENTIFIER ;");
    b.append("cfg AND :=  \"0\" ;");
    b.append("cfg ARRAY :=  \"1\" ;");
    b.append("cfg BECOMES :=  \"2\" ;");
    b.append("cfg CASE :=  \"3\" ;");
    b.append("cfg CONST :=  \"4\" ;");
    b.append("cfg DIV :=  \"5\" ;");
    b.append("cfg DO :=  \"6\" ;");
    b.append("DOTDOT: \"7\" ;");
    b.append("DOWNTO: \"8\" ;");
    b.append("cfg ELSE :=  \"9\" ;");
    b.append("cfg END :=  \"a\" ;");
    b.append("cfg FOR :=  \"b\" ;");
    b.append("FUNCTION: \"c\" ;");
    b.append("cfg GE :=  \"d\" ;");
    b.append("cfg GOTO :=  \"e\" ;");
    b.append("IDENTIFIER: \"f\" ;");
    b.append("cfg IF :=  \"g\" ;");
    b.append("cfg IN :=  \"h\" ;");
    b.append("cfg LABEL :=  \"i\" ;");
    b.append("cfg LE :=  \"j\" ;");
    b.append("cfg MOD :=  \"k\" ;");
    b.append("cfg NE :=  \"l\" ;");
    b.append("cfg NIL :=  \"m\" ;");
    b.append("cfg NOT :=  \"n\" ;");
    b.append("cfg OF :=  \"o\" ;");
    b.append("cfg OR :=  \"p\" ;");
    b.append("cfg PACKED :=  \"q\" ;");
    b.append("cfg PROCEDURE :=  \"r\" ;");
    b.append("PROGRAM: \"s\" ;");
    b.append("cfg RECORD :=  \"t\" ;");
    b.append("cfg REPEAT :=  \"u\" ;");
    b.append("cfg SBEGIN :=  \"v\" ;");
    b.append("cfg SET :=  \"w\" ;");
    b.append("cfg SFILE :=  \"x\" ;");
    b.append("cfg STRING :=  \"y\" ;");
    b.append("cfg THEN :=  \"z\" ;");
    b.append("cfg TO :=  \"A\" ;");
    b.append("cfg TYPE :=  \"B\" ;");
    b.append("cfg UNSIGNED_INT :=  \"C\" ;");
    b.append("cfg UNSIGNED_REAL :=  \"D\" ;");
    b.append("cfg UNTIL :=  \"E\" ;");
    b.append("cfg VAR :=  \"F\" ;");
    b.append("cfg WHILE :=  \"G\" ;");
    b.append("cfg WITH :=  \"H\" ;");
    b.append("cfg mult_op :=  \".\" ;");
    b.append("reg limit := fix(program, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  public void test_pascal_2_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 10;");
    b.append("cfg program :=  PROGRAM newident external_files \";\" block \".\" ;");
    b.append("cfg external_files :=  | \"(\" newident_list \")\" ;");
    b.append("cfg block :=  opt_declarations statement_part ;");
    b.append("opt_declarations: | declarations ;");
    b.append("cfg declarations :=  declarations declaration | declaration ;");
    b.append("cfg declaration :=  label_dcl_part | const_dcl_part | type_dcl_part | var_dcl_part | proc_dcl_part ;");
    b.append("cfg label_dcl_part :=  LABEL labels \";\" ;");
    b.append("cfg labels :=  labels \",\" label | label ;");
    b.append("cfg label :=  UNSIGNED_INT ;");
    b.append("cfg const_dcl_part :=  CONST const_defs \";\" ;");
    b.append("cfg const_defs :=  const_defs \";\" const_def | const_def ;");
    b.append("cfg const_def :=  newident \"=\" constant ;");
    b.append("cfg constant :=  unsigned_num | \"+\" unsigned_num | \"-\" unsigned_num | ident | \"+\" ident | \"-\" ident | STRING ;");
    b.append("cfg unsigned_num :=  UNSIGNED_INT | UNSIGNED_REAL ;");
    b.append("cfg type_dcl_part :=  TYPE type_defs \";\" ;");
    b.append("cfg type_defs :=  type_defs \";\" type_def | type_def ;");
    b.append("cfg type_def :=  newident \"=\" type ;");
    b.append("cfg type :=  simple_type | PACKED struct_type | struct_type | \"^\" IDENTIFIER ;");
    b.append("cfg simple_type :=  \"(\" newident_list \")\" | constant DOTDOT constant | ident ;");
    b.append("cfg struct_type :=  ARRAY \"[\" index_t_list \"]\" OF type | RECORD field_list END | SET OF simple_type | SFILE OF type ;");
    b.append("cfg index_t_list :=  index_t_list \",\" simple_type | simple_type ;");
    b.append("cfg field_list :=  fixed_part | fixed_part \";\" variant_part | variant_part ;");
    b.append("cfg fixed_part :=  fixed_part \";\" record_section | record_section ;");
    b.append("cfg record_section :=  newident_list \":\" type | ;");
    b.append("cfg variant_part :=  CASE tag_field OF variants ;");
    b.append("cfg tag_field :=  newident \":\" ident | ident ;");
    b.append("cfg variants :=  variants \";\" variant | variant ;");
    b.append("cfg variant :=  case_label_list \":\" \"(\" field_list \")\" | ;");
    b.append("cfg var_dcl_part :=  VAR variable_dcls \";\" ;");
    b.append("cfg variable_dcls :=  variable_dcls \";\" variable_dcl | variable_dcl ;");
    b.append("cfg variable_dcl :=  newident_list \":\" type ;");
    b.append("cfg newident_list :=  new_id_list ;");
    b.append("cfg new_id_list :=  new_id_list \",\" newident | newident ;");
    b.append("cfg proc_dcl_part :=  proc_or_func ;");
    b.append("cfg proc_or_func :=  proc_heading \";\" body \";\" | func_heading \";\" body \";\" ;");
    b.append("cfg proc_heading :=  PROCEDURE newident formal_params ;");
    b.append("cfg func_heading :=  FUNCTION newident function_form ;");
    b.append("cfg function_form :=  | formal_params \":\" ident ;");
    b.append("cfg body :=  block | IDENTIFIER ;");
    b.append("cfg formal_params :=  | \"(\" formal_p_sects \")\" ;");
    b.append("cfg formal_p_sects :=  formal_p_sects \";\" formal_p_sect | formal_p_sect ;");
    b.append("cfg formal_p_sect :=  param_group | VAR param_group | proc_heading | func_heading ;");
    b.append("cfg param_group :=  newident_list \":\" paramtype ;");
    b.append("cfg paramtype :=  ident | ARRAY \"[\" index_specs \"]\" OF paramtype | PACKED ARRAY \"[\" index_spec \"]\" OF ident ;");
    b.append("cfg index_specs :=  index_specs \";\" index_spec | index_spec ;");
    b.append("cfg index_spec :=  newident DOTDOT newident \":\" ident ;");
    b.append("cfg statement_part :=  compound_stmt ;");
    b.append("cfg compound_stmt :=  SBEGIN statements END ;");
    b.append("cfg statements :=  statements \";\" statement | statement ;");
    b
        .append("cfg statement :=  | label \":\" statement | compound_stmt | assignment | procedure_call | GOTO label | IF expression THEN statement | IF expression THEN statement ELSE statement | CASE expression OF case_list END | WHILE expression DO statement | REPEAT statements UNTIL expression | FOR ident BECOMES expression direction expression DO statement | WITH rec_var_list DO statement ;");
    b.append("cfg direction :=  TO | DOWNTO ;");
    b.append("cfg assignment :=  variable BECOMES expression ;");
    b.append("cfg procedure_call :=  ident actual_params ;");
    b.append("cfg actual_params :=  | \"(\" actuals_list \")\" ;");
    b.append("cfg actuals_list :=  actuals_list \",\" actual_param | actual_param ;");
    b.append("cfg actual_param :=  expression | expression colon_things ;");
    b.append("cfg colon_things :=  \":\" expression | \":\" expression \":\" expression ;");
    b.append("cfg case_list :=  case_list \";\" case_list_elem | case_list_elem ;");
    b.append("cfg case_list_elem :=  case_label_list \":\" statement | ;");
    b.append("cfg case_label_list :=  case_label_list \",\" case_label | case_label ;");
    b.append("cfg case_label :=  constant ;");
    b.append("cfg rec_var_list :=  rec_var_list \",\" record_var | record_var ;");
    b.append("cfg expression :=  simple_expr | simple_expr relational_op simple_expr ;");
    b.append("cfg relational_op :=  \"=\" | \"<\" | \">\" | LE | GE | NE | IN ;");
    b.append("cfg simple_expr :=  term | \"+\" term | \"-\" term | simple_expr add_op term ;");
    b.append("cfg add_op :=  \"+\" | \"-\" | OR ;");
    b.append("cfg term :=  factor | term mult_op factor ;");
    b.append("cfg mult_op :=  \"*\" | \"/\" | DIV | MOD | AND ;");
    b.append("cfg factor :=  variable | unsigned_lit | \"(\" expression \")\" | set | NOT factor ;");
    b.append("cfg unsigned_lit :=  unsigned_num | STRING | NIL ;");
    b.append("cfg set :=  \"[\" member_list \"]\" ;");
    b.append("cfg member_list :=  | members ;");
    b.append("cfg members :=  members \",\" member | member ;");
    b.append("cfg member :=  expression | expression DOTDOT expression ;");
    b.append("cfg variable :=  ident actual_params | variable \"[\" expressions \"]\" | variable \".\" ident | variable \"^\" ;");
    b.append("cfg expressions :=  expressions \",\" expression | expression ;");
    b.append("cfg record_var :=  variable ;");
    b.append("cfg ident :=  IDENTIFIER ;");
    b.append("cfg newident :=  IDENTIFIER ;");
    b.append("cfg AND :=  \"0\" ;");
    b.append("cfg ARRAY :=  \"1\" ;");
    b.append("cfg BECOMES :=  \"2\" ;");
    b.append("cfg CASE :=  \"3\" ;");
    b.append("cfg CONST :=  \"4\" ;");
    b.append("cfg DIV :=  \"5\" ;");
    b.append("cfg DO :=  \"6\" ;");
    b.append("DOTDOT: \"7\" ;");
    b.append("DOWNTO: \"8\" ;");
    b.append("cfg ELSE :=  \"9\" ;");
    b.append("cfg END :=  \"a\" ;");
    b.append("cfg FOR :=  \"b\" ;");
    b.append("FUNCTION: \"c\" ;");
    b.append("cfg GE :=  \"d\" ;");
    b.append("cfg GOTO :=  \"e\" ;");
    b.append("IDENTIFIER: \"f\" ;");
    b.append("cfg IF :=  \"g\" ;");
    b.append("cfg IN :=  \"h\" ;");
    b.append("cfg LABEL :=  \"i\" ;");
    b.append("cfg LE :=  \"j\" ;");
    b.append("cfg MOD :=  \"k\" ;");
    b.append("cfg NE :=  \"l\" ;");
    b.append("cfg NIL :=  \"m\" ;");
    b.append("cfg NOT :=  \"n\" ;");
    b.append("cfg OF :=  \"o\" ;");
    b.append("cfg OR :=  \"p\" ;");
    b.append("cfg PACKED :=  \"q\" ;");
    b.append("cfg PROCEDURE :=  \"r\" ;");
    b.append("PROGRAM: \"s\" ;");
    b.append("cfg RECORD :=  \"t\" ;");
    b.append("cfg REPEAT :=  \"u\" ;");
    b.append("cfg SBEGIN :=  \"v\" ;");
    b.append("cfg SET :=  \"w\" ;");
    b.append("cfg SFILE :=  \"x\" ;");
    b.append("cfg STRING :=  \"y\" ;");
    b.append("cfg THEN :=  \"z\" ;");
    b.append("cfg TO :=  \"A\" ;");
    b.append("cfg TYPE :=  \"B\" ;");
    b.append("cfg UNSIGNED_INT :=  \"C\" ;");
    b.append("cfg UNSIGNED_REAL :=  \"D\" ;");
    b.append("cfg UNTIL :=  \"E\" ;");
    b.append("cfg VAR :=  \"F\" ;");
    b.append("cfg WHILE :=  \"G\" ;");
    b.append("cfg WITH :=  \"H\" ;");
    b.append("cfg statement :=  \"IF\" expression \"THEN\" statement ;");
    b.append("reg limit := fix(program, 10);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

  //this takes forever
  public void test_sml_cfg() throws Exception{
    StringBuilder b = new StringBuilder();
    b.append("var hampiStringVar : 5;");
    b
        .append("cfg atexp :=  SCON | op VID | \"{\" exprow \"}\" | \"{\" \"}\" | \"#\" LAB | \"(\" \")\" | \"(\" expcn2 \")\" | \"[\" expcn \"]\" | \"[\" \"]\" | \"(\" expsn2 \")\" | LET dec IN expsn END | \"(\" exp \")\" ;");
    b.append("cfg expcn :=  exp | expcn \",\" exp ;");
    b.append("cfg expcn2 :=  exp \",\" exp | expcn2 \",\" exp ;");
    b.append("cfg expsn :=  exp | expsn \";\" exp ;");
    b.append("cfg expsn2 :=  exp \";\" exp | expsn2 \";\" exp ;");
    b.append("cfg exprow :=  LAB \"=\" exp | exprow \",\" LAB \"=\" exp ;");
    b.append("cfg appexp :=  atexp | appexp atexp ;");
    b.append("cfg infexp :=  appexp | infexp VID infexp ;");
    b.append("cfg exp :=  infexp | exp \":\" ty | exp ANDALSO exp | exp ORELSE exp | exp HANDLE match | RAISE exp | IF exp THEN exp ELSE exp | WHILE exp DO exp | CASE exp OF match | FN match ;");
    b.append("cfg match :=  mrule | match \":\" mrule ;");
    b.append("cfg mrule :=  pat MATCH exp ;");
    b
        .append("cfg dec :=  VAL tyvarseq valbind | FUN fvalbind | TYPE typbind | DATATYPE datbind | DATATYPE datbind WITHTYPE typbind | DATATYPE TYCON \"=\" DATATYPE TYCON | ABSTYPE datbind WITH dec END | ABSTYPE datbind WITHTYPE typbind WITH dec END | EXCEPTION exbind | LOCAL dec IN dec END | OPEN stridn | | dec dec | dec \";\" dec | INFIX vidn | INFIX DIGIT vidn | INFIXR vidn | INFIXR DIGIT vidn | NONFIX vidn ;");
    b.append("cfg stridn :=  STRID | stridn STRID ;");
    b.append("cfg vidn :=  VID | vidn VID ;");
    b.append("cfg valbind :=  pat \"=\" exp | valbind AND pat \"=\" exp | REC valbind ;");
    b.append("cfg fvalbind :=  mfvalbind | fvalbind AND mfvalbind ;");
    b.append("cfg mfvalbind :=  sfvalbind | mfvalbind \":\" sfvalbind ;");
    b.append("cfg sfvalbind :=  op VID atpatn \"=\" tyop exp ;");
    b.append("cfg op :=  | OP ;");
    b.append("cfg tyop :=  | \":\" ty ;");
    b.append("cfg atpatn :=  atpat | atpatn atpat ;");
    b.append("cfg typbind :=  tyvarseq TYCON \"=\" ty | typbind AND tyvarseq TYCON \"=\" ty ;");
    b.append("cfg tyvarseq :=  TYVAR | \"(\" tyvarcn \")\" | \"(\" \")\" | ;");
    b.append("cfg tyvarcn :=  TYVAR | tyvarcn \",\" TYVAR ;");
    b.append("cfg datbind :=  tyvarseq TYCON \"=\" conbind | datbind AND tyvarseq TYCON \"=\" conbind ;");
    b.append("cfg conbind :=  sconbind | conbind \":\" sconbind ;");
    b.append("cfg sconbind :=  op VID | op VID OF ty ;");
    b.append("cfg exbind :=  sexbind | exbind AND sexbind ;");
    b.append("cfg sexbind :=  op VID | op VID OF ty | op VID \"=\" op VID ;");
    b.append("cfg atpat :=  \"_\" | SCON | op VID | \"{\" patrow \"}\" | \"{\" \"}\" | \"(\" \")\" | \"(\" patcn2 \")\" | \"[\" \"]\" | \"[\" patcn \"]\" | \"(\" pat \")\" ;");
    b.append("cfg patcn :=  pat | patcn \",\" pat ;");
    b.append("cfg patcn2 :=  pat \",\" pat | patcn2 \",\" pat ;");
    b.append("cfg patrow :=  WILDCARD | spatrow | patrow \",\" spatrow ;");
    b.append("cfg spatrow :=  LAB \"=\" pat | VID tyop | VID tyop AS pat ;");
    b.append("cfg pat :=  atpat | op VID atpat | pat VID pat | pat \":\" ty | op VID tyop AS pat ;");
    b.append("cfg ty :=  TYVAR | \"{\" tyrow \"}\" | tyseq TYCON | tysn2 | ty APPL ty | \"(\" ty \")\" ;");
    b.append("cfg tyseq :=  ty | | \"(\" tycn \")\" | \"(\" \")\" ;");
    b.append("cfg tycn :=  ty | tycn \",\" ty ;");
    b.append("cfg tysn2 :=  ty \"*\" ty | tysn2 \"*\" ty ;");
    b.append("cfg tyrow :=  LAB \":\" ty | tyrow \",\" LAB \":\" ty ;");
    b.append("cfg ABSTYPE :=  \"a\" ;");
    b.append("cfg AND :=  \"b\" ;");
    b.append("cfg ANDALSO :=  \"c\" ;");
    b.append("cfg APPL :=  \"d\" ;");
    b.append("cfg AS :=  \"e\" ;");
    b.append("cfg CASE :=  \"f\" ;");
    b.append("cfg DATATYPE :=  \"g\" ;");
    b.append("cfg DIGIT :=  \"h\" ;");
    b.append("cfg DO :=  \"i\" ;");
    b.append("cfg ELSE :=  \"j\" ;");
    b.append("cfg END :=  \"k\" ;");
    b.append("cfg EXCEPTION :=  \"l\" ;");
    b.append("cfg FN :=  \"m\" ;");
    b.append("cfg FUN :=  \"n\" ;");
    b.append("cfg HANDLE :=  \"o\" ;");
    b.append("cfg IF :=  \"p\" ;");
    b.append("cfg IN :=  \"q\" ;");
    b.append("cfg INFIX :=  \"r\" ;");
    b.append("cfg INFIXR :=  \"s\" ;");
    b.append("cfg LAB :=  \"t\" ;");
    b.append("cfg LET :=  \"u\" ;");
    b.append("cfg LOCAL :=  \"v\" ;");
    b.append("cfg MATCH :=  \"w\" ;");
    b.append("cfg NONFIX :=  \"x\" ;");
    b.append("cfg OF :=  \"y\" ;");
    b.append("cfg OP :=  \"z\" ;");
    b.append("cfg OPEN :=  \"A\" ;");
    b.append("cfg ORELSE :=  \"B\" ;");
    b.append("cfg RAISE :=  \"C\" ;");
    b.append("cfg REC :=  \"D\" ;");
    b.append("cfg SCON :=  \"E\" ;");
    b.append("cfg STRID :=  \"F\" ;");
    b.append("cfg THEN :=  \"G\" ;");
    b.append("cfg TYCON :=  \"H\" ;");
    b.append("cfg TYPE :=  \"I\" ;");
    b.append("cfg TYVAR :=  \"J\" ;");
    b.append("cfg VAL :=  \"K\" ;");
    b.append("cfg VID :=  \"L\" ;");
    b.append("cfg WHILE :=  \"M\" ;");
    b.append("cfg WILDCARD :=  \"N\" ;");
    b.append("cfg WITH :=  \"O\" ;");
    b.append("cfg WITHTYPE :=  \"P\" ;");
    b.append("reg limit := fix(atexp, 5);");
    b.append("assert hampiStringVar in limit;");
    String c = b.toString();
    Hampi.run(true, true, new ByteArrayInputStream(c.getBytes()));
  }

}
