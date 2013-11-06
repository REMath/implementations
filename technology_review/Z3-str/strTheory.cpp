#include "strTheory.h"

FILE * logFile = NULL;
int sLevel = 0;
int searchStart = 0;
int tmpStringVarCount = 0;
int tmpIntVarCount = 0;
int tmpXorVarCount = 0;
int tmpBoolVarCount = 0;
int tmpConcatCount = 0;

std::map<std::string, Z3_ast> constStr_astNode_map;
std::map<Z3_ast, Z3_ast>      length_astNode_map;
std::map<Z3_ast, Z3_ast>      containsReduced_bool_str_map;
std::map<Z3_ast, Z3_ast>      containsReduced_bool_subStr_map;
std::map<Z3_ast, int>         basicStrVarAxiom_added;
std::map<Z3_ast, Z3_ast>      concat_eqc_index;

std::map<std::pair<Z3_ast, Z3_ast>, Z3_ast> concat_astNode_map;
std::map<std::pair<Z3_ast, Z3_ast>, Z3_ast> contains_astNode_map;
std::map<std::pair<Z3_ast, Z3_ast>, std::map<int, Z3_ast> > varForBreakConcat;
std::map<std::pair<Z3_ast, Z3_ast>, int> strEqLengthMap;

//----------------------------------------------------------------
// Data structure for modified algorithm
// backtrack-able cut information
struct T_cut
{
    int level;
    Z3_ast node;
    T_cut()
    {
        level = -100;
        node = NULL;
    }
    T_cut(int inLevel, Z3_ast inNode)
    {
        level = inLevel;
        node = inNode;
    }
};

// x1^{y}: Say x = x1.x2 and y cut x => x1 is a suffix of y. It's denoted as x1^{y}
// VAR(x1): x1 is a part of x => VAR
std::map<Z3_ast, std::stack<T_cut *> > cut_SuffixMap;
std::map<Z3_ast, std::stack<T_cut *> > cut_VARMap;

/*
 *
 */
void getCutSuffix(Z3_ast node, int & outLevel, Z3_ast & outNode)
{
    if (cut_SuffixMap.find(node) != cut_SuffixMap.end())
    {
        outLevel = cut_SuffixMap[node].top()->level;
        outNode = cut_SuffixMap[node].top()->node;
    }
    else
    {
        outLevel = -100;
        outNode = NULL;
    }
}

/*
 *
 */
void checkandInit_cutSuffixInfo(Z3_theory t, Z3_ast node)
{
    if (cut_SuffixMap.find(node) != cut_SuffixMap.end())
    {
        return;
    }
    else
    {
        if (getNodeType(t, node) != my_Z3_ConstStr)
        {
            T_cut * varInfo = new T_cut(-1, node);
            cut_SuffixMap[node].push(varInfo);
        }
    }
}


#ifdef DEBUGLOG
void printCutSuffix(Z3_theory t, Z3_ast node)
{
    if(getNodeType(t, node) != my_Z3_ConstStr)
    {
        int varLevel = -2;
        Z3_ast varNode = NULL;
        __debugPrint(logFile, "Suffix [ ");
        printZ3Node(t, node);
        __debugPrint(logFile, " ] = ");
        getCutSuffix(node, varLevel, varNode);
        if(varNode != NULL)
        {
            printZ3Node(t, varNode);
            __debugPrint(logFile, " (%d)\n", varLevel);
        }
        else
        {
            __debugPrint(logFile, " Unknown\n");
        }
    }
}
#endif

/*
 *
 */
void getCutVAR(Z3_ast node, int & outLevel, Z3_ast & outNode)
{
    if (cut_VARMap.find(node) != cut_VARMap.end())
    {
        outLevel = cut_VARMap[node].top()->level;
        outNode = cut_VARMap[node].top()->node;
    }
    else
    {
        outLevel = -100;
        outNode = NULL;
    }
}

/*
 *
 */
void checkandInit_cutVAR(Z3_theory t, Z3_ast node)
{
    if (cut_VARMap.find(node) != cut_VARMap.end())
    {
        return;
    }
    else
    {
        if (getNodeType(t, node) != my_Z3_ConstStr)
        {
            T_cut * varInfo = new T_cut(-1, node);
            cut_VARMap[node].push(varInfo);
        }
    }
}

/*
 *
 */
#ifdef DEBUGLOG
void printCutVAR(Z3_theory t, Z3_ast node)
{
    if(getNodeType(t, node) != my_Z3_ConstStr)
    {
        int varLevel = -2;
        Z3_ast varNode = NULL;

        __debugPrint(logFile, "VAR [ ");
        printZ3Node(t, node);
        __debugPrint(logFile, " ] = ");
        getCutVAR(node, varLevel, varNode);
        if(varNode != NULL)
        {
            printZ3Node(t, varNode);
            __debugPrint(logFile, " (%d)\n", varLevel);
        }
        else
        {
            __debugPrint(logFile, " Unknown\n");
        }
    }
}
#endif
//----------------------------------------------------------------

/*
 *
 */
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol s = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

/*
 *
 */
Z3_ast mk_bool_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_bool_sort(ctx);
    return mk_var(ctx, name, ty);
}

/*
 *
 */
Z3_ast mk_int_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return mk_var(ctx, name, ty);
}

/*
 *
 */
Z3_ast mk_int(Z3_context ctx, int v)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return Z3_mk_int(ctx, v, ty);
}

/*
 *
 */
Z3_ast my_mk_str_value(Z3_theory t, char const * str)
{
    Z3_context ctx = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData *) Z3_theory_get_ext_data(t);

    // if the empty string is not created, create one
    if (constStr_astNode_map.find("") == constStr_astNode_map.end())
    {
        Z3_symbol empty_str_sym = Z3_mk_string_symbol(ctx, "\"\"");
        Z3_ast emptyStrNode = Z3_theory_mk_value(ctx, t, empty_str_sym, td->String);
        constStr_astNode_map[""] = emptyStrNode;
    }

    std::string keyStr = std::string(str);
    // if the str is not created, create one
    if (constStr_astNode_map.find(keyStr) == constStr_astNode_map.end())
    {
        Z3_symbol str_sym = Z3_mk_string_symbol(ctx, str);
        Z3_ast strNode = Z3_theory_mk_value(ctx, t, str_sym, td->String);
        constStr_astNode_map[keyStr] = strNode;
    }
    return constStr_astNode_map[keyStr];
}

/*
 *
 */
Z3_ast my_mk_str_var(Z3_theory t, char const * name)
{
    Z3_context ctx = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData *) Z3_theory_get_ext_data(t);
    Z3_ast varAst = mk_var(ctx, name, td->String);
    basicStrVarAxiom(t, varAst, __LINE__);
    return varAst;
}

/*
 *
 */
Z3_ast my_mk_internal_string_var(Z3_theory t)
{
    std::stringstream ss;
    ss << tmpStringVarCount;
    tmpStringVarCount++;
    std::string name = "_t_str" + ss.str();
    return my_mk_str_var(t, name.c_str());
}

/*
 * Make an integer variable used for intermediated representation
 */
Z3_ast my_mk_internal_int_var(Z3_theory t)
{
    Z3_context ctx = Z3_theory_get_context(t);
    std::stringstream ss;
    ss << tmpIntVarCount;
    tmpIntVarCount++;
    std::string name = "_t_int_" + ss.str();
    return mk_int_var(ctx, name.c_str());
}

/*
 *
 */
Z3_ast mk_internal_xor_var(Z3_theory t)
{
    Z3_context ctx = Z3_theory_get_context(t);
    std::stringstream ss;
    ss << tmpXorVarCount;
    tmpXorVarCount++;
    std::string name = "_t_xor_" + ss.str();
    return mk_int_var(ctx, name.c_str());
}

/*
 * Return the node type in Enum
 */
T_myZ3Type getNodeType(Z3_theory t, Z3_ast n)
{
    Z3_context ctx = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);

    Z3_ast_kind z3Kind = Z3_get_ast_kind(ctx, n);
    switch (z3Kind)
    {
        case Z3_NUMERAL_AST:
            return my_Z3_Num;
            break;

        case Z3_APP_AST:
        {
            if (Z3_theory_is_value(t, n))
            {
                Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
                if (d == td->Compare || d == td->Concat || d == td->Length || d == td->SubString || d == td->Contains
                        || d == td->Indexof || d == td->Replace)
                    return my_Z3_Func;
                else
                    return my_Z3_ConstStr;
            }
            else
            {
                //Z3 native functions fall into this category
                Z3_sort s = Z3_get_sort(ctx, n);
                if (s == td->String)
                    return my_Z3_Str_Var;
                else
                    return my_Z3_Func;
            }
            break;
        }
        case Z3_VAR_AST:
        {
            return my_Z3_Var;
            break;
        }
        default:
        {
            break;
        }
    }
    return my_Z3_Unknown;
}

/*
 *
 */
Z3_ast mk_2_and(Z3_theory t, Z3_ast and1, Z3_ast and2)
{
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast and_items[2] = { and1, and2 };
    return Z3_mk_and(ctx, 2, and_items);
}

/*
 *
 */
Z3_ast mk_1_arg_app(Z3_context ctx, Z3_func_decl f, Z3_ast x)
{
    Z3_ast args[1] = { x };
    return Z3_mk_app(ctx, f, 1, args);
}

/*
 *
 *
 */
Z3_ast mk_2_arg_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y)
{
    Z3_ast args[2] = { x, y };
    return Z3_mk_app(ctx, f, 2, args);
}

/*
 *
 *
 */
Z3_ast mk_length(Z3_theory t, Z3_ast n)
{
    Z3_context ctx = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    if (length_astNode_map.find(n) == length_astNode_map.end())
    {
        if (getNodeType(t, n) == my_Z3_ConstStr)
        {
            length_astNode_map[n] = mk_int(ctx, getConstStrValue(t, n).length());
        }
        else
        {
            length_astNode_map[n] = mk_1_arg_app(ctx, td->Length, n);
        }
    }
    return length_astNode_map[n];
}

/*
 *
 *
 */
Z3_ast mk_contains(Z3_theory t, Z3_ast n1, Z3_ast n2)
{
    Z3_context ctx = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    std::pair<Z3_ast, Z3_ast> containsKey(n1, n2);
    if (contains_astNode_map.find(containsKey) == contains_astNode_map.end())
    {
        if (getNodeType(t, n1) == my_Z3_ConstStr && getNodeType(t, n2) == my_Z3_ConstStr)
        {
            std::string n1Str = getConstStrValue(t, n1);
            std::string n2Str = getConstStrValue(t, n2);
            if (n1Str.find(n2Str) != std::string::npos)
                contains_astNode_map[containsKey] = Z3_mk_true(ctx);
            else
                contains_astNode_map[containsKey] = Z3_mk_false(ctx);
        }
        else
        {
            contains_astNode_map[containsKey] = mk_2_arg_app(ctx, td->Contains, n1, n2);
        }
    }
    return contains_astNode_map[containsKey];
}

/*
 *
 *
 */
Z3_ast mk_concat(Z3_theory t, Z3_ast n1, Z3_ast n2)
{
    Z3_context ctx = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    if (n1 == NULL || n2 == NULL)
    {
        fprintf(stderr, "Error: the strings to be concat cannot be NULL (@ %d).\nExit...\n", __LINE__);
        exit(1);
        return NULL;
    }
    else
    {
        n1 = get_eqc_value(t, n1);
        n2 = get_eqc_value(t, n2);
        T_myZ3Type n1_type = getNodeType(t, n1);
        T_myZ3Type n2_type = getNodeType(t, n2);
        if (n1_type == my_Z3_ConstStr && n2_type == my_Z3_ConstStr)
        {
            return Concat(t, n1, n2);
        }
        else if (n1_type == my_Z3_ConstStr && n2_type != my_Z3_ConstStr)
        {
            bool n2_isConcatFunc = isConcatFunc(t, n2);
            if (getConstStrValue(t, n1) == "")
            {
                return n2;
            }
            if (n2_isConcatFunc)
            {
                Z3_ast n2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n2), 0);
                Z3_ast n2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n2), 1);
                if (getNodeType(t, n2_arg0) == my_Z3_ConstStr)
                {
                    n1 = Concat(t, n1, n2_arg0); // n1 will be a constant
                    n2 = n2_arg1;
                }
            }
        }
        else if (n1_type != my_Z3_ConstStr && n2_type == my_Z3_ConstStr)
        {
            bool n1_isConcatFunc = isConcatFunc(t, n1);
            if (getConstStrValue(t, n2) == "")
            {
                return n1;
            }

            if (n1_isConcatFunc)
            {
                Z3_ast n1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n1), 0);
                Z3_ast n1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n1), 1);
                if (getNodeType(t, n1_arg1) == my_Z3_ConstStr)
                {
                    n1 = n1_arg0;
                    n2 = Concat(t, n1_arg1, n2); // n2 will be a constant
                }
            }
        }
        else
        {
            if (isConcatFunc(t, n1) && isConcatFunc(t, n2))
            {
                Z3_ast n1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n1), 0);
                Z3_ast n1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n1), 1);
                Z3_ast n2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n2), 0);
                Z3_ast n2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n2), 1);

                T_myZ3Type n1_arg1_type = getNodeType(t, n1_arg1);
                T_myZ3Type n2_arg0_type = getNodeType(t, n2_arg0);

                if (n1_arg1_type == my_Z3_ConstStr && n2_arg0_type == my_Z3_ConstStr)
                {
                    Z3_ast tmpN1 = n1_arg0;
                    Z3_ast tmpN2 = Concat(t, n1_arg1, n2_arg0);
                    n1 = mk_concat(t, tmpN1, tmpN2);
                    n2 = n2_arg1;
                }
            }
        }

        //------------------------------------------------------
        // * Z3_ast ast1 = mk_2_arg_app(ctx, td->Concat, n1, n2);
        // * Z3_ast ast2 = mk_2_arg_app(ctx, td->Concat, n1, n2);
        // Z3 treats (ast1) and (ast2) as two different nodes.
        //-------------------------------------------------------
        std::pair<Z3_ast, Z3_ast> concatArgs(n1, n2);
        Z3_ast concatAst = NULL;
        if (concat_astNode_map.find(concatArgs) == concat_astNode_map.end())
        {
            concatAst = mk_2_arg_app(ctx, td->Concat, n1, n2);
#ifdef DEBUGLOG
            __debugPrint(logFile, "[Concat made] ");
            printZ3Node(t, concatAst);
            __debugPrint(logFile, "\n");
#endif
            concat_astNode_map[concatArgs] = concatAst;
            Z3_ast concat_length = mk_length(t, concatAst);
            Z3_ast n1_length = mk_length(t, n1);
            Z3_ast n2_length = mk_length(t, n2);
            Z3_ast addArg[2] = { n1_length, n2_length };
            Z3_ast lenAssert = Z3_mk_eq(ctx, concat_length, Z3_mk_add(ctx, 2, addArg));
            addAxiom(t, lenAssert, __LINE__, false);
            basicConcatAxiom(t, concatAst, __LINE__);
        }
        else
        {
            concatAst = concat_astNode_map[concatArgs];
        }
        return concatAst;
    }
}

/*
 *
 */
bool isTwoStrEqual(std::string str1, std::string str2)
{
    return (str1 == str2);
}

/*
 *
 */
void addAxiom(Z3_theory t, Z3_ast toAssert, int line, bool display)
{
#ifdef DEBUGLOG
    if(display)
    {
        if( searchStart == 1 )
        {
            __debugPrint(logFile, "---------------------\nAxiom Add(@%d, Level %d):\n", line, sLevel);
            printZ3Node(t, toAssert);
            __debugPrint(logFile, "\n---------------------\n");
        }
        else
        {
            __debugPrint(logFile, "---------------------\nAssertion Add(@%d, Level %d):\n", line, sLevel);
            printZ3Node(t, toAssert);
            __debugPrint(logFile, "\n---------------------\n");
        }
    }
#endif
    if (searchStart == 1)
    {
        Z3_theory_assert_axiom(t, toAssert);
    }
    else
    {
        Z3_context ctx = Z3_theory_get_context(t);
        Z3_assert_cnstr(ctx, toAssert);
    }
}

/*
 *
 */
void print_eq_class(Z3_theory t, Z3_ast n)
{
    __debugPrint(logFile, " EQC={ ");
    Z3_ast curr = n;
    int count = 0;
    do
    {
        if (count != 0)
        {
            __debugPrint(logFile, ", ");
        }
        printZ3Node(t, curr);
        curr = Z3_theory_get_eqc_next(t, curr);
        count++;
    } while (curr != n);
    __debugPrint(logFile, " }");
}

/*
 *
 */
void __printZ3Node(Z3_theory t, Z3_ast node)
{
#ifdef DEBUGLOG
    Z3_context ctx = Z3_theory_get_context(t);
    T_myZ3Type nodeType = getNodeType(t, node);
    switch (nodeType)
    {
        case my_Z3_ConstStr:
        {
            std::string str = getConstStrValue(t, node);
            __debugPrint(logFile, "\"%s\"", str.c_str());
            break;
        }
        case my_Z3_Func:
        {
            __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
            break;
        }
        case my_Z3_Num:
        {
            __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
            break;
        }
        case my_Z3_Var:
        {
            __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
            break;
        }
        case my_Z3_Str_Var:
        {
            __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
            break;
        }
        case my_Z3_Quantifier:
        {
            __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
            break;
        }
        case my_Z3_Unknown:
        {
            __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
            break;
        }
        default:
        {
            __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
            break;
        }
    }
#endif
}

/*
 * Look for the equivalent constant for a node "n"
 * Iterate the equivalence class
 * If there is a constant,
 *    return the constant
 * Otherwise,
 *    return n
 */
Z3_ast get_eqc_value(Z3_theory t, Z3_ast n)
{
    Z3_ast curr = n;
    do
    {
        if (Z3_theory_is_value(t, curr))
        {
            if (my_Z3_ConstStr == getNodeType(t, curr))
                return curr;
        }
        curr = Z3_theory_get_eqc_next(t, curr);
    } while (curr != n);
    return n;
}


/*
 *
 */
inline bool isConcatFunc(Z3_theory t, Z3_ast n)
{
    Z3_context ctx = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
    if (d == td->Concat)
        return true;
    else
        return false;
}


/*
 *
 */
bool isStrInt(std::string & strValue)
{
    bool isNum = true;
    if (strValue == "")
    {
        isNum = false;
    }
    else
    {
        std::string::iterator it = strValue.begin();
        if (*it == '-')
            ++it;
        while (it != strValue.end())
        {
            if (!std::isdigit(*it))
            {
                isNum = false;
                break;
            }
            ++it;
        }
    }
    return isNum;
}

/*
 *
 */
bool isStr2IntFunc(Z3_theory t, Z3_ast n)
{
    Z3_context ctx = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
    if (d == td->Str2Int)
        return true;
    else
        return false;
}

/*
 *
 */
std::string getConstStrValue(Z3_theory t, Z3_ast n)
{
    Z3_context ctx = Z3_theory_get_context(t);
    std::string strValue;
    if (getNodeType(t, n) == my_Z3_ConstStr)
    {
        char * str = (char *) Z3_ast_to_string(ctx, n);
        if (strcmp(str, "\"\"") == 0)
            strValue = std::string("");
        else
            strValue = std::string(str);
    }
    else
    {
        strValue == std::string("__NotConstStr__");
    }
    return strValue;
}

/*
 *
 */
// If not reducible, return NULL
Z3_ast Concat(Z3_theory t, Z3_ast n1, Z3_ast n2)
{
    Z3_ast result_ast;
    Z3_ast v1 = get_eqc_value(t, n1);
    Z3_ast v2 = get_eqc_value(t, n2);
    if (getNodeType(t, v1) == my_Z3_ConstStr && getNodeType(t, v2) == my_Z3_ConstStr)
    {
        std::string n1_str = getConstStrValue(t, v1);
        std::string n2_str = getConstStrValue(t, v2);
        std::string result = n1_str + n2_str;
        result_ast = my_mk_str_value(t, result.c_str());
        return result_ast;
    }
    else if (getNodeType(t, v1) == my_Z3_ConstStr && getNodeType(t, v2) != my_Z3_ConstStr)
    {
        if (getConstStrValue(t, v1) == "")
            return n2;
    }

    else if (getNodeType(t, v1) != my_Z3_ConstStr && getNodeType(t, v2) == my_Z3_ConstStr)
    {
        if (getConstStrValue(t, v2) == "")
            return n1;
    }
    return NULL;
}


/*
 * The inputs:
 *    ~ nn: non const node
 *    ~ eq_str: the equivalent constant string of nn
 *  Iterate the parent of all eqc nodes of nn, looking for:
 *    ~ concat node
 *  to see whether some concat nodes can be simplified.
 */
void simplifyStrWithEqConstStr(Z3_theory t, Z3_ast nn, Z3_ast eq_str)
{
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast n_eqNode = nn;
    std::string eq_strValue = getConstStrValue(t, eq_str);
    do
    {
        unsigned num_parents = Z3_theory_get_num_parents(t, n_eqNode);
        for (unsigned i = 0; i < num_parents; i++)
        {
            Z3_ast parent = Z3_theory_get_parent(t, n_eqNode, i);
            if (isConcatFunc(t, parent))
            {
                Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, parent), 0);
                Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, parent), 1);
                if (arg0 == n_eqNode)
                {
#ifdef DEBUGLOG
                    __debugPrint(logFile, "\n>> [Simplify Concat 1-1 @ %d] ", __LINE__);
                    printZ3Node(t, parent);
                    __debugPrint(logFile, "\n");
#endif
                    // (Concat n_eqNode arg1) /\ arg1 has eq const
                    Z3_ast concatResult = Concat(t, eq_str, arg1);
                    if (concatResult != NULL)
                    {
                        Z3_ast arg1Value = get_eqc_value(t, arg1);
                        Z3_ast implyL = NULL;
                        if (arg1Value != arg1)
                        {
                            Z3_ast eq_ast1 = Z3_mk_eq(ctx, n_eqNode, eq_str);
                            Z3_ast eq_ast2 = Z3_mk_eq(ctx, arg1, arg1Value);
                            implyL = mk_2_and(t, eq_ast1, eq_ast2);
                        }
                        else
                        {
                            implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                        }
                        if (!areTwoNodesInSameEqc(t, parent, concatResult))
                        {
                            Z3_ast implyR = Z3_mk_eq(ctx, parent, concatResult);
                            Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                            addAxiom(t, implyToAssert, __LINE__);
                        }
                    }
                    else if (isConcatFunc(t, n_eqNode))
                    {
                        Z3_ast simpleConcat = mk_concat(t, eq_str, arg1);
                        if (!areTwoNodesInSameEqc(t, parent, simpleConcat))
                        {
                            Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                            Z3_ast implyR = Z3_mk_eq(ctx, parent, simpleConcat);
                            Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                            addAxiom(t, implyToAssert, __LINE__);
                        }
                    }
                }

                if (arg1 == n_eqNode)
                {
#ifdef DEBUGLOG
                    __debugPrint(logFile, "\n>> [Simplify Concat 1-2 @ %d] ", __LINE__);
                    printZ3Node(t, parent);
                    __debugPrint(logFile, "\n");
#endif
                    // (Concat arg0 n_eqNode) /\ arg0 has eq const
                    Z3_ast concatResult = Concat(t, arg0, eq_str);
                    if (concatResult != NULL)
                    {
                        Z3_ast arg0Value = get_eqc_value(t, arg0);
                        Z3_ast implyL = NULL;
                        if (arg0Value != arg0)
                        {
                            Z3_ast eq_ast1 = Z3_mk_eq(ctx, arg0, arg0Value);
                            Z3_ast eq_ast2 = Z3_mk_eq(ctx, n_eqNode, eq_str);
                            implyL = mk_2_and(t, eq_ast1, eq_ast2);
                        }
                        else
                        {
                            implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                        }

                        if (!areTwoNodesInSameEqc(t, parent, concatResult))
                        {
                            Z3_ast implyR = Z3_mk_eq(ctx, parent, concatResult);
                            Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                            addAxiom(t, implyToAssert, __LINE__);
                        }
                    }

                    else if (isConcatFunc(t, n_eqNode))
                    {
                        Z3_ast simpleConcat = mk_concat(t, arg0, eq_str);
                        if (!areTwoNodesInSameEqc(t, parent, simpleConcat))
                        {
                            Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                            Z3_ast implyR = Z3_mk_eq(ctx, parent, simpleConcat);
                            Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                            addAxiom(t, implyToAssert, __LINE__);
                        }
                    }
                }
                //-------------------------------------------------
                // Case (2-1): (Concat n_eqNode (Concat str var))
                if (arg0 == n_eqNode && isConcatFunc(t, arg1))
                {
#ifdef DEBUGLOG
                    __debugPrint(logFile, "\n>> [Simplify Concat 2-1 @ %d] ", __LINE__);
                    printZ3Node(t, parent);
                    __debugPrint(logFile, "\n");
#endif
                    Z3_ast r_concat_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, arg1), 0);
                    if (getNodeType(t, r_concat_arg0) == my_Z3_ConstStr)
                    {
                        Z3_ast combined_str = Concat(t, eq_str, r_concat_arg0);
                        Z3_ast r_concat_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, arg1), 1);
                        Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                        Z3_ast simplifiedAst = mk_concat(t, combined_str, r_concat_arg1);

                        if (!areTwoNodesInSameEqc(t, parent, simplifiedAst))
                        {
                            Z3_ast implyR = Z3_mk_eq(ctx, parent, simplifiedAst);
                            Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                            addAxiom(t, implyToAssert, __LINE__);
                        }
                    }
                }

                // Case (2-2): (Concat (Concat var str) n_eqNode)
                if (isConcatFunc(t, arg0) && arg1 == n_eqNode)
                {
#ifdef DEBUGLOG
                    __debugPrint(logFile, "\n>> [Simplify Concat 2-2 @ %d] ", __LINE__);
                    printZ3Node(t, parent);
                    __debugPrint(logFile, "\n");
#endif
                    Z3_ast l_concat_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, arg0), 1);
                    if (getNodeType(t, l_concat_arg1) == my_Z3_ConstStr)
                    {
                        Z3_ast combined_str = Concat(t, l_concat_arg1, eq_str);
                        Z3_ast l_concat_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, arg0), 0);
                        Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                        Z3_ast simplifiedAst = mk_concat(t, l_concat_arg0, combined_str);

                        if (!areTwoNodesInSameEqc(t, parent, simplifiedAst))
                        {
                            Z3_ast implyR = Z3_mk_eq(ctx, parent, simplifiedAst);
                            Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                            addAxiom(t, implyToAssert, __LINE__);
                        }
                    }
                }

                // Have to look up one more layer: if the parent of the concat is another concat
                //-------------------------------------------------
                // Case (3-1): (Concat (Concat var n_eqNode) str )
                if (arg1 == n_eqNode)
                {
                    int concat_parent_num = Z3_theory_get_num_parents(t, parent);
                    for (int j = 0; j < concat_parent_num; j++)
                    {
                        Z3_ast concat_parent = Z3_theory_get_parent(t, parent, j);
                        if (isConcatFunc(t, concat_parent))
                        {
                            Z3_ast concat_parent_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concat_parent), 0);
                            Z3_ast concat_parent_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concat_parent), 1);
                            if (concat_parent_arg0 == parent && getNodeType(t, concat_parent_arg1) == my_Z3_ConstStr)
                            {
#ifdef DEBUGLOG
                                __debugPrint(logFile, "\n>> [Simplify Concat 3-1 @ %d] ", __LINE__);
                                printZ3Node(t, concat_parent);
                                __debugPrint(logFile, "\n");
#endif
                                Z3_ast combinedStr = Concat(t, eq_str, concat_parent_arg1);
                                Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                                Z3_ast simplifiedAst = mk_concat(t, arg0, combinedStr);

                                if (!areTwoNodesInSameEqc(t, concat_parent, simplifiedAst))
                                {
                                    Z3_ast implyR = Z3_mk_eq(ctx, concat_parent, simplifiedAst);
                                    Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                                    addAxiom(t, implyToAssert, __LINE__);
                                }
                            }
                        }
                    }
                }

                // Case (3-2): (Concat str (Concat n_eqNode var) )
                if (arg0 == n_eqNode)
                {
                    int concat_parent_num = Z3_theory_get_num_parents(t, parent);
                    for (int j = 0; j < concat_parent_num; j++)
                    {
                        Z3_ast concat_parent = Z3_theory_get_parent(t, parent, j);
                        if (isConcatFunc(t, concat_parent))
                        {
                            Z3_app parent_app = Z3_to_app(ctx, concat_parent);
                            Z3_ast concat_parent_arg0 = Z3_get_app_arg(ctx, parent_app, 0);
                            Z3_ast concat_parent_arg1 = Z3_get_app_arg(ctx, parent_app, 1);
                            if (concat_parent_arg1 == parent && getNodeType(t, concat_parent_arg0) == my_Z3_ConstStr)
                            {
#ifdef DEBUGLOG
                                __debugPrint(logFile, "\n>> [Simplify Concat 3-2 @ %d] ", __LINE__);
                                printZ3Node(t, concat_parent);
                                __debugPrint(logFile, "\n");
#endif
                                Z3_ast combinedStr = Concat(t, concat_parent_arg0, eq_str);
                                Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                                Z3_ast simplifiedAst = mk_concat(t, combinedStr, arg1);

                                if (!areTwoNodesInSameEqc(t, concat_parent, simplifiedAst))
                                {
                                    Z3_ast implyR = Z3_mk_eq(ctx, concat_parent, simplifiedAst);
                                    Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                                    addAxiom(t, implyToAssert, __LINE__);
                                }
                            }
                        }
                    }
                }
                //-------------------------------------------------
            }

            //*******************
            //
            //*******************
            else if (isStr2IntFunc(t, parent))
            {
#ifdef DEBUGLOG
                __debugPrint(logFile, "\n** simplify Str2Int With Eq ConstStr: ");
                printZ3Node(t, parent);
                __debugPrint(logFile, " << WITH >> ");
                printZ3Node(t, n_eqNode);
                __debugPrint(logFile, " = ");
                printZ3Node(t, eq_str);
                __debugPrint(logFile, "\n---------------------------------\n");
#endif
                std::string strValue = getConstStrValue(t, eq_str);
                bool isNum = isStrInt(strValue);
                Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, parent), 0);
                if (isNum)
                {
                    int value = atoi(strValue.c_str());
                    Z3_ast implyL = Z3_mk_eq(ctx, arg0, eq_str);
                    Z3_ast implyR = Z3_mk_eq(ctx, parent, mk_int(ctx, value));
                    Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                    addAxiom(t, implyToAssert, __LINE__);
                }
                else
                {
                    Z3_ast toAssert = Z3_mk_not(ctx, Z3_mk_eq(ctx, arg0, eq_str));
                    addAxiom(t, toAssert, __LINE__);
                }
            }

        }
        n_eqNode = Z3_theory_get_eqc_next(t, n_eqNode);
    } while (n_eqNode != nn);
}


/*
 * Check whether Concat(a, b) can eqaul to a constant string
 */
int canConcatEqStr(Z3_theory t, Z3_ast concat, std::string str)
{
    int strLen = str.length();
    if (isConcatFunc(t, concat))
    {
        Z3_ast ml_node = getMostLeftNodeInConcat(t, concat);
        if (getNodeType(t, ml_node) == my_Z3_ConstStr)
        {
            std::string ml_str = getConstStrValue(t, ml_node);
            int ml_len = ml_str.length();
            if (ml_len > strLen)
                return 0;
            int cLen = ml_len;
            if (ml_str != str.substr(0, cLen))
                return 0;
        }

        Z3_ast mr_node = getMostRightNodeInConcat(t, concat);
        if (getNodeType(t, mr_node) == my_Z3_ConstStr)
        {
            std::string mr_str = getConstStrValue(t, mr_node);
            int mr_len = mr_str.length();
            if (mr_len > strLen)
                return 0;
            int cLen = mr_len;
            if (mr_str != str.substr(strLen - cLen, cLen))
                return 0;
        }
    }
    return 1;
}

/*
 * For two concats "assumed" to be equal by Z3, before having their concrete values:
 * Check whether the two concat can be equal
 */
int canConcatEqConcat(Z3_theory t, Z3_ast concat1, Z3_ast concat2)
{
    // make sure left and right are concat functions
    if (isConcatFunc(t, concat1) && isConcatFunc(t, concat2))
    {
        // Suppose concat1 = concat(x, y), concat2 = concat(m, n)
        Z3_ast concat1_mostL = getMostLeftNodeInConcat(t, concat1);
        Z3_ast concat2_mostL = getMostLeftNodeInConcat(t, concat2);

        // if both x and m are const strings, check whether they have the same prefix
        if (getNodeType(t, concat1_mostL) == my_Z3_ConstStr && getNodeType(t, concat2_mostL) == my_Z3_ConstStr)
        {
            std::string concat1_mostL_str = getConstStrValue(t, concat1_mostL);
            std::string concat2_mostL_str = getConstStrValue(t, concat2_mostL);
            int cLen =
                    (concat1_mostL_str.length() > concat2_mostL_str.length()) ?
                            concat2_mostL_str.length() : concat1_mostL_str.length();
            if (concat1_mostL_str.substr(0, cLen) != concat2_mostL_str.substr(0, cLen))
                return 0;
        }

        Z3_ast concat1_mostR = getMostRightNodeInConcat(t, concat1);
        Z3_ast concat2_mostR = getMostRightNodeInConcat(t, concat2);
        // if both m and n are const strings, check whether they have the same suffix
        if (getNodeType(t, concat1_mostR) == my_Z3_ConstStr && getNodeType(t, concat2_mostR) == my_Z3_ConstStr)
        {
            std::string concat1_mostR_str = getConstStrValue(t, concat1_mostR);
            std::string concat2_mostR_str = getConstStrValue(t, concat2_mostR);
            int cLen = (concat1_mostR_str.length() > concat2_mostR_str.length()) ?
                            concat2_mostR_str.length() : concat1_mostR_str.length();
            if (concat1_mostR_str.substr(concat1_mostR_str.length() - cLen, cLen)
                    != concat2_mostR_str.substr(concat2_mostR_str.length() - cLen, cLen))
                return 0;
        }
    }
    return 1;
}

/*
 * Decide whether two n1 and n2 are ALREADY in a same eq class
 * Or n1 and n2 are ALREADY treated equal by the core
 * BUT, they may or may not be really equal
 */
bool areTwoNodesInSameEqc(Z3_theory t, Z3_ast n1, Z3_ast n2)
{
    if (n1 == n2)
        return true;

    Z3_ast curr = Z3_theory_get_eqc_next(t, n1);
    while (curr != n1)
    {
        if (curr == n2)
            return true;
        curr = Z3_theory_get_eqc_next(t, curr);
    }
    return false;
}

/*
 *
 */
bool canTwoNodesEq(Z3_theory t, Z3_ast n1, Z3_ast n2)
{
    Z3_ast n1_curr = n1;
    Z3_ast n2_curr = n2;

    // case 0: n1_curr is const string, n2_curr is const string
    if (getNodeType(t, n1_curr) == my_Z3_ConstStr && getNodeType(t, n2_curr) == my_Z3_ConstStr)
    {
        if (n1_curr != n2_curr)
        {
            return false;
        }
    }
    // case 1: n1_curr is concat, n2_curr is const string
    else if (isConcatFunc(t, n1_curr) && getNodeType(t, n2_curr) == my_Z3_ConstStr)
    {
        std::string n2_curr_str = getConstStrValue(t, n2_curr);
        if (canConcatEqStr(t, n1_curr, n2_curr_str) != 1)
        {
            return false;
        }
    }
    // case 2: n2_curr is concat, n1_curr is const string
    else if (isConcatFunc(t, n2_curr) && getNodeType(t, n1_curr) == my_Z3_ConstStr)
    {
        std::string n1_curr_str = getConstStrValue(t, n1_curr);
        if (canConcatEqStr(t, n2_curr, n1_curr_str) != 1)
        {
            return false;
        }
    }
    else if (isConcatFunc(t, n1_curr) && isConcatFunc(t, n2_curr))
    {
        if (canConcatEqConcat(t, n1_curr, n2_curr) != 1)
        {
            return false;
        }
    }

    return true;
}

//------------------------------------------------------------
// solve concat of pattern:
//    constStr == Concat( constrStr, xx )
//    constStr == Concat( xx, constrStr )
//------------------------------------------------------------
void solve_concat_eq_str(Z3_theory t, Z3_ast concatAst, Z3_ast constStr)
{
#ifdef DEBUGLOG
    __debugPrint(logFile, "** solve_concat_eq_str: ");
    printZ3Node(t, concatAst);
    __debugPrint(logFile, " = ");
    printZ3Node(t, constStr);
    __debugPrint(logFile, "\n");
#endif
    Z3_context ctx = Z3_theory_get_context(t);
    if (isConcatFunc(t, concatAst) && getNodeType(t, constStr) == my_Z3_ConstStr)
    {
        std::string const_str = getConstStrValue(t, constStr);
        Z3_ast a1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst), 0);
        Z3_ast a2 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst), 1);
        Z3_ast arg1 = get_eqc_value(t, a1);
        Z3_ast arg2 = get_eqc_value(t, a2);
        Z3_ast newConcat = NULL;
        if (a1 != arg1 || a2 != arg2)
        {
            int iPos = 0;
            Z3_ast item1[2];
            if (a1 != arg1)
                item1[iPos++] = Z3_mk_eq(ctx, a1, arg1);
            if (a2 != arg2)
                item1[iPos++] = Z3_mk_eq(ctx, a2, arg2);
            Z3_ast implyL1 = NULL;
            if (iPos == 1)
                implyL1 = item1[0];
            else
                implyL1 = Z3_mk_and(ctx, 2, item1);

            newConcat = Concat(t, arg1, arg2);
            if (newConcat == NULL)
                newConcat = mk_concat(t, arg1, arg2);

            if (newConcat != constStr)
            {
                Z3_ast implyR1 = Z3_mk_eq(ctx, concatAst, newConcat);
                addAxiom(t, Z3_mk_implies(ctx, implyL1, implyR1), __LINE__);
            }
        }
        else
        {
            newConcat = concatAst;
        }

        if (newConcat == constStr)
            return;

        if (!isConcatFunc(t, newConcat))
            return;

        //---------------------------------------------------------------------
        // (1) Concat(const_Str, const_Str) = const_Str
        //---------------------------------------------------------------------
        if (getNodeType(t, arg1) == my_Z3_ConstStr && getNodeType(t, arg2) == my_Z3_ConstStr)
        {
            std::string arg1_str = getConstStrValue(t, arg1);
            std::string arg2_str = getConstStrValue(t, arg2);
            std::string result_str = arg1_str + arg2_str;
            if (result_str != const_str)
            {
                // negate
                addAxiom(t, Z3_mk_not(ctx, Z3_mk_eq(ctx, concatAst, constStr)), __LINE__);
                return;
            }
        }

        //---------------------------------------------------------------------
        // (2) Concat( var, const_Str ) = const_Str
        //---------------------------------------------------------------------
        else if (getNodeType(t, arg1) != my_Z3_ConstStr && getNodeType(t, arg2) == my_Z3_ConstStr)
        {
            std::string arg2_str = getConstStrValue(t, arg2);
            int resultStrLen = const_str.length();
            int arg2StrLen = arg2_str.length();
            if (resultStrLen < arg2StrLen)
            {
                // negate
                addAxiom(t, Z3_mk_not(ctx, Z3_mk_eq(ctx, newConcat, constStr)), __LINE__);
                return;
            }
            else
            {
                int varStrLen = resultStrLen - arg2StrLen;
                std::string firstPart = const_str.substr(0, varStrLen);
                std::string secondPart = const_str.substr(varStrLen, arg2StrLen);
                if (isTwoStrEqual(arg2_str, secondPart) != true)
                {
                    // negate
                    Z3_ast negateAst = Z3_mk_not(ctx, Z3_mk_eq(ctx, newConcat, constStr));
                    addAxiom(t, negateAst, __LINE__);
                    return;
                }
                else
                {
                    Z3_ast tmpStrConst = my_mk_str_value(t, firstPart.c_str());
                    Z3_ast implyL = Z3_mk_eq(ctx, newConcat, constStr);
                    Z3_ast implyR = Z3_mk_eq(ctx, arg1, tmpStrConst);
                    strEqLengthAxiom(t, arg1, tmpStrConst, __LINE__);
                    addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                }
            }
        }

        //---------------------------------------------------------------------
        // (3) Concat(const_Str, var) = const_Str
        //---------------------------------------------------------------------
        else if (getNodeType(t, arg1) == my_Z3_ConstStr && getNodeType(t, arg2) != my_Z3_ConstStr)
        {
            std::string arg1_str = getConstStrValue(t, arg1);
            int resultStrLen = const_str.length();
            int arg1StrLen = arg1_str.length();
            if (resultStrLen < arg1StrLen)
            {
                // negate
                addAxiom(t, Z3_mk_not(ctx, Z3_mk_eq(ctx, newConcat, constStr)), __LINE__);
                return;
            }
            else
            {
                int varStrLen = resultStrLen - arg1StrLen;
                std::string firstPart = const_str.substr(0, arg1StrLen);
                std::string secondPart = const_str.substr(arg1StrLen, varStrLen);
                if (isTwoStrEqual(arg1_str, firstPart) != true)
                {
                    // negate
                    Z3_ast negateAst = Z3_mk_not(ctx, Z3_mk_eq(ctx, newConcat, constStr));
                    addAxiom(t, negateAst, __LINE__);
                    return;
                }
                else
                {
                    Z3_ast tmpStrConst = my_mk_str_value(t, secondPart.c_str());
                    Z3_ast implyL = Z3_mk_eq(ctx, newConcat, constStr);
                    Z3_ast implyR = Z3_mk_eq(ctx, arg2, tmpStrConst);
                    strEqLengthAxiom(t, arg2, tmpStrConst, __LINE__);
                    addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                }
            }
        }
        //---------------------------------------------------------------------
        // (4) Concat(var, var) = const_Str
        //     Only when arg1 and arg2 do not have eq constant string values
        //---------------------------------------------------------------------
        else
        {
            if (Concat(t, arg1, arg2) == NULL)
            {
                Z3_ast xorFlag = NULL;
                std::pair<Z3_ast, Z3_ast> key1(arg1, arg2);
                std::pair<Z3_ast, Z3_ast> key2(arg2, arg1);
                if (varForBreakConcat.find(key1) == varForBreakConcat.end()
                        && varForBreakConcat.find(key2) == varForBreakConcat.end())
                {
                    xorFlag = mk_internal_xor_var(t);
                    varForBreakConcat[key1][0] = xorFlag;
                }
                else
                {
                    if (varForBreakConcat.find(key1) != varForBreakConcat.end())
                    {
                        xorFlag = varForBreakConcat[key1][0];
                    }
                    else
                    {
                        xorFlag = varForBreakConcat[key2][0];
                    }
                }

                int concatStrLen = const_str.length();
                int xor_pos = 0;
                int and_count = 1;
                Z3_ast * xor_items = new Z3_ast[concatStrLen + 1];
                Z3_ast * and_items = new Z3_ast[2 * (concatStrLen + 1) + 1];
                Z3_ast arg1_eq = NULL;
                Z3_ast arg2_eq = NULL;
                for (int i = 0; i < concatStrLen + 1; i++)
                {
                    std::string prefixStr = const_str.substr(0, i);
                    std::string suffixStr = const_str.substr(i, concatStrLen - i);

                    // skip invalidate options
                    if (isConcatFunc(t, arg1) && canConcatEqStr(t, arg1, prefixStr) == 0)
                    {
                        continue;
                    }
                    if (isConcatFunc(t, arg2) && canConcatEqStr(t, arg2, suffixStr) == 0)
                    {
                        continue;
                    }

                    Z3_ast xorAst = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, xor_pos));
                    xor_items[xor_pos++] = xorAst;

                    Z3_ast prefixAst = my_mk_str_value(t, prefixStr.c_str());
                    arg1_eq = Z3_mk_eq(ctx, arg1, prefixAst);
                    and_items[and_count++] = Z3_mk_eq(ctx, xorAst, arg1_eq);
                    strEqLengthAxiom(t, arg1, prefixAst, __LINE__);

                    Z3_ast suffixAst = my_mk_str_value(t, suffixStr.c_str());
                    arg2_eq = Z3_mk_eq(ctx, arg2, suffixAst);
                    and_items[and_count++] = Z3_mk_eq(ctx, xorAst, arg2_eq);
                    strEqLengthAxiom(t, arg2, suffixAst, __LINE__);
                }

                Z3_ast implyL = Z3_mk_eq(ctx, concatAst, constStr);
                Z3_ast implyR1 = NULL;
                if (xor_pos == 0)
                {
                    // negate
                    Z3_ast negateAst = Z3_mk_not(ctx, Z3_mk_eq(ctx, concatAst, constStr));
                    addAxiom(t, negateAst, __LINE__);
                }
                else
                {
                    if (xor_pos == 1)
                    {
                        and_items[0] = xor_items[0];
                        implyR1 = Z3_mk_and(ctx, and_count, and_items);
                    }
                    else
                    {
                        and_items[0] = Z3_mk_or(ctx, xor_pos, xor_items);
                        implyR1 = Z3_mk_and(ctx, and_count, and_items);
                    }
                    Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR1);
                    addAxiom(t, implyToAssert, __LINE__);
                }
                delete[] xor_items;
                delete[] and_items;
            }
        }
    }
}

bool eqClassHasStr2Int(Z3_theory t, Z3_ast n, Z3_ast & str2intArg, Z3_ast & str2intNode)
{
    Z3_ast n_eqNode = n;
    do
    {
        unsigned num_parents = Z3_theory_get_num_parents(t, n_eqNode);
        for (unsigned i = 0; i < num_parents; i++)
        {
            Z3_ast parent = Z3_theory_get_parent(t, n_eqNode, i);
            if (isStr2IntFunc(t, parent))
            {
                str2intNode = parent;
                str2intArg = n_eqNode;
                return true;
            }
        }
        n_eqNode = Z3_theory_get_eqc_next(t, n_eqNode);
    } while (n_eqNode != n);
    return false;
}

/*
 * Add axiom for free variable
 */
Z3_ast axiomForFreeVar(Z3_theory t, Z3_ast n)
{
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast assertion = NULL;

    Z3_ast str2IntArg = NULL;
    Z3_ast str2IntNode = NULL;
    if (eqClassHasStr2Int(t, n, str2IntArg, str2IntNode))
    {
        Z3_ast and2[3];
        and2[0] = Z3_mk_ge(ctx, str2IntNode, mk_int(ctx, str2Int_MinInt));
        and2[1] = Z3_mk_le(ctx, str2IntNode, mk_int(ctx, str2Int_MaxInt));

        std::list<Z3_ast> option_items;
        for (int i = str2Int_MinInt; i <= str2Int_MaxInt; i++)
        {
            char buf[20];
            sprintf(buf, "%d", i);
            Z3_ast option1 = Z3_mk_eq(ctx, str2IntArg, my_mk_str_value(t, buf));
            option_items.push_back(option1);
        }
        Z3_ast * or_items = new Z3_ast[option_items.size()];
        int pos = 0;
        std::list<Z3_ast>::iterator itor = option_items.begin();
        for (; itor != option_items.end(); itor++)
            or_items[pos++] = *itor;

        and2[2] = Z3_mk_or(ctx, pos, or_items);
        Z3_ast str2IntRange = Z3_mk_and(ctx, 3, and2);

        delete or_items;
        return str2IntRange;
    }
    else
    {
        std::list<Z3_ast> option_items;
        std::list<Z3_ast> imply_items;

        Z3_ast n_lenAst = mk_length(t, n);
        for (int i = 0; i < unCstrStrMaxLen + 1; i++)
        {
            std::string tmp = "";
            for (int j = 0; j < i; j++)
                tmp += "@";

            Z3_ast strAst = my_mk_str_value(t, tmp.c_str());
            Z3_ast valueEqAst = Z3_mk_eq(ctx, n, strAst);
            option_items.push_back(valueEqAst);
            if (i != 0)
            {
                Z3_ast lenEqAst = Z3_mk_eq(ctx, n_lenAst, mk_int(ctx, i));
                Z3_ast lenImply = Z3_mk_implies(ctx, valueEqAst, lenEqAst);
                imply_items.push_back(lenImply);
            }
        }

        Z3_ast * or_items = new Z3_ast[option_items.size()];
        int pos = 0;
        std::list<Z3_ast>::iterator itor = option_items.begin();
        for (; itor != option_items.end(); itor++)
            or_items[pos++] = *itor;

        Z3_ast * and_items = new Z3_ast[2 + imply_items.size()];
        and_items[0] = Z3_mk_or(ctx, pos, or_items);
        int pos1 = 1;
        itor = imply_items.begin();
        for (; itor != imply_items.end(); itor++)
            and_items[pos1++] = *itor;

        and_items[pos1++] = Z3_mk_le(ctx, n_lenAst, mk_int(ctx, unCstrStrMaxLen));
        assertion = Z3_mk_and(ctx, pos1, and_items);
        delete[] and_items;
        delete[] or_items;

        return assertion;
    }
}


/*
 * Get variable count in an AST node
 */
int getVarCountInAst(Z3_theory t, Z3_ast n)
{
    Z3_context ctx = Z3_theory_get_context(t);
    if (getNodeType(t, n) == my_Z3_Str_Var)
        return 1;
    else if (getNodeType(t, n) == my_Z3_Func)
    {
        int varCountInFunc = 0;
        Z3_app func_app = Z3_to_app(ctx, n);
        int argCount = Z3_get_app_num_args(ctx, func_app);
        for (int i = 0; i < argCount; i++)
        {
            Z3_ast argAst = Z3_get_app_arg(ctx, func_app, i);
            varCountInFunc += getVarCountInAst(t, argAst);
        }
        return varCountInFunc;
    }
    else
        return 0;
}

/*
 * Get variables in an AST node and return them in astList
 */
void getStrVarsInNode(Z3_theory t, Z3_ast node, std::map<Z3_ast, int> & astMap)
{
    Z3_context ctx = Z3_theory_get_context(t);
    if (getNodeType(t, node) == my_Z3_Str_Var)
    {
        if (astMap.find(node) == astMap.end())
            astMap[node] = 1;
    }
    else if (getNodeType(t, node) == my_Z3_Func)
    {
        Z3_app func_app = Z3_to_app(ctx, node);
        int argCount = Z3_get_app_num_args(ctx, func_app);
        for (int i = 0; i < argCount; i++)
        {
            Z3_ast argAst = Z3_get_app_arg(ctx, func_app, i);
            getStrVarsInNode(t, argAst, astMap);
        }
    }
}

/*
 * Get constant strings (from left to right) in an AST node and return them in astList
 */
void getconstStrAstsInNode(Z3_theory t, Z3_ast node, std::list<Z3_ast> & astList)
{
    Z3_context ctx = Z3_theory_get_context(t);
    if (getNodeType(t, node) == my_Z3_ConstStr)
        astList.push_back(node);
    else if (getNodeType(t, node) == my_Z3_Func)
    {
        Z3_app func_app = Z3_to_app(ctx, node);
        int argCount = Z3_get_app_num_args(ctx, func_app);
        for (int i = 0; i < argCount; i++)
        {
            Z3_ast argAst = Z3_get_app_arg(ctx, func_app, i);
            getconstStrAstsInNode(t, argAst, astList);
        }
    }
}

/*
 *
 */
void strEqLengthAxiom(Z3_theory t, Z3_ast varAst, Z3_ast strAst, int line)
{
    std::pair<Z3_ast, Z3_ast> key1(varAst, strAst);
    std::pair<Z3_ast, Z3_ast> key2(strAst, varAst);
    if (strEqLengthMap.find(key1) != strEqLengthMap.end() || strEqLengthMap.find(key2) != strEqLengthMap.end())
    {
        return;
    }

    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast implyL = Z3_mk_eq(ctx, varAst, strAst);
    Z3_ast toAssert = NULL;
    if (getNodeType(t, strAst) == my_Z3_ConstStr)
    {
        std::string str = getConstStrValue(t, strAst);
        if (str == "")
        {
            if (getNodeType(t, varAst) != my_Z3_Str_Var)
            {
                Z3_ast lenAst = mk_int(ctx, 0);
                toAssert = Z3_mk_eq(ctx, implyL, Z3_mk_eq(ctx, mk_length(t, varAst), lenAst));
            }
            else
            {
                // basicStrVarAxiom() already adds above axiom. Not necessary to assert it again
                return;
            }
        }
        else
        {
            Z3_ast lenAst = mk_int(ctx, str.length());
            toAssert = Z3_mk_implies(ctx, implyL, Z3_mk_eq(ctx, mk_length(t, varAst), lenAst));
        }
    }
    else
    {
        Z3_ast lenAst = mk_length(t, strAst);
        toAssert = Z3_mk_implies(ctx, implyL, Z3_mk_eq(ctx, mk_length(t, varAst), lenAst));
    }
    addAxiom(t, toAssert, line, false);
    strEqLengthMap[key1] = 1;
#ifdef DEBUGLOG
    __debugPrint(logFile, "[Length Axiom added] ");
    printZ3Node(t, implyL);
    __debugPrint(logFile, " @ %d\n", line);
#endif
}


/*
 * Handle two equivalent Concats. nn1 and nn2 are two concat functions
 */
int simplifyConcatEq(Z3_theory t, Z3_ast nn1, Z3_ast nn2, int duplicateCheck)
{
    Z3_context ctx = Z3_theory_get_context(t);

    Z3_ast a1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn1), 0);
    Z3_ast a1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn1), 1);
    Z3_ast a2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn2), 0);
    Z3_ast a2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn2), 1);

    int axiomAdded = 0;
    Z3_ast item1[5];
    int iPos = 0;
    //-----------------------------------------
    Z3_ast v1_arg0 = get_eqc_value(t, a1_arg0);
    Z3_ast v1_arg1 = get_eqc_value(t, a1_arg1);
    Z3_ast new_nn1 = NULL;
    if (a1_arg0 != v1_arg0 || a1_arg1 != v1_arg1)
    {
        if (a1_arg0 != v1_arg0)
            item1[iPos++] = Z3_mk_eq(ctx, a1_arg0, v1_arg0);
        if (a1_arg1 != v1_arg1)
            item1[iPos++] = Z3_mk_eq(ctx, a1_arg1, v1_arg1);

        new_nn1 = Concat(t, v1_arg0, v1_arg1);
        if (new_nn1 == NULL)
        {
            new_nn1 = mk_concat(t, v1_arg0, v1_arg1);
        }
    }
    else
    {
        new_nn1 = nn1;
    }

    //------------------------------------------------------

    Z3_ast v2_arg0 = get_eqc_value(t, a2_arg0);
    Z3_ast v2_arg1 = get_eqc_value(t, a2_arg1);
    Z3_ast new_nn2 = NULL;
    if (a2_arg0 != v2_arg0 || a2_arg1 != v2_arg1)
    {
        if (a2_arg0 != v2_arg0)
            item1[iPos++] = Z3_mk_eq(ctx, a2_arg0, v2_arg0);
        if (a2_arg1 != v2_arg1)
            item1[iPos++] = Z3_mk_eq(ctx, a2_arg1, v2_arg1);

        new_nn2 = Concat(t, v2_arg0, v2_arg1);
        if (new_nn2 == NULL)
        {
            new_nn2 = mk_concat(t, v2_arg0, v2_arg1);
        }
    }
    else
    {
        new_nn2 = nn2;
    }

    if (new_nn1 == new_nn2)
    {
        return 0;
    }

    if (!canTwoNodesEq(t, new_nn1, new_nn2))
    {
        __debugPrint(logFile, "[Wrong_imply]");
        printZ3Node(t, new_nn1);
        __debugPrint(logFile, " != ");
        printZ3Node(t, new_nn2);
        __debugPrint(logFile, "\n");
        return 0;
    }

    if (iPos != 0)
    {
        if (!areTwoNodesInSameEqc(t, new_nn1, new_nn2))
        {
            item1[iPos++] = Z3_mk_eq(ctx, nn1, nn2);
            Z3_ast implyL = Z3_mk_and(ctx, iPos, item1);
            Z3_ast implyR = Z3_mk_eq(ctx, new_nn1, new_nn2);
            addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
            axiomAdded = 1;

            if (new_nn1 != nn1 && concat_eqc_index.find(nn1) != concat_eqc_index.end())
            {
                concat_eqc_index[new_nn1] = concat_eqc_index[nn1];
            }

            if (new_nn2 != nn2 && concat_eqc_index.find(nn2) != concat_eqc_index.end())
            {
                concat_eqc_index[new_nn2] = concat_eqc_index[nn2];
            }
        }
    }

    if (duplicateCheck)
    {
        if (isConcatFunc(t, new_nn1) && isConcatFunc(t, new_nn2))
        {
            Z3_ast concatIndex = NULL;
            if (concat_eqc_index.find(new_nn1) != concat_eqc_index.end()
                    && concat_eqc_index.find(new_nn2) != concat_eqc_index.end())
            {
                std::pair<Z3_ast, Z3_ast> v(new_nn1, new_nn2);
                std::pair<Z3_ast, Z3_ast> key2(new_nn2, new_nn1);
                {
                    return axiomAdded;
                }

            }
            else if (concat_eqc_index.find(new_nn1) == concat_eqc_index.end()
                    && concat_eqc_index.find(new_nn2) != concat_eqc_index.end())
            {
                concatIndex = concat_eqc_index[new_nn2];
                concat_eqc_index[new_nn1] = concatIndex;
            }
            else if (concat_eqc_index.find(new_nn1) != concat_eqc_index.end()
                    && concat_eqc_index.find(new_nn2) == concat_eqc_index.end())
            {
                concatIndex = concat_eqc_index[new_nn1];
                concat_eqc_index[new_nn2] = concatIndex;
            }
            else
            {
                concatIndex = new_nn1;
                concat_eqc_index[new_nn1] = concatIndex;
                concat_eqc_index[new_nn2] = concatIndex;
            }
        }
        else
        {
            return axiomAdded;
        }
    }

    //*****************************************************
    // Start to break down two equal irreducible Concats
    //*****************************************************

    //-----------------------------------------------------
    // in context: may be the order id "new_nn2 = new_nn1"
    // after splitting axiom added, a duplicated assertion may be added:
    //     "new_nn1 = new_nn2"
    // Such duplicated assertion may cause problems
    // So, let's look for the "new_nn2 = new_nn1" in the context
    //------------------------------------------------------------------
    Z3_ast implyL = NULL;
    Z3_ast ctxAssign = Z3_get_context_assignment(ctx);
    if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, ctxAssign))) != Z3_OP_AND)
    {
        if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, ctxAssign))) == Z3_OP_EQ)
        {
            Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, ctxAssign), 0);
            Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, ctxAssign), 1);
            if ((arg0 == new_nn1 && arg1 == new_nn2) || (arg1 == new_nn1 && arg0 == new_nn2))
                implyL = ctxAssign;
        }
    }
    else
    {
        int argCount = Z3_get_app_num_args(ctx, Z3_to_app(ctx, ctxAssign));
        for (int i = 0; i < argCount; i++)
        {
            Z3_ast itemAssign = Z3_get_app_arg(ctx, Z3_to_app(ctx, ctxAssign), i);
            if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, itemAssign))) == Z3_OP_EQ)
            {
                Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, itemAssign), 0);
                Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, itemAssign), 1);
                if ((arg0 == new_nn1 && arg1 == new_nn2) || (arg1 == new_nn1 && arg0 == new_nn2))
                {
                    implyL = itemAssign;
                    break;
                }
            }
        }
    }

    if (implyL == NULL)
    {
        implyL = Z3_mk_eq(ctx, new_nn1, new_nn2);
    }

    std::pair<Z3_ast, Z3_ast> key11(new_nn1, new_nn2);
    std::pair<Z3_ast, Z3_ast> key22(new_nn2, new_nn1);

    checkandInit_cutSuffixInfo(t, v1_arg0);
    checkandInit_cutSuffixInfo(t, v1_arg1);
    checkandInit_cutSuffixInfo(t, v2_arg0);
    checkandInit_cutSuffixInfo(t, v2_arg1);
    checkandInit_cutVAR(t, v1_arg0);
    checkandInit_cutVAR(t, v1_arg1);
    checkandInit_cutVAR(t, v2_arg0);
    checkandInit_cutVAR(t, v2_arg1);

    //*************************************************************
    // case 1: concat(x, y) = concat(m, n)
    //*************************************************************
    if ((getNodeType(t, v1_arg0) != my_Z3_ConstStr && getNodeType(t, v1_arg1) != my_Z3_ConstStr
            && getNodeType(t, v2_arg0) != my_Z3_ConstStr && getNodeType(t, v2_arg1) != my_Z3_ConstStr))
    {
#ifdef DEBUGLOG
        __debugPrint(logFile, "\n");
        __debugPrint(logFile, "#############################\n");
        __debugPrint(logFile, "#  SimplifyConcatEq Type 1  #\n");
        __debugPrint(logFile, "#############################\n");
#endif
        Z3_ast x = v1_arg0;
        Z3_ast y = v1_arg1;
        Z3_ast m = v2_arg0;
        Z3_ast n = v2_arg1;

        if (x == m)
        {
            if (!areTwoNodesInSameEqc(t, y, n))
            {
                Z3_ast t_implyR = Z3_mk_eq(ctx, y, n);
                Z3_ast toAssert = Z3_mk_implies(ctx, implyL, t_implyR);
                addAxiom(t, toAssert, __LINE__);
                axiomAdded = 1;
            }
        }
        else if (y == n)
        {
            if (!areTwoNodesInSameEqc(t, x, m))
            {
                Z3_ast t_implyR = Z3_mk_eq(ctx, x, m);
                Z3_ast toAssert = Z3_mk_implies(ctx, implyL, t_implyR);
                addAxiom(t, toAssert, __LINE__);
                axiomAdded = 1;
            }
        }
        else
        {
            Z3_ast m1 = NULL;
            Z3_ast m2 = NULL;
            Z3_ast n1 = NULL;
            Z3_ast n2 = NULL;
            Z3_ast xorFlag = NULL;

            std::pair<Z3_ast, Z3_ast> key1(new_nn1, new_nn2);
            std::pair<Z3_ast, Z3_ast> key2(new_nn2, new_nn1);

            if (varForBreakConcat.find(key1) == varForBreakConcat.end()
                    && varForBreakConcat.find(key2) == varForBreakConcat.end())
            {
                m1 = my_mk_internal_string_var(t);
                m2 = my_mk_internal_string_var(t);
                n1 = my_mk_internal_string_var(t);
                n2 = my_mk_internal_string_var(t);
                xorFlag = mk_internal_xor_var(t);

                varForBreakConcat[key1][0] = m1;
                varForBreakConcat[key1][1] = m2;
                varForBreakConcat[key1][2] = n1;
                varForBreakConcat[key1][3] = n2;
                varForBreakConcat[key1][4] = xorFlag;
            }
            else
            {
                if (varForBreakConcat.find(key1) != varForBreakConcat.end())
                {
                    m1 = varForBreakConcat[key1][0];
                    m2 = varForBreakConcat[key1][1];
                    n1 = varForBreakConcat[key1][2];
                    n2 = varForBreakConcat[key1][3];
                    xorFlag = varForBreakConcat[key1][4];
                }
                else
                {
                    m1 = varForBreakConcat[key2][0];
                    m2 = varForBreakConcat[key2][1];
                    n1 = varForBreakConcat[key2][2];
                    n2 = varForBreakConcat[key2][3];
                    xorFlag = varForBreakConcat[key2][4];
                }
            }

            Z3_ast m1_m2 = mk_concat(t, m1, m2);
            Z3_ast m_eq_concat_m1_m2 = Z3_mk_eq(ctx, m, m1_m2);
            Z3_ast n1_n2 = mk_concat(t, n1, n2);
            Z3_ast n_eq_concat_n1_n2 = Z3_mk_eq(ctx, n, n1_n2);

            Z3_ast * or_item = new Z3_ast[3];
            Z3_ast * and_item = new Z3_ast[13];
            int option = 0;
            int pos = 1;
            int lastLevel = -100;
            Z3_ast lastNode = NULL;
            getCutSuffix(x, lastLevel, lastNode);

            //--------------------------------------
            // break option 1: x cut m
            //--------------------------------------
            // if x cut y (meaning x is the cause of split of y)
            // Check whether
            //   suffix(x) ?= VAR(y)
            //   - Yes. Do not cut y again
            //   - NO. OK to proceed
            //--------------------------------------
            Z3_ast x_suffix = lastNode;
            Z3_ast m_var = NULL;
            int m_var_level = -100;
            getCutVAR(m, m_var_level, m_var);

            if (!((x_suffix != NULL) && (x_suffix == m_var)))
            {
                // break down option 1-1
                Z3_ast m2_n = mk_concat(t, m2, n);
                or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
                and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, x, m1));
                and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, m2_n));
                and_item[pos++] = Z3_mk_eq(ctx, or_item[option], m_eq_concat_m1_m2);
                option++;

                //"str_eq --> length_eq" constraints
                strEqLengthAxiom(t, x, m1, __LINE__);
                strEqLengthAxiom(t, y, m2_n, __LINE__);
                strEqLengthAxiom(t, m, m1_m2, __LINE__);

                // Cut Info
                cut_VARMap[m1].push(new T_cut(sLevel, m));
                cut_VARMap[m2].push(new T_cut(sLevel, m));
                if (lastLevel == -100)
                    cut_SuffixMap[m1].push(new T_cut(sLevel, x));
                else
                    cut_SuffixMap[m1].push(new T_cut(sLevel, lastNode));
                cut_SuffixMap[m2].push(new T_cut(sLevel, m));
            }
            else
            {
#ifdef DEBUGLOG
                __debugPrint(logFile, "[option 1 @ %d] Skip. Duplicate Cut\n", __LINE__);
#endif
            }
            //--------------------------------------
            // break option 2: x cut n
            //--------------------------------------
            Z3_ast n_var = NULL;
            int n_var_level = -100;
            getCutVAR(n, n_var_level, n_var);

            if (!((x_suffix != NULL) && (x_suffix == n_var)))
            {
                // break down option 1-2
                Z3_ast m_n1 = mk_concat(t, m, n1);
                or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
                and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, x, m_n1));
                and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, n2));
                and_item[pos++] = Z3_mk_eq(ctx, or_item[option], n_eq_concat_n1_n2);
                option++;

                //"str_eq --> length_eq" constraints
                strEqLengthAxiom(t, x, m_n1, __LINE__);
                strEqLengthAxiom(t, y, n2, __LINE__);
                strEqLengthAxiom(t, n, n1_n2, __LINE__);

                // Cut Info
                cut_VARMap[n1].push(new T_cut(sLevel, n));
                cut_VARMap[n2].push(new T_cut(sLevel, n));
                if (lastLevel == -100)
                    cut_SuffixMap[n1].push(new T_cut(sLevel, x));
                else
                    cut_SuffixMap[n1].push(new T_cut(sLevel, lastNode));
                cut_SuffixMap[n2].push(new T_cut(sLevel, n));
            }
            else
            {
#ifdef DEBUGLOG
                __debugPrint(logFile, "[option 2 @ %d] Skip. Duplicate Cut\n", __LINE__);
#endif
            }

            if (option > 0)
            {
                if (option == 1)
                {
                    and_item[0] = or_item[0];
                }
                else
                {
                    and_item[0] = Z3_mk_or(ctx, option, or_item);
                }

                Z3_ast implyR = Z3_mk_and(ctx, pos, and_item);
                Z3_ast toAssert = Z3_mk_implies(ctx, implyL, implyR);

                addAxiom(t, toAssert, __LINE__);
                axiomAdded = 1;
            }
            else
            {
                __debugPrint(logFile, "\n[STOP @ %d] Should not split two EQ concats:", __LINE__);
                __debugPrint(logFile, "\n            ");
                printZ3Node(t, implyL);
                __debugPrint(logFile, "\n");
                return axiomAdded;
            }
            delete[] or_item;
            delete[] and_item;
            return axiomAdded;
        }
        return axiomAdded;
    }

    //*************************************************************
    // case 2: concat(x, y) = concat(m, "str")
    //*************************************************************
    if ((getNodeType(t, v1_arg0) != my_Z3_ConstStr && getNodeType(t, v1_arg1) == my_Z3_ConstStr
            && getNodeType(t, v2_arg0) != my_Z3_ConstStr && getNodeType(t, v2_arg1) != my_Z3_ConstStr)
            || (getNodeType(t, v2_arg0) != my_Z3_ConstStr && getNodeType(t, v2_arg1) == my_Z3_ConstStr
                    && getNodeType(t, v1_arg0) != my_Z3_ConstStr && getNodeType(t, v1_arg1) != my_Z3_ConstStr))
    {
        __debugPrint(logFile, "\n");
        __debugPrint(logFile, "#############################\n");
        __debugPrint(logFile, "#  SimplifyConcatEq Type 2  #\n");
        __debugPrint(logFile, "#############################\n");
        Z3_ast x = NULL;
        Z3_ast y = NULL;
        Z3_ast strAst = NULL;
        Z3_ast m = NULL;
        Z3_ast xorFlag = NULL;

        if (getNodeType(t, v1_arg1) == my_Z3_ConstStr && getNodeType(t, v2_arg1) != my_Z3_ConstStr)
        {
            m = v1_arg0;
            strAst = v1_arg1;
            x = v2_arg0;
            y = v2_arg1;
        }
        else
        {
            m = v2_arg0;
            strAst = v2_arg1;
            x = v1_arg0;
            y = v1_arg1;
        }

        //Quick path
        if (getConstStrValue(t, strAst) == "")
        {
        }
        else
        {
            Z3_ast m1 = NULL;
            Z3_ast m2 = NULL;
            std::pair<Z3_ast, Z3_ast> key1(new_nn1, new_nn2);
            std::pair<Z3_ast, Z3_ast> key2(new_nn2, new_nn1);
            if (varForBreakConcat.find(key1) == varForBreakConcat.end()
                    && varForBreakConcat.find(key2) == varForBreakConcat.end())
            {
                m1 = my_mk_internal_string_var(t);
                m2 = my_mk_internal_string_var(t);
                xorFlag = mk_internal_xor_var(t);

                varForBreakConcat[key1][0] = m1;
                varForBreakConcat[key1][1] = m2;
                varForBreakConcat[key1][2] = xorFlag;
            }
            else
            {
                if (varForBreakConcat.find(key1) != varForBreakConcat.end())
                {
                    m1 = varForBreakConcat[key1][0];
                    m2 = varForBreakConcat[key1][1];
                    xorFlag = varForBreakConcat[key1][2];
                }
                else if (varForBreakConcat.find(key2) != varForBreakConcat.end())
                {
                    m1 = varForBreakConcat[key2][0];
                    m2 = varForBreakConcat[key2][1];
                    xorFlag = varForBreakConcat[key2][2];
                }
            }

            std::string strValue = getConstStrValue(t, strAst);
            int optionTotal = 2 + strValue.length();
            Z3_ast * or_item = new Z3_ast[optionTotal];
            Z3_ast * and_item = new Z3_ast[1 + 6 + 4 * (strValue.length() + 1)];
            int option = 0;
            int pos = 1;

            int lastLevel = -100;
            Z3_ast lastNode = NULL;
            getCutSuffix(x, lastLevel, lastNode);

            // option 1
            Z3_ast m1_m2 = mk_concat(t, m1, m2);
            Z3_ast m2_strAst = mk_concat(t, m2, strAst);
            //--------------------------------------------------------
            // x cut m
            //--------------------------------------------------------
            Z3_ast x_suffix = lastNode;
            Z3_ast m_var = NULL;
            int m_var_level = -100;
            getCutVAR(m, m_var_level, m_var);

            if (canTwoNodesEq(t, y, m2_strAst))
            {
                if (!((x_suffix != NULL) && (x_suffix == m_var)))
                {
                    // break down option 2-1
                    or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, m, m1_m2));
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, x, m1));
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, m2_strAst));
                    option++;

                    //"str_eq --> length_eq" constraints
                    strEqLengthAxiom(t, m, m1_m2, __LINE__);
                    strEqLengthAxiom(t, x, m1, __LINE__);
                    strEqLengthAxiom(t, y, m2_strAst, __LINE__);

                    //Cut Info
                    cut_VARMap[m1].push(new T_cut(sLevel, m));
                    cut_VARMap[m2].push(new T_cut(sLevel, m));
                    if (lastLevel == -100)
                        cut_SuffixMap[m1].push(new T_cut(sLevel, x));
                    else
                        cut_SuffixMap[m1].push(new T_cut(sLevel, lastNode));
                    cut_SuffixMap[m2].push(new T_cut(sLevel, m));
                }
                else
                {
#ifdef DEBUGLOG
                    __debugPrint(logFile, "[option @ %d] Skip. Duplicate Cut\n", __LINE__);
#endif
                }
            }

            for (int i = 0; i <= (int) strValue.size(); i++)
            {
                std::string part1Str = strValue.substr(0, i);
                std::string part2Str = strValue.substr(i, strValue.size() - i);
                Z3_ast x_concat = mk_concat(t, m, my_mk_str_value(t, part1Str.c_str()));
                Z3_ast cropStr = my_mk_str_value(t, part2Str.c_str());
                if (canTwoNodesEq(t, x, x_concat) && canTwoNodesEq(t, y, cropStr))
                {
                    // break down option 2-2
                    or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, x, x_concat));
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, cropStr));
                    option++;

                    //"str_eq --> length_eq" constraints
                    strEqLengthAxiom(t, y, cropStr, __LINE__);
                    strEqLengthAxiom(t, x, x_concat, __LINE__);
                }
            }

            if (option > 0)
            {
                if (option == 1)
                    and_item[0] = or_item[0];
                else
                    and_item[0] = Z3_mk_or(ctx, option, or_item);
                Z3_ast implyR = Z3_mk_and(ctx, pos, and_item);
                addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                axiomAdded = 1;
            }
            else
            {
                __debugPrint(logFile, "\n[STOP @ %d] Should not split two EQ concats:", __LINE__);
                __debugPrint(logFile, "\n            ");
                printZ3Node(t, implyL);
                __debugPrint(logFile, "\n");
                return axiomAdded;
            }
            delete or_item;
            delete and_item;
            return axiomAdded;
        }
        return axiomAdded;
    }

    //*************************************************************
    // case 3: concat(x, y) = concat("str", n)
    //*************************************************************
    if ((getNodeType(t, v1_arg0) == my_Z3_ConstStr && getNodeType(t, v1_arg1) != my_Z3_ConstStr
            && getNodeType(t, v2_arg0) != my_Z3_ConstStr && getNodeType(t, v2_arg1) != my_Z3_ConstStr)
            || (getNodeType(t, v2_arg0) == my_Z3_ConstStr && getNodeType(t, v2_arg1) != my_Z3_ConstStr
                    && getNodeType(t, v1_arg0) != my_Z3_ConstStr && getNodeType(t, v1_arg1) != my_Z3_ConstStr))
    {
        __debugPrint(logFile, "\n");
        __debugPrint(logFile, "#############################\n");
        __debugPrint(logFile, "#  SimplifyConcatEq Type 3  #\n");
        __debugPrint(logFile, "#############################\n");
        Z3_ast x = NULL;
        Z3_ast y = NULL;
        Z3_ast strAst = NULL;
        Z3_ast n = NULL;
        Z3_ast xorFlag = NULL;

        if (getNodeType(t, v1_arg0) == my_Z3_ConstStr && getNodeType(t, v2_arg0) != my_Z3_ConstStr)
        {
            strAst = v1_arg0;
            n = v1_arg1;
            x = v2_arg0;
            y = v2_arg1;
        }
        else
        {
            strAst = v2_arg0;
            n = v2_arg1;
            x = v1_arg0;
            y = v1_arg1;
        }
        //Quick path
        if (getConstStrValue(t, strAst) == "")
        {

        }
        else
        {
            Z3_ast n1 = NULL;
            Z3_ast n2 = NULL;
            std::pair<Z3_ast, Z3_ast> key1(new_nn1, new_nn2);
            std::pair<Z3_ast, Z3_ast> key2(new_nn2, new_nn1);
            if (varForBreakConcat.find(key1) == varForBreakConcat.end()
                    && varForBreakConcat.find(key2) == varForBreakConcat.end())
            {
                n1 = my_mk_internal_string_var(t);
                n2 = my_mk_internal_string_var(t);
                xorFlag = mk_internal_xor_var(t);

                varForBreakConcat[key1][0] = n1;
                varForBreakConcat[key1][1] = n2;
                varForBreakConcat[key1][2] = xorFlag;
            }
            else
            {
                if (varForBreakConcat.find(key1) != varForBreakConcat.end())
                {
                    n1 = varForBreakConcat[key1][0];
                    n2 = varForBreakConcat[key1][1];
                    xorFlag = varForBreakConcat[key1][2];
                }
                else if (varForBreakConcat.find(key2) != varForBreakConcat.end())
                {
                    n1 = varForBreakConcat[key2][0];
                    n2 = varForBreakConcat[key2][1];
                    xorFlag = varForBreakConcat[key2][2];
                }
            }

            std::string strValue = getConstStrValue(t, strAst);
            int optionTotal = 2 + strValue.length();
            Z3_ast * or_item = new Z3_ast[optionTotal];
            int option = 0;
            Z3_ast * and_item = new Z3_ast[2 + 3 * optionTotal];
            int pos = 1;
            for (int i = 0; i <= (int) strValue.size(); i++)
            {
                std::string part1Str = strValue.substr(0, i);
                std::string part2Str = strValue.substr(i, strValue.size() - i);
                Z3_ast cropStr = my_mk_str_value(t, part1Str.c_str());
                Z3_ast y_concat = mk_concat(t, my_mk_str_value(t, part2Str.c_str()), n);

                if (canTwoNodesEq(t, x, cropStr) && canTwoNodesEq(t, y, y_concat))
                {
                    // break down option 3-1
                    Z3_ast x_eq_str = Z3_mk_eq(ctx, x, cropStr);
                    or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], x_eq_str);
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, y_concat));
                    option++;
                    //"str_eq --> length_eq" constraints
                    strEqLengthAxiom(t, x, cropStr, __LINE__);
                    strEqLengthAxiom(t, y, y_concat, __LINE__);
                }
            }

            Z3_ast n1_n2 = mk_concat(t, n1, n2);
            Z3_ast strAst_n1 = mk_concat(t, strAst, n1);
            int lastLevel = -100;
            Z3_ast lastNode = NULL;
            getCutSuffix(x, lastLevel, lastNode);
            //--------------------------------------------------------
            // x cut n
            //--------------------------------------------------------
            Z3_ast x_suffix = lastNode;
            Z3_ast n_var = NULL;
            int n_var_level = -100;
            getCutVAR(n, n_var_level, n_var);

            if (canTwoNodesEq(t, x, strAst_n1))
            {
                if (!((x_suffix != NULL) && (x_suffix == n_var)))
                {
                    // break down option 3-2
                    or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, n, n1_n2));
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, x, strAst_n1));
                    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, n2));
                    option++;

                    //"str_eq --> length_eq" constraints
                    strEqLengthAxiom(t, n, n1_n2, __LINE__);
                    strEqLengthAxiom(t, x, strAst_n1, __LINE__);
                    strEqLengthAxiom(t, y, n2, __LINE__);

                    //--- Cut Info----
                    cut_VARMap[n1].push(new T_cut(sLevel, n));
                    cut_VARMap[n2].push(new T_cut(sLevel, n));
                    if (lastLevel == -100)
                        cut_SuffixMap[n1].push(new T_cut(sLevel, x));
                    else
                        cut_SuffixMap[n1].push(new T_cut(sLevel, lastNode));
                    cut_SuffixMap[n2].push(new T_cut(sLevel, n));
                }
                else
                {
#ifdef DEBUGLOG
                    __debugPrint(logFile, "[option @ %d] Skip. Duplicate Cut\n", __LINE__);
#endif
                }
            }

            if (option > 0)
            {
                if (option == 1)
                    and_item[0] = or_item[0];
                else
                    and_item[0] = Z3_mk_or(ctx, option, or_item);
                Z3_ast implyR = Z3_mk_and(ctx, pos, and_item);
                addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                axiomAdded = 1;
            }
            else
            {
                __debugPrint(logFile, "\n[STOP @ %d] Should not split two EQ concats:", __LINE__);
                __debugPrint(logFile, "\n            ");
                printZ3Node(t, implyL);
                __debugPrint(logFile, "\n");
                return axiomAdded;
            }
            delete or_item;
            delete and_item;
            return axiomAdded;
        }
        return axiomAdded;
    }

    //*************************************************************
    //  case 4: concat("str1", y) = concat("str2", n)
    //*************************************************************
    if ((getNodeType(t, v1_arg0) == my_Z3_ConstStr && getNodeType(t, v1_arg1) != my_Z3_ConstStr
            && getNodeType(t, v2_arg0) == my_Z3_ConstStr && getNodeType(t, v2_arg1) != my_Z3_ConstStr))
    {

        Z3_ast str1Ast = v1_arg0;
        Z3_ast y = v1_arg1;
        Z3_ast str2Ast = v2_arg0;
        Z3_ast n = v2_arg1;
        std::string str1Value = getConstStrValue(t, str1Ast);
        std::string str2Value = getConstStrValue(t, str2Ast);
        int str1Len = str1Value.length();
        int str2Len = str2Value.length();

        __debugPrint(logFile, "\n");
        __debugPrint(logFile, "#############################\n");
        __debugPrint(logFile, "#  SimplifyConcatEq Type 4  #\n");
        __debugPrint(logFile, "#############################\n");

        int commonLen = (str1Len > str2Len) ? str2Len : str1Len;
        if (str1Value.substr(0, commonLen) != str2Value.substr(0, commonLen))
        {
            __debugPrint(logFile, "  - Conflict [new_eq:4-1] ");
            printZ3Node(t, new_nn1);
            __debugPrint(logFile, " is not equal to ");
            printZ3Node(t, new_nn2);
            __debugPrint(logFile, "\n");
            Z3_ast toNegate = Z3_mk_not(ctx, Z3_mk_eq(ctx, new_nn1, new_nn2));
            addAxiom(t, toNegate, __LINE__);
            axiomAdded = 1;
            return 1;
        }
        else
        {
            if (str1Len > str2Len)
            {
                std::string deltaStr = str1Value.substr(str2Len, str1Len - str2Len);
                Z3_ast tmpAst = mk_concat(t, my_mk_str_value(t, deltaStr.c_str()), y);
                if (!areTwoNodesInSameEqc(t, tmpAst, n))
                {
                    // break down option 4-1
                    Z3_ast implyR = Z3_mk_eq(ctx, n, tmpAst);
                    addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                    //"str_eq --> length_eq" constraints
                    strEqLengthAxiom(t, n, tmpAst, __LINE__);
                    axiomAdded = 1;
                }
            }
            else if (str1Len == str2Len)
            {
                if (!areTwoNodesInSameEqc(t, n, y))
                {
                    //break down option 4-2
                    Z3_ast implyR = Z3_mk_eq(ctx, n, y);
                    addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                    //"str_eq --> length_eq" constraints
                    strEqLengthAxiom(t, n, y, __LINE__);
                    axiomAdded = 1;
                }
            }
            else
            {
                std::string deltaStr = str2Value.substr(str1Len, str2Len - str1Len);
                Z3_ast tmpAst = mk_concat(t, my_mk_str_value(t, deltaStr.c_str()), n);
                if (!areTwoNodesInSameEqc(t, y, tmpAst))
                {
                    //break down option 4-3
                    Z3_ast implyR = Z3_mk_eq(ctx, y, tmpAst);
                    addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                    //"str_eq --> length_eq" constraints
                    strEqLengthAxiom(t, y, tmpAst, __LINE__);
                    axiomAdded = 1;
                }
            }
        }
        return axiomAdded;
    }

    //*************************************************************
    //  case 5: concat(x, "str1") = concat(m, "str2")
    //*************************************************************
    if ((getNodeType(t, v1_arg0) != my_Z3_ConstStr && getNodeType(t, v1_arg1) == my_Z3_ConstStr
            && getNodeType(t, v2_arg0) != my_Z3_ConstStr && getNodeType(t, v2_arg1) == my_Z3_ConstStr))
    {
        __debugPrint(logFile, "\n");
        __debugPrint(logFile, "#############################\n");
        __debugPrint(logFile, "#  SimplifyConcatEq Type 5  #\n");
        __debugPrint(logFile, "#############################\n");
        Z3_ast x = v1_arg0;
        Z3_ast str1Ast = v1_arg1;
        Z3_ast m = v2_arg0;
        Z3_ast str2Ast = v2_arg1;
        std::string str1Value = getConstStrValue(t, str1Ast);
        std::string str2Value = getConstStrValue(t, str2Ast);
        int str1Len = str1Value.length();
        int str2Len = str2Value.length();

        int cLen = (str1Len > str2Len) ? str2Len : str1Len;
        if (str1Value.substr(str1Len - cLen, cLen) != str2Value.substr(str2Len - cLen, cLen))
        {
            __debugPrint(logFile, "\n  - Conflict [new_eq:5-1] { ");
            printZ3Node(t, new_nn1);
            __debugPrint(logFile, " } is not equal to { ");
            printZ3Node(t, new_nn2);
            __debugPrint(logFile, " }\n");
            Z3_ast toNegate = Z3_mk_not(ctx, Z3_mk_eq(ctx, new_nn1, new_nn2));
            addAxiom(t, toNegate, __LINE__);
            return 1;
        }
        else
        {
            if (str1Len > str2Len)
            {
                std::string deltaStr = str1Value.substr(0, str1Len - str2Len);
                Z3_ast x_deltaStr = mk_concat(t, x, my_mk_str_value(t, deltaStr.c_str()));
                Z3_ast implyR = Z3_mk_eq(ctx, m, x_deltaStr);
                addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                //"str_eq --> length_eq" constraints
                strEqLengthAxiom(t, m, x_deltaStr, __LINE__);
                axiomAdded = 1;
            }
            else if (str1Len == str2Len)
            {
                Z3_ast implyR = Z3_mk_eq(ctx, x, m);
                addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                //"str_eq --> length_eq" constraints
                strEqLengthAxiom(t, x, m, __LINE__);
                axiomAdded = 1;
            }
            else
            {
                std::string deltaStr = str2Value.substr(0, str2Len - str1Len);
                Z3_ast m_deltaStr = mk_concat(t, m, my_mk_str_value(t, deltaStr.c_str()));
                Z3_ast implyR = Z3_mk_eq(ctx, x, m_deltaStr);
                addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
                //"str_eq --> length_eq" constraints
                strEqLengthAxiom(t, x, m_deltaStr, __LINE__);
                axiomAdded = 1;
            }
        }
        return axiomAdded;
    }
    //*************************************************************
    //  case 6: concat("str1", y) = concat(m, "str2")
    //*************************************************************
    if ((getNodeType(t, v1_arg0) == my_Z3_ConstStr && getNodeType(t, v1_arg1) != my_Z3_ConstStr
            && getNodeType(t, v2_arg0) != my_Z3_ConstStr && getNodeType(t, v2_arg1) == my_Z3_ConstStr)
            || (getNodeType(t, v2_arg0) == my_Z3_ConstStr && getNodeType(t, v2_arg1) != my_Z3_ConstStr
                    && getNodeType(t, v1_arg0) != my_Z3_ConstStr && getNodeType(t, v1_arg1) == my_Z3_ConstStr))
    {
        __debugPrint(logFile, "\n");
        __debugPrint(logFile, "#############################\n");
        __debugPrint(logFile, "#  SimplifyConcatEq Type 6  #\n");
        __debugPrint(logFile, "#############################\n");

        Z3_ast str1Ast = NULL;
        Z3_ast y = NULL;
        Z3_ast m = NULL;
        Z3_ast str2Ast = NULL;

        if (getNodeType(t, v1_arg0) == my_Z3_ConstStr)
        {
            str1Ast = v1_arg0;
            y = v1_arg1;
            m = v2_arg0;
            str2Ast = v2_arg1;
        }
        else
        {
            str1Ast = v2_arg0;
            y = v2_arg1;
            m = v1_arg0;
            str2Ast = v1_arg1;
        }
        std::string str1Value = getConstStrValue(t, str1Ast);
        std::string str2Value = getConstStrValue(t, str2Ast);
        //----------------------------------------
        //(a)  |---str1---|----y----|
        //     |--m--|-----str2-----|
        //
        //(b)  |---str1---|----y----|
        //     |-----m----|--str2---|
        //
        //(c)  |---str1---|----y----|
        //     |------m------|-str2-|
        //----------------------------------------
        std::list<int> overlapLen;
        overlapLen.push_back(0);
        int str1Len = str1Value.length();
        int str2Len = str2Value.length();
        for (int i = 1; i <= str1Len && i <= str2Len; i++)
        {
            if (str1Value.substr(str1Len - i, i) == str2Value.substr(0, i))
                overlapLen.push_back(i);
        }

        //----------------------------------------------------------------
        Z3_ast commonVar = NULL;
        Z3_ast xorFlag = NULL;
        std::pair<Z3_ast, Z3_ast> key1(new_nn1, new_nn2);
        std::pair<Z3_ast, Z3_ast> key2(new_nn2, new_nn1);
        if (varForBreakConcat.find(key1) == varForBreakConcat.end()
                && varForBreakConcat.find(key2) == varForBreakConcat.end())
        {
            commonVar = my_mk_internal_string_var(t);
            xorFlag = mk_internal_xor_var(t);
            varForBreakConcat[key1][0] = commonVar;
            varForBreakConcat[key1][1] = xorFlag;
        }
        else
        {
            if (varForBreakConcat.find(key1) != varForBreakConcat.end())
            {
                commonVar = varForBreakConcat[key1][0];
                xorFlag = varForBreakConcat[key1][1];
            }
            else
            {
                commonVar = varForBreakConcat[key2][0];
                xorFlag = varForBreakConcat[key2][1];
            }
        }
        Z3_ast * or_item = new Z3_ast[overlapLen.size() + 1];
        int option = 0;
        Z3_ast * and_item = new Z3_ast[1 + 4 * (overlapLen.size() + 1)];
        int pos = 1;
        for (std::list<int>::iterator itor = overlapLen.begin(); itor != overlapLen.end(); itor++)
        {
            int overLen = *itor;
            std::string prefix = str1Value.substr(0, str1Len - overLen);
            std::string suffix = str2Value.substr(overLen, str2Len - overLen);
            or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));

            Z3_ast prefixAst = my_mk_str_value(t, prefix.c_str());
            Z3_ast x_eq_prefix = Z3_mk_eq(ctx, m, prefixAst);
            and_item[pos++] = Z3_mk_eq(ctx, or_item[option], x_eq_prefix);
            strEqLengthAxiom(t, m, prefixAst, __LINE__);

            Z3_ast suffixAst = my_mk_str_value(t, suffix.c_str());
            Z3_ast y_eq_surfix = Z3_mk_eq(ctx, y, suffixAst);
            and_item[pos++] = Z3_mk_eq(ctx, or_item[option], y_eq_surfix);
            strEqLengthAxiom(t, y, suffixAst, __LINE__);

            option++;
        }

        if (!(m == y && str1Ast != str2Ast))
        {
            or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));

            Z3_ast str1_commonVar = mk_concat(t, str1Ast, commonVar);
            and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, m, str1_commonVar));
            strEqLengthAxiom(t, m, str1_commonVar, __LINE__);

            Z3_ast commonVar_str2 = mk_concat(t, commonVar, str2Ast);
            and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, commonVar_str2));
            strEqLengthAxiom(t, y, commonVar_str2, __LINE__);

            option++;
        }
        and_item[0] = Z3_mk_or(ctx, option, or_item);
        Z3_ast implyR = Z3_mk_and(ctx, pos, and_item);
        addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
        delete or_item;
        delete and_item;
        return 1;
    }
    return axiomAdded;
}

/*
 * Process two nodes that are assumed to be equal by Z3
 */
void handleNodesEqual(Z3_theory t, Z3_ast v1, Z3_ast v2)
{
    if (v1 == v2)
        return;

    bool v1IsConcat = isConcatFunc(t, v1);
    bool v2IsConcat = isConcatFunc(t, v2);
    T_myZ3Type v1_Type = getNodeType(t, v1);
    T_myZ3Type v2_Type = getNodeType(t, v2);
    //**********************************************************
    // Concat(... , ....) = Constant String
    //----------------------------------------------------------
    if (v1IsConcat && v2_Type == my_Z3_ConstStr)
    {
        solve_concat_eq_str(t, v1, v2);
    }

    else if (v2IsConcat && v1_Type == my_Z3_ConstStr)
    {
        solve_concat_eq_str(t, v2, v1);
    }
    //**********************************************************
    // Concat(... , ....) = Concat(... , ... )
    //----------------------------------------------------------
    else if (v1IsConcat && v2IsConcat)
    {
        simplifyConcatEq(t, v1, v2);
    }
}

/*
 *
 *
 */
void cb_new_eq(Z3_theory t, Z3_ast nn1, Z3_ast nn2)
{
    Z3_context ctx = Z3_theory_get_context(t);

#ifdef DEBUGLOG
    __debugPrint(logFile, "\n\n===============================================\n");
    __debugPrint(logFile, "** cb_new_eq():\n  ");
    printZ3Node(t, nn1);
    __debugPrint(logFile, " = ");
    printZ3Node(t, nn2);
    __debugPrint(logFile, "\n===============================================\n");
#endif

    //"str_eq --> length_eq" constraints
    strEqLengthAxiom(t, nn1, nn2, __LINE__);
    //==================================================
    // Should do equal check among eqc members of nn1 and nn2
    // to discover incorrect nn1 = nn2, e.g
    //--------------------------------------------------
    //** cb_new_eq() : y2 = _t_str3
    // * [EQC] : { y2, (Concat ce m2) }, size = 2
    // * [EQC] : { _t_str3, (Concat abc x2) }, size = 2
    //--------------------------------------------------
    // y2 can not be equal to _t_str3.
    // Add an assertion: {y2 = (Concat ce m2)} /\ {_t_str3 = (Concat abc x2)} --> y2 != _t_str3
    //==================================================
    Z3_ast eqc_nn1 = nn1;
    do
    {
        Z3_ast eqc_nn2 = nn2;
        do
        {
            // if we can find any conflict, we can return and let the core backtrack
            if (canTwoNodesEq(t, eqc_nn1, eqc_nn2) == false)
            {
                Z3_ast l_item[3];
                int l_pos = 0;
                if (nn1 != eqc_nn1)
                    l_item[l_pos++] = Z3_mk_eq(ctx, nn1, eqc_nn1);
                if (nn2 != eqc_nn2)
                    l_item[l_pos++] = Z3_mk_eq(ctx, nn2, eqc_nn2);
                Z3_ast toAssert = NULL;
                Z3_ast implyR = Z3_mk_not(ctx, Z3_mk_eq(ctx, nn1, nn2));
                if (l_pos == 0)
                {
                    toAssert = implyR;
                }
                else if (l_pos == 1)
                {
                    toAssert = Z3_mk_implies(ctx, l_item[0], implyR);
                }
                else
                {
                    Z3_ast implyL = Z3_mk_and(ctx, l_pos, l_item);
                    toAssert = Z3_mk_implies(ctx, implyL, implyR);
                }

                __debugPrint(logFile, "\n\n>>> Conflicting in *cb_new_eq*:");
                addAxiom(t, toAssert, __LINE__);
                __debugPrint(logFile, "\n");
                return;
            }
            else
            {
                handleNodesEqual(t, eqc_nn1, eqc_nn2);
            }
            eqc_nn2 = Z3_theory_get_eqc_next(t, eqc_nn2);
        } while (eqc_nn2 != nn2);
        eqc_nn1 = Z3_theory_get_eqc_next(t, eqc_nn1);
    } while (eqc_nn1 != nn1);

    //----------------------------------------------
    // A possible new_eq order:
    //   (1) v1 = "const": use "const" to simplify nodes having v1
    //   (2) v2 = v1:
    //       If we only check whether v1 or v2 is constant, we will miss the chance to
    //       simplify nodes with v2 since eqc(v1)="const"
    // Therefore, let's look at the eqc value of nn1 and nn2.
    //----------------------------------------------
    Z3_ast nn1_value = get_eqc_value(t, nn1);
    if (getNodeType(t, nn1_value) == my_Z3_ConstStr && getNodeType(t, nn2) != my_Z3_ConstStr)
    {
#ifdef DEBUGLOG
        __debugPrint(logFile, " >> EQC(nn1) = ");
        printZ3Node(t, nn1_value);
        __debugPrint(logFile, ", use it to simplify nn2\n");
#endif
        simplifyStrWithEqConstStr(t, nn2, nn1_value);
    }
    Z3_ast nn2_value = get_eqc_value(t, nn2);
    if (getNodeType(t, nn2_value) == my_Z3_ConstStr && getNodeType(t, nn1) != my_Z3_ConstStr)
    {
#ifdef DEBUGLOG
        __debugPrint(logFile, " >> EQC(nn2) = ");
        printZ3Node(t, nn2_value);
        __debugPrint(logFile, ", use it to simplify nn1\n");
#endif
        simplifyStrWithEqConstStr(t, nn1, nn2_value);
    }
}

/*
 * Add axioms that are true for any string var
 */
void basicStrVarAxiom(Z3_theory t, Z3_ast vNode, int line)
{
    if (basicStrVarAxiom_added.find(vNode) == basicStrVarAxiom_added.end())
    {
        Z3_context ctx = Z3_theory_get_context(t);
        Z3_ast lenTerm = mk_length(t, vNode);
        Z3_ast strlen_ge = Z3_mk_ge(ctx, lenTerm, mk_int(ctx, 0));
        addAxiom(t, strlen_ge, line, false);

        Z3_ast strLen_zero = Z3_mk_eq(ctx, lenTerm, mk_int(ctx, 0));
        Z3_ast str_empty = Z3_mk_eq(ctx, vNode, my_mk_str_value(t, ""));
        Z3_ast str_eq_ast2 = Z3_mk_eq(ctx, strLen_zero, str_empty);
        addAxiom(t, str_eq_ast2, line, false);

        basicStrVarAxiom_added[vNode] = 1;
#ifdef DEBUGLOG
        __debugPrint(logFile, "[strVar_Length Add] ");
        printZ3Node(t, vNode);
        __debugPrint(logFile, " @ %d\n", line);
#endif
    }
}

/*
 * Add axioms that are true for any string var
 */
void basicConcatAxiom(Z3_theory t, Z3_ast vNode, int line)
{
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast lenAst = mk_length(t, vNode);
    std::list<Z3_ast> astList;
    getconstStrAstsInNode(t, vNode, astList);
    int len = 0;
    std::list<Z3_ast>::iterator itor = astList.begin();
    for (; itor != astList.end(); itor++)
        len += getConstStrValue(t, (*itor)).length();

    if (len != 0)
        addAxiom(t, Z3_mk_ge(ctx, lenAst, mk_int(ctx, len)), __LINE__, false);
}

/*
 * Mark variable appeared in map "varAppearMap"
 */
void classifyAstByType(Z3_theory t, Z3_ast node, std::map<Z3_ast, int> & varMap, std::map<Z3_ast, int> & concatMap)
{
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    Z3_context ctx = Z3_theory_get_context(t);
    T_myZ3Type nodeType = getNodeType(t, node);

    if (nodeType == my_Z3_Str_Var)
    {
        varMap[node] = 1;
    }
    else if (getNodeType(t, node) == my_Z3_Func)
    {
        Z3_app func_app = Z3_to_app(ctx, node);
        Z3_func_decl funcDecl = Z3_get_app_decl(ctx, func_app);

        // ignore  AST in NOT (...)
        if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, func_app)) == Z3_OP_NOT)
            return;

        if (funcDecl == td->Concat)
        {
            if (concatMap.find(node) == concatMap.end())
                concatMap[node] = 1;
        }

        int argCount = Z3_get_app_num_args(ctx, func_app);
        for (int i = 0; i < argCount; i++)
        {
            Z3_ast argAst = Z3_get_app_arg(ctx, func_app, i);
            classifyAstByType(t, argAst, varMap, concatMap);
        }
    }
}

/*
 *
 */
inline Z3_ast getAliasIndexAst(std::map<Z3_ast, Z3_ast> & aliasIndexMap, Z3_ast node)
{
    if (aliasIndexMap.find(node) != aliasIndexMap.end())
        return aliasIndexMap[node];
    else
        return node;
}

/*
 *
 */
Z3_ast getMostLeftNodeInConcat(Z3_theory t, Z3_ast node)
{
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    Z3_context ctx = Z3_theory_get_context(t);

    if (getNodeType(t, node) != my_Z3_Func
            || (getNodeType(t, node) == my_Z3_Func && Z3_get_app_decl(ctx, Z3_to_app(ctx, node)) != td->Concat))
        return node;
    else
    {
        Z3_ast concatArgL = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 0);
        return getMostLeftNodeInConcat(t, concatArgL);
    }
}

/*
 *
 */
Z3_ast getMostRightNodeInConcat(Z3_theory t, Z3_ast node)
{
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    Z3_context ctx = Z3_theory_get_context(t);

    if (getNodeType(t, node) != my_Z3_Func
            || (getNodeType(t, node) == my_Z3_Func && Z3_get_app_decl(ctx, Z3_to_app(ctx, node)) != td->Concat))
        return node;
    else
    {
        Z3_ast concatArgR = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 1);
        return getMostRightNodeInConcat(t, concatArgR);
    }
}

/*
 * Dependence analysis from current context assignment
 */
int ctxDepAnalysis(Z3_theory t, std::map<Z3_ast, int> & strVarMap, std::map<Z3_ast, int> & concatMap,
        std::map<Z3_ast, Z3_ast> & aliasIndexMap, std::map<Z3_ast, Z3_ast> & var_eq_constStr_map,
        std::map<Z3_ast, std::map<Z3_ast, int> > & var_eq_concat_map, std::map<Z3_ast, Z3_ast> & concat_eq_constStr_map,
        std::map<Z3_ast, std::map<Z3_ast, int> > & concat_eq_concat_map, std::map<Z3_ast, int> & freeVarMap,
        std::map<Z3_ast, std::map<Z3_ast, int> > & depMap)
{
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast ctxAssign = Z3_get_context_assignment(ctx);

#ifdef DEBUGLOG
    __debugPrint(logFile, "\n******************************************\n");
    __debugPrint(logFile, "       Dependence Analysis\n");
    __debugPrint(logFile, "------------------------------------------\n");
#endif

    //--------------------------------------------
    // Step 1. get variables/Concat AST appeared in context
    classifyAstByType(t, ctxAssign, strVarMap, concatMap);

    //--------------------------------------------
    // Step 2. Collect alias relation
    // e.g EQC={x, y, z}
    //     aliasIndexMap[y] = x
    //     aliasIndexMap[z] = x
    std::map<Z3_ast, int>::iterator varItor = strVarMap.begin();
    for (; varItor != strVarMap.end(); varItor++)
    {
        if (aliasIndexMap.find(varItor->first) != aliasIndexMap.end())
            continue;

        Z3_ast aRoot = NULL;
        Z3_ast curr = varItor->first;
        do
        {
            if (getNodeType(t, curr) == my_Z3_Str_Var)
            {
                if (aRoot == NULL)
                    aRoot = curr;
                else
                    aliasIndexMap[curr] = aRoot;
            }
            curr = Z3_theory_get_eqc_next(t, curr);
        } while (curr != varItor->first);
    }

    //--------------------------------------------
    // Step 3: Collect interested cases
    varItor = strVarMap.begin();
    for (; varItor != strVarMap.end(); varItor++)
    {
        Z3_ast deAliasNode = getAliasIndexAst(aliasIndexMap, varItor->first);
        // (1) var_eq_constStr
        //     e.g,  z = "str1"
        //           var_eq_constStr_map[z] = "str1"
        //--------------------------------------------------------------
        if (var_eq_constStr_map.find(deAliasNode) == var_eq_constStr_map.end())
        {
            Z3_ast nodeValue = get_eqc_value(t, deAliasNode);
            if (deAliasNode != nodeValue)
                var_eq_constStr_map[deAliasNode] = nodeValue;
        }
        // (2) var_eq_concat       : e.g,  z = concat("str1", b) z = concat(c, "str2")
        //-----------------------------------------------------------------
        if (var_eq_concat_map.find(deAliasNode) == var_eq_concat_map.end())
        {
            Z3_ast curr = Z3_theory_get_eqc_next(t, deAliasNode);
            while (curr != deAliasNode)
            {
                if (isConcatFunc(t, curr))
                {
                    Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, curr), 0);
                    Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, curr), 1);
                    Z3_ast arg0_value = get_eqc_value(t, arg0);
                    Z3_ast arg1_value = get_eqc_value(t, arg1);
                    T_myZ3Type arg0_vType = getNodeType(t, arg0_value);
                    T_myZ3Type arg1_vType = getNodeType(t, arg1_value);
                    bool is_arg0_emptyStr = (arg0_vType == my_Z3_ConstStr) && (getConstStrValue(t, arg0_value) == "");
                    bool is_arg1_emptyStr = (arg1_vType == my_Z3_ConstStr) && (getConstStrValue(t, arg1_value) == "");
                    if (!is_arg0_emptyStr && !is_arg1_emptyStr)
                    {
                        var_eq_concat_map[deAliasNode][curr] = 1;
                    }
                }
                curr = Z3_theory_get_eqc_next(t, curr);
            }
        }
    }

    std::map<Z3_ast, Z3_ast> concats_eq_Index_map;
    std::map<Z3_ast, int>::iterator concatItor = concatMap.begin();
    for (; concatItor != concatMap.end(); concatItor++)
    {
        if (concats_eq_Index_map.find(concatItor->first) != concats_eq_Index_map.end())
            continue;

        Z3_ast aRoot = NULL;
        Z3_ast curr = concatItor->first;
        do
        {
            if (isConcatFunc(t, curr))
            {
                if (aRoot == NULL)
                    aRoot = curr;
                else
                    concats_eq_Index_map[curr] = aRoot;
            }
            curr = Z3_theory_get_eqc_next(t, curr);
        } while (curr != concatItor->first);
    }

    concatItor = concatMap.begin();
    for (; concatItor != concatMap.end(); concatItor++)
    {
        Z3_ast deAliasConcat = NULL;
        if (concats_eq_Index_map.find(concatItor->first) != concats_eq_Index_map.end())
            deAliasConcat = concats_eq_Index_map[concatItor->first];
        else
            deAliasConcat = concatItor->first;

        // (3) concat_eq_constStr:
        //     e.g,  concat(a,b) = "str1"
        if (concat_eq_constStr_map.find(deAliasConcat) == concat_eq_constStr_map.end())
        {
            Z3_ast nodeValue = get_eqc_value(t, deAliasConcat);
            if (deAliasConcat != nodeValue)
                concat_eq_constStr_map[deAliasConcat] = nodeValue;
        }

        // (4) concat_eq_concat:
        //     e.g,  concat(a,b) = concat("str1", c) /\ z = concat(a, b) /\ z = concat(e, f)
        if (concat_eq_concat_map.find(deAliasConcat) == concat_eq_concat_map.end())
        {
            Z3_ast curr = deAliasConcat;
            do
            {
                if (isConcatFunc(t, curr))
                    concat_eq_concat_map[deAliasConcat][curr] = 1;
                curr = Z3_theory_get_eqc_next(t, curr);
            } while (curr != deAliasConcat);
        }
    }

#ifdef DEBUGLOG
    {
        __debugPrint(logFile, "(0) alias: variables\n");
        std::map<Z3_ast, std::map<Z3_ast, int> > aliasSumMap;

        std::map<Z3_ast, Z3_ast>::iterator itor0 = aliasIndexMap.begin();
        for (; itor0 != aliasIndexMap.end(); itor0++)
        aliasSumMap[itor0->second][itor0->first] = 1;

        std::map<Z3_ast, std::map<Z3_ast, int> >::iterator keyItor = aliasSumMap.begin();
        for (; keyItor != aliasSumMap.end(); keyItor++)
        {
            __debugPrint(logFile, "  * ");
            printZ3Node(t, keyItor->first);
            __debugPrint(logFile, "\t: ");
            std::map<Z3_ast, int>::iterator innerItor = keyItor->second.begin();
            for(; innerItor!=keyItor->second.end(); innerItor++)
            {
                printZ3Node(t, innerItor->first);
                __debugPrint(logFile, ", ");
            }
            __debugPrint(logFile, "\n");
        }
        __debugPrint(logFile, "\n");
    }

    {
        __debugPrint(logFile, "(1) var = constStr:\n");
        std::map<Z3_ast, Z3_ast>::iterator itor1 = var_eq_constStr_map.begin();
        for (; itor1 != var_eq_constStr_map.end(); itor1++)
        {
            __debugPrint(logFile, "  ");
            printZ3Node(t, itor1->first);
            __debugPrint(logFile, " = ");
            printZ3Node(t, itor1->second);
            if (!areTwoNodesInSameEqc(t, itor1->first, itor1->second))
            __debugPrint(logFile, "  (notTrue in ctx)");
            __debugPrint(logFile, "\n");
        }
        __debugPrint(logFile, "\n");
    }

    {
        __debugPrint(logFile, "(2) var = concat:\n");
        std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor2 = var_eq_concat_map.begin();
        for (; itor2 != var_eq_concat_map.end(); itor2++)
        {
            __debugPrint(logFile, "  ");
            printZ3Node(t, itor2->first);
            __debugPrint(logFile, " = { ");
            std::map<Z3_ast, int>::iterator i_itor = itor2->second.begin();
            for(; i_itor != itor2->second.end(); i_itor++)
            {
                printZ3Node(t, i_itor->first);
                __debugPrint(logFile, ", ");
            }
            __debugPrint(logFile, "}\n");
        }
        __debugPrint(logFile, "\n");
    }

    {
        __debugPrint(logFile, "(3) concat = constStr:\n");
        std::map<Z3_ast, Z3_ast>::iterator itor3 = concat_eq_constStr_map.begin();
        for (; itor3 != concat_eq_constStr_map.end(); itor3++)
        {
            __debugPrint(logFile, "  ");
            printZ3Node(t, itor3->first);
            __debugPrint(logFile, " = ");
            printZ3Node(t, itor3->second);
            __debugPrint(logFile, "\n");

        }
        __debugPrint(logFile, "\n");
    }

    {
        __debugPrint(logFile, "(4) eq concats:\n");
        std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor4 = concat_eq_concat_map.begin();
        for (; itor4 != concat_eq_concat_map.end(); itor4++)
        {
            if (itor4->second.size() > 1)
            {
                std::map<Z3_ast, int>::iterator i_itor = itor4->second.begin();
                __debugPrint(logFile, "  >> ");
                for (; i_itor != itor4->second.end(); i_itor++)
                {
                    printZ3Node(t, i_itor->first);
                    __debugPrint(logFile, " , ");
                }
                __debugPrint(logFile, "\n");
            }
        }
    }

#endif

    //*****************************
    // Step 4. Dependence analysis
    //---------------------
    // (1) var = constStr
    for (std::map<Z3_ast, Z3_ast>::iterator itor = var_eq_constStr_map.begin(); itor != var_eq_constStr_map.end();
            itor++)
    {
        Z3_ast var = getAliasIndexAst(aliasIndexMap, itor->first);
        Z3_ast strAst = itor->second;
        depMap[var][strAst] = 1;
    }

    // (2) var = concat
    for (std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor = var_eq_concat_map.begin();
            itor != var_eq_concat_map.end(); itor++)
    {
        Z3_ast var = getAliasIndexAst(aliasIndexMap, itor->first);
        for (std::map<Z3_ast, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++)
        {
            Z3_ast concat = itor1->first;
            std::map<Z3_ast, int> inVarMap;
            std::map<Z3_ast, int> inConcatMap;
            classifyAstByType(t, concat, inVarMap, inConcatMap);
            for (std::map<Z3_ast, int>::iterator itor2 = inVarMap.begin(); itor2 != inVarMap.end(); itor2++)
            {
                Z3_ast varInConcat = getAliasIndexAst(aliasIndexMap, itor2->first);
                if (!(depMap[var].find(varInConcat) != depMap[var].end() && depMap[var][varInConcat] == 1))
                    depMap[var][varInConcat] = 2;
            }
        }
    }

    //(3) concat = constStr
    for (std::map<Z3_ast, Z3_ast>::iterator itor = concat_eq_constStr_map.begin(); itor != concat_eq_constStr_map.end();
            itor++)
    {
        Z3_ast concatAst = itor->first;
        Z3_ast constStr = itor->second;
        std::map<Z3_ast, int> inVarMap;
        std::map<Z3_ast, int> inConcatMap;
        classifyAstByType(t, concatAst, inVarMap, inConcatMap);
        for (std::map<Z3_ast, int>::iterator itor2 = inVarMap.begin(); itor2 != inVarMap.end(); itor2++)
        {
            Z3_ast varInConcat = getAliasIndexAst(aliasIndexMap, itor2->first);
            if (!(depMap[varInConcat].find(constStr) != depMap[varInConcat].end() && depMap[varInConcat][constStr] == 1))
                depMap[varInConcat][constStr] = 3;
        }
    }

    // (4) equivlent concats
    //     - possiblity 1 : concat("str", v1) = concat(concat(v2, v3), v4) = concat(v5, v6)
    //         ==> v2, v5 are constrainted by "str"
    //     - possiblity 2 : concat(v1, "str") = concat(v2, v3) = concat(v4, v5)
    //         ==> v2, v4 are constrainted by "str"
    for (std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor = concat_eq_concat_map.begin();
            itor != concat_eq_concat_map.end(); itor++)
    {
        std::map<Z3_ast, int> mostLeftNodes;
        std::map<Z3_ast, int> mostRightNodes;
        Z3_ast mostLeftConstrAst = NULL;
        Z3_ast mostRightConstrAst = NULL;
        for (std::map<Z3_ast, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++)
        {
            Z3_ast concatNode = itor1->first;
            Z3_ast concatNodeMostLeft = getMostLeftNodeInConcat(t, concatNode);
            if (getNodeType(t, concatNodeMostLeft) == my_Z3_ConstStr)
            {
                if (mostLeftConstrAst == NULL && getConstStrValue(t, concatNodeMostLeft) != "")
                {
                    mostLeftConstrAst = concatNodeMostLeft;
                }
            }
            else
            {
                mostLeftNodes[concatNodeMostLeft] = 1;
            }

            Z3_ast concatNodeMostRight = getMostRightNodeInConcat(t, concatNode);
            if (getNodeType(t, concatNodeMostRight) == my_Z3_ConstStr && getConstStrValue(t, concatNodeMostRight) != "")
            {
                if (mostRightConstrAst == NULL)
                {
                    mostRightConstrAst = concatNodeMostRight;
                }
            }
            else
            {
                mostRightNodes[concatNodeMostRight] = 1;
            }
        }

        if (mostLeftConstrAst != NULL)
        {
            for (std::map<Z3_ast, int>::iterator itor1 = mostLeftNodes.begin(); itor1 != mostLeftNodes.end(); itor1++)
            {
                Z3_ast deVar = getAliasIndexAst(aliasIndexMap, itor1->first);
                if (!(depMap[deVar].find(mostLeftConstrAst) != depMap[deVar].end()
                        && depMap[deVar][mostLeftConstrAst] == 1))
                    depMap[deVar][mostLeftConstrAst] = 4;
            }
        }

        if (mostRightConstrAst != NULL)
        {
            for (std::map<Z3_ast, int>::iterator itor1 = mostRightNodes.begin(); itor1 != mostRightNodes.end(); itor1++)
            {
                Z3_ast deVar = getAliasIndexAst(aliasIndexMap, itor1->first);
                if (!(depMap[deVar].find(mostRightConstrAst) != depMap[deVar].end()
                        && depMap[deVar][mostRightConstrAst] == 1))
                    depMap[deVar][mostRightConstrAst] = 5;
            }
        }
    }

#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> Dependence Map:\n");
    for (std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor = depMap.begin();
            itor != depMap.end(); itor++)
    {
        printZ3Node(t, itor->first);
        __debugPrint(logFile, "\t-->\t");
        for (std::map<Z3_ast, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end();
                itor1++)
        {
            printZ3Node(t, itor1->first);
            __debugPrint(logFile, "(%d), ", itor1->second);
        }
        __debugPrint(logFile, "\n");
    }

    // print out variable appeared
    {
        std::map<Z3_ast, int> varPrinted;
        __debugPrint(logFile, "\n>> Variable appear\n");
        for (std::map<Z3_ast, int>::iterator itor = strVarMap.begin(); itor != strVarMap.end(); itor++)
        {
            Z3_ast aliasedVar = getAliasIndexAst(aliasIndexMap, itor->first);
            if (varPrinted.find(aliasedVar) == varPrinted.end() )
            {
                printZ3Node(t, itor->first);
                Z3_ast vNode = get_eqc_value(t, itor->first);
                if (itor->first != vNode)
                {
                    __debugPrint(logFile, " (");
                    printZ3Node(t, vNode);
                    __debugPrint(logFile, ")");
                }
                __debugPrint(logFile, "\t");
                print_eq_class(t, itor->first);
                __debugPrint(logFile, "\n");
                varPrinted[aliasedVar] = 1;
            }
        }
    }
#endif

    //****************
    // Step 6. Compute free variables based on dependence map.
    // the case dependence map is empty, every var in VarMap is free
    if (depMap.size() == 0)
    {
        std::map<Z3_ast, int>::iterator itor = strVarMap.begin();
        for (; itor != strVarMap.end(); itor++)
        {
            Z3_ast var = getAliasIndexAst(aliasIndexMap, itor->first);
            freeVarMap[var] = 1;
        }
    }
    else
    {
        // if the keys in aliasIndexMap are not contained in keys in depMap, they are free
        // e.g.,  x= y /\ x = z /\ t = "abc"
        //        aliasIndexMap[y]= x, aliasIndexMap[z] = x
        //        depMap        t ~ "abc"(1)
        //        x should be free
        std::map<Z3_ast, int>::iterator itor2 = strVarMap.begin();
        for (; itor2 != strVarMap.end(); itor2++)
        {
            if (aliasIndexMap.find(itor2->first) != aliasIndexMap.end())
            {
                Z3_ast var = aliasIndexMap[itor2->first];
                if (depMap.find(var) == depMap.end())
                    freeVarMap[var] = 1;
            }
            else if (aliasIndexMap.find(itor2->first) == aliasIndexMap.end())
            {
                // if a variable is not in aliasIndexMap and not in depMap, it's free
                if (depMap.find(itor2->first) == depMap.end())
                    freeVarMap[itor2->first] = 1;
            }
        }

        std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor = depMap.begin();
        for (; itor != depMap.end(); itor++)
        {
            for (std::map<Z3_ast, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++)
            {
                if (getNodeType(t, itor1->first) == my_Z3_Str_Var)
                {
                    Z3_ast var = getAliasIndexAst(aliasIndexMap, itor1->first);
                    // if a var is dep on itself and all dependence are type 2, it's a free variable
                    // e.g {y --> x(2), y(2), m --> m(2), n(2)} y,m are free
                    {
                        if (depMap.find(var) == depMap.end())
                        {
                            if (freeVarMap.find(var) == freeVarMap.end())
                                freeVarMap[var] = 1;
                            else
                                freeVarMap[var] = freeVarMap[var] + 1;
                        }
                    }
                }
            }
        }
    }
    return 0;
}


/*
 *
 *
 */
void selectAstForFreeVar(Z3_theory t, Z3_ast node, std::list<Z3_ast> & nodeList)
{
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    Z3_context ctx = Z3_theory_get_context(t);
    if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, node))) == Z3_OP_EQ)
    {
        Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 0);
        if (Z3_get_sort(ctx, arg0) == td->String)
        {
            nodeList.push_back(node);
            return;
        }
    }
}

/*
 * When add an axiom for a free var, return the left side of that axiom
 * It should be a part of current context to indicate "From this part of context, this var is free"
 */
Z3_ast getConditionForFreeVar(Z3_theory t)
{

    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast ctxAssign = Z3_get_context_assignment(ctx);
    std::list<Z3_ast> nodeList;
    if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, ctxAssign))) != Z3_OP_AND)
    {
        selectAstForFreeVar(t, ctxAssign, nodeList);
    }
    else
    {
        int argCount = Z3_get_app_num_args(ctx, Z3_to_app(ctx, ctxAssign));
        for (int i = 0; i < argCount; i++)
        {
            Z3_ast itemAssign = Z3_get_app_arg(ctx, Z3_to_app(ctx, ctxAssign), i);
            selectAstForFreeVar(t, itemAssign, nodeList);
        }
    }

    Z3_ast result = NULL;
    int pos = 0;
    Z3_ast * items = new Z3_ast[nodeList.size()];
    for (std::list<Z3_ast>::iterator itor = nodeList.begin(); itor != nodeList.end(); itor++)
    {
        items[pos++] = *itor;
    }
    if (pos == 0)
        result = NULL;
    else if (pos == 1)
        result = items[0];
    else
        result = Z3_mk_and(ctx, pos, items);
    delete[] items;
    return result;
}

/*
 *
 */
Z3_bool cb_final_check(Z3_theory t)
{
    Z3_context ctx = Z3_theory_get_context(t);

#ifdef DEBUGLOG
    __debugPrint(logFile, "\n\n\n");
    __debugPrint(logFile, "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv\n");
    __debugPrint(logFile, "                cb_final_check @ Level [%d] \n", sLevel);
    __debugPrint(logFile, "=============================================================\n");

//    __debugPrint(logFile, "\n* Ctx Assignment:\n-----------------------------\n");
//    Z3_ast ctxAssign = Z3_get_context_assignment(ctx);
//    printZ3Node(t, ctxAssign);
//    __debugPrint(logFile, "\n-----------------------------\n\n");
#endif

    //----------------------------------------------------------------------------------
    //run dependence analysis, find free string vars
    std::map<Z3_ast, int> varAppearInAssign;
    std::map<Z3_ast, int> concatMap;
    std::map<Z3_ast, Z3_ast> aliasIndexMap;
    std::map<Z3_ast, Z3_ast> var_eq_constStr_map;
    std::map<Z3_ast, Z3_ast> concatAstEqConst_map;
    std::map<Z3_ast, std::map<Z3_ast, int> > var_eq_concat_map;
    std::map<Z3_ast, Z3_ast> concat_eq_constStr_map;
    std::map<Z3_ast, std::map<Z3_ast, int> > concat_eq_concat_map;
    std::map<Z3_ast, std::map<Z3_ast, int> > depMap;
    std::map<Z3_ast, int> freeVar_map;

    int conflictInDep = ctxDepAnalysis(t, varAppearInAssign, concatMap, aliasIndexMap, var_eq_constStr_map,
            var_eq_concat_map, concat_eq_constStr_map, concat_eq_concat_map, freeVar_map, depMap);

    if (conflictInDep == -1)
    {
        __debugPrint(logFile, "\n\n###########################################################\n\n");
        return Z3_TRUE;
    }

    //**************************************************************
    // double check depdence map for unbroken deps, e.g
    //    * (Concat ef y2) , ..., (Concat _t_str2 abc)
    //      [1]  y2  --> "abc"(5),
    //      [2]  _t_str2 --> "ef"(4),
    //**************************************************************
    Z3_ast nodeToSplitRoot = NULL;
    std::map<Z3_ast, std::map<Z3_ast, int> >::iterator depListItor = depMap.begin();
    for (; depListItor != depMap.end(); depListItor++)
    {
        Z3_ast depRoot = depListItor->first;
        int unbroken = 1;
        std::map<Z3_ast, int>::iterator itor = depListItor->second.begin();
        for (; itor != depListItor->second.end(); itor++)
        {
            int depType = itor->second;
            if (depType != 4 && depType != 5)
            {
                unbroken = 0;
                break;
            }
        }
        if (unbroken == 1)
        {
            nodeToSplitRoot = depRoot;
            break;
        }
    }

    if (nodeToSplitRoot != NULL)
    {
        Z3_ast nodeDepOn = depMap[nodeToSplitRoot].begin()->first;
        int depType = depMap[nodeToSplitRoot].begin()->second;

#ifdef DEBUGLOG
        __debugPrint(logFile, "\n************************************************\n");
        __debugPrint(logFile, "Further split needed for: ");
        printZ3Node(t, nodeToSplitRoot);
        __debugPrint(logFile, " with ");
        printZ3Node(t, nodeDepOn);
        __debugPrint(logFile, ", [depType = %d]\n************************************************\n",depType);
#endif

        Z3_ast toBreak1 = NULL;
        int toBreak1VarCount = -1;
        Z3_ast toBreak2 = NULL;
        int toBreak2VarCount = -1;

        // find the simplest two nodes to break
        std::map<Z3_ast, std::map<Z3_ast, int> >::iterator setItor = concat_eq_concat_map.begin();
        for (; setItor != concat_eq_concat_map.end(); setItor++)
        {
            Z3_ast toBreak1_Candidate = NULL;
            int toBreak1_Candidate_VarCount = -1;
            Z3_ast toBreak2_Candidate = NULL;
            int toBreak2_Candidate_VarCount = -1;

            std::map<Z3_ast, int>::iterator concatItor = setItor->second.begin();
            for (; concatItor != setItor->second.end(); concatItor++)
            {
                Z3_ast concatNode = concatItor->first;
                Z3_ast sideNode = NULL;

                if (depType == 4)
                    sideNode = getMostLeftNodeInConcat(t, concatNode);
                else
                    sideNode = getMostRightNodeInConcat(t, concatNode);
                int varCount = getVarCountInAst(t, concatNode);

                if (sideNode == nodeToSplitRoot)
                {
                    if (toBreak1_Candidate_VarCount == -1)
                    {
                        toBreak1_Candidate = concatNode;
                        toBreak1_Candidate_VarCount = varCount;
                    }
                    else if (toBreak1_Candidate_VarCount > varCount)
                    {
                        toBreak1_Candidate = concatNode;
                        toBreak1_Candidate_VarCount = varCount;
                    }
                }

                if (sideNode == nodeDepOn)
                {
                    if (toBreak2_Candidate_VarCount == -1)
                    {
                        toBreak2_Candidate = concatNode;
                        toBreak2_Candidate_VarCount = varCount;
                    }
                    else if (toBreak2_Candidate_VarCount > varCount)
                    {
                        toBreak2_Candidate = concatNode;
                        toBreak2_Candidate_VarCount = varCount;
                    }
                }
            }

            if (toBreak1_Candidate_VarCount != -1 && toBreak2_Candidate_VarCount != -1)
            {
                if (toBreak1VarCount == -1)
                {
                    toBreak1 = toBreak1_Candidate;
                    toBreak1VarCount = toBreak1_Candidate_VarCount;
                    toBreak2 = toBreak2_Candidate;
                    toBreak2VarCount = toBreak2_Candidate_VarCount;
                }
                else if ((toBreak1_Candidate_VarCount + toBreak2_Candidate_VarCount)
                        < (toBreak1VarCount + toBreak2VarCount))
                {
                    toBreak1 = toBreak1_Candidate;
                    toBreak1VarCount = toBreak1_Candidate_VarCount;
                    toBreak2 = toBreak2_Candidate;
                    toBreak2VarCount = toBreak2_Candidate_VarCount;
                }
            }
        }

        if (toBreak1 != NULL && toBreak2 != NULL)
        {
#ifdef DEBUGLOG
            __debugPrint(logFile, "* toBreak1: ");
            printZ3Node(t, toBreak1);
            __debugPrint(logFile, "\n* toBreak2: ");
            printZ3Node(t, toBreak2);
            __debugPrint(logFile, "\n");
#endif
            // disable duplicate check when reducing eq concat
            simplifyConcatEq(t, toBreak1, toBreak2, 0);
        }
#ifdef DEBUGLOG
        __debugPrint(logFile, "\n###########################################################\n\n");
#endif
        return Z3_TRUE;
    }

    //**************************************************************
    // Check whether variables appeared have eq string constants
    // If yes, all input variables are all assigned.
    //         we don't need to instantiate them as free var
    // If no, need to go ahead and assign free variables
    //**************************************************************
    int needToAssignFreeVar = 0;
    std::map<Z3_ast, int>::iterator itor = varAppearInAssign.begin();
    for (; itor != varAppearInAssign.end(); itor++)
    {
        std::string vName = std::string(Z3_ast_to_string(ctx, itor->first));
        if (vName.length() >= 3 && vName.substr(0, 3) == "_t_")
            continue;

        Z3_ast vNode = get_eqc_value(t, itor->first);
        if (itor->first == vNode)
        {
            needToAssignFreeVar = 1;
            break;
        }
    }
    if (needToAssignFreeVar == 0)
    {
        doubleCheckForNotContain(t);
        __debugPrint(logFile, "\n * All non-internal variables are assigned. Done!\n");
        __debugPrint(logFile, "###########################################################\n\n");
        return Z3_TRUE;
    }
    // Assign free variables
#ifdef DEBUGLOG
    {
        std::map<Z3_ast, int>::iterator freeVarItor1 = freeVar_map.begin();
        __debugPrint(logFile, "* Free Variables:\n----------------------------------\n");
        int varPrintedCount = 0;
        for (; freeVarItor1 != freeVar_map.end(); freeVarItor1++)
        {
            Z3_ast freeVar = freeVarItor1->first;
            printZ3Node(t, freeVar);
            __debugPrint(logFile, "(%d), ", freeVarItor1->second);
            varPrintedCount++;
            if (varPrintedCount % 5 == 0)
                __debugPrint(logFile, "\n");
        }
        __debugPrint(logFile, "\n----------------------------------\n");
    }
#endif

    std::map<Z3_ast, int>::iterator freeVarItor = freeVar_map.begin();
    Z3_ast freeVarAST_L = getConditionForFreeVar(t);
    for (; freeVarItor != freeVar_map.end(); freeVarItor++)
    {
        Z3_ast freeVar = freeVarItor->first;
        std::string vName = std::string(Z3_ast_to_string(ctx, freeVar));
        if (vName.length() >= 3 && vName.substr(0, 3) == "_t_" && freeVarItor->second == 1)
            continue;

        Z3_ast freeVarAST_R = axiomForFreeVar(t, freeVar);
        Z3_ast toAssert = freeVarAST_R;
        if (freeVarAST_L != NULL)
        {
            toAssert = Z3_mk_implies(ctx, freeVarAST_L, freeVarAST_R);
        }
        addAxiom(t, toAssert, __LINE__, false);
#ifdef DEBUGLOG
        __debugPrint(logFile, "\n---------------------\nAssign free var(@%d, Level %d):\n", __LINE__, sLevel);
        printZ3Node(t, freeVar);
        __debugPrint(logFile, "\n---------------------\n");
#endif
    }
    __debugPrint(logFile, "###########################################################\n\n");
    return Z3_TRUE;
}

/*
 *
 *
 */
void strReplaceAll(std::string & str, const std::string & from, const std::string & to)
{
    if (from.empty())
        return;
    size_t start_pos = 0;
    while ((start_pos = str.find(from, start_pos)) != std::string::npos)
    {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length(); // In case 'to' contains 'from', like replacing 'x' with 'yx'
    }
}

/****************************************
 *  Z3 input parser doesn't understand constant string
 *  So, we pass const string by adding a special mark "$",
 * --------------------------------------
 *
 ****************************************/
std::string convertInputTrickyConstStr(std::string inputStr)
{
    std::string outputStr = inputStr.substr(11, inputStr.length() - 11);
    strReplaceAll(outputStr, "_aScIi_040", " ");
    strReplaceAll(outputStr, "_aScIi_042", "\"");
    strReplaceAll(outputStr, "_aScIi_043", "#");
    strReplaceAll(outputStr, "_aScIi_044", "$");
    strReplaceAll(outputStr, "_aScIi_047", "'");
    strReplaceAll(outputStr, "_aScIi_050", "(");
    strReplaceAll(outputStr, "_aScIi_051", ")");
    strReplaceAll(outputStr, "_aScIi_054", ",");
    strReplaceAll(outputStr, "_aScIi_072", ":");
    strReplaceAll(outputStr, "_aScIi_073", ";");
    strReplaceAll(outputStr, "_aScIi_133", "[");
    strReplaceAll(outputStr, "_aScIi_135", "]");
    strReplaceAll(outputStr, "_aScIi_134", "\\");
    strReplaceAll(outputStr, "_aScIi_140", "`");
    strReplaceAll(outputStr, "_aScIi_173", "{");
    strReplaceAll(outputStr, "_aScIi_175", "}");
    strReplaceAll(outputStr, "_aScIi_174", "|");
    strReplaceAll(outputStr, "_aScIi_011", "\t");
    strReplaceAll(outputStr, "_aScIi_012", "\n");
    return outputStr;
}

/*
 *
 *
 */
Z3_bool cb_reduce_eq(Z3_theory t, Z3_ast s1, Z3_ast s2, Z3_ast * r)
{
    Z3_context ctx = Z3_theory_get_context(t);
    std::string s1_str = std::string(Z3_ast_to_string(ctx, s1));
    std::string s2_str = std::string(Z3_ast_to_string(ctx, s2));
    Z3_ast s1_new = s1;
    Z3_ast s2_new = s2;

    // Convert the tricky "string" representation to string constant
    if (s1_str.length() >= 11 && s1_str.substr(0, 11) == "__cOnStStR_")
        s1_new = my_mk_str_value(t, convertInputTrickyConstStr(s1_str).c_str());
    if (s2_str.length() >= 11 && s2_str.substr(0, 11) == "__cOnStStR_")
        s2_new = my_mk_str_value(t, convertInputTrickyConstStr(s2_str).c_str());

    if (s2_new != s2 || s1_new != s1)
    {
        *r = Z3_mk_eq(ctx, s1_new, s2_new);
#ifdef DEBUGLOG
        __debugPrint(logFile, "[convert_Str_Const] (= ");
        printZ3Node(t, s1);
        __debugPrint(logFile, " ");
        printZ3Node(t, s2);
        __debugPrint(logFile, ") => ");
        printZ3Node(t, *r);
        __debugPrint(logFile, "\n");
#endif
        return Z3_TRUE;
    }
    else
    {
        return Z3_FALSE;
    }
}

/*
 *
 */
void cb_init_search(Z3_theory t)
{
#ifdef DEBUGLOG
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast ctxAssign = Z3_get_context_assignment(ctx);
    __debugPrint(logFile, "\n\n");
    __debugPrint(logFile, "***********************************************\n");
    __debugPrint(logFile, "*               Starting Search               *\n");
    __debugPrint(logFile, "-----------------------------------------------\n");
    printZ3Node(t, ctxAssign);
    __debugPrint(logFile, "\n");
    __debugPrint(logFile, "***********************************************\n");
#endif
    searchStart = 1;
}

/*
 *
 */
Z3_ast reduce_subStr(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert)
{
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast ts0 = my_mk_internal_string_var(t);
    Z3_ast ts1 = my_mk_internal_string_var(t);
    Z3_ast ts2 = my_mk_internal_string_var(t);
    Z3_ast and_item[4];
    and_item[0] = Z3_mk_eq(ctx, args[0], mk_concat(t, ts0, mk_concat(t, ts1, ts2)));
    and_item[1] = Z3_mk_eq(ctx, args[1], mk_length(t, ts0));
    and_item[2] = Z3_mk_eq(ctx, args[2], mk_length(t, ts1));
    breakdownAssert = Z3_mk_and(ctx, 3, and_item);
    return ts1;
}

/*
 * -----------------------------------------------------
 *  Reduce contains to concat & length
 * -----------------------------------------------------
 */
void getBoolAssignmentFromCtx(Z3_theory t, std::map<Z3_ast, bool> & boolAssignMap)
{
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast ctxAssign = Z3_get_context_assignment(ctx);
    if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, ctxAssign))) != Z3_OP_AND)
    {
        if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, ctxAssign))) == Z3_OP_NOT)
        {
            Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, ctxAssign), 0);
            boolAssignMap[arg0] = false;
        }
        else
        {
            boolAssignMap[ctxAssign] = true;
        }
    }
    else
    {
        int argCount = Z3_get_app_num_args(ctx, Z3_to_app(ctx, ctxAssign));
        for (int i = 0; i < argCount; i++)
        {
            Z3_ast itemAssign = Z3_get_app_arg(ctx, Z3_to_app(ctx, ctxAssign), i);
            if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, itemAssign))) == Z3_OP_NOT)
            {
                Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, itemAssign), 0);
                boolAssignMap[arg0] = false;
            }
            else
            {
                boolAssignMap[itemAssign] = true;
            }
        }
    }
}

/*
 *
 *
 */
void doubleCheckForNotContain(Z3_theory t)
{
    if (containsReduced_bool_str_map.size() == 0)
    {
        return;
    }
    else
    {
        std::map<Z3_ast, bool> boolAssignMap;
        getBoolAssignmentFromCtx(t, boolAssignMap);

        std::map<Z3_ast, Z3_ast>::iterator strItor = containsReduced_bool_str_map.begin();
        for (; strItor != containsReduced_bool_str_map.end(); strItor++)
        {
            Z3_ast boolVar = strItor->first;
            Z3_ast strVar = strItor->second;
            Z3_ast subStrVar = containsReduced_bool_subStr_map[boolVar];
            bool boolVarValue = boolAssignMap[boolVar];
            if (!boolVarValue)
            {
#ifdef DEBUGLOG
                __debugPrint(logFile, " >> Bool var: { ");
                printZ3Node(t, boolVar);
                if ( boolVarValue )
                {
                    __debugPrint(logFile, " =  TRUE}. Check Contains( ");
                }
                else
                {
                    __debugPrint(logFile, " =  FALSE}. Check ! Contains( ");
                }
                printZ3Node(t, strVar);
                __debugPrint(logFile, ", ");
                printZ3Node(t, subStrVar);
                __debugPrint(logFile, ") for conflict...\n");
#endif
                Z3_ast strValue = get_eqc_value(t, strVar);
                Z3_ast substrValue = get_eqc_value(t, subStrVar);
                if (getNodeType(t, strValue) == my_Z3_ConstStr && getNodeType(t, substrValue) == my_Z3_ConstStr)
                {
                    std::string strConst = getConstStrValue(t, strValue);
                    std::string subStrConst = getConstStrValue(t, substrValue);

                    if (!boolVarValue)
                    {
                        if (strConst.find(subStrConst) != std::string::npos)
                        {
                            Z3_context ctx = Z3_theory_get_context(t);
                            int pos = 0;
                            Z3_ast l_set[2];
                            if (strValue != strVar)
                                l_set[pos++] = Z3_mk_eq(ctx, strVar, strValue);
                            if (subStrVar != substrValue)
                                l_set[pos++] = Z3_mk_eq(ctx, subStrVar, substrValue);

                            Z3_ast r_imply = boolVar;
                            Z3_ast toAssert = NULL;
                            if (pos == 0)
                            {
                                toAssert = r_imply;
                            }
                            else if (pos == 1)
                            {
                                toAssert = Z3_mk_implies(ctx, l_set[0], r_imply);
                            }
                            else
                            {
                                Z3_ast l_imply = Z3_mk_and(ctx, 2, l_set);
                                toAssert = Z3_mk_implies(ctx, l_imply, r_imply);
                            }
                            addAxiom(t, toAssert, __LINE__);
                        }
                    }
                }
            }
        }
    }
}

/*
 *
 *
 */
Z3_ast reduce_contains(Z3_theory t, Z3_ast const args[])
{
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast reduceAst = NULL;
    if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr)
    {
        std::string arg0Str = getConstStrValue(t, args[0]);
        std::string arg1Str = getConstStrValue(t, args[1]);
        if (arg0Str.find(arg1Str) != std::string::npos)
            reduceAst = Z3_mk_true(ctx);
        else
            reduceAst = Z3_mk_false(ctx);
    }
    else
    {
        Z3_ast ts0 = my_mk_internal_string_var(t);
        Z3_ast ts1 = my_mk_internal_string_var(t);
        reduceAst = Z3_mk_eq(ctx, args[0], mk_concat(t, ts0, mk_concat(t, args[1], ts1)));
        //--------------------------------------------------
        //* Current model can not rule out the possibility: {contains(x, "efg") /\ ! contains(x, "ef")}
        //* So, in final_check, double check such case.
        //* Remember reduced bool and str searched for, used to check whether args[0] contains args[1]
        //--------------------------------------------------
        containsReduced_bool_str_map[reduceAst] = args[0];
        containsReduced_bool_subStr_map[reduceAst] = args[1];
    }
    return reduceAst;
}

/*
 *
 *
 */
Z3_ast reduce_indexof(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert)
{
    Z3_context ctx = Z3_theory_get_context(t);
    if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr)
    {
        std::string arg0Str = getConstStrValue(t, args[0]);
        std::string arg1Str = getConstStrValue(t, args[1]);
        if (arg0Str.find(arg1Str) != std::string::npos)
        {
            int index = arg0Str.find(arg1Str);
            return mk_int(ctx, index);
        }
        else
        {
            return mk_int(ctx, -1);
        }
    }
    else
    {
        Z3_ast x1 = my_mk_internal_string_var(t);
        Z3_ast x2 = my_mk_internal_string_var(t);
        Z3_ast x3 = my_mk_internal_string_var(t);
        Z3_ast indexAst = my_mk_internal_int_var(t);

        int pos = 0;
        Z3_ast and_items[7];
        and_items[pos++] = Z3_mk_eq(ctx, args[0], mk_concat(t, x1, mk_concat(t, x2, x3)));
        Z3_ast i_minus_one = Z3_mk_eq(ctx, indexAst, mk_int(ctx, -1));
        Z3_ast i_ge_zero = Z3_mk_ge(ctx, indexAst, mk_int(ctx, 0));
        and_items[pos++] = Z3_mk_xor(ctx, i_minus_one, i_ge_zero);
        and_items[pos++] = Z3_mk_iff(ctx, i_minus_one, Z3_mk_not(ctx, mk_contains(t, args[0], args[1])));

        Z3_ast tmp_andItems[4];
        tmp_andItems[0] = Z3_mk_eq(ctx, indexAst, mk_length(t, x1));
        tmp_andItems[1] = Z3_mk_eq(ctx, x2, args[1]);
        tmp_andItems[2] = Z3_mk_not(ctx, mk_contains(t, x1, args[1]));

        and_items[pos++] = Z3_mk_iff(ctx, i_ge_zero, Z3_mk_and(ctx, 3, tmp_andItems));

        breakdownAssert = Z3_mk_and(ctx, pos, and_items);
        return indexAst;
    }
}

/*
 *
 */
Z3_ast reduce_replace(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert)
{
    Z3_context ctx = Z3_theory_get_context(t);
    if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr
            && getNodeType(t, args[2]) == my_Z3_ConstStr)
    {
        std::string arg0Str = getConstStrValue(t, args[0]);
        std::string arg1Str = getConstStrValue(t, args[1]);
        std::string arg2Str = getConstStrValue(t, args[2]);
        if (arg0Str.find(arg1Str) != std::string::npos)
        {
            int index1 = arg0Str.find(arg1Str);
            int index2 = index1 + arg1Str.length();
            std::string substr0 = arg0Str.substr(0, index1);
            std::string substr2 = arg0Str.substr(index2);
            std::string replaced = substr0 + arg2Str + substr2;
            return my_mk_str_value(t, replaced.c_str());
        }
        else
        {
            return args[0];
        }
    }
    else
    {
        Z3_ast x1 = my_mk_internal_string_var(t);
        Z3_ast x2 = my_mk_internal_string_var(t);
        Z3_ast x3 = my_mk_internal_string_var(t);
        Z3_ast indexAst = my_mk_internal_int_var(t);
        Z3_ast result = my_mk_internal_string_var(t);

        int pos = 0;
        Z3_ast and_items[8];

        and_items[pos++] = Z3_mk_eq(ctx, args[0], mk_concat(t, x1, mk_concat(t, x2, x3)));
        Z3_ast i_minus_one = Z3_mk_eq(ctx, indexAst, mk_int(ctx, -1));
        Z3_ast i_ge_zero = Z3_mk_ge(ctx, indexAst, mk_int(ctx, 0));
        and_items[pos++] = Z3_mk_xor(ctx, i_minus_one, i_ge_zero);
        //-------------------------------------------
        and_items[pos++] = Z3_mk_iff(ctx, i_minus_one, Z3_mk_not(ctx, mk_contains(t, args[0], args[1])));
        and_items[pos++] = Z3_mk_iff(ctx, i_minus_one, Z3_mk_eq(ctx, result, args[0]));
        //-------------------------------------------
        and_items[pos++] = Z3_mk_iff(ctx, i_ge_zero, Z3_mk_eq(ctx, indexAst, mk_length(t, x1)));
        and_items[pos++] = Z3_mk_iff(ctx, i_ge_zero, Z3_mk_eq(ctx, x2, args[1]));
        and_items[pos++] = Z3_mk_iff(ctx, i_ge_zero, Z3_mk_not(ctx, mk_contains(t, x1, args[1])));
        and_items[pos++] = Z3_mk_eq(ctx, result, mk_concat(t, x1, mk_concat(t, args[2], x3)));
        //-------------------------------------------
        breakdownAssert = Z3_mk_and(ctx, pos, and_items);
        return result;
    }
}

/*
 *
 *
 */
Z3_bool cb_reduce_app(Z3_theory t, Z3_func_decl d, unsigned n, Z3_ast const * args, Z3_ast * result)
{
    Z3_context ctx = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);

    // Convert the tricky "string" representation to string constant
    int convertedFlag = 0;
    Z3_ast * convertedArgs = new Z3_ast[n];
    for (int i = 0; i < (int) n; i++)
    {
        std::string symbolStr = std::string(Z3_ast_to_string(ctx, args[i]));
        if (symbolStr.length() >= 11 && symbolStr.substr(0, 11) == "__cOnStStR_")
        {
            convertedFlag = 1;
            convertedArgs[i] = my_mk_str_value(t, convertInputTrickyConstStr(symbolStr).c_str());
        }
        else
        {
            convertedArgs[i] = args[i];
        }
    }

    //---------------------------------
    // reduce app: Concat
    //---------------------------------
    if (d == td->Concat)
    {
        Z3_ast result_ast = Concat(t, convertedArgs[0], convertedArgs[1]);
        if (result_ast != 0)
        {
            *result = result_ast;
#ifdef DEBUGLOG
            __debugPrint(logFile, "\n** cb_reduce_app(): concat( ");
            printZ3Node(t, convertedArgs[0]);
            __debugPrint(logFile, " , ");
            printZ3Node(t, convertedArgs[1]);
            __debugPrint(logFile, " )\n");
#endif
            delete[] convertedArgs;
            return Z3_TRUE;
        }
        else
        {
            *result = mk_concat(t, convertedArgs[0], convertedArgs[1]);
            delete[] convertedArgs;
            return Z3_TRUE;
        }
    }
    //---------------------------------
    // reduce app: Length
    //---------------------------------
    if (d == td->Length)
    {
        if (getNodeType(t, convertedArgs[0]) == my_Z3_ConstStr)
        {
            int size = getConstStrValue(t, convertedArgs[0]).size();
            *result = mk_int(ctx, size);
#ifdef DEBUGLOG
            __debugPrint(logFile, "\n** cb_reduce_app(): Length( ");
            printZ3Node(t, convertedArgs[0]);
            __debugPrint(logFile, " ) = ");
            __debugPrint(logFile, "%d\n", size);
#endif
            delete[] convertedArgs;
            return Z3_TRUE;
        }
        else
        {
            if (convertedFlag == 1)
            {
                *result = mk_1_arg_app(ctx, d, convertedArgs[0]);
                delete[] convertedArgs;
                return Z3_TRUE;
            }
            else
            {
                delete[] convertedArgs;
                return Z3_FALSE;
            }
        }
    }

    //---------------------------------
    // reduce app: SubString
    //---------------------------------
    if (d == td->SubString)
    {
        Z3_ast breakDownAst = NULL;
        *result = reduce_subStr(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
        __debugPrint(logFile, "\n===================\n");
        __debugPrint(logFile, "** cb_reduce_app(): SubString(");
        printZ3Node(t, convertedArgs[0]);
        __debugPrint(logFile, ", ");
        printZ3Node(t, convertedArgs[1]);
        __debugPrint(logFile, ", ");
        printZ3Node(t, convertedArgs[2]);
        __debugPrint(logFile, ")  =>  ");
        printZ3Node(t, *result);
        __debugPrint(logFile, "\n-- ADD(@%d, Level %d):\n", __LINE__, sLevel);
        printZ3Node(t, breakDownAst);
        __debugPrint(logFile, "\n===================\n");
#endif
        Z3_assert_cnstr(ctx, breakDownAst);
        delete[] convertedArgs;
        return Z3_TRUE;
    }

    //------------------------------------------
    // Reduce app: Contains
    //------------------------------------------
    if (d == td->Contains)
    {
        *result = reduce_contains(t, convertedArgs);
#ifdef DEBUGLOG
        __debugPrint(logFile, "\n===================\n");
        __debugPrint(logFile, "** cb_reduce_app(): Contains( ");
        printZ3Node(t, convertedArgs[0]);
        __debugPrint(logFile, ", ");
        printZ3Node(t, convertedArgs[1]);
        __debugPrint(logFile, " )");
        __debugPrint(logFile, "  =>  ");
        printZ3Node(t, *result);
        __debugPrint(logFile, "\n===================\n");
#endif
        delete[] convertedArgs;
        return Z3_TRUE;
    }

    //------------------------------------------
    // Reduce app: Indexof
    //------------------------------------------
    if (d == td->Indexof)
    {
        Z3_ast breakDownAst = NULL;
        *result = reduce_indexof(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
        __debugPrint(logFile, "\n===================\n");
        __debugPrint(logFile, "** cb_reduce_app(): Indexof(");
        printZ3Node(t, convertedArgs[0]);
        __debugPrint(logFile, ", ");
        printZ3Node(t, convertedArgs[1]);
        __debugPrint(logFile, ")");
        __debugPrint(logFile, "  =>  ");
        printZ3Node(t, *result);
        if( breakDownAst != NULL )
        {
            __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
            printZ3Node(t, breakDownAst);
        }
        __debugPrint(logFile, "\n===================\n");
#endif
        // when quick path is taken, breakDownAst == NULL;
        if (breakDownAst != NULL)
            Z3_assert_cnstr(ctx, breakDownAst);
        delete[] convertedArgs;
        return Z3_TRUE;
    }

    //------------------------------------------
    // Reduce app: Replace
    //------------------------------------------
    if (d == td->Replace)
    {
        Z3_ast breakDownAst = NULL;
        *result = reduce_replace(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
        __debugPrint(logFile, "\n===================\n");
        __debugPrint(logFile, "** cb_reduce_app(): Replace(");
        printZ3Node(t, convertedArgs[0]);
        __debugPrint(logFile, ", ");
        printZ3Node(t, convertedArgs[1]);
        __debugPrint(logFile, ", ");
        printZ3Node(t, convertedArgs[2]);
        __debugPrint(logFile, ")");
        __debugPrint(logFile, "  =>  ");
        printZ3Node(t, *result);
        if( breakDownAst != NULL )
        {
            __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
            printZ3Node(t, breakDownAst);
        }
        __debugPrint(logFile, "\n===================\n");
#endif
        if (breakDownAst != NULL)
            Z3_assert_cnstr(ctx, breakDownAst);
        delete[] convertedArgs;
        return Z3_TRUE;
    }

    if (d == td->Str2Int)
    {
#ifdef DEBUGLOG
        __debugPrint(logFile, "\n===================\n");
        __debugPrint(logFile, "** cb_reduce_app(): Str2Int(");
        printZ3Node(t, convertedArgs[0]);
        __debugPrint(logFile, ")");
        __debugPrint(logFile, "\n===================\n");
#endif
        if (getNodeType(t, convertedArgs[0]) == my_Z3_ConstStr)
        {
            std::string strValue = getConstStrValue(t, convertedArgs[0]);
            bool isNum = isStrInt(strValue);
            if (isNum)
            {
                int value = atoi(strValue.c_str());
                *result = mk_int(ctx, value);
                return true;
            }
            return false;
        }
        return false;
    }
    delete[] convertedArgs;
    return Z3_FALSE; // failed to simplify
}

/*
 *
 *
 */
void cb_push(Z3_theory t)
{
    sLevel++;
    __debugPrint(logFile, "\n*******************************************\n");
    __debugPrint(logFile, "[PUSH]: Level = %d", sLevel);
    __debugPrint(logFile, "\n*******************************************\n");
}

/*
 *
 */
void cb_pop(Z3_theory t)
{
//  Z3_context ctx = Z3_theory_get_context(t);
    sLevel--;
    __debugPrint(logFile, "\n*******************************************\n");
    __debugPrint(logFile, "[POP]: Level = %d", sLevel);
    __debugPrint(logFile, "\n*******************************************\n");

    std::map<Z3_ast, std::stack<T_cut *> >::iterator sfxItor = cut_SuffixMap.begin();
    while (sfxItor != cut_SuffixMap.end())
    {
        while ((sfxItor->second.size() > 0) && (sfxItor->second.top()->level != 0)
                && (sfxItor->second.top()->level >= sLevel))
        {
            T_cut * aCut = sfxItor->second.top();
            sfxItor->second.pop();
            delete aCut;
        }
        if (sfxItor->second.size() == 0)
            cut_SuffixMap.erase(sfxItor++);
        else
            sfxItor++;
    }

    std::map<Z3_ast, std::stack<T_cut *> >::iterator varItor = cut_VARMap.begin();
    while (varItor != cut_VARMap.end())
    {
        while ((varItor->second.size() > 0) && (varItor->second.top()->level != 0)
                && (varItor->second.top()->level >= sLevel))
        {
            T_cut * aCut = varItor->second.top();
            varItor->second.pop();
            delete aCut;
        }
        if (varItor->second.size() == 0)
            cut_VARMap.erase(varItor++);
        else
            varItor++;
    }

}

void cb_reset(Z3_theory t)
{
    __debugPrint(logFile, "\n** Reset():\n");
}

void cb_restart(Z3_theory t)
{
    __debugPrint(logFile, "\n** Restart():\n");
}

/*
 *
 */
void cb_new_relevant(Z3_theory t, Z3_ast n)
{
    if (getNodeType(t, n) == my_Z3_Str_Var)
    {
        __debugPrint(logFile, "\n===============================================\n");
        __debugPrint(logFile, "** cb_new_relevant: ");
        printZ3Node(t, n);
        __debugPrint(logFile, "\n");
        basicStrVarAxiom(t, n, __LINE__);
        __debugPrint(logFile, "===============================================\n");
    }
}

/*
 *
 */
void cb_delete(Z3_theory t)
{
    __debugPrint(logFile, "\n** Delete()\n");

    PATheoryData * td = (PATheoryData *) Z3_theory_get_ext_data(t);
    free(td);
}

int check(Z3_context ctx)
{
    int isSAT = -1;
    Z3_model m = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);
    __debugPrint(logFile, "\n*****************************\n");
    printf("************************\n>> ");

    switch (result)
    {
        case Z3_L_FALSE:
            isSAT = -1;
            printf("UNSAT\n");
            __debugPrint(logFile, "UNSAT\n")
            ;
            break;
        case Z3_L_UNDEF:
            isSAT = 0;
            __debugPrint(logFile, "Unknown\n ")
            ;
            __debugPrint(logFile, "POSSIBLE MODEL:\n-----------------------------\n%s", Z3_model_to_string(ctx, m))
            ;
            printf("Unknown\n");
            printf("POSSIBLE MODEL:\n------------------------\n%s", Z3_model_to_string(ctx, m));
            break;
        case Z3_L_TRUE:
            isSAT = 1;
            std::string modelStr = std::string(Z3_model_to_string(ctx, m));
            __debugPrint(logFile, "SAT\n-----------------------------\n%s", modelStr.c_str())
            ;
            printf("SAT\n------------------------\n%s", Z3_model_to_string(ctx, m));
            break;
    }
    __debugPrint(logFile, "*****************************\n");
    printf("************************\n");

    if (m)
        Z3_del_model(ctx, m);

    return isSAT;
}

/**
 *
 *Procedural attachment theory example.
 *
 */
Z3_theory mk_pa_theory(Z3_context ctx)
{
    PATheoryData * td = (PATheoryData *) malloc(sizeof(PATheoryData));
    Z3_theory Th = Z3_mk_theory(ctx, "StringAttachment", td);
    Z3_sort BoolSort = Z3_mk_bool_sort(ctx);
    Z3_sort IntSort = Z3_mk_int_sort(ctx);
    Z3_sort RealSort = Z3_mk_real_sort(ctx);
    Z3_symbol string_name = Z3_mk_string_symbol(ctx, "String");
    td->String = Z3_theory_mk_sort(ctx, Th, string_name);

    //---------------------------
    Z3_symbol compare_name = Z3_mk_string_symbol(ctx, "Compare");
    Z3_sort compare_domain[2];
    compare_domain[0] = td->String;
    compare_domain[1] = td->String;
    td->Compare = Z3_theory_mk_func_decl(ctx, Th, compare_name, 2, compare_domain, BoolSort);
    //---------------------------
    Z3_symbol concat_name = Z3_mk_string_symbol(ctx, "Concat");
    Z3_sort concat_domain[2];
    concat_domain[0] = td->String;
    concat_domain[1] = td->String;
    td->Concat = Z3_theory_mk_func_decl(ctx, Th, concat_name, 2, concat_domain, td->String);
    //---------------------------
    Z3_symbol length_name = Z3_mk_string_symbol(ctx, "Length");
    Z3_sort length_domain[1];
    length_domain[0] = td->String;
    td->Length = Z3_theory_mk_func_decl(ctx, Th, length_name, 1, length_domain, IntSort);
    //---------------------------
    Z3_symbol substring_name = Z3_mk_string_symbol(ctx, "Substring");
    Z3_sort substring_domain[3];
    substring_domain[0] = td->String;
    substring_domain[1] = IntSort;
    substring_domain[2] = IntSort;
    td->SubString = Z3_theory_mk_func_decl(ctx, Th, substring_name, 3, substring_domain, td->String);
    //---------------------------
    Z3_symbol indexof_name = Z3_mk_string_symbol(ctx, "Indexof");
    Z3_sort indexof_domain[2];
    indexof_domain[0] = td->String;
    indexof_domain[1] = td->String;
    td->Indexof = Z3_theory_mk_func_decl(ctx, Th, indexof_name, 2, indexof_domain, IntSort);
    //---------------------------
    Z3_symbol contains_name = Z3_mk_string_symbol(ctx, "Contains");
    Z3_sort contains_domain[2];
    contains_domain[0] = td->String;
    contains_domain[1] = td->String;
    td->Contains = Z3_theory_mk_func_decl(ctx, Th, contains_name, 2, contains_domain, BoolSort);
    //---------------------------
    Z3_symbol replace_name = Z3_mk_string_symbol(ctx, "Replace");
    Z3_sort replace_domain[3];
    replace_domain[0] = td->String;
    replace_domain[1] = td->String;
    replace_domain[2] = td->String;
    td->Replace = Z3_theory_mk_func_decl(ctx, Th, replace_name, 3, replace_domain, td->String);
    //---------------------------
    Z3_symbol str2Int_name = Z3_mk_string_symbol(ctx, "Str2Int");
    Z3_sort str2Int_domain[1];
    str2Int_domain[0] = td->String;
    td->Str2Int = Z3_theory_mk_func_decl(ctx, Th, str2Int_name, 1, str2Int_domain, IntSort);
    //---------------------------
    Z3_symbol str2Real_name = Z3_mk_string_symbol(ctx, "Str2Real");
    Z3_sort str2Real_domain[1];
    str2Real_domain[0] = td->String;
    td->Str2Real = Z3_theory_mk_func_decl(ctx, Th, str2Real_name, 1, str2Real_domain, RealSort);
    //---------------------------
    Z3_set_delete_callback(Th, cb_delete);
    Z3_set_new_eq_callback(Th, cb_new_eq);
    Z3_set_final_check_callback(Th, cb_final_check);
    Z3_set_init_search_callback(Th, cb_init_search);
    Z3_set_push_callback(Th, cb_push);
    Z3_set_pop_callback(Th, cb_pop);
    Z3_set_reset_callback(Th, cb_reset);
    Z3_set_restart_callback(Th, cb_restart);
    Z3_set_new_relevant_callback(Th, cb_new_relevant);
    Z3_set_reduce_eq_callback(Th, cb_reduce_eq);
    Z3_set_reduce_app_callback(Th, cb_reduce_app);
    return Th;
}

void throw_z3_error(Z3_context ctx, Z3_error_code c)
{ }

/*
 *
 */
Z3_context mk_context_custom(Z3_config cfg)
{
    Z3_context ctx;
    Z3_set_param_value(cfg, "MODEL", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, throw_z3_error);
    return ctx;
}

/*
 *
 */
Z3_context mk_my_context()
{
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx;
    ctx = mk_context_custom(cfg);
    Z3_del_config(cfg);
    return ctx;
}

