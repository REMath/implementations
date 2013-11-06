# Converts a Yacc grammar to Hampi format (outputs to stdout)
#   Usage: python yacc2hmp.py bc.y
#
# Requires the Python PLY package to be installed:
#   http://www.dabeaz.com/ply/
#
# Written by Philip Guo (pg@cs.stanford.edu)


# based on yparse.py, which is included in the PLY distribution:
#
# parser for Unix yacc-based grammars
#
# Author: David Beazley (dave@dabeaz.com)
# Date  : October 2, 2006



# inlined code from ylex.py:

# lexer for yacc-grammars
#
# Author: David Beazley (dave@dabeaz.com)
# Date  : October 2, 2006

import sys
sys.path.append("../..")

from ply import *

tokens = (
    'LITERAL','SECTION','TOKEN','LEFT','RIGHT','PREC','START','TYPE','NONASSOC','UNION','CODE',
    'ID','QLITERAL','NUMBER',
)

states = (('code','exclusive'),)

literals = [ ';', ',', '<', '>', '|',':' ]
t_ignore = ' \t'

t_TOKEN     = r'%token'
t_LEFT      = r'%left'
t_RIGHT     = r'%right'
t_NONASSOC  = r'%nonassoc'
t_PREC      = r'%prec'
t_START     = r'%start'
t_TYPE      = r'%type'
t_UNION     = r'%union'
t_ID        = r'[a-zA-Z_][a-zA-Z_0-9]*'
t_QLITERAL  = r'''(?P<quote>['"]).*?(?P=quote)'''
t_NUMBER    = r'\d+'

def t_SECTION(t):
    r'%%'
    if getattr(t.lexer,"lastsection",0):
         t.value = t.lexer.lexdata[t.lexpos+2:]
         t.lexer.lexpos = len(t.lexer.lexdata)
    else:
         t.lexer.lastsection = 0
    return t

# Comments
def t_ccomment(t):
    r'/\*(.|\n)*?\*/'
    t.lexer.lineno += t.value.count('\n')

t_ignore_cppcomment = r'//.*'

def t_LITERAL(t):
   r'%\{(.|\n)*?%\}'
   t.lexer.lineno += t.value.count("\n")
   return t

def t_NEWLINE(t):
   r'\n'
   t.lexer.lineno += 1

def t_code(t):
   r'\{'
   t.lexer.codestart = t.lexpos
   t.lexer.level = 1
   t.lexer.begin('code')

def t_code_ignore_string(t):
    r'\"([^\\\n]|(\\.))*?\"'

def t_code_ignore_char(t):
    r'\'([^\\\n]|(\\.))*?\''

def t_code_ignore_comment(t):
   r'/\*(.|\n)*?\*/'

def t_code_ignore_cppcom(t):
   r'//.*'

def t_code_lbrace(t):
    r'\{'
    t.lexer.level += 1

def t_code_rbrace(t):
    r'\}'
    t.lexer.level -= 1
    if t.lexer.level == 0:
         t.type = 'CODE'
         t.value = t.lexer.lexdata[t.lexer.codestart:t.lexpos+1]
         t.lexer.begin('INITIAL')
         t.lexer.lineno += t.value.count('\n')
         return t

t_code_ignore_nonspace   = r'[^\s\}\'\"\{]+'
t_code_ignore_whitespace = r'\s+'
t_code_ignore = ""

def t_code_error(t):
    raise RuntimeError

def t_error(t):
    print "%d: Illegal character '%s'" % (t.lexer.lineno, t.value[0])
    print t.value
    t.lexer.skip(1)

lex.lex()




from ply import *

tokenlist = []
preclist  = []

def p_yacc(p):
    '''yacc : defsection rulesection'''

def p_defsection(p):
    '''defsection : definitions SECTION
                  | SECTION'''
    p.lexer.lastsection = 1

def p_rulesection(p):
    '''rulesection : rules SECTION'''
    pass


def p_definitions(p):
    '''definitions : definitions definition
                   | definition'''

def p_definition_literal(p):
    '''definition : LITERAL'''
    pass

def p_definition_start(p):
    '''definition : START ID'''
    print "// start token = '%s'" % p[2]
    print

def p_definition_token(p):
    '''definition : toktype opttype idlist optsemi '''
    for i in p[3]:
       if i[0] not in "'\"":
           tokenlist.append(i)
    if p[1] == '%left':
        preclist.append(('left',) + tuple(p[3]))
    elif p[1] == '%right':
        preclist.append(('right',) + tuple(p[3]))
    elif p[1] == '%nonassoc':
        preclist.append(('nonassoc',)+ tuple(p[3]))

def p_toktype(p):
    '''toktype : TOKEN
               | LEFT
               | RIGHT
               | NONASSOC'''
    p[0] = p[1]

def p_opttype(p):
    '''opttype : '<' ID '>'
               | empty'''

def p_idlist(p):
    '''idlist  : idlist optcomma tokenid
               | tokenid'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = p[1]
        p[1].append(p[3])

def p_tokenid(p):
    '''tokenid : ID 
               | ID NUMBER
               | QLITERAL
               | QLITERAL NUMBER'''
    p[0] = p[1]
    
def p_optsemi(p):
    '''optsemi : ';'
               | empty'''

def p_optcomma(p):
    '''optcomma : ','
                | empty'''

def p_definition_type(p):
    '''definition : TYPE '<' ID '>' namelist optsemi'''
    # type declarations are ignored

def p_namelist(p):
    '''namelist : namelist optcomma ID
                | ID'''

def p_definition_union(p):
    '''definition : UNION CODE optsemi'''
    # Union declarations are ignored

def p_rules(p):
    '''rules   : rules rule
               | rule'''
    if len(p) == 2:
       rule = p[1]
    else:
       rule = p[2]

    rulename = rule[0]

    rhs_lst = []
    for r in rule[1]:
        # r contains one of the rule possibilities
        prod = []
        for i in range(len(r)):
             item = r[i]
             if item[0] == '{':    # A code block
                  if i == len(r) - 1:
                      if len(r) == 1:
                        prod.append('" "') # EMPTY!
                      break
             else:
                  # always use double quotes
                  prod.append(item.replace("'", '"'))
        rhs_lst.append(" ".join(prod))

    print 'cfg', rulename, ':=', '\n    | '.join(rhs_lst), ';'
    print


def p_rule(p):
   '''rule : ID ':' rulelist ';' '''
   p[0] = (p[1],[p[3]])

def p_rule2(p):
   '''rule : ID ':' rulelist morerules ';' '''
   p[4].insert(0,p[3])
   p[0] = (p[1],p[4])

def p_rule_empty(p):
   '''rule : ID ':' ';' '''
   p[0] = (p[1],[[]])

def p_rule_empty2(p):
   '''rule : ID ':' morerules ';' '''
   
   p[3].insert(0,[])
   p[0] = (p[1],p[3])

def p_morerules(p):
   '''morerules : morerules '|' rulelist
                | '|' rulelist
                | '|'  '''
 
   if len(p) == 2:   
       p[0] = [[]]
   elif len(p) == 3: 
       p[0] = [p[2]]
   else:
       p[0] = p[1]
       p[0].append(p[3])


def p_rulelist(p):
   '''rulelist : rulelist ruleitem
               | ruleitem'''

   if len(p) == 2:
        p[0] = [p[1]]
   else:
        p[0] = p[1]
        p[1].append(p[2])

def p_ruleitem(p):
   '''ruleitem : ID
               | QLITERAL
               | CODE
               | PREC'''
   p[0] = p[1]

def p_empty(p):
    '''empty : '''

def p_error(p):
    pass

yacc.yacc(debug=0)

import sys
filename = sys.argv[1]
yacc.parse(open(filename).read(), debug=0)

