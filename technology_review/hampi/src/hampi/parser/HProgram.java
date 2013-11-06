package hampi.parser;

import hampi.HampiException;

import java.util.*;

public final class HProgram extends HAbstractGrammarElement{

  private final List<HStatement> statements;

  public HProgram(){
    super(HGrammarElementKind.PROGRAM);
    this.statements = new ArrayList<HStatement>();
  }

  /**
   * Returns the minimal size of the declared variable
   */
  public int getVarSizeMin(){
    return getVarDecl().getSizeMin();
  }

  /**
   * Returns the maximmal size of the declared variable
   */
  public int getVarSizeMax(){
    return getVarDecl().getSizeMax();
  }

  private HVarDeclStatement getVarDecl(){
    List<HStatement> statements = getStatements(HGrammarElementKind.STMT_VARDECL);
    //there must be just one
    return (HVarDeclStatement) statements.get(0);
  }

  public void add(HStatement stmt){
    assert stmt != null;
    this.statements.add(stmt);
  }

  public List<HStatement> getStatements(){
    return statements;
  }

  @Override
  public String unparse(){
    StringBuilder b = new StringBuilder();
    for (Iterator<HStatement> iter = statements.iterator(); iter.hasNext();){
      HStatement stmt = iter.next();
      b.append(stmt.toString());
      if (iter.hasNext()){
        b.append("\n");
      }
    }
    return b.toString();
  }

  public void typeCheck(){
    for (HStatement stmt : statements){
      stmt.typeCheck(getTypeEnvironment(), getVarDecl());
    }
  }

  /**
   * Returns all statements of the given kind.
   */
  public List<HStatement> getStatements(HGrammarElementKind kind){
    List<HStatement> res = new ArrayList<HStatement>();
    for (HStatement s : statements){
      if (s.getKind() == kind){
        res.add(s);
      }
    }
    return res;
  }

  /**
   * Returns the reg statement for the given variable name.
   */
  public HRegDeclStatement getRegDecl(String varName){
    for (HStatement s : statements){
      if (s.getKind() == HGrammarElementKind.STMT_REGDECL){
        HRegDeclStatement reglDecl = (HRegDeclStatement) s;
        if (reglDecl.getVarName().equals(varName))
          return reglDecl;
      }
    }
    return null;
  }

  /**
   * Returns the CFG statement for the given nonterminal name.
   */
  public CFGStatement getCFGDecl(String nonterminal){
    for (HStatement s : statements){
      if (s.getKind() == HGrammarElementKind.STMT_CFG){
        CFGStatement cfgDecl = (CFGStatement) s;
        if (nonterminal.contains(cfgDecl.getVarName()))
          return cfgDecl;
      }
    }
    return null;
  }

  /**
   * Returns the CFG statements for the given nonterminal names.
   */
  public Set<CFGStatement> getCFGDecls(Set<String> nonterminals){
    Set<CFGStatement> result = new LinkedHashSet<CFGStatement>();
    for (HStatement s : statements){
      if (s.getKind() == HGrammarElementKind.STMT_CFG){
        CFGStatement cfgDecl = (CFGStatement) s;
        if (nonterminals.contains(cfgDecl.getVarName())){
          result.add(cfgDecl);
        }
      }
    }
    return result;
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitProgram(this);
    for (HStatement stmt : statements){
      stmt.accept(v);
    }
  }

  /**
   * Returns the statement that declares the variable given by the name or null
   * of no such statement exists. The variable can be of different kinds: CFG,
   * REG, VAR, or VAL.
   */
  public HStatement getDecl(String varName){
    for (HStatement s : statements){
      switch (s.getKind()){
      case STMT_CFG: {
        CFGStatement decl = (CFGStatement) s;
        if (varName.equals(decl.getVarName()))
          return decl;
        break;
      }
      case STMT_REGDECL: {
        HRegDeclStatement decl = (HRegDeclStatement) s;
        if (varName.equals(decl.getVarName()))
          return decl;
        break;
      }
      case STMT_VALDECL: {
        HValDeclStatement decl = (HValDeclStatement) s;
        if (varName.equals(decl.getVarName()))
          return decl;
        break;
      }
      case STMT_VARDECL: {
        HVarDeclStatement decl = (HVarDeclStatement) s;
        if (varName.equals(decl.getVarName()))
          return decl;
        break;
      }
      default:
        continue;
      }
    }
    return null;
  }

  /**
   * Returns the set of all CFG terminals.
   */
  public Set<String> getCFGTerminals(){
    Set<String> result = new LinkedHashSet<String>();
    List<HStatement> decls = getStatements(HGrammarElementKind.STMT_CFG);
    for (HStatement decl : decls){
      CFGStatement cfg = (CFGStatement) decl;
      result.addAll(cfg.getTerminals());
    }
    return result;
  }

  public static class HTypeEnvironment{
    private final Map<String, HType> types;

    public HTypeEnvironment(){
      types = new LinkedHashMap<String, HType>();
    }

    /**
     * Sets the new type, returns the old type or null if there was no old type.
     */
    public HType add(String name, HType type){
      return types.put(name, type);
    }

    public HType getType(String varname){
      return types.get(varname);
    }

    public Set<String> getVarNames(){
      return types.keySet();
    }

    @Override
    public String toString(){
      return types.toString();
    }
  }

  /**
   * Creates a mapping from variable names to types.
   */
  private HTypeEnvironment getTypeEnvironment(){
    HTypeEnvironment tenv = new HTypeEnvironment();
    for (HStatement stmt : getStatements()){
      if (stmt instanceof HVarDeclStatement){
        HVarDeclStatement s = (HVarDeclStatement) stmt;
        HType oldType = tenv.add(s.getVarName(), HType.STRING_TYPE);
        if (oldType != null)
          throw new HampiException("multiply defined variable " + s.getVarName());
      }
      if (stmt instanceof CFGStatement){
        CFGStatement s = (CFGStatement) stmt;
        HType oldType = tenv.add(s.getVarName(), HType.CFG_TYPE);
        if (oldType != null)
          throw new HampiException("multiply defined variable " + s.getVarName());
      }
      if (stmt instanceof HRegDeclStatement){
        HRegDeclStatement s = (HRegDeclStatement) stmt;
        HType oldType = tenv.add(s.getVarName(), HType.REG_TYPE);
        if (oldType != null)
          throw new HampiException("multiply defined variable " + s.getVarName());
      }
      if (stmt instanceof HValDeclStatement){
        HValDeclStatement s = (HValDeclStatement) stmt;
        HType oldType = tenv.add(s.getVarName(), s.getExpression().getType(tenv));
        if (oldType != null)
          throw new HampiException("multiply defined variable " + s.getVarName());
      }
    }
    return tenv;
  }

}
