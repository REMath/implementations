package hampi.parser;

public abstract class HAbstractGrammarElement{
  private final HGrammarElementKind kind;

  protected HAbstractGrammarElement(HGrammarElementKind kind){
    this.kind = kind;
  }

  public final HGrammarElementKind getKind(){
    return kind;
  }

  @Override
  public final String toString(){
    return unparse();
  }

  public abstract String unparse();

  public abstract void accept(HGrammarVisitor v);
}
