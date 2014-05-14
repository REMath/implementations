package hampi.parser;

import hampi.HampiException;
import hampi.parser.HProgram.HTypeEnvironment;

public final class HSizeFixRegDefinition extends HRegDefinition{

  private final String id;
  private final int    size;

  public HSizeFixRegDefinition(String id, String size){
    super(HGrammarElementKind.REG_FIX);
    this.id = id;
    this.size = Integer.parseInt(size);
  }

  public String getNonterminal(){
    return id;
  }

  @Override
  public String unparse(){
    return "fix(" + id + ", " + size + ")";
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    if (tenv.getType(id) != HType.CFG_TYPE)
      throw new HampiException(id + " not of type " + HType.CFG_TYPE);
  }

  public int getSize(){
    return size;
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitSizeFixRegDefinition(this);
  }
}
