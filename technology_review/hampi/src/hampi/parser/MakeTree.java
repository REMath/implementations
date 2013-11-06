package hampi.parser;

import org.antlr.Tool;

public class MakeTree {
public static void main(String[] args) {
    Tool.main(new String[] { "-lib", "src/hampi/parser/", "src/hampi/parser/HampiTree.g" });
}
}
