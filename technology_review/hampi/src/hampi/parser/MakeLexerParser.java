package hampi.parser;

import org.antlr.Tool;

public class MakeLexerParser {
public static void main(String[] args) {
    Tool.main(new String[] { "src/hampi/parser/Hampi.g" });
}
}
