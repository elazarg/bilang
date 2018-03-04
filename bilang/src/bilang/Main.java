package bilang;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.antlr.v4.runtime.*;

import bilang.generated.*;

public final class Main {

    static public void main(String argv[]) throws IOException {
        final BiLangParser.ProgramContext program = parse(Paths.get("/dev/stdin"));
        System.out.println(program.toStringTree());
    }

    private static String typecheck(BiLangParser.ProgramContext program) {
        try {
            program.accept(new TypeChecker());
        } catch (StaticError ex) {
            System.err.println(String.format("ERROR(%d): %s", ex.line, ex.getMessage()));
            return String.format("ERROR(%d)", ex.line);
        }
        return "OK";
    }

    private static BiLangParser.ProgramContext parse(Path inputFilename) throws IOException {
        final BiLangLexer lexer = new BiLangLexer(CharStreams.fromPath(inputFilename));
        final BiLangParser p = new BiLangParser(new CommonTokenStream(lexer));
        //p.setErrorHandler(new BailErrorStrategy());
        return p.program();
    }

    static void require(boolean cond, String reason, ParserRuleContext ctx) {
        require(cond, reason, ctx.getStart());
    }

    private static List<Path> iterate(Stream<Path> paths) {
        return paths.sorted(Comparator.comparing(x -> x.getFileName().toString()))
                .collect(Collectors.toList());
    }

    static void require(boolean cond, String reason, Token t) {
        int line = t.getLine();
        if (!cond)
            throw new StaticError(line, reason);
    }

}

class StaticError extends RuntimeException {
    final int line;
    StaticError(int line, String reason) {
        super(reason);
        this.line = line;
    }
}