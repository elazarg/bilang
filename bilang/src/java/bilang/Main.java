package bilang;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.antlr.v4.runtime.*;
import static bilang.XXX.INSTANCE;
import bilang.generated.*;

public final class Main {

    static public void main(String argv[]) throws IOException {
        //final String infile = argv.length > 1 ? argv[0] : "/dev/stdin";
        System.out.println(argv[0]);
        final BiLangParser.ProgramContext program = parse(Paths.get(argv[0]));
        String t = typecheck(program);
        Sast.Protocol scribble = INSTANCE.programToScribble(new AstTranslator().visitProgram(program));
        System.out.println(scribble.prettyPrint(null, 0));
        System.out.println(scribble.prettyPrint("Host", 0));
        //if (t.equals("OK")) { run(program); }
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

    private static void run(BiLangParser.ProgramContext program) {
        // FIX: this is program-specific and should not be here
        List<List<Map<String, Value>>> msgsForMontyHall = List.of(
                List.of(Map.of("Host", new Address(0x15))),
                List.of(Map.of("Guest", new Address(0x16))),
                List.of(Map.of("car", new Hidden<>(new IntVals(2)))),
                List.of(Map.of("d", new IntVals(1))),
                List.of(Map.of("goat", new IntVals(3))),
                List.of(Map.of("switch", BoolVals.TRUE)),
                List.of(Map.of("car", BoolVals.TRUE))
        );
        program.accept(new Interpreter(new PredefinedStrategy(msgsForMontyHall)));
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