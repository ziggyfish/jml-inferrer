package com.z3x;

import com.z3x.solver.Solver;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

public final class Main {
    public static void main(String[] args) throws IOException {
        if (args.length == 0) {
            System.err.println("usage: z3x <file.smt2>");
            System.exit(64);
        }
        String src = Files.readString(Path.of(args[0]));
        Solver solver = new Solver();
        List<Solver.Verdict> verdicts = solver.run(src);
        for (Solver.Verdict v : verdicts) {
            System.out.println(switch (v) {
                case SAT -> "sat";
                case UNSAT -> "unsat";
                case UNKNOWN -> "unknown";
            });
        }
    }
}
