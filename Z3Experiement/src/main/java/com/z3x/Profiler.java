package com.z3x;

import com.z3x.solver.Solver;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Stream;

/** Profile Z3Experiement phase timings on a corpus. */
public final class Profiler {

    public static void main(String[] args) throws Exception {
        if (!Boolean.getBoolean("z3x.prof")) {
            System.err.println("Run with -Dz3x.prof=true");
            System.exit(64);
        }
        Path root = Path.of(args[0]);
        List<Path> files = new ArrayList<>();
        try (Stream<Path> stream = Files.walk(root)) {
            stream.filter(p -> p.toString().endsWith(".smt2"))
                    .sorted(Comparator.naturalOrder()).forEach(files::add);
        }
        long preTot = 0, cnfTot = 0, satTot = 0;
        // Warm 5
        for (int i = 0; i < Math.min(5, files.size()); i++) {
            new Solver().run(Files.readString(files.get(i)));
        }
        for (int i = 5; i < files.size(); i++) {
            String src = Files.readString(files.get(i));
            Solver s = new Solver();
            s.run(src);
            preTot += s.lastTimePreNs;
            cnfTot += s.lastTimeCnfNs;
            satTot += s.lastTimeSatNs;
        }
        long total = preTot + cnfTot + satTot;
        System.out.printf("Profile over %d files (post 5-warmup):%n", files.size() - 5);
        System.out.printf("  preprocess (parse → CNF input):  %8.1f ms  (%.1f%%)%n", preTot/1e6, 100.0*preTot/total);
        System.out.printf("  CNF encode:                       %8.1f ms  (%.1f%%)%n", cnfTot/1e6, 100.0*cnfTot/total);
        System.out.printf("  SAT + theory:                     %8.1f ms  (%.1f%%)%n", satTot/1e6, 100.0*satTot/total);
        System.out.printf("  TOTAL:                            %8.1f ms%n", total/1e6);
    }
}
