import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;

import java.io.InputStream;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Enumeration;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * Dumps the source of every method in a sources jar, keyed as
 * SimpleClass.method/arity (matching make-examples.sh's Daikon/JML key), so the
 * comparison can show the method body alongside each tool's output.
 *
 * Output format (read by make-examples.sh):
 *   @@@KEY@@@ <key>
 *   <method source lines...>
 *   @@@KEY@@@ <next key>
 *   ...
 */
public class MethodSourceDumper {
    public static void main(String[] args) throws Exception {
        Path sourcesJar = Paths.get(args[0]);
        Path out = Paths.get(args[1]);
        JavaParser parser = new JavaParser();
        try (JarFile jar = new JarFile(sourcesJar.toFile());
             PrintWriter w = new PrintWriter(Files.newBufferedWriter(out))) {
            Enumeration<JarEntry> entries = jar.entries();
            while (entries.hasMoreElements()) {
                JarEntry e = entries.nextElement();
                if (!e.getName().endsWith(".java") || e.getName().startsWith("META-INF/")) continue;
                String src;
                try (InputStream in = jar.getInputStream(e)) { src = new String(in.readAllBytes()); }
                CompilationUnit cu;
                try { cu = parser.parse(src).getResult().orElse(null); }
                catch (RuntimeException ex) { continue; }
                if (cu == null) continue;
                for (ClassOrInterfaceDeclaration clazz : cu.findAll(ClassOrInterfaceDeclaration.class)) {
                    String cls = clazz.getNameAsString();
                    for (MethodDeclaration m : clazz.getMethods()) {
                        String key = cls + "." + m.getNameAsString() + "/" + m.getParameters().size();
                        w.println("@@@KEY@@@ " + key);
                        // declaration + body, without Javadoc, trimmed of leading blank lines
                        MethodDeclaration clone = m.clone();
                        clone.removeComment();
                        clone.getAllContainedComments().forEach(c -> c.remove());
                        w.println(clone.toString());
                    }
                }
            }
        }
        System.out.println("dumped method sources to " + out);
    }
}
