package com.jml.inferrer.validation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.*;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Optional;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

/**
 * Locates or downloads an OpenJML installation for theorem proving.
 *
 * Search order:
 * 1. OPENJML_HOME environment variable
 * 2. openjml on system PATH
 * 3. tools/openjml/ relative to project root
 * 4. Download from GitHub releases to tools/openjml/
 */
public class OpenJMLInstaller {

    private static final Logger logger = LoggerFactory.getLogger(OpenJMLInstaller.class);

    private static final String OPENJML_RELEASE_URL =
            "https://github.com/OpenJML/OpenJML/releases/latest/download/openjml-";

    private final Path projectRoot;

    public OpenJMLInstaller(Path projectRoot) {
        this.projectRoot = projectRoot;
    }

    /**
     * Finds or installs OpenJML, returning the path to the openjml executable.
     *
     * @param autoDownload if true, download OpenJML when not found
     * @return path to the openjml executable, or empty if not found/installable
     */
    public Optional<Path> findOrInstall(boolean autoDownload) {
        // 1. Check OPENJML_HOME environment variable
        String openjmlHome = System.getenv("OPENJML_HOME");
        if (openjmlHome != null && !openjmlHome.isBlank()) {
            Path executable = findExecutable(Paths.get(openjmlHome));
            if (executable != null) {
                logger.info("Found OpenJML via OPENJML_HOME: {}", executable);
                return Optional.of(executable);
            }
        }

        // 2. Check system PATH
        Path pathExec = findOnPath();
        if (pathExec != null) {
            logger.info("Found OpenJML on PATH: {}", pathExec);
            return Optional.of(pathExec);
        }

        // 3. Check tools/openjml/ directory
        Path toolsDir = projectRoot.resolve("tools").resolve("openjml");
        if (Files.isDirectory(toolsDir)) {
            Path executable = findExecutable(toolsDir);
            if (executable != null) {
                logger.info("Found OpenJML in tools directory: {}", executable);
                return Optional.of(executable);
            }
        }

        // 4. Download if requested
        if (autoDownload) {
            logger.info("OpenJML not found. Attempting to download...");
            return downloadOpenJML(toolsDir);
        }

        logger.warn("OpenJML not found. Set OPENJML_HOME or add openjml to PATH.");
        return Optional.empty();
    }

    /**
     * Finds the openjml executable in a directory.
     */
    private Path findExecutable(Path dir) {
        boolean isWindows = System.getProperty("os.name").toLowerCase().contains("win");

        // Check for openjml script/executable
        Path exec = isWindows ? dir.resolve("openjml.bat") : dir.resolve("openjml");
        if (Files.isRegularFile(exec)) {
            return exec;
        }

        // Also check openjml.jar
        Path jar = dir.resolve("openjml.jar");
        if (Files.isRegularFile(jar)) {
            return jar;
        }

        return null;
    }

    /**
     * Checks if openjml is available on the system PATH.
     */
    private Path findOnPath() {
        boolean isWindows = System.getProperty("os.name").toLowerCase().contains("win");
        String command = isWindows ? "where" : "which";

        try {
            ProcessBuilder pb = new ProcessBuilder(command, "openjml");
            pb.redirectErrorStream(true);
            Process process = pb.start();
            String output = new String(process.getInputStream().readAllBytes()).trim();
            int exitCode = process.waitFor();

            if (exitCode == 0 && !output.isBlank()) {
                Path found = Paths.get(output.split("\n")[0].trim());
                if (Files.exists(found)) {
                    return found;
                }
            }
        } catch (Exception e) {
            logger.debug("PATH check failed: {}", e.getMessage());
        }
        return null;
    }

    /**
     * Downloads OpenJML from GitHub releases.
     */
    private Optional<Path> downloadOpenJML(Path targetDir) {
        String osName = System.getProperty("os.name").toLowerCase();
        String platform;
        if (osName.contains("win")) {
            platform = "windows.zip";
        } else if (osName.contains("mac") || osName.contains("darwin")) {
            platform = "macos.zip";
        } else {
            platform = "linux.zip";
        }

        String downloadUrl = OPENJML_RELEASE_URL + platform;

        try {
            Files.createDirectories(targetDir);

            logger.info("Downloading OpenJML from: {}", downloadUrl);

            HttpClient client = HttpClient.newBuilder()
                    .followRedirects(HttpClient.Redirect.NORMAL)
                    .build();

            HttpRequest request = HttpRequest.newBuilder()
                    .uri(URI.create(downloadUrl))
                    .GET()
                    .build();

            Path zipFile = targetDir.resolve("openjml-download.zip");
            HttpResponse<Path> response = client.send(request,
                    HttpResponse.BodyHandlers.ofFile(zipFile));

            if (response.statusCode() == 200) {
                logger.info("Download complete. Extracting...");
                extractZip(zipFile, targetDir);
                Files.deleteIfExists(zipFile);

                Path executable = findExecutable(targetDir);
                if (executable != null) {
                    // Make executable on Unix
                    if (!osName.contains("win")) {
                        executable.toFile().setExecutable(true);
                    }
                    logger.info("OpenJML installed to: {}", executable);
                    return Optional.of(executable);
                }
            } else {
                logger.error("Download failed with status: {}", response.statusCode());
            }
        } catch (Exception e) {
            logger.error("Failed to download OpenJML: {}", e.getMessage());
        }

        return Optional.empty();
    }

    /**
     * Extracts a ZIP file to a target directory.
     */
    private void extractZip(Path zipFile, Path targetDir) throws IOException {
        try (ZipInputStream zis = new ZipInputStream(Files.newInputStream(zipFile))) {
            ZipEntry entry;
            while ((entry = zis.getNextEntry()) != null) {
                Path destPath = targetDir.resolve(entry.getName()).normalize();

                // Security check: prevent zip slip
                if (!destPath.startsWith(targetDir)) {
                    throw new IOException("Zip entry outside target directory: " + entry.getName());
                }

                if (entry.isDirectory()) {
                    Files.createDirectories(destPath);
                } else {
                    Files.createDirectories(destPath.getParent());
                    Files.copy(zis, destPath);
                }
                zis.closeEntry();
            }
        }
    }
}
