package com.jml.spec.write;

import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Map;

public interface JmlSpecWriter {

    void embedJar(Path inputJar, Path outputJar, Map<MethodKey, MethodSpec> specs) throws IOException;

    byte[] embedClass(byte[] inputClass, Map<String, MethodSpec> specs);

    void writeSidecar(Path inputJar, Path sidecarJar, Map<MethodKey, MethodSpec> specs) throws IOException;
}
