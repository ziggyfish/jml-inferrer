package com.jml.spec.read;

import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Map;
import java.util.Optional;

public interface JmlSpecReader {

    Optional<MethodSpec> readForMethod(Class<?> clazz, String methodName, Class<?>... paramTypes);

    Map<MethodKey, MethodSpec> readAll(Class<?> clazz);

    Map<MethodKey, MethodSpec> readJar(Path jar) throws IOException;
}
