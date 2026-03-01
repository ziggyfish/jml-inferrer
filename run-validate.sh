#!/bin/bash
# Build the project and run inference + OpenJML validation on sample code

echo "Building JML Inferrer..."
mvn clean package -q

if [ $? -ne 0 ]; then
    echo "Build failed!"
    exit 1
fi

echo "Running inference and validation on sample code..."
java -jar target/jml-inferrer-1.0.0-jar-with-dependencies.jar experiment/sample_code --validate
