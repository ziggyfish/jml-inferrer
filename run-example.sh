#!/bin/bash

echo "Building JML Inferrer..."
./mvnw clean package -q

if [ $? -ne 0 ]; then
    echo "Build failed!"
    exit 1
fi

echo ""
echo "Running JML Inferrer on example code..."
java -jar target/jml-inferrer-1.0.0-jar-with-dependencies.jar experiment/sample_code

echo ""
echo "Done! Check experiment/sample_code/ to see the generated JML specifications."
