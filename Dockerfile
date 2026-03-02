# =============================================================================
# JML Experiment Runner - Docker Image
# =============================================================================
# Builds a reproducible environment for running the full experiment pipeline:
#   JML inference -> Gemini test generation -> test execution -> PiTest
# =============================================================================

FROM maven:3.9.6-eclipse-temurin-21

# Install bc (needed by run-experiment.sh for percentage calculations)
RUN apt-get update && apt-get install -y --no-install-recommends bc \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# --------------- Dependency caching layers ---------------
# Main project dependencies (changes rarely)
COPY pom.xml ./
RUN mvn dependency:go-offline -B

# Sub-project dependencies (changes rarely)
COPY experiment/commons-test-project/pom.xml ./experiment/commons-test-project/
RUN cd experiment/commons-test-project && mvn dependency:go-offline -B

# --------------- Build layer ---------------
COPY src/ ./src/
RUN mvn clean package -DskipTests -B -q

# --------------- Data layer ---------------
# Experiment source files needed at runtime
COPY experiment/commons-test-project/src/ ./experiment/commons-test-project/src/
COPY experiment/commons-lang-subset/ ./experiment/commons-lang-subset/
COPY experiment/sample_code/ ./experiment/sample_code/

# --------------- Script layer ---------------
COPY run-experiment.sh ./
RUN chmod +x run-experiment.sh

ENTRYPOINT ["./run-experiment.sh"]
