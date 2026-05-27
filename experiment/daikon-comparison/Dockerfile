# Daikon comparison harness: dynamic invariant detection over the same 11
# Apache Commons Lang classes used in Article 1, for comparison against
# JML-Inferrer's static output.
FROM eclipse-temurin:11-jdk

RUN apt-get update \
 && apt-get install -y --no-install-recommends wget perl ca-certificates \
 && rm -rf /var/lib/apt/lists/*

WORKDIR /work

# Daikon distribution (prebuilt daikon.jar is included in the tarball).
ARG DAIKON_VERSION=5.8.24
RUN wget -q https://plse.cs.washington.edu/daikon/download/daikon-${DAIKON_VERSION}.tar.gz \
 && tar xzf daikon-${DAIKON_VERSION}.tar.gz \
 && mv daikon-${DAIKON_VERSION} daikon \
 && rm daikon-${DAIKON_VERSION}.tar.gz \
 && ls -la daikon/daikon.jar

ENV DAIKONDIR=/work/daikon
ENV CLASSPATH=/work/daikon/daikon.jar

COPY commons-lang3.jar /work/commons-lang3.jar
COPY DaikonDriver.java /work/DaikonDriver.java
COPY run-daikon.sh /work/run-daikon.sh
RUN chmod +x /work/run-daikon.sh

CMD ["/work/run-daikon.sh"]
