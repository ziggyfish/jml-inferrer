// RQ4 Phase 3.4 — Declarative Jenkins pipeline for JML inference + verification.
//
// Per journal/rq4_cicd_design.md §5.3. Mirrors the GitHub Actions / GitLab CI
// templates: cached per-PR analysis, fail-open semantics, in-place PR comment
// updates via the GitHub or Bitbucket plugin.
//
// Place this Jenkinsfile at the repository root and configure a Multibranch
// Pipeline job pointed at the repo. The pipeline auto-detects PRs via the
// CHANGE_TARGET environment variable.

pipeline {
    agent any
    options {
        timestamps()
        timeout(time: 30, unit: 'MINUTES')
    }
    environment {
        JML_CACHE_DIR = '.jml-cache'
        JML_JAR = 'target/jml-inferrer-1.0.0-jar-with-dependencies.jar'
    }
    stages {
        stage('Build inferrer') {
            steps {
                sh './mvnw -B -q package -DskipTests'
            }
        }

        stage('Restore JML cache') {
            // Stash from a known location on the controller. In a multi-agent
            // setup, swap to a Jenkins shared cache volume.
            steps {
                script {
                    try {
                        unstash name: 'jml-cache'
                    } catch (Exception e) {
                        echo "[jml-ci] no prior cache; starting cold"
                    }
                }
                sh 'mkdir -p $JML_CACHE_DIR'
            }
        }

        stage('Inference') {
            steps {
                script {
                    def diffArg = ''
                    if (env.CHANGE_TARGET) {
                        sh "git fetch origin ${env.CHANGE_TARGET}"
                        diffArg = "--diff origin/${env.CHANGE_TARGET}..HEAD"
                    }
                    sh """
                        java -cp ${JML_JAR} com.jml.inferrer.ci.JmlCi \\
                          infer --root src/main/java \\
                                --cache-dir ${JML_CACHE_DIR} \\
                                ${diffArg}
                    """
                }
            }
        }

        stage('Verification') {
            when { expression { return params.RUN_VERIFY == 'true' } }
            steps {
                sh """
                    java -cp ${JML_JAR} com.jml.inferrer.ci.JmlCi \\
                      verify --root src/main/java \\
                             --report ${JML_CACHE_DIR}/verify-report.json
                """
            }
        }

        stage('Summary') {
            steps {
                sh """
                    java -cp ${JML_JAR} com.jml.inferrer.ci.JmlCi \\
                      summary \\
                      --infer-report ${JML_CACHE_DIR}/infer-report.json \\
                      --verify-report ${JML_CACHE_DIR}/verify-report.json \\
                      --format markdown \\
                      --out ${JML_CACHE_DIR}/summary.md
                """
            }
        }

        stage('Post PR comment') {
            when { expression { return env.CHANGE_ID != null } }
            steps {
                script {
                    def summary = readFile("${JML_CACHE_DIR}/summary.md")
                    // Requires the GitHub Branch Source plugin (for GitHub)
                    // or Bitbucket Branch Source plugin (for Bitbucket); both
                    // expose pullRequest.comment(body) on the env-injected
                    // pullRequest object.
                    try {
                        if (env.CHANGE_URL?.contains('github.com')) {
                            pullRequest.comment(summary)
                        } else {
                            echo "[jml-ci] non-GitHub PR; printing summary instead:"
                            echo summary
                        }
                    } catch (Exception e) {
                        echo "[jml-ci] PR-comment plugin unavailable; logging summary:"
                        echo summary
                    }
                }
            }
        }
    }
    post {
        always {
            archiveArtifacts artifacts: "${JML_CACHE_DIR}/*.json,${JML_CACHE_DIR}/*.md",
                             allowEmptyArchive: true
            stash name: 'jml-cache', includes: "${JML_CACHE_DIR}/**", allowEmpty: true
        }
        // Fail-open: the pipeline succeeds even if the JML inference reports errors.
        // Set the build status to UNSTABLE to surface the issue without blocking
        // downstream stages.
        unsuccessful {
            unstable "JML inference reported issues; see archived summary.md"
        }
    }
}
