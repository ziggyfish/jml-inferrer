# RQ4 — CI/CD Integration: Design Notes

**Drafted:** 2026-05-06 (autonomous probe-sweep week, day 1)
**Status:** working draft — informs implementation in March 2027
**Source plan:** `journal/rq2_rq4_execution_plan.md` §4

RQ4 (verbatim): *How can formal methods, particularly specification inference and verification, be integrated into Agile software development workflows without introducing significant overhead or workflow disruption?*

---

## 1. Reference workflow — the three trigger points

The plan §3.1 specifies three triggers for spec inference: per-commit (incremental), per-PR (full diff), per-merge (release-candidate). The design needs to be concrete about what runs at each.

| Trigger | What runs | What gates |
|---|---|---|
| **Per-commit** (push to feature branch) | Inference on changed files only; no verification | None (informational) |
| **Per-PR** (PR opened or updated) | Inference on full diff; verification on inferred specs; comment posted to PR | Optional: `infer-clean` label gates merge |
| **Per-merge** (merge to main) | Full inference re-run on all touched packages; cache primed for next PR | None (post-merge) |

**Why three triggers, not one or two?**

- A single per-PR trigger misses incremental feedback during development.
- A per-commit-only trigger duplicates work and wastes CI time on unfinished branches.
- A per-merge-only trigger means PRs see no inference output, defeating the point.

Three triggers, three caches: per-commit reuses the previous push's cache; per-PR reuses the per-commit cache plus the base branch's per-merge cache; per-merge produces the canonical cache.

---

## 2. Caching strategy

The dominant cost of inference is the JavaParser AST construction + analyser pass per method. Caching at the **method level** rather than file level is required because most files in active development have many unchanged methods alongside the few that changed.

### 2.1 Cache key

```
sha256(
    method-source-text +
    "|" +
    canonical-form-of-each-callee-spec +
    "|" +
    inferrer-version
)
```

The callee-spec hash is what makes the cache compositional-friendly: when a callee's spec changes, every caller's hash changes too, invalidating the right slice without invalidating the wrong slice. Inferrer-version invalidates the whole cache on engine upgrade, which is the right default.

### 2.2 Cache storage

- **GitHub Actions:** the `actions/cache` action keyed on the inferrer version + the touched-files manifest. Tier-1 (per-method) keys cached as a single tarball; restoration is O(1) regardless of how many methods are restored.
- **GitLab CI:** the built-in `cache:` directive. Same shape.
- **Jenkins:** the `Stash`/`Unstash` step plus a shared workspace under `JENKINS_HOME/workspace/jml-inferrer-cache`.

### 2.3 Cache eviction

Per-method entries expire 30 days after last touch; the GH Actions cache itself expires per its 7-day default (acceptable — re-priming costs ~5 minutes on a typical mid-sized library and is a reasonable upper bound for a Friday morning's first PR).

---

## 3. Failure-mode decision tree

```
Spec inference invoked
  ├─ Inferrer crashes (engine bug)
  │   → log to PR, do not block, fail open
  ├─ Inferrer times out (>5 min for a single method)
  │   → log to PR, fall back to "no spec for this method", do not block
  ├─ OpenJML rejects an inferred clause
  │   → log clause + assertion to PR, do not block
  │     (the clause is flagged; merging is not gated on verification cleanliness
  │      because verification false positives exist — flagging is sufficient)
  ├─ Inferred spec contains a known unsupported pattern
  │   → log warning, emit best-effort clauses, do not block
  └─ Successful run
      → post a one-line summary to the PR (clauses added/modified/removed,
        verification pass/fail counts)
```

Key principle: inference output is informational, not gating. The merge decision stays with the human reviewer; the inferrer's role is to surface what it found, not to hold up the merge train.

The optional gate (a label-based "infer-clean required" mode) exists for repositories that want stronger guarantees, but the default ships with no gate.

---

## 4. GitHub Actions reusable workflow

```yaml
# .github/workflows/jml-verify.yml (canonical)
name: JML Inference and Verification
on:
  workflow_call:
    inputs:
      java-version: { type: string, default: '21' }
      cache-key-suffix: { type: string, default: '' }
    secrets:
      gemini-api-key: { required: false }

jobs:
  infer:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with: { fetch-depth: 0 }
      - uses: actions/setup-java@v4
        with: { distribution: 'temurin', java-version: ${{ inputs.java-version }} }
      - name: Restore inferrer cache
        uses: actions/cache@v4
        with:
          path: .jml-cache
          key: jml-${{ inputs.cache-key-suffix }}-${{ hashFiles('**/*.java') }}
          restore-keys: jml-${{ inputs.cache-key-suffix }}-
      - name: Run inferrer on changed files
        run: ./jml-inferrer infer --diff origin/${{ github.base_ref }}..HEAD
      - name: Run OpenJML on inferred specs
        run: ./jml-inferrer verify --diff origin/${{ github.base_ref }}..HEAD
      - name: Post PR comment
        if: github.event_name == 'pull_request'
        uses: actions/github-script@v7
        with:
          script: |
            const summary = require('fs').readFileSync('jml-summary.md', 'utf8');
            const { data } = await github.rest.issues.listComments({
              owner: context.repo.owner, repo: context.repo.repo,
              issue_number: context.issue.number
            });
            const existing = data.find(c => c.body.startsWith('## JML inference summary'));
            if (existing) {
              await github.rest.issues.updateComment({ /* update in place */ });
            } else {
              await github.rest.issues.createComment({ /* new */ });
            }
```

A consumer repo opts in by referencing the workflow in their own pipeline:

```yaml
jobs:
  jml:
    uses: jml-inferrer/.github/workflows/jml-verify.yml@v1
    with:
      java-version: '21'
```

This is the deliverable the plan calls for at §4.1 3.2.

---

## 5. Cross-CI portability

The plan calls for GitHub Actions, GitLab CI, and Jenkins prototypes. Three observations.

### 5.1 GitHub Actions is the primary target

GitHub Actions has the best community for reusable workflows and the least integration friction. The other two CIs adapt the same logic but need bespoke pipeline definitions. If schedule pressure forces de-scoping, the plan's risk register already accepts stopping at GitHub Actions and writing the others as design exercises.

### 5.2 GitLab MR pipelines

Translate the GH workflow to a `.gitlab-ci.yml` template. The MR-comment posting requires the GitLab CI `CI_MERGE_REQUEST_IID` variable plus a `glab api projects/$CI_PROJECT_ID/merge_requests/$CI_MERGE_REQUEST_IID/notes` call. Cache uses GitLab's `cache:` directive.

### 5.3 Jenkins declarative pipeline

Translate to a `Jenkinsfile` plus a small Jenkins shared library. Caching uses `stash`/`unstash`. PR-comment posting is plugin-dependent (the Jenkins GitHub Plugin or Bitbucket Plugin); the design doc should specify support for both.

---

## 6. Empirical study design

### 6.1 Synthetic projects (plan §3.5)

Three projects, each with six simulated sprints. Each sprint adds/removes/refactors ≥10% of methods. Multiple-developer pattern: alternate authors, occasional merge conflicts.

The synthetic design is chosen because it gives the only ground truth: the experimenter knows exactly which methods changed, which specs should change as a consequence, and what the cache hit/miss rate should be. Real-repo experiments (§6.2) lack this ground truth.

Recommendation not in the plan: **two of the three synthetic projects should have known interprocedural dependencies that make the spec-changes propagate**. The third should have flat, mostly-independent methods. This stratification surfaces whether the cache invalidation is correctly compositional (project 1+2) and whether independent changes don't cause unnecessary cache misses (project 3).

### 6.2 Real-repo experiments (plan §3.6)

Five active OSS Java repos. Replay last 6 months of commits through the inferrer pipeline.

Two practical concerns:

1. **Repo selection bias.** Apache Commons Lang, Caffeine, Vavr, Resilience4j, jOOL — all five are mature, well-maintained, with clean test suites. Reviewer 2 will note this. Mitigation: add at least one less-tidy repo (a popular GitHub project with mixed code quality) to broaden the threat-to-validity coverage. Candidate: Apache Pulsar or JabRef.

2. **Commit replay determinism.** Replaying commits in sequence introduces hidden state if the inferrer's cache survives between commits. Decision: **two replay configurations** — (a) cold-cache per commit, (b) warm-cache per commit. The cold-cache run measures the inferrer's worst-case runtime; the warm-cache run measures its expected runtime in CI. Both numbers go into the report.

### 6.3 Metrics

The plan §3.7 lists median/p95/p99 build-time delta, frequency and size of inferred-spec changes, stability over multiple sprints, ease of integration. Add three:

1. **Cache hit rate per commit.** Histogram of methods reused from cache vs re-inferred. Drives the cost story.
2. **Spec churn rate.** Lines of inferred spec added/removed/modified per commit. Captures whether the inferrer is stable across the lifetime of a method (the user wants this to be small — frequent spec churn signals an inferrer that is too sensitive to inconsequential code edits).
3. **Spec-change-to-code-change ratio.** Inferred-spec lines changed divided by source lines changed. A ratio near 1.0 is "intuitive"; a ratio of 5+ suggests the inferrer is over-reacting.

### 6.4 Qualitative dimension

The plan flags this as the only phase that benefits from real human input. The user has 2-3 colleagues available; budget two weeks of their time for a structured trial of the GitHub Actions workflow on their own repos. Survey questions to decide ahead of the trial:

- Would you adopt this in your own CI? Why or why not?
- What output formats made the inferrer's findings actionable?
- What was the worst false positive you saw?
- What was the most useful clause you saw?
- Did the build-time overhead change your behaviour (e.g., made you push less often)?

---

## 7. The "minimal overhead" claim

The plan's decision criterion is p95 build-time overhead <30% on real repos for the strong story, 30–60% defensible with caching, >60% requires re-architecture for incremental analysis.

Historical context (relevant to the threats section of Article 4):

- 88 ms/file × ~500 files in a mid-size library = 44 s end-to-end without parallelism.
- With 4-way parallel inference: ~11 s.
- A typical Maven build is 60–120 s; GitHub Actions adds 15–30 s of housekeeping (checkout, setup-java, cache restore).
- 11 s on top of 90 s is ~12%. Comfortably under the 30% threshold even without aggressive caching.

The 30% threshold is therefore plausible *on average*. The risk is on the long-tail: a 2,000-file library does 80 s of inference, on top of a 5-minute Maven build, gives 27% — right at the limit. If the cache hit rate is below 80%, this regresses to 40% and triggers the "defensible with caching" tier.

Conclusion: caching is load-bearing for this RQ's headline claim. If §2 (caching strategy) does not perform as designed, the RQ4 conclusion has to be hedged.

---

## 8. Algorithmic risks

### 8.1 Concurrent inferrer runs on a shared cache

Two PRs running CI simultaneously may both miss the same cache and both write to it. Concurrency-correctness:

- GitHub Actions caches are per-key immutable: the first writer wins, subsequent writers no-op silently. Acceptable.
- GitLab Runner caches are LRU per-project; concurrent writes can race. Mitigation: a per-key lock file in the cache directory.
- Jenkins workspace caches are shared across builds on the same agent; concurrency-controlled by a shared lock per-key. Mitigation: same.

### 8.2 Inferrer crash during PR run

The PR comment must still post. The decision tree (§3) handles this: a top-level wrapper script catches non-zero exits and posts a "JML inference crashed; manual review recommended" message. The merge is not gated.

### 8.3 PR-comment spam on iterative pushes

A PR that gets 10 pushes generates 10 comments unless the bot updates in place. The GH Actions snippet in §4 already does the in-place update via the `existing` lookup. The other CIs need the same logic.

### 8.4 Stale cache after inferrer upgrade

The cache key includes the inferrer version (§2.1), so an upgrade fully invalidates. A graceful degradation pattern: when the cache has the previous inferrer version, restore-keys lets the old cache prime the new one for methods whose source is unchanged — but only if the inferrer can verify by-hash that its output for that method would be identical. This is the same problem as compositional invalidation; the same `inferrer-version + source-hash + callee-hash` cache key resolves it.

---

## 9. Open items

1. **PR comment format.** Markdown table vs collapsed `<details>` block vs inline annotations. Recommendation: collapsed `<details>` with a summary table, expandable for the full clause list. Avoid inline annotations — they pollute the diff view and don't survive a force-push.

2. **Spec-change visualisation.** Should the comment show only the changed clauses, or all clauses for the changed methods? Recommendation: only the changed clauses; provide a link to a side-rendered HTML doc with the full set.

3. **Self-hosted runners.** The GitHub Actions reusable workflow assumes ubuntu-latest. Self-hosted runners need the OpenJML toolchain pre-installed; document a setup playbook.

4. **API rate limits.** The GitHub API rate limit is 5,000 requests/hour for authenticated calls. PR comments + status checks hit this on busy repos. Recommendation: rate-limit the inferrer's PR-comment writes to one per push (in-place update), not one per inference event.

5. **Encrypted secrets.** The inferrer doesn't currently need any secrets. The Article 4 prototype may need a Gemini API key (for the test-generator integration) — define the secret naming convention up front (`GEMINI_API_KEY` recommended; it's the convention the rest of the project uses).

6. **Multi-module Maven projects.** A repo with a parent pom and 20 child modules needs the inferrer invoked per module. The reusable workflow should auto-detect module structure (presence of `<modules>` in pom) and parallelise across them.

---

## 10. Sequencing dependencies

```
Phase 2A.4 (extractor) ─→ Phase 3.2 (GH Actions PR-comment uses extractor for callee specs)
Phase 2B.2 (test-gen)  ─→ Phase 3.2 (Action 3: jml-test-gen integrates with the EvoSuite bridge)
Phase 2B (compositional) ─→ Phase 3 spec-change-rate metric only meaningful with composed specs
```

Phase 3 cannot start in earnest until Phase 2A and 2B are functional. The plan's March 2027 start is consistent with that. Slippage in 2B propagates to 3.
