# Reproducing the frozen Lean package

The manifest identifies **690 frozen project modules** and all their named
source theorems. Verification concerns these declarations and their actual
Lean dependencies. It does not turn the unformalized nonlinear Euler-window
or strong-current targets into verified theorems. Definitions, hypotheses,
shared-measure identifications and theorem scope still require mathematical
review; a build or axiom audit alone does not establish that a theorem says
what a reader intended.

## Requirements and setup

Use Python 3.10 or newer, Git, and Lean/Lake through `elan`. The repository's
`lean-toolchain` selects Lean 4.29.0. The exact Mathlib commit is pinned in both
`lake-manifest.json` and `verification/manifest.json`. The verifier uses only
the Python standard library; it has no machine-specific configuration or
third-party Python dependencies.

From the repository root, install the pinned dependencies and, optionally,
obtain their build cache:

```sh
lake exe cache get
```

The verifier expects `.lake/packages/mathlib` to be an installed Git checkout
at the manifest commit, with no modifications to tracked files. It does not
run `lake update` or silently choose a newer dependency. A verification run
creates a fresh project build directory and links its `.lake/packages` to the
installed dependency packages. Your filesystem must permit directory symbolic
links. Linux and macOS normally support this; other platforms may require
permission to create symbolic links. Dependency build caches may be reused;
the project's `Resonance` artifacts are rebuilt from the frozen source bytes.

## Commands

For a quick integrity and inventory check without invoking Lean:

```sh
python3 scripts/verify.py --source-only
```

For the default reproducibility check:

```sh
python3 scripts/verify.py
```

For an additional replay of all imported declarations from an empty kernel:

```sh
python3 scripts/verify.py --fresh
```

The last command explicitly invokes:

```sh
lake env leanchecker --fresh Resonance
```

It can take substantially longer than the default run. `leanchecker` uses
the same Lean kernel; it is not an independent proof assistant. The default
run does **not** claim to have performed this replay. A historical replay,
if recorded in `verification/historical/`, remains a separate run.

Optional arguments are `--output NEW_DIRECTORY` and `--timeout SECONDS`.
The output directory must not exist. The positive timeout applies separately
to each external command. `--source-only` and `--fresh` are mutually exclusive.
No option relaxes source coverage, dependency-cone coverage, or the axiom and
safety restrictions.

## What the default run checks

1. **Exact source snapshot.** SHA-256 is checked for every listed
   `Resonance/*.lean` file, `Resonance.lean`, `lean-toolchain`, `lakefile.toml`
   and `lake-manifest.json`. The bytes checked are the bytes copied into the
   clean build. Unlisted or missing project Lean files are rejected.
2. **Complete source inventory.** The restricted, fail-closed source scanner
   handles nested comments, module scopes, attributes, public and private
   `theorem`/`lemma` declarations. Its complete ordered inventory must equal
   the manifest. Unsupported or missed declaration syntax fails verification;
   no name is silently dropped. Project imports must be present in the
   ordered manifest, and the umbrella module must import exactly those modules.
   Forbidden proof escapes or project axioms are rejected lexically before
   compilation. This conservative source scan complements the actual Lean
   environment audit; it is not a replacement Lean parser.
3. **Pinned environment and build.** The runtime Lean version, installed
   Mathlib revision and clean tracked Mathlib sources are checked. Then
   `lake build Resonance` runs in a fresh project directory. Frozen files
   must remain byte-identical after the build.
4. **Actual theorem types.** Every listed theorem is checked by Lean and its
   type is logged, with full names and universe parameters. Main-root types
   are additionally printed with explicit arguments. Private source names
   are resolved using Lean's `privateToUserName?` in the actual imported
   environment. Their numerical compiler-name components are never guessed
   when constructing a Lean identifier: the corresponding theorem type is
   read directly from that environment.
5. **The complete theorem dependency cone.**
   `verification/CheckAxioms.lean` selects every imported theorem whose
   normalized user name belongs to `Resonance`, including private and
   compiler-generated theorem roots. It traverses all transitive constants
   occurring in their types and values. Dependencies are not skipped because
   of their name, namespace or library. The Lean checker rejects unsafe or
   partial constants, missing dependencies and axioms outside:

   ```text
   propext
   Classical.choice
   Quot.sound
   ```

   Python independently checks the logged root/constant counts, uniqueness,
   coverage of every manifest theorem and membership of every root in the
   visited cone. Generated roots are audited even when they are not named
   source declarations. The union of cone axioms is an upper bound for each
   theorem's dependencies; it is **not** a claim that every theorem uses all
   three axioms or an exact per-theorem `#print axioms` report.

If `--fresh` was requested, full-import fresh kernel replay is an additional
required stage. A failure or interruption never produces a passing result.

## Results and historical evidence

Each run writes a new ignored directory:

```text
.verification-runs/<UTC timestamp>/
  result.json
  manifest.json
  source-sha256.json
  clean/                       # only for a default/fresh run
  logs/
  CheckAxioms.lean              # checker bytes used by this run
  CheckTypes.lean               # generated full type audit
  resolved-theorems.json
  actual-proof-cone.json
```

`result.json` records **this run's** stages and counters. Its status is one of:

- `SOURCE_EQUIVALENCE_ONLY`: all source hashes and inventories match; Lean was
  not invoked. This is not a new proof-assistant verification result.
- `PASS_FOR_FROZEN_DECLARATIONS_ONLY`: the default stages passed, plus fresh
  replay if explicitly requested. Inspect `fresh_replay`; the default value
  is `not_requested`.
- `FAILED_OR_INTERRUPTED`: a required check or command failed or was
  interrupted. The logs and partial stage records are retained.

Historical counters are informational and do not supply any runtime success
condition. The verifier neither copies historical counters into its result
nor substitutes a historical replay for a requested new replay. Both modes
keep `whole_paper_end_to_end_verified` false. New root and dependency counts
are measured from the current imported environment, rather than assumed to
equal the historical counts.

The recorded publication run measured 9,160 roots and 82,345 dependency
constants, compared with 9,154 roots and 82,339 constants in the historical
audit. Comparing the recorded root inventories shows no removed historical
roots and six additional private generated match-equation roots, whose exact
names appear in `verification/publication-check.json`. This is an observed
inventory comparison; no cause is attributed to the difference. The publication
run did not request fresh replay, and the historical replay remains separate.

Hashes establish consistency with the supplied manifest, not the manifest's
authenticity. Obtain the manifest and verifier from the repository revision
you intend to trust. The verifier and checker hashes are recorded so that the
particular audit program used is identifiable. Local run logs can contain
paths chosen on the reader's own machine; review them before publishing them.

## Manifest schema

`verification/manifest.json` uses schema version 1:

- `modules`: exactly 690 distinct modules, in dependency order. Bare names
  such as `Entropy` and qualified names such as `Resonance.Entropy` are both
  accepted and normalized.
- `theorems`: the complete ordered named source inventory. Public names are
  fully qualified. Private declarations may use
  `PRIVATE:Resonance.Module.local_name`; an explicit private kernel name is
  also accepted only when it resolves to that exact actual theorem.
- `source_sha256`: relative POSIX paths mapped to lowercase SHA-256 hashes,
  covering precisely the modules and four configuration files listed above.
- `allowed_axioms`: exactly the three standard axioms listed above. Editing
  this field cannot authorize additional axioms.
- `toolchain`: the exact released `elan` toolchain identifier.
- `mathlib_revision`: the full 40-character Git commit in the lockfile.
- `main_roots`: public source theorems to print with explicit arguments;
  every entry must already occur in `theorems`.
- `historical_counts`, `snapshot`, and historical scope metadata: provenance,
  not fresh verification outcomes.

## Tests of the verifier

The standard-library test suite checks the comment/declaration scanner,
private-name resolution, exact cone coverage, and rejection of actual source
hash or manifest/inventory mutations. It does not run Lean or claim any
mathematical theorem:

```sh
python3 -m unittest discover -s scripts -p 'test_verify.py' -v
```

Tests use temporary copies and do not alter the frozen source package.
