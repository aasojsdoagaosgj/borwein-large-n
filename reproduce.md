# Reproduction

Run commands from the repository root unless stated otherwise.

## 1. Integrity checks

Python 3, standard library only:

```bash
python tools/verify.py
python lean/tools/verify_release.py
python lean/tools/rebuild.py --check-only
```

These check file hashes, Markdown links, the local Lean import graph, required
inputs, and the absence of proof placeholders. They do not compile Lean or
prove a theorem.

## 2. Interval computations

The five JSON files in `computation/results/` are recorded certificates from
the analytic proof. The scripts evaluate intervals, not sampled polynomial
coefficients. They are supplementary numerical checks, separate from the Lean
proof.

Install the pinned dependency, then write fresh outputs to a new directory so
the recorded results are not overwritten:

```bash
python -m pip install -r computation/requirements.txt
python computation/verification/certify_scalars.py --output-dir rerun
python computation/verification/certify_resonant_gap.py --output-dir rerun
python computation/verification/certify_threshold_boundary.py --output-dir rerun
```

`certify_scalars.py` also runs the profile and localization checks. Every
generated certificate must report `status: passed`; a recorded passing file
does not override a failure. Not all of these scripts were rerun for the
current version.

## 3. Lean build

Use Lean 4.32.2, pinned by `lean/lean-toolchain`. Exact third-party revisions
are fixed in `lean/lake-manifest.json`. From the `lean` directory:

```bash
lake exe cache get
python tools/rebuild.py --check-only
python tools/rebuild_parallel.py . --jobs 2
```

The last command compiles all 451 local modules into a new `.clean-build`
directory in dependency order, then audits the axioms of the three main
theorems. An existing `.clean-build` directory is never reused or overwritten.
Independent modules may compile concurrently; modules using `decide +kernel`
run alone. On Windows, a compiler exceeding 24 GiB of private memory is stopped
and reported as a resource failure. A failed module blocks its dependents, and
a failed run is never recorded as a successful proof.

For a sequential build, run `python tools/rebuild.py`; it writes to
`.release-build`. Only the pinned Lean distribution and third-party library
binaries may be reused; no previously compiled Borwein modules are needed.

## 4. Recorded results

All 451 modules passed the recorded fresh build, and the axiom audit passed for
the sign theorem, zero classification, and zero count. See
[clean-build.json](lean/evidence/clean-build.json) and
[axioms.log](lean/evidence/axioms.log).

An earlier version failed its first full rebuild because of a missing
dependency; [repair.md](lean/evidence/repair.md) describes the fix. Audits made
with earlier cached build outputs are not evidence for the current version.

These checks do not constitute independent human peer review.
