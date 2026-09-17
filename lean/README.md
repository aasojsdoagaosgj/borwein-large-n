# Lean formalization

The mathematics is explained in [the paper](../paper.md).

| Statement | Lean entry point |
| --- | --- |
| All coefficient signs for n ≥ 31,147 | `Borwein.CertifiedLargeN.coefficient_sign` |
| Exact zero classification within the polynomial degree | `Borwein.CertifiedLargeNZeroSet.coefficient_zero_iff` |
| Number of zeros within degree is 4n+6 | `Borwein.CertifiedLargeNZeroSet.zero_count` |

All 451 local modules were compiled from an empty output tree, and these three
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. They
require no external numerical input, finite-run witness, or hypothesis about
n < 31,147.

Only Lean 4.32.2 and the pinned third-party library binaries were reused.
`SOURCES.json` fixes every source hash and the build order. See the
[build record](evidence/clean-build.json), [axiom output](evidence/axioms.log),
and [repair note](evidence/repair.md), and [reproduce.md](../reproduce.md) for
the commands.
