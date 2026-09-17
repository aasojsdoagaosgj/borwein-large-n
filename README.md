# The third Borwein conjecture for large n

This repository proves the coefficient signs for every **n ≥ 31,147** and
determines the complete zero set within the polynomial degree (**4n+6 zeros**).

Start with [paper.pdf](paper.pdf) (source: [paper.md](paper.md)).

## Contents

| Path | Contents |
| --- | --- |
| [paper.pdf](paper.pdf), [paper.md](paper.md) | Statements and outline of the argument |
| [proof/](proof/analysis.md) | Detailed analytic derivation |
| [lean/](lean/README.md) | Lean 4 formalization of the main theorems |
| [computation/](computation/) | Interval-arithmetic scripts and recorded certificates |
| [tools/](tools/) | Integrity check and PDF build script |
| [reproduce.md](reproduce.md) | Integrity checks, numerical reruns, and Lean rebuild |

## Scope

- The Lean sign theorem assumes only n ≥ 31,147. It uses no finite coefficient
  computation and no external numerical data files.
- No claim is made for n < 31,147.
- All 451 local Lean modules were rebuilt from source in an empty output tree,
  and the three main theorems passed an axiom audit. See the
  [build record](lean/evidence/clean-build.json).

## AI use

Anonymous, AI-assisted research. OpenAI Codex and additional parallel AI agents
contributed to mathematics, formalization, code, review and documentation;
suggestions and audit material from other AI systems were also used. No
independent human peer review or novelty determination is claimed.
