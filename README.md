# Six Birds Foundations IX

**Exact Reachability for Audited Markov Edits**

Ioannis Tsiokos · Version 1

The paper classifies arbitrarily fine rational edit chains that preserve
held experiments in a class of marked Markov instruments. It proves a
signed-core reachability criterion, a six-effect omission theorem, and
the five-family minimum for the declared command language. The same
coupled instrument realizes the six witness predicates from
Foundations II. [Manuscript source](paper/main.tex) · [Foundations II](https://doi.org/10.5281/zenodo.23096828)

## Build the paper

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

The PDF is at `paper/build/main.pdf`. Figure 1 includes its vector PDF
and its standalone LaTeX source. [Figure source](paper/figures/signed_core_path.tex)

## Build the Lean proofs

```sh
cd lean
lake exe cache get
lake build
```

The project pins Lean and Mathlib v4.28.0. The theorem-to-declaration
correspondence is in the manuscript. The fixed-projection and finite-event
appendix contains written proofs. [Lean entry point](lean/MovingProjection.lean) · [Correspondence](paper/sections/appendices.tex)

The bundled modules `SixBirds.Roles` and `SixBirds.FATCD` are unchanged
from Foundations II at revision `b52b6b74f34a516f56803534cc55efd8feec2007`.
They supply the prior role and record definitions for the witness bridge.
[Foundations II source](https://github.com/ioannist/six-birds-foundations-ii/tree/b52b6b74f34a516f56803534cc55efd8feec2007/lean/full/SixBirds)
