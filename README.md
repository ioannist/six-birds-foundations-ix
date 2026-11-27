# Six Birds Foundations IX

**One Word Against Two: The Complexity of Revising Markov Laws Under Held Tests**

Ioannis Tsiokos · Preprint v1.0, 25 November 2026 ·
DOI [10.5281/zenodo.24494014](https://doi.org/10.5281/zenodo.24494014)

For labeled shared-probe Markov chains with a hidden register, the paper
proves that revising parameters under held tests goes from P-complete to
PSPACE-hard at one step of test syntax: single-word tests give a
P-complete fine-reachability problem with polynomial-size certificates for
both answers, and one test comparing a word with a sum of two words makes it
PSPACE-hard. The Zenodo record holds the paper, the Lean source and the
supplement *Lean Correspondence Tables*.

## Layout

```
paper/v2/     Current manuscript (acmart), its figures, bibliography and the
              supplement Lean Correspondence Tables (paper/v2/supplement/)
paper/        First draft of Foundations IX, kept for reference; Six Birds
              Foundations II, Version 4, builds its Section 10 on it
lean/         Lean 4 development (MovingProjection) and proof notes (*.md)
```

## Build the paper

```sh
cd paper/v2
latexmk
```

The PDF is at `paper/v2/build/main.pdf`. Build the supplement after the
paper, since it reads the paper's theorem numbers:

```sh
cd paper/v2/supplement
latexmk -pdf -outdir=../build/supplement lean-correspondence.tex
```

## Build the Lean proofs

```sh
cd lean
lake exe cache get
lake build
```

The project pins Lean and Mathlib v4.28.0. Appendix A of the paper and the
supplement identify the Lean declarations behind each checked result and the
steps proved only on paper. [Lean entry point](lean/MovingProjection.lean)

## Citation

```bibtex
@misc{tsiokos2026onewordagainsttwo,
  author = {Tsiokos, Ioannis},
  title  = {One Word Against Two: The Complexity of Revising {Markov} Laws Under Held Tests},
  year   = {2026},
  doi    = {10.5281/zenodo.24494014},
  note   = {Six Birds Foundations IX. Preprint v1.0}
}
```

Licence: CC BY 4.0.
