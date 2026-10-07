# Area Stability of Planar Plank Covers and Bezdek's Annulus Theorem

This repository contains a complete Lean 4 formalization of the quantitative area stability of planar plank covers and Bezdek's annulus theorem, based on the paper **"Area stability of plank covers"** by **Egor Bakaev** and **Amir Yehudayoff** ([arXiv:2609.30409](https://arxiv.org/abs/2609.30409)).

The conjecture was originally posed by **Andras Bezdek** in:
> Andras Bezdek, *Covering an annulus by strips*, Discrete & Computational Geometry **30** (2003), no. 2, 177–180. [doi:10.1007/s00454-003-0002-y](https://doi.org/10.1007/s00454-003-0002-y).

The project is prepared and packaged for submission to the **Palomar Registry**.

## Main Results

1. **Bezdek's Annulus Theorem** (`bezdek_annulus` in [`Challenge.lean`](Challenge.lean) and [`Solution.lean`](Solution.lean)):
   There exists $r > 0$ such that whenever finitely many planar planks cover the closed annulus $r \le \|x\| \le 1$, their total width is at least $2$.

2. **The Quantitative Overlap Theorem** (`Annulus.overlap_theorem` in [`RequestProject/Overlap/Main.lean`](RequestProject/Overlap/Main.lean)):
   Establishes Theorem 2.1 with an explicit positive constant $c > 0$, bounding the excess overlap cost from below by $(c/r) |H(\mathcal{P})|$ whenever the hole satisfies $H(\mathcal{P}) \subseteq rD$.

3. **Unconditional Annulus Theorem** (`Annulus.bezdek_annulus'` in [`RequestProject/Overlap/Main.lean`](RequestProject/Overlap/Main.lean)):
   The full unconditional formulation in terms of finite sets of planks.

All proofs in `Solution.lean` and `RequestProject` are machine-checked and depend only on the standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`) with no `sorry` outside the challenge specification in `Challenge.lean`.

## Environment and Building

The project is configured for the latest Lean 4 toolchain:

* **Lean Version:** `leanprover/lean4:v4.35.0-rc3`
* **Mathlib Revision:** `v4.35.0-rc3`

### Build Instructions

```bash
# Update dependencies and download Mathlib cache
lake update

# Build the entire library and solution
lake build
```

## Palomar Registry Configuration

The repository layout conforms to the Palomar submission standard:
* `Challenge.lean`: The minimal self-contained challenge specification.
* `Solution.lean`: The verified implementation derived from the library.
* `comparator.json`: Comparator configuration specifying the verified declarations and permitted axioms.
* `formalization.yaml`: Structured metadata and provenance conforming to standard v0.4.
* `LICENSE`: Apache-2.0 license.

## Authorship and Credits

* **Formalization:** Arseniy Akopyan
* **Assistance and AI Tooling:**
  * **Aristotle (Harmonic)** was used for automated theorem proving and formalizing the core quantitative stability and pruning arguments.
  * **Gemini** and **ChatGPT** were used for development, code synthesis, upgrade to the latest Lean toolchain, and Palomar submission packaging.