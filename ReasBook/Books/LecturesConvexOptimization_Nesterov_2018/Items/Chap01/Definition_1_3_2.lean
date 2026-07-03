import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.3.2 lies in the finite-dimensional `ℓ∞`-geometry domain on `ℝⁿ`.

Relevant owner-style declarations sampled before refining:
* `Pi.norm_def`, the canonical sup-norm formula on `Fin n → ℝ`;
* `EuclideanSpace.equiv (Fin n) ℝ`, the canonical coordinate identification of `ℝⁿ`;
* `EuclideanSpace.linftyNorm` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_2.lean`, the chapter owner for
  the textbook `ℓ∞` norm on `EuclideanSpace ℝ (Fin n)`;
* `linftyNorm_eq_sup` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_2.lean`, the source-facing coordinate
  supremum formula for that owner.

Best owner abstraction:
* the chapter owner `EuclideanSpace.linftyNorm`

Primitive data:
* a vector `x : EuclideanSpace ℝ (Fin n)`

Derived API:
* the textbook notation `‖x‖∞`
* the coordinate bridge `linftyNorm_eq_coordNorm`
* the coordinate supremum formula `linftyNorm_eq_sup`

Source/core/bridge triage:
* source-facing: the textbook `ℓ∞` norm on `ℝⁿ`
* core/canonical: the ordinary norm on `Fin n → ℝ`
* bridge/view: transport along `EuclideanSpace.equiv (Fin n) ℝ`

This item is therefore recall-first: the chapter file already owns the `ℓ∞` norm and its
coordinate formula, so the item file reuses that owner directly instead of keeping a parallel local
copy. -/

/- Definition 1.3.2: the textbook `ℓ∞` norm on `ℝⁿ`. -/
recall EuclideanSpace.linftyNorm

/- The textbook `ℓ∞` norm is the maximum absolute value of the coordinates. -/
recall linftyNorm_eq_sup {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖∞ = ↑(Finset.univ.sup fun i ↦ ‖x i‖₊)
