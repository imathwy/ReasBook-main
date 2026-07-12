import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixGroups Manifold ContDiff

-- `lean_leansearch` was unavailable in this environment; the canonical owners below were verified
-- directly against mathlib's `Matrix.GeneralLinearGroup`, `Matrix.GLPos`,
-- `ContinuousLinearEquiv.unitsEquiv`, `LinearEquiv.toContinuousLinearEquiv`,
-- `LieAddGroup`, `OpenSubgroup`, and the standard Lie-group instances for units, products,
-- and `Circle`.

recall Matrix.GeneralLinearGroup
recall Matrix.GLPos
recall OpenSubgroup
recall LieAddGroup
recall ContinuousLinearEquiv.unitsEquiv

section

universe u

variable {n : ℕ}
variable {G : Type u} [Group G] [TopologicalSpace G]

/- Example 7.3 (Lie Groups) is recall-only.

The standard examples in this item are represented in Lean as follows.

* Matrix `GL(n, ℝ)` and `GL(n, ℂ)` use `GL (Fin n) 𝕜`.
* The basis-independent general linear group is the intrinsic automorphism type `V ≃L[ℝ] V`;
  `ContinuousLinearEquiv.unitsEquiv ℝ V` identifies it with the units model `(V →L[ℝ] V)ˣ`, and
  in finite dimensions `LinearEquiv.toContinuousLinearEquiv` upgrades the basis transport
  `Matrix.GeneralLinearGroup.toLin'` to the continuous-linear owner.
* Positive-determinant matrix groups such as `GL(n, ℝ)⁺` use the canonical subgroup owner
  `Matrix.GLPos`; `OpenSubgroup G` is the more general owner for arbitrary open subgroups.
* Additive examples such as `ℝ`, `ℝⁿ`, `ℂ`, and `ℂⁿ` use `LieAddGroup`.
* Direct products, including finite products and tori, use the product Lie-group instance.
* The circle group `S¹` is the real Lie group `Circle`. -/
#check GL (Fin n) ℝ
#check GL (Fin n) ℂ
#check GL(n, ℝ)⁺
#check OpenSubgroup G

end

section

universe u

variable {n : ℕ}
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable [FiniteDimensional ℝ V]
variable (b : Module.Basis (Fin n) ℝ V)

#check (V ≃L[ℝ] V)
#check ContinuousLinearEquiv.unitsEquiv ℝ V
#check LinearEquiv.toContinuousLinearEquiv
#check (fun A : GL (Fin n) ℝ ↦ (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv.toContinuousLinearEquiv)
#check (inferInstance : LieGroup (𝓘(ℝ, V →L[ℝ] V)) ∞ (V →L[ℝ] V)ˣ)

end

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

#check (inferInstance : LieAddGroup (𝓘(ℝ, E)) ∞ E)
#check (inferInstance : LieAddGroup (𝓘(ℝ, Fin n → ℂ)) ∞ (Fin n → ℂ))

end

section

universe uG uH uEG uEH uHG uHH

variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace ℝ EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners ℝ EG HG} {J : ModelWithCorners ℝ EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup I ∞ G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H] [LieGroup J ∞ H]

#check (inferInstance : LieGroup (I.prod J) ∞ (G × H))

end

section

#check (inferInstance : LieGroup (𝓡 1) ∞ Circle)

end
