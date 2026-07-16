import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.Lemma_15_72_1

-- Declarations for this item will be appended below by the statement pipeline.

open CochainComplex.HomComplex
open HomologicalComplex

/- Domain-style sampling for 15.72.6.2:
- primary domain: the componentwise differential calculation for a pure tensor
  `α^{p,q,r} ∈ Hom_R(L^{-q}, M^p) ⊗ K^r` inside
  `HomologicalComplex.tensorObj (module_complex_internal_hom L M) K`;
- sampled owner declarations:
  `Cochain.single_v`,
  `Cochain.single_v_eq_zero`,
  `CochainComplex.HomComplex.δ_zero_cochain_v`,
  `HomologicalComplex.mapBifunctor.d_eq`,
  `HomologicalComplex.mapBifunctor.ι_D₁`,
  `HomologicalComplex.mapBifunctor.ι_D₂`,
  `HomologicalComplex.mapBifunctor.d₁_eq`,
  `HomologicalComplex.mapBifunctor.d₂_eq`;
- best owner abstraction:
  `core/canonical`: the inserted component is the standard one-term cochain from
  `Cochain.single`, the internal-Hom differential is the owner differential `δ`, and the tensor
  total differential is the owner map-bifunctor differential split into `D₁ + D₂`;
  `source-facing`: the sign formula
  `d(α^{p,q,r}) = d_M(α^{p,q,r}) - (-1)^(p + q) d_L(α^{p,q,r}) + (-1)^(p + q) d_K(α^{p,q,r})`;
  `bridge/view`: this item is only a recall layer collecting the owner formulas used in the
  proof of Lemma `15.72.6`.
-/

/- 15.72.6.2: the displayed formula for `d(α^{p,q,r})` is exactly the combination of the
single-cochain component formulas for the internal-Hom differential with the standard
tensor-totalization decomposition into `D₁` and `D₂`. -/
recall Cochain.single_v

/- Companion recall: the inserted one-term cochain has no other surviving source index. -/
recall Cochain.single_v_eq_zero

/- Companion recall: in degree `0`, the internal-Hom differential splits into the `d_M` and
signed `d_L` terms. -/
recall δ_zero_cochain_v

/- Companion recall: the tensor total differential is the sum of its horizontal and vertical
pieces. -/
recall HomologicalComplex.mapBifunctor.d_eq

/- Companion recall: projecting a tensor summand into the horizontal differential gives the
owner-side `D₁` branch. -/
recall HomologicalComplex.mapBifunctor.ι_D₁

/- Companion recall: projecting a tensor summand into the vertical differential gives the
owner-side `D₂` branch. -/
recall HomologicalComplex.mapBifunctor.ι_D₂

/- Companion recall: the horizontal branch is induced by the first differential. -/
recall HomologicalComplex.mapBifunctor.d₁_eq

/- Companion recall: the vertical branch is induced by the second differential with the standard
sign. -/
recall HomologicalComplex.mapBifunctor.d₂_eq
