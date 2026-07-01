import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_14
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_2_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Example_39_0_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar SetRel

universe u

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.4.2 computes the supremum-oriented pairing, the adjoint fiber,
  and the inverse-adjoint fiber for the Chapter 39 process attached to a linear map
  `B : ℝⁿ → ℝⁿ`, namely `u ↦ {x | x ≤ B u}` on the nonnegative orthant and `∅` elsewhere.
- `core/canonical`: the chapter already owns this process as `Function.lowerSetProcess B`, the
  supremum pairing as `SetRel.supremumProcessPairing`, and process adjoints as `A∗[...]`.
- `bridge/view`: the process owner is function-level, while the Hilbert adjoint is canonical on
  the Euclidean-space model `EuclideanSpace ℝ ι`. The needed coordinate-space bridge is therefore
  the thin owner-level transport `LinearMap.euclideanAdjoint`, which keeps
  `EuclideanSpace.equiv` internal and leaves the source-facing theorems stated on `B` itself.

Primary mathematical domain:
- convex processes on finite coordinate spaces and their adjoint fibers.

Domain-style sampling used here:
- `Function.lowerSetProcess` from `Example_39_0_3`;
- `SetRel.supremumProcessPairing` from `Definition_39_2_1`;
- `SetRel.adjoint` / `A∗[...]` from `Definition_39_0_14`;
- `LinearMap.adjoint` from mathlib's inner-product operator API.

Primitive data vs derived API:
- primitive source data: a finite index type `ι` and a linear map
  `B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)`, representing the same finite-dimensional linear datum as the
  textbook map `ℝⁿ → ℝⁿ`;
- reused owner data: the process `Function.lowerSetProcess B`;
- bridge data: the coordinate-space adjoint bridge `B.euclideanAdjoint`;
- derived API: the source pairing case formulas, the two adjoint-fiber cases, and the
  inverse-adjoint fiber formula, where the source `B*` is rendered by `B.euclideanAdjoint`.

Layer target: `source-facing`, stated directly on the existing owners
`Function.lowerSetProcess B`, `supremumProcessPairing`, and `A∗[...]`, with the Euclidean adjoint
passage hidden in the owner-level bridge `LinearMap.euclideanAdjoint`.
-/

namespace LinearMap

section

variable {ι : Type u} [Fintype ι]

/-- The Euclidean adjoint of a coordinate linear map `B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)`, obtained by
transporting the canonical Hilbert adjoint on `EuclideanSpace ℝ ι` along
`EuclideanSpace.equiv ι ℝ`. This is the coordinate-space bridge for the source notation `B*`. -/
abbrev euclideanAdjoint
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  let e := (EuclideanSpace.equiv ι ℝ).toLinearEquiv
  (e.arrowCongr e) (((e.symm.arrowCongr e.symm) B).adjoint)

-- Proof sketch: when `u ≥ 0`, Example 39.0.3 identifies the fiber with `Set.Iic (B u)`. For a
-- nonnegative `x⋆`, the support over that lower set is attained at the endpoint `B u`, giving the
-- value `⟪x⋆, B u⟫ₚ`.
/-- Proposition 39.4.2 (1): if `u` and `x⋆` are both nonnegative, then the
supremum-oriented process pairing of `Function.lowerSetProcess B` is exactly `⟪B u, x⋆⟫`. -/
theorem supremumProcessPairing_lowerSetProcess_of_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {u xStar : ι → ℝ}
    (hu : 0 ≤ u) (hxStar : 0 ≤ xStar) :
    SetRel.supremumProcessPairing ℝ (ι → ℝ) (Function.lowerSetProcess B) u xStar =
      ((⟪xStar, B u⟫ₚ : ℝ) : WithBotTop ℝ) := sorry

-- Proof sketch: for `u ≥ 0`, the fiber is again `Set.Iic (B u)`. If `x⋆` has a negative
-- coordinate, moving the corresponding primal coordinate to `-∞` inside that lower set forces the
-- supremum to `⊤`.
/-- Proposition 39.4.2 (2): if `u` is nonnegative but `x⋆` is not, then the
supremum-oriented process pairing of `Function.lowerSetProcess B` is `+∞`, written as `⊤` in
`WithBotTop ℝ`. -/
theorem supremumProcessPairing_lowerSetProcess_of_nonneg_of_not_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {u xStar : ι → ℝ}
    (hu : 0 ≤ u) (hxStar : ¬ 0 ≤ xStar) :
    SetRel.supremumProcessPairing ℝ (ι → ℝ) (Function.lowerSetProcess B) u xStar = ⊤ := sorry

-- Proof sketch: if `u` is not nonnegative, Example 39.0.3 gives an empty fiber. The
-- supremum-oriented support value of the empty set is `⊥`.
/-- Proposition 39.4.2 (3): if `u` is not nonnegative, then the supremum-oriented process pairing
of `Function.lowerSetProcess B` is `-∞`, written as `⊥` in `WithBotTop ℝ`. -/
theorem supremumProcessPairing_lowerSetProcess_of_not_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {u xStar : ι → ℝ}
    (hu : ¬ 0 ≤ u) :
    SetRel.supremumProcessPairing ℝ (ι → ℝ) (Function.lowerSetProcess B) u xStar = ⊥ := sorry

-- Proof sketch: unfold adjoint membership for `Function.lowerSetProcess B`. The universal
-- inequality
-- against all `x ≤ B u` and all `u ≥ 0` is equivalent to the pointwise lower bound
-- `B.euclideanAdjoint x⋆ ≤ u⋆`. If `x⋆` is not nonnegative, the primal fiber can be pushed to
-- force the support value to `⊤`, so the adjoint fiber is empty.
/-- Proposition 39.4.2 (4): if `x⋆` is nonnegative, then the adjoint fiber of
`Function.lowerSetProcess B` at `x⋆` is the upper orthant above `B* x⋆`, rendered here by the
coordinate bridge `B.euclideanAdjoint`. -/
theorem adjoint_lowerSetProcess_image_singleton_of_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {xStar : ι → ℝ}
    (hxStar : 0 ≤ xStar) :
    ((Function.lowerSetProcess B)∗[ℝ]).image ({xStar} : Set (ι → ℝ)) =
      Set.Ici (B.euclideanAdjoint xStar) := sorry

-- Proof sketch: if `x⋆` is not nonnegative, the universal adjoint inequality fails on some
-- nonnegative primal direction, so the adjoint fiber at `x⋆` is empty.
/-- Proposition 39.4.2 (5): if `x⋆` is not nonnegative, then the adjoint fiber of
`Function.lowerSetProcess B` at `x⋆` is empty. -/
theorem adjoint_lowerSetProcess_image_singleton_of_not_nonneg
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {xStar : ι → ℝ}
    (hxStar : ¬ 0 ≤ xStar) :
    ((Function.lowerSetProcess B)∗[ℝ]).image ({xStar} : Set (ι → ℝ)) =
      (∅ : Set (ι → ℝ)) := sorry

-- Proof sketch: apply the adjoint-membership definition to the inverse relation
-- `(Function.lowerSetProcess B)⁻¹`. Membership of `x⋆` in the fiber over `u⋆` means exactly that
-- `x⋆ ≥ 0` and `B.euclideanAdjoint x⋆ ≤ u⋆`. This is the source formula
-- `(A⁻¹)* u⋆ = {x⋆ | x⋆ ≥ 0, B* x⋆ ≤ u⋆}`.
/-- Proposition 39.4.2 (6): the fiber of the adjoint of the inverse process is exactly the set of
nonnegative `x⋆` satisfying `B* x⋆ ≤ u⋆`, rendered here by the coordinate bridge
`B.euclideanAdjoint`. -/
theorem inverse_adjoint_lowerSetProcess_image_singleton_eq
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (uStar : ι → ℝ) :
    (((Function.lowerSetProcess B)⁻¹)∗[ℝ]).image ({uStar} : Set (ι → ℝ)) =
      {xStar : ι → ℝ | 0 ≤ xStar ∧ B.euclideanAdjoint xStar ≤ uStar} := sorry

end

end LinearMap
