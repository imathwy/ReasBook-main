import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section

universe u v w z

variable {E : Type u} {F : Type v} {EStar : Type w} {FStar : Type z}
variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [DenselyOrdered α] [NoBotOrder α] [NoTopOrder α] [Nonempty α]
variable [Zero FStar]
variable [HasPairing E EStar α] [HasPairing F FStar α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.0.3 is the first-coordinate specialization of Theorem 16.3.1:
  for `h(ξ₁) = inf_{ξ₂} f(ξ₁, ξ₂)`, one gets `h*(ξ₁⋆) = f*(ξ₁⋆, 0)`.
- `core/canonical`: the owner abstractions are the linear-image owner `Function.linearImage`
  (notation `◁`) and Fenchel conjugation `convexConjugate` (notation `⋆`).
- `bridge/view`: the projection owner is the canonical product map `Prod.fst`, and the dual
  insertion map is `fun ξ₁⋆ : EStar ↦ (ξ₁⋆, 0)`.

Domain-style sampling used here:
- `convexConjugate_linearImage_eq_comp` from Theorem 16.3.1;
- canonical product owners `Prod.fst` and `fun ξ₁⋆ : EStar ↦ (ξ₁⋆, 0)`;
- product pairing decomposition `pairing_prod`.

Layer target: `source-facing`, with the pairing/product owner-level statement first; the scalar
specialization belongs downstream rather than in this source-item API surface.

Redundant-source-assumption elimination: the source says `f` is convex, but the specialization of
Theorem 16.3.1 remains valid for arbitrary `WithTopBot α`-valued `f`, so no convexity
hypothesis is kept in the public statement.

Primitive side condition: for this concrete projection/insertion specialization, the second
pairing must annihilate the zero dual element (`∀ x : F, ⟪x, 0⟫ₚ = 0`).
-/

-- Proof sketch: apply `convexConjugate_linearImage_eq_comp` with primal map
-- `Prod.fst` and dual map `fun ξ₁⋆ : EStar ↦ (ξ₁⋆, 0)`, verify the pairing compatibility by
-- `pairing_prod`, then evaluate at `ξ₁⋆`.
/-- Text 16.0.3 in owner-level function form: if `h` is the image of `f` under the projection
`(ξ₁, ξ₂) ↦ ξ₁`, then `h* = f* ∘ inl`, where `inl ξ₁⋆ = (ξ₁⋆, 0)`. -/
theorem convexConjugate_firstCoordinateProjectionImage_eq_comp_inl
    (f : E × F → WithTopBot α)
    (hpair_zero_right : ∀ x : F, (⟪x, (0 : FStar)⟫ₚ : α) = 0) :
    (Prod.fst ◁ f)⋆ = f⋆ ∘ (fun ξ₁Star : EStar ↦ (ξ₁Star, (0 : FStar))) := by
  simpa using
    (convexConjugate_linearImage_eq_comp
      (A := Prod.fst)
      (Astar := fun ξ₁Star : EStar ↦ (ξ₁Star, (0 : FStar)))
      (hA := by
        intro x yStar
        simp [pairing_prod, hpair_zero_right])
      (f := f))

/-- Text 16.0.3 in owner-level form: if `h` is the image of `f` under the projection
`(ξ₁, ξ₂) ↦ ξ₁`, so that `h(ξ₁) = inf_{ξ₂} f(ξ₁, ξ₂)`, then
`h*(ξ₁⋆) = f*(ξ₁⋆, 0)`. -/
theorem convexConjugate_firstCoordinateProjectionImage_eq
    (f : E × F → WithTopBot α)
    (hpair_zero_right : ∀ x : F, (⟪x, (0 : FStar)⟫ₚ : α) = 0)
    (ξ₁Star : EStar) :
    (Prod.fst ◁ f)⋆ ξ₁Star = f⋆ (ξ₁Star, (0 : FStar)) := by
  simpa using
    congrFun
      (convexConjugate_firstCoordinateProjectionImage_eq_comp_inl
        (f := f) hpair_zero_right)
      ξ₁Star

end
