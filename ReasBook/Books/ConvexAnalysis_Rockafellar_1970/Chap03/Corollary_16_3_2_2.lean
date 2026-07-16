import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_16_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w z

section

open scoped Rockafellar

variable {α : Type*} [ConditionallyCompleteLattice α] [One α]
variable {E : Type u} {F : Type v} {EStar : Type w} {FStar : Type z}
variable [HasPairing FStar F α] [HasPairing F FStar α]
variable [HasPairing EStar E α] [HasPairing E EStar α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.2.2 states that the polar of the inverse image
  `A⁻¹ (closure D)` is the closure of the dual-side image `A^*(D^*)`.
- `core/canonical`: the owner form is pairing-level and scalar-generic: for primal/dual maps
  `A`, `Astar` and compatibility `⟪y, Astar x*⟫ = ⟪A y, x*⟫`, if `C` satisfies bipolarity
  `((Cᵒ)ᵒ = C)`, then `(A⁻¹ C)ᵒ = ((A*(Cᵒ))ᵒ)ᵒ`.
- `bridge/view`: the closure identity is exposed from the core theorem using explicit bipolar
  hypotheses for `C` and for `Astar '' Cᵒ`.

Domain-style sampling used here:
- `Set.polar_image_eq_preimage` from `Corollary_16_3_2_1`;
- `Set.polar_closure` from `Text_14_0_5`;
- `LinearMap.adjoint` only for the inner-product bridge theorem.

Primitive data vs derived API:
- primitive owner data: primal/dual maps `A`, `Astar`, pairing compatibility, and bipolarity
  inputs for `C` and `Astar '' Cᵒ`;
- derived bridge data: `Astar = A.adjoint` yields the adjoint bridge, and `C = closure D`
  yields the closure specialization.

Layer target: the main theorem is the pairing owner theorem; Euclidean/adjoint/closure forms are
retained as bridge corollaries.

Semantic note: the origin-closure hypothesis is mathematically necessary for this polar identity.
Without it, the displayed equation already fails for the zero map and a convex set whose closure
does not meet `0`.
-/

-- Proof sketch: apply Corollary 16.3.2.1 to `Astar` with dual map `A` to identify
-- `(Astar '' Cᵒ[α])ᵒ[α]` as `A ⁻¹' ((Cᵒ[α])ᵒ[α])`,
-- then rewrite by bipolarity of `C`.
/-- Pairing owner form of Corollary 16.3.2.2: if `C` is bipolar and `A`, `Astar` satisfy
`⟪y, Astar x*⟫ = ⟪A y, x*⟫`, then the polar of `A ⁻¹' C` is
the double polar of `Astar '' Cᵒ[α]`.
-/
theorem polar_preimage_eq_double_polar_image_polar
    (A : E → F) (Astar : FStar → EStar)
    (hAstar : ∀ xStar : FStar, ∀ y : E, (⟪y, Astar xStar⟫ₚ : α) = ⟪A y, xStar⟫ₚ)
    (C : Set F) (hC_bipolar : Set.polar α (Set.polar α C : Set FStar) = C) :
    ((A ⁻¹' C)ᵒ[α] : Set EStar) =
      (((Astar '' (Cᵒ[α] : Set FStar))ᵒ[α] : Set E)ᵒ[α]) := by
  have himage_polar :
      ((Astar '' (Cᵒ[α] : Set FStar))ᵒ[α] : Set E) = A ⁻¹' C := by
    calc
      (Astar '' (Cᵒ[α] : Set FStar))ᵒ[α] =
          A ⁻¹' Set.polar α (Set.polar α C : Set FStar) := by
        simpa using
          Set.polar_image_eq_preimage (A := Astar) (Astar := A) (hA := hAstar)
            (C := (Set.polar α C : Set FStar))
      _ = A ⁻¹' C := by simp [hC_bipolar]
  rw [himage_polar]

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

-- Proof sketch: apply the pairing-level double-polar owner theorem and rewrite both double-polars
-- by the supplied primitive bipolar hypotheses.
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Bipolar bridge form of Corollary 16.3.2.2: for primal/dual linear maps
`A : E → F`, `Astar : F → E` satisfying `⟪y, Astar x*⟫ = ⟪A y, x*⟫`, if `C` is bipolar and
`Astar '' Cᵒ[ℝ]` has closure as its bipolar, then
`(A ⁻¹' C)ᵒ[ℝ] = closure (Astar '' Cᵒ[ℝ])`. -/
theorem polar_preimage_eq_closure_image_polar
    (A : E →ₗ[ℝ] F) (Astar : F →ₗ[ℝ] E)
    (hA : ∀ xStar : F, ∀ y : E, (⟪y, Astar xStar⟫ₚ : ℝ) = ⟪A y, xStar⟫ₚ)
    (C : Set F)
    (hC_bipolar : Set.polar ℝ (Set.polar ℝ C : Set F) = C)
    (himage_bipolar :
      Set.polar ℝ (Set.polar ℝ (Astar '' (Set.polar ℝ C : Set F)) : Set E) =
        closure (Astar '' (Set.polar ℝ C : Set F))) :
    (A ⁻¹' C)ᵒ[ℝ] = closure (Astar '' Cᵒ[ℝ]) := by
  calc
    (A ⁻¹' C)ᵒ[ℝ] = Set.polar ℝ (Set.polar ℝ (Astar '' (Set.polar ℝ C : Set F)) : Set E) := by
      simpa using
        polar_preimage_eq_double_polar_image_polar
          (A := A) (Astar := Astar) (hAstar := hA) (C := C) (hC_bipolar := hC_bipolar)
    _ = closure (Astar '' (Set.polar ℝ C : Set F)) := himage_bipolar
    _ = closure (Astar '' Cᵒ[ℝ]) := by rfl

-- Proof sketch: specialize the owner theorem with `Astar = A.adjoint`; the pairing
-- compatibility witness is `LinearMap.adjoint_inner_right`.
/-- Inner-product bridge form: specialize the owner theorem with `Astar = A.adjoint`. -/
theorem polar_preimage_eq_closure_image_adjoint_polar
    (A : E →ₗ[ℝ] F) (C : Set F)
    (hC_bipolar : Set.polar ℝ (Set.polar ℝ C : Set F) = C)
    (himage_bipolar :
      Set.polar ℝ (Set.polar ℝ (A.adjoint '' (Set.polar ℝ C : Set F)) : Set E) =
        closure (A.adjoint '' (Set.polar ℝ C : Set F))) :
    (A ⁻¹' C)ᵒ[ℝ] = closure (A.adjoint '' Cᵒ[ℝ]) := by
  simpa using
    polar_preimage_eq_closure_image_polar (A := A) (Astar := A.adjoint)
      (hA := fun xStar y => by
        simpa using (A.adjoint_inner_right y xStar))
      (C := C) hC_bipolar himage_bipolar

-- Proof sketch: specialize the adjoint bridge theorem to `C = closure D` and simplify the polar
-- by `Set.polar_closure`.
/-- Source-facing closure specialization under explicit bipolar hypotheses for `closure D` and for
`A.adjoint '' (closure D)ᵒ[ℝ]`. -/
theorem polar_preimage_closure_eq_closure_image_adjoint_polar
    (A : E →ₗ[ℝ] F) (D : Set F)
    (hclosureD_bipolar : Set.polar ℝ (Set.polar ℝ (closure D) : Set F) = closure D)
    (himage_bipolar :
      Set.polar ℝ (Set.polar ℝ (A.adjoint '' (Set.polar ℝ (closure D) : Set F)) : Set E) =
        closure (A.adjoint '' (Set.polar ℝ (closure D) : Set F))) :
    (A ⁻¹' closure D)ᵒ[ℝ] = closure (A.adjoint '' Dᵒ[ℝ]) := by
  simpa [Set.polar_closure] using
    polar_preimage_eq_closure_image_adjoint_polar
      A (closure D) hclosureD_bipolar himage_bipolar

end
