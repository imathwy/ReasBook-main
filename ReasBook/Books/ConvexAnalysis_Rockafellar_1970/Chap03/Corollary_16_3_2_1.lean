import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_16_3_1_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped Rockafellar

variable {α : Type*} [ConditionallyCompleteLattice α] [One α]
variable {E : Type u} {F : Type v} {EStar : Type*} {FStar : Type*}
variable [HasPairing FStar F α] [HasPairing EStar E α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.2.1 states that the polar of the image `AC` is the inverse image
  of the polar `C*` under a dual map `A*`.
- `core/canonical`: the owner layer is pairing-based: set image `A '' C`, chapter polar owner
  `Set.polar` (notation `ᵒ[α]`), and an explicit dual-side map `Astar` constrained by
  pairing compatibility.
- `bridge/view`: the inner-product adjoint form is provided at the canonical continuous-operator
  layer, where `Astar` is instantiated by `A.adjoint`.

Domain-style sampling used here:
- `Set.polar` and the parameterized notation `ᵒ[α]` from `Text_14_0_5`;
- `supportFunction_image_eq_supportFunction_comp` from `Corollary_16_3_1_1`.

Primitive data vs derived API:
- primitive inputs: `A`, `Astar`, pairing compatibility, and the set `C`;
- derived API: the polar-image identity.

Layer target: `source-facing`, stated first at the pairing owner layer; the adjoint theorem is the
continuous-operator bridge specialization.

Semantic note: because `Set.polar C` is defined as the `1`-sublevel set of `supportFunction C`,
Corollary 16.3.1.1 already yields the displayed identity for arbitrary sets `C`; the source's
convexity hypothesis is therefore redundant and omitted.

Codomain note: the main theorem is stated at the extended-codomain layer `WithBotTop α`, matching
the support-function and polar owners.
-/

namespace Set

-- Proof sketch: `Cᵒ[α]` is the `1`-sublevel set of `supportFunction C` by definition. Apply the
-- pairing-level support-function image theorem and take preimages of `Set.Iic 1`.
/-- Corollary 16.3.2.1 at the pairing owner layer: if `A` and `Astar` satisfy
`⟪yStar, A x⟫ = ⟪Astar yStar, x⟫`, then the polar of `A '' C` is the preimage of `Cᵒ[α]` under
`Astar`. -/
theorem polar_image_eq_preimage
    (A : E → F) (Astar : FStar → EStar)
    (hA : ∀ x : E, ∀ yStar : FStar, (⟪yStar, A x⟫ₚ : α) = ⟪Astar yStar, x⟫ₚ)
    (C : Set E) :
    (A '' C)ᵒ[α] = Astar ⁻¹' Cᵒ[α] := by
  simpa [Set.polar] using
    congrArg (fun f ↦ f ⁻¹' Set.Iic (1 : WithTopBot α))
      (supportFunction_image_eq_supportFunction_comp (A := A) (Astar := Astar)
        (hA := hA) (C := C))

end Set

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

namespace ContinuousLinearMap

/-- Corollary 16.3.2.1, inner-product bridge form: the polar of `A '' C` is the inverse image of
`Cᵒ` under `A.adjoint`. -/
theorem polar_image_eq_preimage_adjoint_polar
    (A : E →L[ℝ] F) (C : Set E) :
    (A '' C)ᵒ[ℝ] = A.adjoint ⁻¹' Cᵒ[ℝ] := by
  simpa using
    (Set.polar_image_eq_preimage (A := A) (Astar := A.adjoint)
      (hA := fun x yStar => by
        simpa using (ContinuousLinearMap.adjoint_inner_left A x yStar).symm)
      (C := C))

end ContinuousLinearMap

end
