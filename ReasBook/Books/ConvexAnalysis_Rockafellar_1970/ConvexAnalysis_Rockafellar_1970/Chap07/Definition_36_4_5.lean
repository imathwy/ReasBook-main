import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1

noncomputable section

universe u v u' v'

open scoped Rockafellar

namespace Rockafellar

/- Textbook notation for the Chapter 36 mixed inverse-adjoint owner. -/
scoped postfix:max " _*^*" => fun F ↦ (F⋆) _*

end Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [Neg UStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]
variable [HasPairingNegRight U UStar α]
variable (F : U → X → WithTopBot α)

omit [ConditionallyCompleteLinearOrder α] in
private theorem pairing_neg_right_withTopBot (u : U) (uStar : UStar) :
    (⟪u, -uStar⟫ₚ : WithTopBot α) = -(⟪u, uStar⟫ₚ : WithTopBot α) := by
  change ((⟪u, -uStar⟫ₚ : α) : WithTopBot α) = -((⟪u, uStar⟫ₚ : α) : WithTopBot α)
  simpa using
    congrArg ((↑) : α → WithTopBot α)
      (HasPairingNegRight.pairing_neg_right u uStar)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 36.4.5 says the inverse bifunction operation commutes with the
  adjoint-side source formula `F_*^*`, now exposed directly by scoped notation on the canonical
  owner expression `((adjoint XStar UStar F) _*)`.
- `core/canonical`: upstream already supplies the inverse notation layer `F _*` from
  `Definition_36_4_1` and the owner `Bifunction.adjoint` from `Chap06.Definition_6_30_14`.
- `bridge/view`: this file keeps the source formula as a bridge for the existing owner
  `((adjoint XStar UStar F) _*)`.

Domain-style sampling used here:
- `Bifunction.inverse_apply` and notation `F _*` from `Definition_36_4_1`;
- `Bifunction.adjoint` and `Bifunction.adjoint_apply` from `Chap06.Definition_6_30_14`;
- product-pairing owner `pairing_prod` from `Chap01.HasPairing`.

Primitive data vs derived API:
- primitive layer: the notation `F _*` and owner `adjoint`;
- derived API: the function-level source formula and its pointwise evaluation theorem.

Layer target: `bridge/view`, on the pairing-based dual owner layer instead of a concrete
inner-product self-dual model.
-/

/-- Definition 36.4.5, bridge form: the source object `F_*^*` is exactly the source `sup`-formula
with dual variables `(uStar, xStar)`. -/
theorem inverse_adjoint :
    (F _*^*) =
      fun (uStar : UStar) (xStar : XStar) ↦
        ⨆ x : X, ⨆ u : U,
          F _* x u +
            ((⟪x, xStar⟫ₚ : WithTopBot α) - (⟪u, uStar⟫ₚ : WithTopBot α)) := by
  funext uStar xStar
  simp only [inverse_apply, adjoint_apply, neg_neg, WithTopBot.sub_eq_add_neg]
  calc
    (⨆ p : U × X, (⟪p, (-uStar, xStar)⟫ₚ : WithTopBot α) - F p.1 p.2)
      = ⨆ p : U × X,
          F _* p.2 p.1 +
            ((⟪p.2, xStar⟫ₚ : WithTopBot α) - (⟪p.1, uStar⟫ₚ : WithTopBot α)) := by
        simp [inverse_apply, pairing_prod, pairing_neg_right_withTopBot, add_left_comm, add_comm]
    _ = ⨆ q : X × U,
          F _* q.1 q.2 +
            ((⟪q.1, xStar⟫ₚ : WithTopBot α) - (⟪q.2, uStar⟫ₚ : WithTopBot α)) := by
        let g : X × U → WithTopBot α := fun q ↦
          F _* q.1 q.2 +
            ((⟪q.1, xStar⟫ₚ : WithTopBot α) - (⟪q.2, uStar⟫ₚ : WithTopBot α))
        simpa [g] using (Equiv.prodComm U X).surjective.iSup_comp g
    _ = ⨆ x : X, ⨆ u : U,
          F _* x u +
            ((⟪x, xStar⟫ₚ : WithTopBot α) - (⟪u, uStar⟫ₚ : WithTopBot α)) := by
        rw [iSup_prod']

/-- Pointwise form of Definition 36.4.5. -/
theorem inverse_adjoint_apply (uStar : UStar) (xStar : XStar) :
    (F _*^*) uStar xStar =
      ⨆ x : X, ⨆ u : U,
        F _* x u +
          ((⟪x, xStar⟫ₚ : WithTopBot α) - (⟪u, uStar⟫ₚ : WithTopBot α)) := by
  simpa using congrFun (congrFun (inverse_adjoint (F := F)) uStar) xStar

end

end Bifunction
