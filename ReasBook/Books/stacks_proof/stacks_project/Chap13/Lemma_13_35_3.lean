import stacks_proof.stacks_project.Chap13.Definition_13_3_4
import stacks_proof.stacks_project.Chap13.Lemma_13_4_10
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

open CategoryTheory
open Limits Pretriangulated

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
variable [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable (P Q : ObjectProperty C)

/- Domain-style sampling for Lemma 13.35.3:
- primary domain: object properties/full subcategories in a pretriangulated category, with the
  owner operations `extensionProduct` and `retractClosure` and the binary-coproduct closure
  predicate `IsClosedUnderBinaryCoproducts`;
- inspected owner declarations:
  `CategoryTheory.ObjectProperty.extensionProduct`,
  `CategoryTheory.ObjectProperty.retractClosure`,
  `CategoryTheory.ObjectProperty.IsClosedUnderBinaryCoproducts`,
  `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso`,
  `CategoryTheory.Limits.coprodIsCoprod`;
- best owner abstraction: the existing `ObjectProperty` owner layer; this file should keep the
  source-facing closure statements for those owners, not introduce new wrapper definitions;
- primitive-vs-derived split:
  primitive data are the owner operations `extensionProduct`, `retractClosure`, and a binary
  coproduct presentation;
  derived API is the induced closure of those owner constructions under direct sums.

Source/core/bridge triage:
- `source-facing`: the two Stacks closure lemmas about `\mathcal A \star \mathcal B` and
  `smd(add(\mathcal A))`;
- `core/canonical`: the mathlib owners `extensionProduct`, `retractClosure`, and
  `IsClosedUnderBinaryCoproducts`;
- `bridge/view`: the upstream colimit comparison
  `IsColimit.coconePointUniqueUpToIso (coprodIsCoprod _ _)`, which turns a generic walking-pair
  colimit witness into the canonical binary coproduct without a local wrapper. -/

-- Proof sketch: represent two objects of `extensionProduct P Q` by distinguished triangles
-- `A ⟶ X ⟶ B` and `A' ⟶ X' ⟶ B'`, take the biproduct triangle from Lemma `13.4.10`, and use
-- closure of `P` and `Q` under binary direct sums to show the outer terms still satisfy the
-- respective properties.
/-- Chap13 Lemma 13 35 3 (1): if `P` and `Q` are full subcategories closed under direct sums, then their
extension product is also closed under direct sums. This is the object-property form of the
closure of `add(\mathcal A) \star add(\mathcal B)` under direct sums. -/
@[stacks 0FX3]
instance extensionProduct_isClosedUnderBinaryCoproducts
    [P.IsClosedUnderBinaryCoproducts] [Q.IsClosedUnderBinaryCoproducts] :
    (extensionProduct P Q).IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    let X₁ := p.diag.obj (.mk .left)
    let X₂ := p.diag.obj (.mk .right)
    let B : BinaryCofan X₁ X₂ := BinaryCofan.mk (p.ι.app (.mk .left)) (p.ι.app (.mk .right))
    have hB : IsColimit B := by
      let hp := ((IsColimit.precomposeHomEquiv (diagramIsoPair p.diag).symm p.cocone).2 p.isColimit)
      simpa [B, BinaryCofan.inl, BinaryCofan.inr] using
        (IsColimit.ofIsoColimit hp (isoBinaryCofanMk _))
    obtain ⟨A₁, B₁, f₁, g₁, h₁, hT₁, hA₁, hB₁⟩ := p.prop_diag_obj (.mk .left)
    obtain ⟨A₂, B₂, f₂, g₂, h₂, hT₂, hA₂, hB₂⟩ := p.prop_diag_obj (.mk .right)
    let T₁ : Triangle C := Triangle.mk f₁ g₁ h₁
    let T₂ : Triangle C := Triangle.mk f₂ g₂ h₂
    have e : X ≅ X₁ ⨿ X₂ := by
      simpa [B] using hB.coconePointUniqueUpToIso (coprodIsCoprod X₁ X₂)
    refine (extensionProduct P Q).prop_of_iso (biprod.isoCoprod X₁ X₂ ≪≫ e.symm) ?_
    refine ⟨A₁ ⊞ A₂, B₁ ⊞ B₂, biprod.map f₁ f₂, biprod.map g₁ g₂,
      biprod.map h₁ h₂ ≫ Functor.biprodComparison' (shiftFunctor C (1 : ℤ)) A₁ A₂, ?_, ?_, ?_⟩
    · -- Proof comment: this is the direct-sum distinguishedness step deferred to Lemma 13.4.10.
      simpa [T₁, T₂] using
        (CategoryTheory.triangle_biprod_distinguished_iff (T₁ := T₁) (T₂ := T₂)).2 ⟨hT₁, hT₂⟩
    · exact P.prop_of_isColimit_binaryCofan (BinaryBiproduct.isColimit A₁ A₂) hA₁ hA₂
    · exact Q.prop_of_isColimit_binaryCofan (BinaryBiproduct.isColimit B₁ B₂) hB₁ hB₂

end

section

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
variable (P : ObjectProperty C)

-- Proof sketch: for a generic binary-coproduct presentation of `X`, rebuild the presenting cocone
-- as a `BinaryCofan`; if its two summands are retracts of `X'` and `Y'` in `P`, then the
-- canonical coproduct is a retract of `X' ⨿ Y'`. Closure of `P` under binary coproducts gives
-- `P (X' ⨿ Y')`, and transport along the cocone-point isomorphism finishes.
/-- The second part of Chap13 Lemma 13 35 3: the retract/direct-summand closure of a full subcategory closed under
direct sums is again closed under direct sums. This is the object-property form of the closure of
`smd(add(\mathcal A))` under direct sums. -/
@[stacks 0FX3]
instance retractClosure_isClosedUnderBinaryCoproducts
    [P.IsClosedUnderBinaryCoproducts] :
    P.retractClosure.IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    let X₁ := p.diag.obj (.mk .left)
    let X₂ := p.diag.obj (.mk .right)
    let B : BinaryCofan X₁ X₂ := BinaryCofan.mk (p.ι.app (.mk .left)) (p.ι.app (.mk .right))
    have hB : IsColimit B := by
      let hp := ((IsColimit.precomposeHomEquiv (diagramIsoPair p.diag).symm p.cocone).2 p.isColimit)
      simpa [B, BinaryCofan.inl, BinaryCofan.inr] using
        (IsColimit.ofIsoColimit hp (isoBinaryCofanMk _))
    obtain ⟨Y₁, hY₁, ⟨r₁⟩⟩ := p.prop_diag_obj (.mk .left)
    obtain ⟨Y₂, hY₂, ⟨r₂⟩⟩ := p.prop_diag_obj (.mk .right)
    have e : X ≅ X₁ ⨿ X₂ := by
      simpa [B] using hB.coconePointUniqueUpToIso (coprodIsCoprod X₁ X₂)
    let r : Retract (X₁ ⨿ X₂) (Y₁ ⨿ Y₂) := {
      i := coprod.map r₁.i r₂.i
      r := coprod.map r₁.r r₂.r
      retract := by simp
    }
    exact prop_retractClosure (P.prop_coprod Y₁ Y₂ hY₁ hY₂) ((Retract.ofIso e).trans r)

end

end CategoryTheory.ObjectProperty
