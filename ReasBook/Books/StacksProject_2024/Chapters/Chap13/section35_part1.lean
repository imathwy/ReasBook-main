import Mathlib
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_35_1 (from Chap13) -/
open CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty.ExtensionProductNotation

/- Source-facing notation for the extension product of object properties in Section `13.35`:
`A ⋆ B` is owned canonically by `CategoryTheory.ObjectProperty.extensionProduct A B`. -/
scoped notation:70 A:70 " ⋆ " B:71 =>
  extensionProduct A B

end CategoryTheory.ObjectProperty.ExtensionProductNotation

open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

/- Domain-style sampling for Lemma 13.35.1:
- primary domain: object properties/full subcategories in a triangulated category, with the
  extension product operation;
- sampled core/canonical declarations:
  `CategoryTheory.ObjectProperty.extensionProduct`,
  `CategoryTheory.ObjectProperty.extensionProduct_iff`,
  `CategoryTheory.ObjectProperty.extensionProduct_assoc`,
  `CategoryTheory.ObjectProperty.extensionProductIter`;
- best owner abstraction: `CategoryTheory.ObjectProperty.extensionProduct` is already the canonical
  owner for the extension product of full subcategories, so the source lemma should remain a pure
  recall of its upstream associativity theorem rather than introduce a parallel local statement;
- primitive-vs-derived split:
  primitive data are object properties `P`, `Q`, and `R`;
  derived API is the canonical associativity equality for their extension products.

Source/core/bridge triage:
- `source-facing`: associativity of the extension product `\mathcal A \star \mathcal B` of full
  subcategories;
- `core/canonical`: `CategoryTheory.ObjectProperty.extensionProduct` and
  `CategoryTheory.ObjectProperty.extensionProduct_assoc`;
- `bridge/view`: the later chapter notation `A ⋆ B` is only surface syntax for the same owner.
-/

/- Lemma 13.35.1: in a triangulated category, the extension product of full subcategories is
associative. This is already the canonical mathlib theorem
`CategoryTheory.ObjectProperty.extensionProduct_assoc`. -/
recall extensionProduct_assoc

/-! ### Lemma_13_35_2 (from Chap13) -/
open CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 13.35.2:
- primary domain: object properties/full subcategories in a triangulated category, specifically
  the interaction of `extensionProduct` with retract/direct-summand closure;
- inspected owner declarations:
  `CategoryTheory.ObjectProperty.extensionProduct`,
  `CategoryTheory.ObjectProperty.retractClosure`,
  `CategoryTheory.ObjectProperty.extensionProduct_retractClosure_retractClosure_le`,
  `CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClosure_retractClosure`;
- best owner abstraction: the ambient `CategoryTheory.ObjectProperty` operations
  `extensionProduct` and `retractClosure`, together with their canonical comparison theorems;
- layer: `core/canonical`; this numbered lemma is already an owner-level mathlib theorem, so the
  refined file should stay a direct recall rather than introduce a parallel wrapper;
- primitive data: the operations `P ↦ P.retractClosure` and `(P, Q) ↦ extensionProduct P Q`;
- derived API: the containment theorem
  `extensionProduct_retractClosure_retractClosure_le` and the induced equality after outer retract
  closure, `retractClosure_extensionProduct_retractClosure_retractClosure`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma about saturation/direct-summand closure and the extension
  product of full subcategories;
- `core/canonical`: the owner operations `extensionProduct`, `retractClosure`, and their canonical
  mathlib theorems named below;
- `bridge/view`: none is needed here, because the numbered item already coincides exactly with the
  canonical owner-level statements.
-/

/- Lemma 13.35.2 (1): for full subcategories `\mathcal A` and `\mathcal B` of a triangulated
category, the extension product of their saturation/direct-summand closures is contained in the
saturation of their extension product. In mathlib this is the canonical theorem
`CategoryTheory.ObjectProperty.extensionProduct_retractClosure_retractClosure_le`. -/
recall extensionProduct_retractClosure_retractClosure_le

/- Lemma 13.35.2 (2): the saturation/direct-summand closure of the extension product of the
saturations of `\mathcal A` and `\mathcal B` coincides with the saturation of
`\mathcal A \star \mathcal B`. In mathlib this is the canonical theorem
`CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClosure_retractClosure`. -/
recall retractClosure_extensionProduct_retractClosure_retractClosure

/-! ### Lemma_13_35_3 (from Chap13) -/
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
/-- Lemma 13.35.3 (1): if `P` and `Q` are full subcategories closed under direct sums, then their
extension product is also closed under direct sums. This is the object-property form of the
closure of `add(\mathcal A) \star add(\mathcal B)` under direct sums. -/
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
    · simpa [T₁, T₂] using
        triangle_biprod_distinguished_iff.2 ⟨hT₁, hT₂⟩
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
/-- Lemma 13.35.3 (2): the retract/direct-summand closure of a full subcategory closed under
direct sums is again closed under direct sums. This is the object-property form of the closure of
`smd(add(\mathcal A))` under direct sums. -/
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

/-! ### Lemma_13_35_4 (from Chap13) -/
open CategoryTheory Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [(n : ℤ) → (shiftFunctor C n).Additive] [Pretriangulated C]

/- Domain-style sampling for Lemma 13.35.4:
- primary domain: object properties/full subcategories in a pretriangulated category, with the
  Section `13.35` owners `CategoryTheory.additiveClosure`, `extensionProductIter`,
  `extensionProduct`, and `retractClosure`; the final addition theorem then upgrades to the
  triangulated layer through `extensionProductIter_add`;
- inspected owner declarations:
  `CategoryTheory.additiveClosure`,
  `CategoryTheory.additiveClosure_isClosedUnderFiniteCoproducts`,
  `CategoryTheory.ObjectProperty.extensionProductIter_add`,
  `CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClosure_retractClosure`,
  `CategoryTheory.ObjectProperty.extensionProduct_isClosedUnderBinaryCoproducts`;
- best owner abstraction: keep the source-facing stage `additiveExtensionStage`, but define it
  directly from the existing chapter owner `CategoryTheory.additiveClosure` rather than duplicating
  a local additive-hull wrapper;
- primitive-vs-derived split:
  primitive data are the chapter owner `additiveClosure` and the core operations
  `extensionProductIter`, `extensionProduct`, and `retractClosure`;
  derived API is the stage wrapper `additiveExtensionStage` together with its coproduct-closure
  and addition lemmas.

Source/core/bridge triage:
- `source-facing`: the stage `C_n = smd(add(\mathcal A)^{\star n})`;
- `core/canonical`: `CategoryTheory.additiveClosure` and the mathlib
  `ObjectProperty` extension/retract owners;
- `bridge/view`: `additiveExtensionStage` as the thin textbook wrapper around those owners. -/

/-- The stage `C_n = smd(add(\mathcal A)^{\star n})` attached to a positive integer `n`. -/
abbrev additiveExtensionStage (P : ObjectProperty C) (n : ℕ+) : ObjectProperty C :=
  (P.additiveClosure.extensionProductIter n.natPred).retractClosure

/-- `additiveExtensionStage` is monotone in the underlying object property. -/
theorem additiveExtensionStage_monotone {P Q : ObjectProperty C} (hPQ : P ≤ Q) (n : ℕ+) :
    additiveExtensionStage P n ≤ additiveExtensionStage Q n := by
  dsimp [additiveExtensionStage]
  exact monotone_retractClosure <|
    monotone_extensionProductIter
      (colimitsClosure_monotone (fun n : ℕ ↦ Discrete (Fin n)) hPQ)
      n.natPred

private instance retractClosure_isStableUnderShift (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] :
    P.retractClosure.IsStableUnderShift ℤ where
  isStableUnderShiftBy a := by
    refine ⟨?_⟩
    rintro X ⟨Y, hY, ⟨r⟩⟩
    exact ⟨Y⟦a⟧, P.le_shift a _ hY, ⟨r.map (shiftFunctor C a)⟩⟩

private instance additiveClosure_isStableUnderShift (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] :
    P.additiveClosure.IsStableUnderShift ℤ where
  isStableUnderShiftBy a := by
    refine ⟨?_⟩
    intro X hX
    change (P.colimitsClosure fun n : ℕ ↦ Discrete (Fin n)) (X⟦a⟧)
    induction hX with
    | of_mem X hX =>
        exact (P.le_colimitsClosure _) _ (P.le_shift a _ hX)
    | of_isoClosure e hX ih =>
        exact .of_isoClosure ((shiftFunctor C a).mapIso e) ih
    | of_colimitPresentation pres h ih =>
        exact .of_colimitPresentation (pres.map (shiftFunctor C a)) ih

/-- Shift-stability propagates from `P` to every additive extension stage `C_n`. -/
instance additiveExtensionStage_isStableUnderShift (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] (n : ℕ+) :
    (additiveExtensionStage P n).IsStableUnderShift ℤ := by
  dsimp [additiveExtensionStage]
  infer_instance

-- Proof sketch: first show `additiveClosure P` is closed under binary coproducts; then use
-- Lemma `13.35.3 (1)` to propagate binary-coproduct closure through `extensionProductIter`, and
-- finally Lemma `13.35.3 (2)` to pass to the outer retract closure.
/-- The stage `C_n` is closed under direct sums. -/
instance additiveExtensionStage_isClosedUnderBinaryCoproducts
    (P : ObjectProperty C) (n : ℕ+) :
    (additiveExtensionStage P n).IsClosedUnderBinaryCoproducts := by
  dsimp [additiveExtensionStage]
  letI : (P.additiveClosure.extensionProductIter n.natPred).IsClosedUnderBinaryCoproducts := by
    induction n.natPred with
    | zero =>
        simpa [extensionProductIter_zero] using
          (inferInstance : P.additiveClosure.IsClosedUnderBinaryCoproducts)
    | succ k hk =>
        rw [extensionProductIter_succ]
        letI := hk
        infer_instance
  infer_instance

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [(n : ℤ) → (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

-- Proof sketch: rewrite both sides using the definition of `additiveExtensionStage`; then apply
-- `retractClosure_extensionProduct_retractClosure_retractClosure` to remove the inner retract
-- closures and `extensionProductIter_add` with the positive-index offsets `n - 1` and `m - 1`.
/-- Lemma 13.35.4: for a full subcategory `\mathcal A` of a triangulated category and positive
integers `n` and `m`, the stage `C_{n + m} = smd(add(\mathcal A)^{\star (n + m)})` is the
retract/direct-summand closure of `C_n \star C_m`. -/
theorem additiveExtensionStage_add
    (P : ObjectProperty C) (n m : ℕ+) :
    additiveExtensionStage P (n + m) =
      ((additiveExtensionStage P n) ⋆ additiveExtensionStage P m).retractClosure := by
  dsimp [additiveExtensionStage]
  rw [retractClosure_extensionProduct_retractClosure_retractClosure]
  have hnm : (n + m).natPred = n.natPred + (m : ℕ) := by
    rcases n with ⟨n, hn⟩
    rcases m with ⟨m, hm⟩
    simp [PNat.natPred]
    rw [Nat.add_comm n m, Nat.add_sub_assoc hn, Nat.add_comm m (n - 1)]
  have hm : (m : ℕ) = m.natPred + 1 := by
    simpa [PNat.natPred] using (Nat.sub_add_cancel m.2).symm
  rw [hnm, P.additiveClosure.extensionProductIter_add' hm]

end

end CategoryTheory.ObjectProperty

/-! ### Remark_13_35_5 (from Chap13) -/
namespace CategoryTheory

open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v₁ v₂ u₁ u₂

/-
Domain-style sampling for Remark 13.35.5:
- primary domain: object properties in pretriangulated categories and their transport along exact
  functors;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.map`,
  `CategoryTheory.ObjectProperty.shift`,
  `CategoryTheory.ObjectProperty.retractClosure`,
  `CategoryTheory.ObjectProperty.extensionProduct`;
- best owner abstraction: the functorial content of the remark should be expressed directly as
  theorem-level compatibility for the canonical owner `P.map F`, not as a second wrapper class on
  functors;
- primitive-vs-derived split:
  primitive data are the Chapter 13 owners `shiftInterval` and `additiveClosure`, together with
  the mathlib owners `map`, `retractClosure`, `extensionProduct`, and `extensionProductIter`;
  derived API is the five source-facing compatibility theorems for exact functors, together with
  the auxiliary owner-level map-commutation lemmas `map_iSup`, `map_shift`, and
  `map_colimitsClosure_le`.

Source/core/bridge triage:
- `source-facing`: the Stacks remark that exact functors preserve the interval-of-shifts
  construction, direct summands, additive closure, extension products, and iterated extension
  products;
- `core/canonical`: `ObjectProperty.map` and the existing closure/extension owners;
- `bridge/view`: none. The file should expose theorem-level compatibilities rather than a wrapper
  package around those owners. -/

namespace ObjectProperty

section

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ]

/-- The bounded shift-interval generated by a single object `E`, i.e. the object property of all
objects isomorphic to a shift `E[n]` with `n ∈ [a, b]`. This is the source-facing textbook
`\mathcal E[a,b]` layer specialized to one object. -/
abbrev objectShiftInterval (E : C) (a b : ℤ) : ObjectProperty C :=
  ⨆ n : Set.Icc a b, ((((singleton E).isoClosure).shift n.1).isoClosure)

/-- The closure of an object property under shifts by integers in the interval `[a, b]`. -/
abbrev shiftInterval (P : ObjectProperty C) (a b : ℤ) : ObjectProperty C :=
  ⨆ n : Set.Icc a b, (P.shift n.1).isoClosure

end

end ObjectProperty

notation:max P "[" a ", " b "]" => ObjectProperty.shiftInterval P a b

namespace ObjectProperty

section

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ]

-- Proof sketch: unfold `shiftInterval`; the `iSup` over `Set.Icc a b` says exactly that the
-- object lies in one of the shifts `P[n]`, and the inserted `isoClosure` accounts for equality of
-- full subcategories up to isomorphism.
/-- Membership in `shiftInterval P a b` means belonging to some shift `P[n]` with `n ∈ [a, b]`,
up to isomorphism. -/
theorem prop_shiftInterval_iff (P : ObjectProperty C) (a b : ℤ) (X : C) :
    P[a, b] X ↔ ∃ n ∈ Set.Icc a b, (P.shift n).isoClosure X := by
  rw [shiftInterval, prop_iSup_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n.1, n.2, hn⟩
  · rintro ⟨n, hn, hX⟩
    exact ⟨⟨n, hn⟩, hX⟩

end

section

variable {C : Type u₁} [Category.{v₁} C]

/-- The additive closure of an object property, generated by finite direct sums and isomorphisms. -/
abbrev additiveClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.colimitsClosure fun n : ℕ ↦ Discrete (Fin n)

/-- The additive closure is closed under finite coproducts. -/
instance additiveClosure_isClosedUnderFiniteCoproducts (P : ObjectProperty C) :
    P.additiveClosure.IsClosedUnderFiniteCoproducts := by
  refine ⟨fun J _ ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  simpa [additiveClosure] using
    (IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence e.symm) :
        P.additiveClosure.IsClosedUnderColimitsOfShape (Discrete J))

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

variable (F : C ⥤ D)

/-- The image of a union of object properties is the union of their images. -/
theorem map_iSup {ι : Sort*} (A : ι → ObjectProperty C) :
    (⨆ i, A i).map F = ⨆ i, (A i).map F := by
  ext Y
  constructor
  · rintro ⟨X, hX, ⟨e⟩⟩
    rcases (prop_iSup_iff A X).mp hX with ⟨i, hX⟩
    exact (prop_iSup_iff (fun i ↦ (A i).map F) Y).mpr ⟨i, ⟨X, hX, ⟨e⟩⟩⟩
  · intro hY
    rcases (prop_iSup_iff (fun i ↦ (A i).map F) Y).mp hY with ⟨i, X, hX, ⟨e⟩⟩
    exact ⟨X, (le_iSup A i) _ hX, ⟨e⟩⟩

/-- Remark 13.35.5 (2): the image of the direct-summand closure `smd(P)` is contained in the
direct-summand closure `smd(F(P))` of the image property. -/
theorem map_retractClosure_le (P : ObjectProperty C) :
    P.retractClosure.map F ≤ (P.map F).retractClosure := by
  rintro Y ⟨X, ⟨Z, hZ, ⟨r⟩⟩, ⟨e⟩⟩
  exact ⟨F.obj Z, P.prop_map_obj F hZ, ⟨(Retract.ofIso e.symm).trans (r.map F)⟩⟩

end

section

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ]
variable {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ]

variable (F : C ⥤ D) [F.CommShift ℤ]

/-- For an isomorphism-closed property, mapping commutes with taking a fixed shift. -/
theorem map_shift (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (n : ℤ) :
    (P.shift n).map F = (P.map F).shift n := by
  ext Y
  constructor
  · rintro ⟨X, hX, ⟨e⟩⟩
    exact ⟨X⟦n⟧, hX, ⟨(F.commShiftIso n).app X ≪≫ (shiftFunctor D n).mapIso e⟩⟩
  · rintro ⟨X, hX, ⟨e⟩⟩
    refine ⟨X⟦-n⟧, P.prop_of_iso (shiftNegShift X n).symm hX, ⟨?_⟩⟩
    exact
      (F.commShiftIso (-n)).app X ≪≫ (shiftFunctor D (-n)).mapIso e ≪≫ shiftShiftNeg Y n

/-- Remark 13.35.5 (1): for an exact functor `F`, the image of the interval-of-shifts full
subcategory `P[a, b]` is exactly the interval-of-shifts full subcategory `(P.map F)[a, b]` of
the image property; this clause uses that `F` commutes with shifts and that `P` is strictly
full. -/
theorem map_shiftInterval (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (a b : ℤ) :
    (P[a, b]).map F = (P.map F)[a, b] := by
  rw [shiftInterval, shiftInterval, map_iSup]
  refine iSup_congr fun n ↦ ?_
  rw [map_isoClosure, map_shift, isoClosure_eq_self]

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {α : Type*} (J : α → Type*)
variable [∀ a, Category (J a)]

variable (F : C ⥤ D)

variable [∀ a, Limits.PreservesColimitsOfShape (J a) F]

/-- The image of a colimit-closure is contained in the corresponding closure of the image
property. -/
theorem map_colimitsClosure_le (P : ObjectProperty C) :
    (P.colimitsClosure J).map F ≤ (P.map F).colimitsClosure J := by
  have hmap : ∀ ⦃X : C⦄, P.colimitsClosure J X → (P.map F).colimitsClosure J (F.obj X) := by
    intro X hX
    induction hX with
    | of_mem X hX =>
        exact ((P.map F).le_colimitsClosure J) _ (P.prop_map_obj F hX)
    | of_isoClosure e _ ih =>
        exact ((P.map F).colimitsClosure J).prop_of_iso (F.mapIso e) ih
    | of_colimitPresentation pres _ ih =>
        exact ((P.map F).colimitsClosure J).prop_of_isColimit (pres.map F).isColimit ih
  rintro Y ⟨X, hX, ⟨e⟩⟩
  exact ((P.map F).colimitsClosure J).prop_of_iso e (hmap hX)

end

section

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]

variable (F : C ⥤ D) [F.Additive]

/-- Remark 13.35.5 (3): the image of the additive closure `add(P)` is contained in the additive
closure `add(F(P))` of the image property. -/
theorem map_additiveClosure_le (P : ObjectProperty C) :
    P.additiveClosure.map F ≤ (P.map F).additiveClosure := by
  simpa [additiveClosure] using
    (map_colimitsClosure_le (fun n : ℕ ↦ Discrete (Fin n)) F P)

end

section

variable {C : Type u₁} [Category.{v₁} C] [Limits.HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [Limits.HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (F : C ⥤ D) [F.CommShift ℤ]

variable [Functor.IsTriangulated F]

/-- Remark 13.35.5 (4): the image of an extension product `P ⋆ Q` is contained in the extension
product `F(P) ⋆ F(Q)` of the image properties. -/
theorem map_extensionProduct_le (P Q : ObjectProperty C) :
    (P ⋆ Q).map F ≤ P.map F ⋆ Q.map F := by
  rintro X ⟨Y, hY, ⟨e⟩⟩
  exact (P.map F ⋆ Q.map F).prop_of_iso e <| by
    rw [extensionProduct_iff] at hY ⊢
    rcases hY with ⟨Y₁, Y₂, f, g, h, hT, h₁, h₂⟩
    refine ⟨F.obj Y₁, F.obj Y₂, F.map f, F.map g,
      F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app Y₁, ?_, P.prop_map_obj F h₁,
      Q.prop_map_obj F h₂⟩
    simpa using F.map_distinguished (Triangle.mk f g h) hT

/-- Remark 13.35.5 (5): the image of the iterated extension product `P^{⋆ n}` is contained in the
iterated extension product `(F(P))^{⋆ n}` of the image property. -/
theorem map_extensionProductIter_le (P : ObjectProperty C) (n : ℕ) :
    (P.extensionProductIter n).map F ≤ (P.map F).extensionProductIter n := by
  induction n with
  | zero =>
      simp
  | succ n hn =>
      rw [extensionProductIter_succ, extensionProductIter_succ]
      exact (map_extensionProduct_le F P (P.extensionProductIter n)).trans <|
        monotone_extensionProduct_right (P.map F) hn

end

end

end ObjectProperty

end CategoryTheory

/-! ### Remark_13_35_6 (from Chap13) -/
open CategoryTheory Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C]

private theorem iSup_isClosedUnderColimitsOfShape_of_monotone
    {J : Type*} [Category J] [Finite J] (A : ℕ → ObjectProperty C) (hA : Monotone A)
    [∀ i, (A i).IsClosedUnderIsomorphisms] [∀ i, (A i).IsClosedUnderColimitsOfShape J] :
    (⨆ i, A i).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    classical
    rintro X ⟨p⟩
    let _ : Fintype J := Fintype.ofFinite J
    choose i hi using fun j : J ↦ (prop_iSup_iff A _).mp (p.prop_diag_obj j)
    let n : ℕ := Finset.univ.sup i
    have hn (j : J) : A n (p.diag.obj j) := by
      exact hA (Finset.le_sup (by simp)) _ (hi j)
    let q : (A n).ColimitOfShape J X :=
      { toColimitPresentation := p.toColimitPresentation
        prop_diag_obj := hn }
    exact (le_iSup A n) _ (ColimitOfShape.prop q)

private theorem colimitsClosure_iSup_of_monotone {α : Type*} (J : α → Type*)
    [∀ a, Category (J a)] [∀ a, Finite (J a)] (A : ℕ → ObjectProperty C) (hA : Monotone A) :
    (⨆ i, A i).colimitsClosure J = ⨆ i, (A i).colimitsClosure J := by
  let B : ℕ → ObjectProperty C := fun i ↦ (A i).colimitsClosure J
  have hB : Monotone B := by
    intro i j hij
    simpa [B] using
      (colimitsClosure_monotone J (hA hij) : (A i).colimitsClosure J ≤ (A j).colimitsClosure J)
  refine le_antisymm ?_ ?_
  · let Q : ObjectProperty C := ⨆ i, B i
    have hAQ : (⨆ i, A i) ≤ Q := by
      refine iSup_le fun i ↦ ?_
      exact ((A i).le_colimitsClosure J).trans <| le_iSup B i
    have hQ (a : α) : Q.IsClosedUnderColimitsOfShape (J a) := by
      simpa [Q, B] using
        (iSup_isClosedUnderColimitsOfShape_of_monotone B hB : Q.IsClosedUnderColimitsOfShape (J a))
    let _ : ∀ a : α, Q.IsClosedUnderColimitsOfShape (J a) := hQ
    intro X hX
    induction hX with
    | of_mem X hX => exact hAQ _ hX
    | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
    | of_colimitPresentation pres h h' => exact Q.prop_of_isColimit pres.isColimit h'
  · refine iSup_le fun i ↦ ?_
    simpa [B] using
      (colimitsClosure_monotone J (le_iSup A i) :
        (A i).colimitsClosure J ≤ (⨆ i, A i).colimitsClosure J)

-- Proof sketch: finite coproduct presentations only use finitely many stages of the chain, so
-- monotonicity lets one dominate all of them by a single index; then retract closures commute with
-- that `iSup`.
/-- Remark 13.35.6 (3): for an increasing family `A_i`, the additive closure `add` of the union is
the union of the additive closures. -/
theorem additiveClosure_iSup_of_monotone (A : ℕ → ObjectProperty C) (hA : Monotone A) :
    additiveClosure (⨆ i, A i) = ⨆ i, additiveClosure (A i) := by
  simpa [additiveClosure] using
    (colimitsClosure_iSup_of_monotone (fun n : ℕ ↦ Discrete (Fin n)) A hA)

end

section

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {ι : Sort*}

/- Domain-style sampling for Remark 13.35.6:
- primary domain: `ObjectProperty` closure operations in a pretriangulated category, especially the
  interval-of-shifts owner from Remark `13.35.5` and the triangulated extension/retract owners
  from mathlib;
- sampled owner declarations:
  `CategoryTheory.shiftInterval`,
  `CategoryTheory.additiveClosure`,
  `CategoryTheory.ObjectProperty.retractClosure`,
  `CategoryTheory.ObjectProperty.extensionProduct`;
- best owner abstraction: the interval construction should use the chapter owner `P[a, b]` rather
  than a second local interval wrapper; the new content of this file is the interaction of `iSup`
  with that owner and with the closure operations `retractClosure`, `additiveClosure`, `⋆`, and
  `extensionProductIter`;
- primitive-vs-derived split:
  primitive data are the existing owners `P[a, b]`, `P.retractClosure`, `additiveClosure P`,
  `P ⋆ Q`, and `P.extensionProductIter n`;
  derived API is the six `iSup`-commutation lemmas recorded below.

Source/core/bridge triage:
- `source-facing`: the Stacks formulas saying that unions commute with bounded shifts, direct
  summands, additive closure, extension products `⋆`, and iterated extension products;
- `core/canonical`: `shiftInterval`, `retractClosure`, `additiveClosure`, `extensionProduct`, and
  `extensionProductIter`;
- `bridge/view`: none beyond using the established notation `P[a, b]` for the interval owner. -/

-- Proof sketch: `P[a, b]` is an `iSup` of shifted-and-iso-closed object properties over the
-- finite interval `Set.Icc a b`; `shift_iSup`, `isoClosure_iSup`, and `iSup_comm` commute the two
-- suprema.
/-- Remark 13.35.6 (1): shifting the union of a family through the interval `[a,b]`
equals the union of the interval shifts. -/
theorem shiftInterval_iSup (A : ι → ObjectProperty C) (a b : ℤ) :
    (⨆ i, A i)[a, b] = ⨆ i, (A i)[a, b] := by
  simp_rw [shiftInterval, shift_iSup, isoClosure_iSup]
  rw [iSup_comm]

end

section

variable {C : Type u} [Category.{v} C]
variable {ι : Sort*}

-- Proof sketch: an object is a direct summand of an object in `⨆ i, A i` exactly when it is a
-- direct summand of an object in some single stage `A i`; this rewrites the retract closure of the
-- supremum as the supremum of the retract closures.
/-- Remark 13.35.6 (2): the direct-summand closure `smd` commutes with the union of a family
`A_i`. -/
theorem retractClosure_iSup (A : ι → ObjectProperty C) :
    (⨆ i, A i).retractClosure = ⨆ i, (A i).retractClosure := by
  ext X
  constructor
  · rintro ⟨Y, hY, ⟨r⟩⟩
    rcases (prop_iSup_iff A Y).mp hY with ⟨i, hi⟩
    exact (prop_iSup_iff (fun i ↦ (A i).retractClosure) X).mpr ⟨i, prop_retractClosure hi r⟩
  · intro hX
    rcases (prop_iSup_iff (fun i ↦ (A i).retractClosure) X).mp hX with ⟨i, hX⟩
    exact monotone_retractClosure (le_iSup A i) _ hX

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [(n : ℤ) → (shiftFunctor C n).Additive] [Pretriangulated C]
variable {ι : Sort*}

-- Proof sketch: membership in an extension product with left factor `⨆ i, A i` already chooses a
-- single left object `Y`, so that object lies in some definite stage `A i`; conversely, every
-- stage maps into the supremum.
/-- Remark 13.35.6 (4): the extension product of `\bigcup A_i` with a fixed full subcategory
`\mathcal B` is the union of the extension products `A_i \star \mathcal B`. -/
theorem extensionProduct_iSup_left (A : ι → ObjectProperty C) (B : ObjectProperty C) :
    (⨆ i, A i) ⋆ B = ⨆ i, A i ⋆ B := by
  ext X
  constructor
  · intro hX
    rw [extensionProduct_iff] at hX
    rcases hX with ⟨Y, Z, f, g, h, hT, hY, hZ⟩
    rcases (prop_iSup_iff A Y).mp hY with ⟨i, hY⟩
    exact (prop_iSup_iff (fun i ↦ A i ⋆ B) X).mpr
      ⟨i, by
        rw [extensionProduct_iff]
        exact ⟨Y, Z, f, g, h, hT, hY, hZ⟩⟩
  · exact (iSup_le fun i ↦ monotone_extensionProduct_left B (le_iSup A i)) X

-- Proof sketch: the same argument as in the left-variable case, now reading the distinguished
-- triangle that defines `extensionProduct` on the right factor.
/-- Remark 13.35.6 (5): the extension product of a fixed full subcategory `\mathcal B` with
`\bigcup A_i` is the union of the extension products `\mathcal B \star A_i`. -/
theorem extensionProduct_iSup_right (B : ObjectProperty C) (A : ι → ObjectProperty C) :
    B ⋆ (⨆ i, A i) = ⨆ i, B ⋆ A i := by
  ext X
  constructor
  · intro hX
    rw [extensionProduct_iff] at hX
    rcases hX with ⟨Y, Z, f, g, h, hT, hY, hZ⟩
    rcases (prop_iSup_iff A Z).mp hZ with ⟨i, hZ⟩
    exact (prop_iSup_iff (fun i ↦ B ⋆ A i) X).mpr
      ⟨i, by
        rw [extensionProduct_iff]
        exact ⟨Y, Z, f, g, h, hT, hY, hZ⟩⟩
  · exact (iSup_le fun i ↦ monotone_extensionProduct_right B (le_iSup A i)) X

private theorem extensionProduct_iSup_of_monotone
    (A B : ℕ → ObjectProperty C) (hA : Monotone A) (hB : Monotone B) :
    (⨆ i, A i) ⋆ (⨆ i, B i) = ⨆ i, A i ⋆ B i := by
  calc
    (⨆ i, A i) ⋆ (⨆ i, B i)
        = ⨆ i, A i ⋆ (⨆ j, B j) :=
      extensionProduct_iSup_left A _
    _ = ⨆ i, ⨆ j, A i ⋆ B j := by
      simp_rw [extensionProduct_iSup_right]
    _ = ⨆ i, A i ⋆ B i := by
      apply le_antisymm
      · refine iSup_le fun i ↦ ?_
        refine iSup_le fun j ↦ ?_
        exact
          (monotone_extensionProduct_left (B j) (hA (Nat.le_max_left i j))).trans <|
            (monotone_extensionProduct_right (A (max i j))
              (hB (Nat.le_max_right i j))).trans <|
              le_iSup (fun k ↦ A k ⋆ B k) (max i j)
      · refine iSup_le fun i ↦ ?_
        exact
          (le_iSup (fun j ↦ A i ⋆ B j) i).trans <|
            le_iSup (fun j ↦ ⨆ k, A j ⋆ B k) i

-- Proof sketch: prove the statement by induction on `n`. Each `⋆`-step involves only finitely
-- many stages of the chain, and monotonicity replaces those finitely many indices by one larger
-- index.
/-- Remark 13.35.6 (6): for an increasing family `A_i`, the `n`-fold extension product of the
union, written source-faithfully as `(\bigcup A_i)^{\star n}`, equals the union of the
`n`-fold extension products `A_i^{\star n}`. -/
theorem extensionProductIter_iSup_of_monotone (A : ℕ → ObjectProperty C) (hA : Monotone A)
    (n : ℕ) :
    (⨆ i, A i).extensionProductIter n = ⨆ i, (A i).extensionProductIter n := by
  induction n with
  | zero =>
      simp
  | succ n hn =>
      let B : ℕ → ObjectProperty C := fun i ↦ (A i).extensionProductIter n
      have hB : Monotone B := by
        intro i j hij
        exact monotone_extensionProductIter (hA hij) n
      rw [extensionProductIter_succ, hn]
      simpa [B, extensionProductIter_succ] using extensionProduct_iSup_of_monotone A B hA hB

end

end CategoryTheory.ObjectProperty
