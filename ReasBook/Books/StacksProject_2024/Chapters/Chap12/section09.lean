import Mathlib
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Noetherian
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_9_1 (from Chap12) -/
namespace CategoryTheory

universe v u

/- Domain triage:
- primary domain: simple objects in an abelian category, using the canonical owner that already
  lives in the broader zero-morphism setting.
- `source-facing`: the textbook predicate that an object is simple.
- `core/canonical`: `Simple X`.
- `bridge/view`: `simple_iff_subobject_isSimpleOrder`.
- Primitive data vs derived API: `Simple` is the primitive owner predicate; the subobject-lattice
  characterization is derived API.
-/

section

variable {C : Type u} [Category.{v} C] [Abelian C] (X : C)

/- Definition 12.9.1: a simple object of an abelian category is the canonical mathlib predicate
`Simple X`; this packages that the object is nonzero and has only the trivial subobjects. -/
#check Simple X

/- Companion recall: `simple_iff_subobject_isSimpleOrder` is the canonical subobject-lattice
characterization of simplicity. -/
recall simple_iff_subobject_isSimpleOrder

end

end CategoryTheory

/-! ### Definition_12_9_2 (from Chap12) -/
universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Definition 12.9.2:
- primary domain: Artinian objects and the resulting objectwise notion of an Artinian category;
- sampled owner-level declarations:
  `isArtinianObject`,
  `IsArtinianObject`,
  `isArtinianObject_iff_antitone_chain_condition`,
  `Artinian`;
- best owner abstraction: the canonical object property `isArtinianObject : ObjectProperty C`;
- primitive data: the owner object property `isArtinianObject`;
- derived API: the pointwise predicate `IsArtinianObject X`, the antitone-chain characterization
  `isArtinianObject_iff_antitone_chain_condition`, and the stronger bundled class `Artinian`.

Source/core/bridge triage:
- `source-facing`: the textbook clause that an object `X` is Artinian, and the textbook condition
  that a category is Artinian iff `∀ X : C, IsArtinianObject X`;
- `core/canonical`: `isArtinianObject`, `IsArtinianObject`;
- `bridge/view`: the characterization theorem
  `isArtinianObject_iff_antitone_chain_condition`, and the stronger bundled class `Artinian`
  whose field `Artinian.isArtinianObject` implies the source-facing category condition.
-/

/- Definition 12.9.2 (1): the owner abstraction for Artinian objects is the canonical object
property `isArtinianObject`, whose values are the Artinian objects of `C`. -/
recall isArtinianObject : ObjectProperty C

/- Companion recall: for a specific object `X`, the textbook predicate that `X` is Artinian is the
canonical proposition `IsArtinianObject X`. -/
recall IsArtinianObject

/- Companion recall: the descending-chain formulation of an Artinian object is the canonical theorem
`isArtinianObject_iff_antitone_chain_condition`. -/
recall isArtinianObject_iff_antitone_chain_condition

/- Definition 12.9.2 (2): a category is Artinian in the textbook sense exactly when every object
is Artinian, i.e. when the proposition `∀ X : C, IsArtinianObject X` holds. Unlike the stronger
bundled owner class `Artinian`, this source-facing condition does not also package essential
smallness. -/
#check ∀ X : C, IsArtinianObject X

/- Companion recall: mathlib's canonical class `Artinian` packages the stronger
notion that `C` is essentially small and every object of `C` is Artinian. -/
recall Artinian

/- Bridge recall: the field `Artinian.isArtinianObject` recovers the source-facing objectwise
Artinian condition from the stronger bundled class `Artinian`. -/
recall Artinian.isArtinianObject

end CategoryTheory

/-! ### Definition_12_9_3 (from Chap12) -/
universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Definition 12.9.3:
- primary domain: Noetherian objects and the resulting objectwise notion of a Noetherian category;
- sampled owner-level declarations:
  `isNoetherianObject`,
  `IsNoetherianObject`,
  `isNoetherianObject_iff_monotone_chain_condition`,
  `Noetherian`;
- best owner abstraction: the canonical object property
  `isNoetherianObject : ObjectProperty C`;
- primitive data: the owner object property `isNoetherianObject`;
- derived API: the pointwise predicate `IsNoetherianObject X`, the monotone-chain
  characterization `isNoetherianObject_iff_monotone_chain_condition`, and the stronger bundled
  class `Noetherian`.

Source/core/bridge triage:
- `source-facing`: the textbook clause that an object `X` is Noetherian, and the textbook
  condition that a category is Noetherian iff `∀ X : C, IsNoetherianObject X`;
- `core/canonical`: `isNoetherianObject`, `IsNoetherianObject`;
- `bridge/view`: the characterization theorem
  `isNoetherianObject_iff_monotone_chain_condition`, and the stronger bundled class
  `Noetherian` whose field `Noetherian.isNoetherianObject` implies the source-facing category
  condition.
-/

/- Definition 12.9.3: the owner abstraction for Noetherian objects is the canonical object
property `CategoryTheory.isNoetherianObject`, whose values are the Noetherian objects of `C`. -/
recall CategoryTheory.isNoetherianObject : ObjectProperty C

/- Companion recall: for a specific object `X`, the textbook predicate that `X` is Noetherian is
the canonical proposition `CategoryTheory.IsNoetherianObject X`. -/
recall IsNoetherianObject

/- Companion recall: the ascending-chain formulation of a Noetherian object is the canonical theorem
`CategoryTheory.isNoetherianObject_iff_monotone_chain_condition`. -/
recall isNoetherianObject_iff_monotone_chain_condition

/- Definition 12.9.3: a category is Noetherian in the textbook sense exactly when every object
is Noetherian, i.e. when the proposition `∀ X : C, IsNoetherianObject X` holds. Unlike the
stronger bundled owner class `Noetherian`, this source-facing condition does not also package
essential smallness. -/
#check ∀ X : C, IsNoetherianObject X

/-
Companion recall: mathlib's canonical class `CategoryTheory.Noetherian` packages the stronger
notion that `C` is essentially small and every object of `C` is Noetherian.
-/
recall Noetherian

/- Bridge recall: the field `Noetherian.isNoetherianObject` recovers the source-facing objectwise
Noetherian condition from the stronger bundled class `Noetherian`. -/
#check Noetherian.isNoetherianObject

end CategoryTheory

/-! ### Lemma_12_9_4 (from Chap12) -/
universe v u

namespace CategoryTheory

open Opposite

/-
Domain-style sampling for Lemma 12.9.4:
- primary domain: object properties in an abelian category, with Artinian and Noetherian
  conditions organized via the owner API `ObjectProperty`;
- inspected owner declarations:
  `isArtinianObject`,
  `isNoetherianObject`,
  `ObjectProperty.IsSerreClass`,
  `ObjectProperty.prop_iff_of_shortExact`;
- best owner abstraction: the object property `isArtinianObject : ObjectProperty C` together with
  the LinearRepresentations_Serre_1977-class owner interface;
- primitive data: only the Artinian object property itself and the short exact sequence;
- derived API: the LinearRepresentations_Serre_1977-class instance and the short-exact characterization obtained from
  `ObjectProperty.prop_iff_of_shortExact`.

Source/core/bridge triage:
- `source-facing`: the textbook statements that Artinian objects are closed under short exact
  sequences;
- `core/canonical`: `isArtinianObject : ObjectProperty C` and the owner theorem
  `ObjectProperty.prop_iff_of_shortExact`;
- `bridge/view`: the Artinian/Noetherian-op duality theorem below, which is the minimal bridge
  needed because mathlib does not yet provide this owner result.
-/

private theorem wellFoundedGT_subobject_iff_wellFoundedLT_subobject_op {C : Type u}
    [Category.{v} C] [Abelian C] (A : C) :
    WellFoundedGT (Subobject A) ↔ WellFoundedLT (Subobject (op A)) := by
  constructor
  · intro hA
    letI : WellFoundedGT (Subobject A) := hA
    letI : WellFoundedGT ((Subobject (op A))ᵒᵈ) :=
      (Abelian.subobjectIsoSubobjectOp A).symm.toOrderEmbedding.wellFoundedGT
    exact (wellFoundedGT_dual_iff (Subobject (op A))).1 inferInstance
  · intro hA
    letI : WellFoundedLT (Subobject (op A)) := hA
    letI : WellFoundedGT ((Subobject (op A))ᵒᵈ) := inferInstance
    exact (Abelian.subobjectIsoSubobjectOp A).toOrderEmbedding.wellFoundedGT

private theorem wellFoundedLT_subobject_iff_wellFoundedGT_subobject_op {C : Type u}
    [Category.{v} C] [Abelian C] (A : C) :
    WellFoundedLT (Subobject A) ↔ WellFoundedGT (Subobject (op A)) := by
  constructor
  · intro hA
    letI : WellFoundedLT (Subobject A) := hA
    letI : WellFoundedLT ((Subobject (op A))ᵒᵈ) :=
      (Abelian.subobjectIsoSubobjectOp A).symm.toOrderEmbedding.wellFoundedLT
    exact (wellFoundedGT_dual_iff ((Subobject (op A))ᵒᵈ)).1 inferInstance
  · intro hA
    letI : WellFoundedGT (Subobject (op A)) := hA
    have : WellFoundedLT ((Subobject (op A))ᵒᵈ) :=
      (wellFoundedGT_dual_iff ((Subobject (op A))ᵒᵈ)).1 inferInstance
    letI : WellFoundedLT (Subobject A) :=
      (Abelian.subobjectIsoSubobjectOp A).toOrderEmbedding.wellFoundedLT
    exact inferInstance

theorem isNoetherianObject_iff_isArtinianObject_op {C : Type u} [Category.{v} C]
    [Abelian C] (A : C) :
    IsNoetherianObject A ↔ IsArtinianObject (op A) := by
  simpa [IsNoetherianObject, ObjectProperty.is_iff, IsArtinianObject] using
    wellFoundedGT_subobject_iff_wellFoundedLT_subobject_op A

theorem isArtinianObject_iff_isNoetherianObject_op {C : Type u} [Category.{v} C]
    [Abelian C] (A : C) :
    IsArtinianObject A ↔ IsNoetherianObject (op A) := by
  simpa [IsArtinianObject, ObjectProperty.is_iff, IsNoetherianObject] using
    wellFoundedLT_subobject_iff_wellFoundedGT_subobject_op A

/-- Lemma 12.9.4 owner abstraction: in an abelian category, Artinian objects form a LinearRepresentations_Serre_1977
class. -/
instance isArtinianObject_isSerreClass {C : Type u} [Category.{v} C] [Abelian C] :
    (isArtinianObject : ObjectProperty C).IsSerreClass where
  exists_zero := ObjectProperty.ContainsZero.exists_zero
  prop_of_mono f _ hX := isArtinianObject.prop_of_mono f hX
  prop_of_epi {X} {Y} f _ hX := by
    rw [← isArtinianObject.is_iff] at hX ⊢
    letI : IsNoetherianObject (op X) :=
      (isArtinianObject_iff_isNoetherianObject_op X).mp hX
    exact (isArtinianObject_iff_isNoetherianObject_op Y).mpr
      (isNoetherianObject_of_mono f.op)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [← isArtinianObject.is_iff] at h₁ h₃ ⊢
    sorry

namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C}

/-- Lemma 12.9.4: in a short exact sequence in an abelian category, the middle object is
Artinian if and only if the left and right objects are Artinian. -/
-- Proof sketch: the owner abstraction is the object property `isArtinianObject`. Once this
-- property is known to form a LinearRepresentations_Serre_1977 class, the statement is the canonical owner theorem
-- `ObjectProperty.prop_iff_of_shortExact`.
lemma isArtinianObject_iff_of_shortExact (hS : S.ShortExact) :
    IsArtinianObject S.X₂ ↔ IsArtinianObject S.X₁ ∧ IsArtinianObject S.X₃ := by
  simpa [IsArtinianObject, ObjectProperty.is_iff] using
    isArtinianObject.prop_iff_of_shortExact hS

end ShortComplex
end CategoryTheory

/-! ### Lemma_12_9_5 (from Chap12) -/
universe v u

namespace CategoryTheory

open Opposite

/-
Domain-style sampling for Lemma 12.9.5:
- primary domain: object properties in an abelian category, with Noetherian objects organized by
  the owner predicate `isNoetherianObject : ObjectProperty C`;
- inspected owner declarations:
  `isNoetherianObject`,
  `ObjectProperty.IsSerreClass`,
  `ObjectProperty.prop_iff_of_shortExact`,
  `ShortComplex.ShortExact.op`,
  `ShortComplex.isArtinianObject_iff_of_shortExact`;
- best owner abstraction: the object property `isNoetherianObject` together with the LinearRepresentations_Serre_1977-class
  owner interface;
- primitive data: a short exact sequence in `C`, together with the canonical opposite short
  complex in `Cᵒᵖ`;
- derived API: the LinearRepresentations_Serre_1977-class instance and the short-exact characterization obtained from
  `ObjectProperty.prop_iff_of_shortExact`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that Noetherian objects are stable in short exact
  sequences;
- `core/canonical`: `isNoetherianObject : ObjectProperty C` and the owner theorem
  `ObjectProperty.prop_iff_of_shortExact`;
- `bridge/view`: the imported duality bridge `isNoetherianObject_iff_isArtinianObject_op` from
  Lemma 12.9.4 together with the canonical opposite short complex `S.op`.
-/

section

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem isNoetherianObject_iff_of_shortExact_aux {S : ShortComplex C} (hS : S.ShortExact) :
    IsNoetherianObject S.X₂ ↔ IsNoetherianObject S.X₁ ∧ IsNoetherianObject S.X₃ := by
  constructor
  · intro h₂
    have h₂' : IsArtinianObject (Opposite.op S.X₂) :=
      (isNoetherianObject_iff_isArtinianObject_op S.X₂).mp h₂
    have hOp := (ShortComplex.isArtinianObject_iff_of_shortExact hS.op).mp h₂'
    exact ⟨
      (isNoetherianObject_iff_isArtinianObject_op S.X₁).mpr (by simpa using hOp.2),
      (isNoetherianObject_iff_isArtinianObject_op S.X₃).mpr (by simpa using hOp.1)⟩
  · rintro ⟨h₁, h₃⟩
    have h₁' : IsArtinianObject (Opposite.op S.X₁) :=
      (isNoetherianObject_iff_isArtinianObject_op S.X₁).mp h₁
    have h₃' : IsArtinianObject (Opposite.op S.X₃) :=
      (isNoetherianObject_iff_isArtinianObject_op S.X₃).mp h₃
    exact (isNoetherianObject_iff_isArtinianObject_op S.X₂).mpr <|
      (ShortComplex.isArtinianObject_iff_of_shortExact hS.op).mpr ⟨h₃', h₁'⟩

/-- Lemma 12.9.5 owner abstraction: in an abelian category, Noetherian objects form a LinearRepresentations_Serre_1977
class. -/
instance isNoetherianObject_isSerreClass :
    (isNoetherianObject : ObjectProperty C).IsSerreClass where
  exists_zero := ObjectProperty.ContainsZero.exists_zero
  prop_of_mono f _ hX := isNoetherianObject.prop_of_mono f hX
  prop_of_epi {X} {Y} f _ hX := by
    rw [← isNoetherianObject.is_iff] at hX ⊢
    letI : IsArtinianObject (Opposite.op X) :=
      (isNoetherianObject_iff_isArtinianObject_op X).mp hX
    exact (isNoetherianObject_iff_isArtinianObject_op Y).mpr
      (isArtinianObject_of_mono f.op)
  prop_X₂_of_shortExact hS h₁ h₃ := by
    rw [← isNoetherianObject.is_iff] at h₁ h₃ ⊢
    exact (isNoetherianObject_iff_of_shortExact_aux hS).mpr ⟨h₁, h₃⟩

namespace ShortComplex

variable {S : ShortComplex C}

/-- Lemma 12.9.5: in a short exact sequence in an abelian category, the middle object is
Noetherian if and only if the left and right objects are Noetherian. -/
lemma isNoetherianObject_iff_of_shortExact (hS : S.ShortExact) :
    IsNoetherianObject S.X₂ ↔ IsNoetherianObject S.X₁ ∧ IsNoetherianObject S.X₃ := by
  simpa [IsNoetherianObject, ObjectProperty.is_iff] using
    isNoetherianObject.prop_iff_of_shortExact hS

end ShortComplex

end
end CategoryTheory

/-! ### Lemma_12_9_6 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Subobject

variable {A : C}

/- Domain triage:
- primary domain: Jordan-Hölder theory for the subobject lattice of an object in an abelian
  category;
- sampled owner API:
  `JordanHolderLattice`,
  `CompositionSeries.jordan_holder`,
  `JordanHolderModule.instJordanHolderLattice`,
  `subobjectSubquotient`;
- `core/canonical`: the ambient owner is `JordanHolderLattice (Subobject A)`;
- `bridge/view`: `iso_iff_nonempty_subobjectSubquotient_iso` and `CompositionSeries.factor`
  translate the generic Jordan-Hölder owner back to canonical subquotients `Y / X`.
-/

-- Proof sketch: a cover `X ⋖ Y` means the interval `[X, Y]` has exactly two points, and in an
-- abelian category the subobjects of the canonical subquotient `Y / X` correspond to this
-- interval. Hence the quotient is simple.
private theorem simple_subobjectSubquotient_of_covBy {X Y : Subobject A} (h : X ⋖ Y) :
    Simple (subobjectSubquotient (CovBy.le h)) := sorry

-- Proof sketch: this is the second isomorphism theorem for subquotients in an abelian category.
private theorem subquotient_sup_iso_subquotient_inf (X Y : Subobject A) :
    Nonempty (subobjectSubquotient (show X ≤ X ⊔ Y from _root_.le_sup_left) ≅
      subobjectSubquotient (show X ⊓ Y ≤ Y from _root_.inf_le_right)) := sorry

open scoped Classical in
/-- The Jordan-Hölder lattice structure on the subobject lattice of an object in an abelian
category, with factors given by canonical subquotients. -/
instance : JordanHolderLattice (Subobject A) where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal := CovBy.lt
  sup_eq_of_isMaximal hxz hyz := WCovBy.sup_eq hxz.wcovBy hyz.wcovBy
  isMaximal_inf_left_of_isMaximal_sup := by
    intro X Y hX hY
    sorry
  Iso X Y := Nonempty
    (subobjectSubquotient (show X.1 ⊓ X.2 ≤ X.2 from _root_.inf_le_right) ≅
      subobjectSubquotient (show Y.1 ⊓ Y.2 ≤ Y.2 from _root_.inf_le_right))
  iso_symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
  iso_trans := fun ⟨e₁⟩ ⟨e₂⟩ ↦ ⟨e₁.trans e₂⟩
  second_iso := by
    intro X Y h
    simpa [inf_eq_left.2 (_root_.le_sup_left : X ≤ X ⊔ Y), inf_assoc] using
      subquotient_sup_iso_subquotient_inf X Y

/-- For comparable pairs of subobjects, the `Iso` relation in the Jordan-Hölder lattice structure
is exactly isomorphism of the canonical subquotients. -/
theorem iso_iff_nonempty_subobjectSubquotient_iso {X₁ X₂ Y₁ Y₂ : Subobject A}
    (hX : X₁ ≤ X₂) (hY : Y₁ ≤ Y₂) :
    JordanHolderLattice.Iso (X₁, X₂) (Y₁, Y₂) ↔
      Nonempty (subobjectSubquotient hX ≅ subobjectSubquotient hY) := by
  change Nonempty
      (subobjectSubquotient (show X₁ ⊓ X₂ ≤ X₂ from _root_.inf_le_right) ≅
        subobjectSubquotient (show Y₁ ⊓ Y₂ ≤ Y₂ from _root_.inf_le_right)) ↔
    Nonempty (subobjectSubquotient hX ≅ subobjectSubquotient hY)
  simp [inf_eq_left.2 hX, inf_eq_left.2 hY]

end Subobject

end CategoryTheory

namespace CompositionSeries

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/-- The `i`-th successive canonical subquotient in a composition series of subobjects. -/
noncomputable abbrev factor (s : CompositionSeries (Subobject A)) (i : Fin s.length) :=
  subobjectSubquotient (s.step i).le

-- Proof sketch: apply `Subobject.simple_subobjectSubquotient_of_covBy` to the `i`-th cover
-- relation.
/-- Each successive canonical subquotient `s (i + 1) / s i` of a composition series in
`Subobject A` is simple. -/
theorem factor_simple (s : CompositionSeries (Subobject A)) (i : Fin s.length) :
    Simple (s.factor i) := by
  simpa using Subobject.simple_subobjectSubquotient_of_covBy (s.step i)

end CompositionSeries

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

-- This is the exact order-theoretic owner construction used for finite-length modules, applied to
-- the well-founded subobject lattice of an Artinian and Noetherian object.
/-- If an object in an abelian category is Artinian and Noetherian, then its subobject lattice
admits a composition series from `0` to the whole object. -/
theorem exists_compositionSeries_of_isArtinianObject_isNoetherianObject (A : C)
    [IsArtinianObject A] [IsNoetherianObject A] :
    ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Subobject A)
  exact ⟨⟨n, fun i ↦ f i, fun i ↦ hn.2 i i.2⟩, f0.eq_bot, hn.1.eq_top⟩

-- Proof sketch: if `A` is Artinian and Noetherian, refine a maximal strict chain in `Subobject A`
-- from `⊥` to `⊤` into a composition series. Conversely, such a composition series bounds strict
-- ascending and descending chains of subobjects.
/-- Lemma 12.9.6: an object of an abelian category is Artinian and Noetherian if and only if it
admits a composition series of subobjects from `0` to itself. -/
lemma isArtinianObject_and_isNoetherianObject_iff_exists_compositionSeries (A : C) :
    (IsArtinianObject A ∧ IsNoetherianObject A) ↔
      ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := by
  constructor
  · rintro ⟨hArtinian, hNoetherian⟩
    letI : IsArtinianObject A := hArtinian
    letI : IsNoetherianObject A := hNoetherian
    exact exists_compositionSeries_of_isArtinianObject_isNoetherianObject A
  · sorry

end CategoryTheory

/-! ### Lemma_12_9_7_Jordan_H_lder (from Chap12) -/
open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/- Domain triage:
- primary domain: Jordan-Hölder theory for composition series in the subobject lattice of an
  object of an abelian category;
- sampled owner API:
  `CompositionSeries.jordan_holder`,
  `CompositionSeries.Equivalent`,
  `Subobject.iso_iff_nonempty_subobjectSubquotient_iso`,
  `CompositionSeries.factor`;
- `source-facing`: the factors of two composition series from `0` to `A` agree up to permutation
  and isomorphism;
- `core/canonical`: `CompositionSeries.jordan_holder`;
- `bridge/view`: `Subobject.iso_iff_nonempty_subobjectSubquotient_iso` translates the owner
  `Equivalent` relation into isomorphisms between the canonical factor objects `s.factor i`;
- primitive data vs derived API: the Jordan-Hölder equivalence relation on composition series is
  primitive owner output, while the factorwise isomorphism statement is derived bridge API.
-/

/- Lemma 12.9.7 (Jordan-Hölder): for composition series in the Jordan-Hölder lattice
`Subobject A`, the canonical owner theorem is `CompositionSeries.jordan_holder`. -/
recall CompositionSeries.jordan_holder

end CategoryTheory

namespace CompositionSeries

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

-- Proof sketch: unpack the owner theorem `CompositionSeries.jordan_holder` and use the owner
-- `Iso` relation on `Subobject A`, which is defined by isomorphism of the canonical factors.
/-- Companion form of Jordan-Hölder: the factors of two composition series from `0` to `A` agree
up to a permutation and isomorphism. -/
theorem jordan_holder_factors
    (F G : CompositionSeries (Subobject A))
    (hF₀ : F.head = ⊥) (hF₁ : F.last = ⊤) (hG₀ : G.head = ⊥) (hG₁ : G.last = ⊤)
    : ∃ σ : Fin F.length ≃ Fin G.length,
        ∀ i : Fin F.length,
          Nonempty (F.factor i ≅ G.factor (σ i)) := by
  obtain ⟨σ, hσ⟩ := F.jordan_holder G (hF₀.trans hG₀.symm) (hF₁.trans hG₁.symm)
  refine ⟨σ, fun i ↦ ?_⟩
  simpa [factor] using
    (Subobject.iso_iff_nonempty_subobjectSubquotient_iso
      (F.step i).le (G.step (σ i)).le).1 (hσ i)

end CompositionSeries
