import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_27_1 (from Chap13) -/
namespace CategoryTheory

scoped[DerivedExt] notation:max "Ext^" n "(" X ", " Y ")" =>
  CategoryTheory.ShiftedHom X Y n

end CategoryTheory

open CategoryTheory
open CategoryTheory.Abelian
open scoped DerivedExt

universe w' w v u

/- Domain-style sampling for Ext groups:
- primary domain: shifted morphism groups in derived categories and their specialization to
  objects of an abelian category;
- sampled owner declarations:
  `ShiftedHom`,
  `ShiftedHom.homEquiv`,
  `Ext`,
  `Ext.homEquiv`;
- best owner abstraction: for `X Y : D(𝒜)` the source-facing surface is `Ext^i(X, Y)`, whose core
  owner is `ShiftedHom X Y i`; for `A B : 𝒜` the canonical object-level bridge is `Ext A B n`,
  together with `Ext.homEquiv`;
- primitive data: a pair of objects in the derived category and a shift degree;
- derived API: the specialization to objects of `𝒜` via the degree-zero single-complex
  embedding.

Source/core/bridge triage:
- `source-facing`: the Stacks definition `Ext^i_𝒜(X, Y)`, written as `Ext^i(X, Y)`
- `core/canonical`: `ShiftedHom X Y i`
- `bridge/view`: `Ext` and `Ext.homEquiv`

No new alias or wrapper is needed here: `Ext^i(X, Y)` is only notation for the canonical owner
`ShiftedHom X Y i`, and the chapter-level `Ext` on objects of `𝒜` is already owned by `Ext`.
-/

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜]
variable (X Y : DerivedCategory 𝒜) (i : ℤ)

/- Definition 13.27.1: for objects `X Y : D(𝒜)`, the `i`-th extension group is written
`Ext^i(X, Y)`; this is exactly the canonical owner `ShiftedHom X Y i`, so by definition it is
`X ⟶ Y⟦i⟧`, and via the shift equivalence it may equally be read as morphisms `X[-i] ⟶ Y`. -/
#check Ext^i(X, Y)

/- Underlying core owner. -/
recall ShiftedHom

end

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜] [HasExt.{w} 𝒜]
variable (A B : 𝒜) (n : ℕ)

/- For objects of the abelian category itself, the canonical owner is
`Ext`, which is already the specialization of derived `Ext^(n : ℤ)(-, -)` to the
single complexes `A[0]` and `B[0]`. -/
recall Ext

/- Companion bridge: `Ext.homEquiv` is the exact owner theorem identifying
`Ext A B n` with the derived extension group
`Ext^(n : ℤ)(((singleFunctor 𝒜 0).obj A), ((singleFunctor 𝒜 0).obj B))`. -/
recall Ext.homEquiv

end

/-! ### Lemma_13_27_2 (from Chap13) -/
open CategoryTheory ComplexShape DerivedCategory HomotopyCategory
open scoped DerivedExt

noncomputable section

universe v u

namespace CochainComplex

section

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling for Lemma 13.27.2:
- primary domain: morphisms in the derived category of cochain complexes, computed from
  K-injective and K-projective resolutions;
- sampled owner API:
  `CategoryTheory.Abelian.Ext.homAddEquiv`,
  `DerivedCategory.Q.commShiftIso`,
  `DerivedCategory.Qh.mapAddHom`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedBelow_injective`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective`,
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.ProjectiveResolution`;
- best owner abstraction: the canonical quotient functors
  `HomotopyCategory.quotient 𝒜 (up ℤ)` and `DerivedCategory.Qh`, together with their shift
  compatibilities and the chapter owner bijectivity theorems for bounded-below injective and
  bounded-above projective complexes;
- primitive data: a chosen injective or projective resolution;
- derived API: the owner-level shifted-Hom comparison equivalences
  `InjectiveResolution.extAddEquiv` and `ProjectiveResolution.extAddEquiv`.

Source/core/bridge triage:
- `source-facing`: the Ext-computation statements with a chosen injective or projective
  resolution;
- `core/canonical`: `Q.commShiftIso`, `quotientCompQhIso`, and the owner bijectivity theorems
  for `Qh.mapAddHom`;
- `bridge/view`: the owner-level equivalences below transporting raw Hom-types to `ShiftedHom`.

The local raw-Hom helper abbreviations were duplicate shells around this owner API, so the file
should expose only the source-facing additive bridge equivalences on the chosen resolution owners.
-/

private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) where
  toEquiv := α.homCongr β
  map_add' := by
    intro f g
    simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

namespace InjectiveResolution

variable {Y : CochainComplex 𝒜 ℤ}

/-- Lemma 13.27.2 (1): if `Y^• ⟶ I^•` is an injective resolution, then
`Ext^i_{\mathcal A}(X^•, Y^•)` is computed by the shifted homotopy-category morphisms
`Hom_{K(\mathcal A)}(X^•, I^•[i])` as an additive equivalence. -/
noncomputable def extAddEquiv (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ) :
    Ext^i(Q.obj X, Q.obj Y) ≃+ Ext^i((KQ).obj X, (KQ).obj I) :=
  (isoHomCongrAddEquiv (Iso.refl _) ((Q.commShiftIso i).app Y).symm).trans
    ((isoHomCongrAddEquiv (Iso.refl _) (asIso (Q.map (I.ι⟦i⟧')))).trans
      ((AddEquiv.ofBijective
          (Qh.mapAddHom : ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) →+ _)
          (show Function.Bijective (Qh.map : ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) → _) from
            IsKInjective.Qh_map_bijective ((KQ).obj X) (I⟦i⟧))).symm.trans
        (isoHomCongrAddEquiv (Iso.refl _) (((quotient 𝒜 (up ℤ)).commShiftIso i).app I))))

end InjectiveResolution

namespace ProjectiveResolution

variable {X : CochainComplex 𝒜 ℤ}

/-- Lemma 13.27.2 (2): if `P^• ⟶ X^•` is a projective resolution, then
`Ext^i_{\mathcal A}(X^•, Y^•)` is computed by the shifted homotopy-category morphisms out of
`P^•`, equivalently by `Hom_{K(\mathcal A)}(P^•[-i], Y^•)`, as an additive equivalence. -/
noncomputable def extAddEquiv (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ) (i : ℤ) :
    Ext^i(Q.obj X, Q.obj Y) ≃+ Ext^i((KQ).obj P, (KQ).obj Y) :=
  (isoHomCongrAddEquiv (Iso.refl _) ((Q.commShiftIso i).app Y).symm).trans
    ((isoHomCongrAddEquiv (asIso (Q.map P.π)).symm (Iso.refl _)).trans
      ((AddEquiv.ofBijective
          (Qh.mapAddHom : ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) →+ _)
          (homotopyCategory_to_derived_bijective_of_boundedAbove_projective P (Y⟦i⟧))).symm.trans
        (isoHomCongrAddEquiv (Iso.refl _) (((quotient 𝒜 (up ℤ)).commShiftIso i).app Y))))

end ProjectiveResolution

end

end CochainComplex

/-! ### Lemma_13_27_3 (from Chap13) -/
noncomputable section

universe u v

namespace CategoryTheory

universe w

open DerivedCategory
open Triangulated
open Abelian.Ext
open scoped DerivedExt

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => homologyFunctor 𝒜
local notation "single₀" => singleFunctor 𝒜 0

/- Domain-style sampling for Lemma 13.27.3:
- primary domain: morphisms in `D(𝒜)` controlled by the canonical `t`-structure and the
  cohomology functors `H^n`;
- sampled owner declarations:
  `DerivedCategory.IsLE`,
  `DerivedCategory.IsGE`,
  `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`,
  `Abelian.Ext.homEquiv`,
  `Abelian.Ext.homEquiv₀`;
- best owner abstraction: the boundedness hypotheses belong to the canonical owners `X.IsLE a`
  and `Y.IsGE b`; the degree-`b - a` comparison is a source-facing bridge from `Ext^(b - a)(X, Y)`
  to `Hom(H^a(X), H^b(Y))`; and the single-object degree-zero clause should reuse the chapter
  owner `Abelian.Ext.homEquiv₀`, reached from the derived-side notation through
  `Abelian.Ext.homEquiv`, rather than rebuilding that identification locally;
- primitive data: objects `X Y : D(𝒜)`, bounds `a b : ℤ`, and the owner hypotheses
  `X.IsLE a`, `Y.IsGE b`;
- derived API: vanishing below `b - a`, the canonical comparison map in degree `b - a`, and the
  single-object special case.

Source/core/bridge triage:
- `source-facing`: the vanishing and comparison statements for `Ext^n(X, Y)` and their
  single-object corollaries;
- `core/canonical`: `DerivedCategory.IsLE`, `DerivedCategory.IsGE`, and
  `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`;
- `bridge/view`: the degree-`b - a` comparison map `shiftedHomToHomologyMap` and the degree-zero
  transport from derived `Ext^0` to `Abelian.Ext B A 0`, followed by `Abelian.Ext.homEquiv₀`.
-/

/-- The canonical degree-`b - a` comparison map
`Ext^(b - a)(X, Y) → Hom(H^a(X), H^b(Y))`. -/
noncomputable def shiftedHomToHomologyMap
    (X Y : DerivedCategory 𝒜) (a b : ℤ) :
    Ext^(b - a)(X, Y) → ((H a).obj X ⟶ (H b).obj Y) :=
  fun f ↦ (H 0).shiftMap f a b (sub_add_cancel b a)

/-- Lemma 13.27.3 (1), vanishing clause: if `X` has no cohomology above degree `a` and `Y` has
no cohomology below degree `b`, then `Ext^n(X, Y)` vanishes for `n < b - a`. -/
theorem shiftedHom_subsingleton_of_lt_sub
    (X Y : DerivedCategory 𝒜) (a b n : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b) (hn : n < b - a) :
    Subsingleton (Ext^n(X, Y)) := by
  letI := hX
  letI := hY
  have hshift : (Y⟦n⟧).IsGE (a + 1) := by
    have hbn : (Y⟦n⟧).IsGE (b - n) := by
      simpa using
        (TStructure.t.isGE_shift Y b n (b - n) (by omega) :
          TStructure.t.IsGE (Y⟦n⟧) (b - n))
    exact TStructure.t.isGE_of_ge (Y⟦n⟧) (a + 1) (b - n) (by omega)
  refine ⟨fun f g ↦ by
    rw [TStructure.t.zero_of_isLE_of_isGE f a (a + 1) (by omega) hX hshift,
      TStructure.t.zero_of_isLE_of_isGE g a (a + 1) (by omega) hX hshift]⟩

/-- Lemma 13.27.3 (1), comparison clause: under the same hypotheses, the canonical degree
`b - a` comparison map is bijective. -/
theorem shiftedHomToHomologyMap_bijective
    (X Y : DerivedCategory 𝒜) (a b : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b) :
    Function.Bijective (shiftedHomToHomologyMap X Y a b) := by
  sorry

/- Lemma 13.27.3 (1), owner form: in degree `b - a`, the canonical comparison identifies
`Ext^(b - a)(X, Y)` with `Hom(H^a(X), H^b(Y))`; this is the equivalence attached to the
preceding bijectivity theorem, so no extra wrapper declaration is needed. -/
section

variable (X Y : DerivedCategory 𝒜) (a b : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b)

#check (Equiv.ofBijective (shiftedHomToHomologyMap X Y a b)
  (shiftedHomToHomologyMap_bijective X Y a b hX hY) :
    Ext^(b - a)(X, Y) ≃ ((H a).obj X ⟶ (H b).obj Y))

end

/-- Lemma 13.27.3 (2), negative-degree clause for objects of `𝒜`: for `i < 0`, the derived
extension group from `B[0]` to `A[0]` vanishes. -/
theorem single_shiftedHom_subsingleton_of_lt_zero
    (B A : 𝒜) (i : ℤ) (hi : i < 0) :
    Subsingleton (Ext^i((single₀).obj B, (single₀).obj A)) := by
  simpa using
    shiftedHom_subsingleton_of_lt_sub ((single₀).obj B) ((single₀).obj A)
      0 0 i inferInstance inferInstance (by simpa using hi)

section

local instance : HasExt.{w} 𝒜 := hasExt_of_hasDerivedCategory 𝒜

/- Lemma 13.27.3 (2), degree-zero clause for objects of `𝒜`: the degree-zero derived extension
group from `B[0]` to `A[0]` identifies canonically with `Hom(B, A)`. This is exactly the
composite of the canonical owner equivalences `Abelian.Ext.homEquiv` and
`Abelian.Ext.homEquiv₀`, so the file should expose that composite directly rather than a
parallel local alias. -/
variable (B A : 𝒜)

#check (((homEquiv : Abelian.Ext B A 0 ≃
    Ext^((0 : ℤ))((single₀).obj B, (single₀).obj A)).symm).trans homEquiv₀ :
  Ext^((0 : ℤ))((single₀).obj B, (single₀).obj A) ≃ (B ⟶ A))

end

end CategoryTheory

/-! ### Definition_13_27_4 (from Chap13) -/
namespace CategoryTheory

universe v u

section

open Limits ComposableArrows

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/- Domain-style sampling for Definition 13.27.4:
- primary domain: finite exact composable chains with fixed endpoints and endpoint mono/epi
  conditions, indexed by the actual Yoneda degree;
- inspected owner declarations:
  `ObjectProperty.FullSubcategory`,
  `ComposableArrows`,
  `ComposableArrows.Exact`,
  `ComposableArrows.Exact.sc`,
  `Extension`;
- source/core/bridge triage:
  `source-facing`: `YonedaExtension A B n`;
  `core/canonical`: `ComposableArrows C (n + 1)` together with `ComposableArrows.Exact` and the
    inherited full-subcategory category structure;
  `bridge/view`: the degree-`1` comparison with `Extension A B` and the endpoint-identity
    predicate on ladders;
- best owner abstraction: keep `YonedaExtension A B n` as the fixed-endpoint source-facing owner,
  but realize it as the full subcategory of `ComposableArrows C (n + 1)` cut out by the fixed
  endpoint and exactness conditions, so that ladders are inherited directly from the canonical
  owner category instead of being rebuilt by a parallel local wrapper;
- primitive-vs-derived split:
  primitive data: the underlying exact composable chain with fixed endpoints and endpoint mono/epi
  conditions;
  derived API: the first and last maps, the degree-one bridge to the earlier source-facing owner
    `Extension`, the endpoint-identity predicate on ladders, and the equivalence relation built
    from those canonical ladders. -/

structure IsYonedaExtension (A B : C) (n : ℕ+) (E : ComposableArrows C (n + 1)) : Prop where
  /-- The left endpoint of the chain is the fixed object `A`. -/
  left_eq : E.left = A
  /-- The right endpoint of the chain is the fixed object `B`. -/
  right_eq : E.right = B
  /-- The first map `A ⟶ Z_(n-1)` is a monomorphism. -/
  mono_first : Mono (eqToHom left_eq.symm ≫ E.map' 0 1)
  /-- The chain is exact at every intermediate object. -/
  exact : E.Exact
  /-- The last map `Z_0 ⟶ B` is an epimorphism. -/
  epi_last : Epi (E.map' n (n + 1) ≫ eqToHom right_eq)

/-- Definition 13.27.4: a degree `n` Yoneda extension of `B` by `A`, for `n : ℕ+`, is the full
subcategory of exact composable chains `A ⟶ Z_(n-1) ⟶ ... ⟶ Z_0 ⟶ B` with monic first map and
epic last map. Equivalently, these are the chains underlying exact sequences
`0 ⟶ A ⟶ Z_(n-1) ⟶ ... ⟶ Z_0 ⟶ B ⟶ 0`. -/
abbrev YonedaExtension (A B : C) (n : ℕ+) :=
  ObjectProperty.FullSubcategory (IsYonedaExtension A B n)

namespace YonedaExtension

variable {A B : C} {n : ℕ+}

/-- The chosen identification of the left endpoint with `A`. -/
abbrev leftEq (E : YonedaExtension A B n) : E.obj.left = A :=
  E.property.left_eq

/-- The chosen identification of the right endpoint with `B`. -/
abbrev rightEq (E : YonedaExtension A B n) : E.obj.right = B :=
  E.property.right_eq

/-- Exactness of the underlying composable chain. -/
abbrev exact (E : YonedaExtension A B n) : E.obj.Exact :=
  E.property.exact

/-- The first nonzero map `A ⟶ Z_(n-1)` in a Yoneda extension. -/
abbrev firstMap (E : YonedaExtension A B n) :
    A ⟶ E.obj.obj' 1 :=
  eqToHom E.leftEq.symm ≫ E.obj.map' 0 1

/-- The last nonzero map `Z_0 ⟶ B` in a Yoneda extension. -/
abbrev lastMap (E : YonedaExtension A B n) :
    E.obj.obj' n ⟶ B :=
  E.obj.map' n (n + 1) ≫ eqToHom E.rightEq

/-- A Yoneda extension carries the canonical monomorphism instance on its first map. -/
instance (E : YonedaExtension A B n) : Mono E.firstMap :=
  E.property.mono_first

/-- A Yoneda extension carries the canonical epimorphism instance on its last map. -/
instance (E : YonedaExtension A B n) : Epi E.lastMap :=
  E.property.epi_last

private theorem firstMap_comp_lastMap (E : YonedaExtension A B 1) :
    E.firstMap ≫ E.lastMap = 0 := by
  let hComplex := E.exact.toIsComplex
  calc
    E.firstMap ≫ E.lastMap
        = eqToHom E.leftEq.symm ≫
            (E.obj.map' 0 1 ≫ E.obj.map' 1 2) ≫
              eqToHom E.rightEq := by
            simp [firstMap, lastMap, Category.assoc]
    _ = 0 := by
      rw [hComplex.zero 0 (by decide)]
      rw [zero_comp, comp_zero]

set_option linter.unnecessarySimpa false in
private theorem shortExact (E : YonedaExtension A B 1) :
    (ShortComplex.mk E.firstMap E.lastMap E.firstMap_comp_lastMap).ShortExact := by
  let e : ShortComplex.mk E.firstMap E.lastMap E.firstMap_comp_lastMap ≅
      E.exact.sc 0 (by decide) :=
    ShortComplex.isoMk
      (eqToIso E.leftEq.symm)
      (Iso.refl _)
      (eqToIso E.rightEq.symm)
      (by
        dsimp [ComposableArrows.sc, ComposableArrows.sc', firstMap]
        simpa using
          congrArg (fun k ↦ eqToHom E.leftEq.symm ≫ E.obj.map k)
            (Subsingleton.elim _ _))
      (by
        dsimp [ComposableArrows.sc, ComposableArrows.sc', lastMap]
        simp)
  refine ShortComplex.ShortExact.mk' ?_ E.property.mono_first E.property.epi_last
  exact ShortComplex.exact_of_iso e.symm (E.exact.exact 0 (by decide))

/-- The canonical bridge from a degree-`1` Yoneda extension to the earlier source-facing owner
`Extension A B`. -/
abbrev toExtension (E : YonedaExtension A B 1) : Extension A B where
  E := E.obj.obj' 1
  f := E.firstMap
  g := E.lastMap
  zero := E.firstMap_comp_lastMap
  shortExact := E.shortExact

/-- A ladder between Yoneda extensions is identity on the fixed endpoints `A` and `B`,
after transporting along the chosen endpoint identifications. -/
private def idOnEndpoints (E F : YonedaExtension A B n)
    (φ : E ⟶ F) : Prop :=
  app' φ.hom 0 = eqToHom (E.leftEq.trans F.leftEq.symm) ∧
    app' φ.hom (n + 1) = eqToHom (E.rightEq.trans F.rightEq.symm)

/-- Two Yoneda extensions of the same degree are equivalent when there exists a third Yoneda
extension mapping to both by a commutative ladder which is the identity on `A` and `B`. -/
def Equivalent (E F : YonedaExtension A B n) : Prop :=
  ∃ (G : YonedaExtension A B n)
    (φ : G ⟶ E)
    (ψ : G ⟶ F),
      idOnEndpoints G E φ ∧ idOnEndpoints G F ψ

/-- In degree `1`, endpoint-fixing isomorphic short exact sequences induce equivalent Yoneda
extensions. This reuses the Chapter `12` owner `Extension.Isomorphic` rather than keeping a
parallel short-exact equivalence notion local to Yoneda extensions. -/
theorem equivalent_of_toExtension_isomorphic {E F : YonedaExtension A B 1}
    (h : Extension.Isomorphic E.toExtension F.toExtension) :
    Equivalent E F := by
  rcases h with ⟨e, hf, hg⟩
  have w₀ : E.obj.map' 0 1 ≫ e.hom =
      eqToHom (E.leftEq.trans F.leftEq.symm) ≫ F.obj.map' 0 1 := by
    simpa [firstMap, Category.assoc] using
      congrArg (fun k ↦ eqToHom E.leftEq ≫ k) hf
  have w₁ : E.obj.map' 1 2 ≫
      eqToHom (E.rightEq.trans F.rightEq.symm) =
      e.hom ≫ F.obj.map' 1 2 := by
    apply (cancel_mono (eqToHom F.rightEq)).1
    change (E.obj.map' 1 2 ≫ eqToHom (E.rightEq.trans F.rightEq.symm)) ≫
        eqToHom F.rightEq =
      (e.hom ≫ F.obj.map' 1 2) ≫ eqToHom F.rightEq
    simpa [lastMap, Category.assoc] using hg.symm
  let i : E.obj ≅ F.obj :=
    ComposableArrows.isoMk₂
      (eqToIso (E.leftEq.trans F.leftEq.symm))
      e
      (eqToIso (E.rightEq.trans F.rightEq.symm))
      w₀
      w₁
  refine ⟨E, 𝟙 E, ObjectProperty.homMk i.hom, ?_, ?_⟩
  · change app' (𝟙 E.obj) 0 =
        eqToHom (E.leftEq.trans E.leftEq.symm) ∧
      app' (𝟙 E.obj) 2 =
        eqToHom (E.rightEq.trans E.rightEq.symm)
    constructor
    · change 𝟙 (E.obj.obj' 0) = 𝟙 E.obj.left
      simp [left]
    · change 𝟙 (E.obj.obj' 2) = 𝟙 E.obj.right
      simp [right]
  · change i.hom.app 0 = eqToHom (E.leftEq.trans F.leftEq.symm) ∧
      i.hom.app 2 = eqToHom (E.rightEq.trans F.rightEq.symm)
    constructor <;> rfl

end YonedaExtension

end

end CategoryTheory

/-! ### Lemma_13_27_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open ComposableArrows

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

namespace YonedaExtension

variable {A B : C}

/-
Domain sampling for Lemma 13.27.5.

Primary domain:
* abelian-category `Ext` classes attached to exact sequences.

Sampled owner-style declarations:
* `CategoryTheory.ExtensionClass.toExt`
* `ShortComplex.ShortExact.extClass`
* `Abelian.Ext.covariant_sequence_exact₁`
* `Abelian.Ext.contravariant_sequence_exact₃`

Layering:
* source-facing: `YonedaExtension A B n`
* core/canonical: `Ext B A n`
* bridge/view: the comparison map `YonedaExtension.toExt`

Primitive data here are only the exact composable chain together with the endpoint mono/epi
conditions already packaged by `YonedaExtension`. The comparison map to `Ext` is derived API; in
degree `1` the chapter-owned bridge is `ExtensionClass.toExt`, applied to the class of
`E.toExtension`. Higher degrees should recurse on the actual positive Yoneda degree rather than on
an auxiliary `n + 1` encoding.
-/

private theorem two_le_length (n : ℕ+) : (2 : ℕ) ≤ ((n + 1 : ℕ+) : ℕ) := by
  simpa using Nat.succ_le_succ (Nat.succ_le_of_lt n.2)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the underlying composable row of a degree `n + 1` Yoneda
extension is long enough to read off the first three arrows. -/
private theorem three_le_length (n : ℕ+) : (3 : ℕ) ≤ (((n + 1 : ℕ+) : ℕ) + 1) := by
  simpa using Nat.succ_le_succ (two_le_length n)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the underlying composable row of a degree `n + 1` Yoneda
extension is long enough to read off the first nontrivial object. -/
private theorem one_le_length_succ (n : ℕ+) : (1 : ℕ) ≤ (((n + 1 : ℕ+) : ℕ) + 1) := by
  exact Nat.succ_le_succ (Nat.zero_le _)

omit [HasExt C] in
private theorem firstMap_comp_next_zero {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.firstMap ≫ E.obj.map' 1 2 (by decide) (two_le_length (n + 1)) = 0 := by
  let hComplex := E.exact.toIsComplex
  calc
    E.firstMap ≫ E.obj.map' 1 2 (by decide) (two_le_length (n + 1))
        = eqToHom E.leftEq.symm ≫ 0 := by
            simpa [firstMap, Category.assoc] using
              congrArg (fun k ↦ eqToHom E.leftEq.symm ≫ k)
                (hComplex.zero 0 (two_le_length (n + 1)))
    _ = 0 := by
      simpa using
        (show eqToHom E.leftEq.symm ≫
            (0 : E.obj.obj' 0 ⟶ E.obj.obj' 2 (two_le_length (n + 1))) = 0 from comp_zero)

omit [HasExt C] in
private theorem headExact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.mk E.firstMap
      (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
      (firstMap_comp_next_zero E)).Exact := by
  let hExact := E.exact
  let hComplex := hExact.toIsComplex
  let e :
      ShortComplex.mk E.firstMap
          (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
          (firstMap_comp_next_zero E) ≅
        E.obj.sc hComplex 0 (two_le_length (n + 1)) :=
    ShortComplex.isoMk
      (eqToIso E.leftEq.symm)
      (Iso.refl _)
      (Iso.refl _)
      (by
        dsimp [ComposableArrows.sc, ComposableArrows.sc', firstMap]
        simpa using
          congrArg (fun k ↦ eqToHom E.leftEq.symm ≫ E.obj.map k)
            (Subsingleton.elim _ _))
      (by
        dsimp [ComposableArrows.sc, ComposableArrows.sc']
        simp)
  exact ShortComplex.exact_of_iso e.symm (hExact.exact 0 (two_le_length (n + 1)))

omit [HasExt C] in
private noncomputable def quotientMap {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    cokernel E.firstMap ⟶ E.obj.obj' 2 (two_le_length (n + 1)) :=
  cokernel.desc E.firstMap
    (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
    (firstMap_comp_next_zero E)

omit [HasExt C] in
private theorem quotientMap_mono {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    Mono (quotientMap E) := by
  simpa [quotientMap] using (headExact E).mono_cokernelDesc

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the quotient map obtained from the first exact pair still composes
to zero with the next differential. -/
private theorem quotientMap_comp_next_zero {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    quotientMap E ≫ (E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2 = 0 := by
  -- Compose with the cokernel projection so the claim becomes the original composable-row
  -- relation `d₁ ≫ d₂ = 0`.
  apply (cancel_epi (cokernel.π E.firstMap)).1
  -- After rewriting the truncated differential, the cokernel-desc equation reduces the claim to
  -- the original composable-row relation `d₁ ≫ d₂ = 0`.
  change cokernel.π E.firstMap ≫ quotientMap E ≫
      E.obj.map' 2 3 (by decide) (three_le_length n) =
    cokernel.π E.firstMap ≫ 0
  simp [quotientMap]
  calc
    E.obj.map' 1 2 (by decide) (two_le_length (n + 1)) ≫
        E.obj.map' 2 3 (by decide) (three_le_length n) = 0 := by
          simpa using E.exact.toIsComplex.zero 1 (three_le_length n)
    _ = cokernel.π E.firstMap ≫ 0 := by rw [comp_zero]

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the middle pair in a degree `n + 1` Yoneda extension composes to
zero. -/
private theorem middle_comp_next_zero {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.obj.map' 1 2 (by decide) (two_le_length (n + 1)) ≫
      E.obj.map' 2 3 (by decide) (three_le_length n) = 0 := by
  simpa using E.exact.toIsComplex.zero 1 (three_le_length n)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the middle pair of consecutive arrows in a degree `n + 1`
Yoneda extension is exact. -/
private theorem middleExact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.mk
      (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
      (E.obj.map' 2 3 (by decide) (three_le_length n))
      (middle_comp_next_zero E)).Exact := by
  -- This is the exactness statement at the first interior object of the original row.
  simpa [ComposableArrows.sc, ComposableArrows.sc'] using
    E.exact.exact 1 (three_le_length n)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the quotient map is available as an instance-level mono for the
canonical image factorization. -/
private instance quotientMap_mono_inst {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    Mono (quotientMap E) :=
  quotientMap_mono E

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the quotient object `cokernel E.firstMap` identifies with the
abelian image of the next differential. -/
private noncomputable def quotient_image_iso {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    cokernel E.firstMap ≅ Abelian.image
      (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) :=
  image.isoStrongEpiMono
      (cokernel.π E.firstMap)
      (quotientMap E)
      (by simp [quotientMap]) ≪≫
    (Abelian.imageIsoImage _).symm

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the quotient-image comparison intertwines the quotient map with the
canonical image inclusion of the middle differential. -/
private theorem quotient_image_iso_hom_comp_image_ι {n : ℕ+}
    (E : YonedaExtension A B (n + 1)) :
    (quotient_image_iso E).hom ≫
        Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) =
      quotientMap E := by
  have hImageIso :
      (Abelian.imageIsoImage
          (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))).inv ≫
        Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) =
      Limits.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) := by
    rw [Abelian.imageIsoImage_inv]
    simp [Abelian.image.ι]
  -- First convert the abelian image inclusion to the categorical image inclusion.
  calc
    (quotient_image_iso E).hom ≫
        Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
        =
      (image.isoStrongEpiMono
          (cokernel.π E.firstMap)
          (quotientMap E)
          (by simp [quotientMap])).hom ≫
        (Abelian.imageIsoImage
          (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))).inv ≫
        Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) := by
            dsimp [quotient_image_iso]
            simp [Category.assoc]
    _
        =
      (image.isoStrongEpiMono
          (cokernel.π E.firstMap)
          (quotientMap E)
          (by simp [quotientMap])).hom ≫
        Limits.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) := by
            let hCompose :=
              congrArg
                (fun k ↦
                  (image.isoStrongEpiMono
                      (cokernel.π E.firstMap)
                      (quotientMap E)
                      (by simp [quotientMap])).hom ≫ k)
                hImageIso
            simpa [Category.assoc] using hCompose
    _ = quotientMap E := by
      simpa using image.isoStrongEpiMono_hom_comp_ι
        (e := cokernel.π E.firstMap)
        (m := quotientMap E)
        (f := E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
        (comm := by simp [quotientMap])

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the inverse quotient-image comparison recovers the abelian image
inclusion from the quotient map. -/
private theorem quotient_image_iso_inv_comp_quotientMap {n : ℕ+}
    (E : YonedaExtension A B (n + 1)) :
    (quotient_image_iso E).inv ≫ quotientMap E =
      Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) := by
  -- Rewrite the quotient map using the forward comparison and then contract the isomorphism.
  rw [← quotient_image_iso_hom_comp_image_ι E]
  rw [← Category.assoc]
  simp

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: after replacing the quotient head map by the canonical abelian image
inclusion, the resulting first short complex is exact. -/
private theorem quotient_nextMap_eq_middle_tail {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2 =
      E.obj.map' 2 3 (by decide) (three_le_length n) := by
  -- Forgetting the first two arrows exposes the original third arrow definitionally.
  rfl

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: after forgetting the new quotient arrow, the tail of the quotient
row is exactly the twice-truncated original row, hence exact. -/
private theorem quotient_tail_exact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (((E.obj.δ₀.δ₀).precomp (quotientMap E)).δ₀).Exact := by
  -- The tail is definitionally `E.obj.δ₀.δ₀`, whose exactness comes from the original row.
  -- Normalizing the positive index once turns the twice-forgotten tail into a literal `δ₀` tail.
  cases' n with n hn
  cases n with
  | zero => cases hn
  | succ n =>
      simpa [ComposableArrows.precomp_δ₀] using (E.exact.δ₀).δ₀

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: after replacing the quotient head map by the canonical abelian image
inclusion, the resulting first short complex is exact. -/
private theorem quotient_head_iso_right_square {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.obj.map' 2 3 (by decide) (three_le_length n) =
      ((E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2) ≫
        (Iso.refl _).hom := by
  -- The second square is the unchanged tail differential, expressed in the exact `isoMk` shape.
  simpa using (quotient_nextMap_eq_middle_tail E).symm

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: after replacing the quotient head map by the canonical abelian image
inclusion, the resulting first short complex is exact. -/
private theorem quotient_head_exact_via_image {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.mk
      (quotientMap E)
      ((E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2)
      (quotientMap_comp_next_zero E)).Exact := by
  let d₁ := E.obj.map' 1 2 (by decide) (two_le_length (n + 1))
  let d₂ := E.obj.map' 2 3 (by decide) (three_le_length n)
  let S : ShortComplex C := ShortComplex.mk d₁ d₂ (middle_comp_next_zero E)
  have hImage :
      (ShortComplex.mk (Abelian.image.ι d₁) d₂
        (Abelian.image_ι_comp_eq_zero (middle_comp_next_zero E))).Exact := by
    -- Exactness of the original middle pair transfers to exactness for the image inclusion.
    exact (ShortComplex.exact_iff_exact_image_ι S).1 (middleExact E)
  -- Transport the image-exact short complex across the quotient/image identification.
  refine ShortComplex.exact_of_iso ?_ hImage
  refine ShortComplex.isoMk (quotient_image_iso E).symm (Iso.refl _) (Iso.refl _) ?_ ?_
  · -- The first square is exactly the identification of `quotientMap E` with `image.ι`.
    simpa [S, d₁] using quotient_image_iso_inv_comp_quotientMap E
  · -- The second square is the dedicated transport-stable adapter for `ShortComplex.isoMk`.
    calc
      (Iso.refl _).hom ≫ d₂ = d₂ := by simp
      _ = (E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2 := (quotient_nextMap_eq_middle_tail E).symm
      _ = ((E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2) ≫ (Iso.refl _).hom := by simp

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the head of the precomposed quotient row is exact in the precise
`ComposableArrows.mk₂` form required by `ComposableArrows.exact_of_δ₀`. -/
private theorem quotient_precomp_head_exact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ComposableArrows.mk₂
      (((E.obj.δ₀.δ₀).precomp (quotientMap E)).map' 0 1
        (by decide)
        (show 1 ≤ ((n : ℕ) + 1) from Nat.succ_le_succ (Nat.zero_le _)))
      (((E.obj.δ₀.δ₀).precomp (quotientMap E)).map' 1 2
        (by decide)
        (show 2 ≤ ((n : ℕ) + 1) from Nat.succ_le_succ (Nat.succ_le_of_lt n.2)))).Exact := by
  -- The first two arrows of the precomposed row are exactly the short complex handled above.
  let S : ShortComplex C := ShortComplex.mk
    (quotientMap E)
    ((E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2)
    (quotientMap_comp_next_zero E)
  have hComp : S.toComposableArrows.Exact :=
    (ShortComplex.exact_iff_exact_toComposableArrows S).1 (quotient_head_exact_via_image E)
  simpa [S, ComposableArrows.mk₂, ComposableArrows.Precomp.map_zero_one,
    ComposableArrows.Precomp.map_one_succ] using hComp

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the composable row obtained by quotienting the leftmost term of a
degree `n + 1` Yoneda extension is exact. -/
private theorem quotient_exact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    ((E.obj.δ₀.δ₀).precomp (quotientMap E)).Exact := by
  -- Assemble exactness from the exact head pair and the already exact twice-truncated tail.
  cases' n with n hn
  cases n with
  | zero => cases hn
  | succ n =>
      exact ComposableArrows.exact_of_δ₀
        (S := ((E.obj.δ₀.δ₀).precomp (quotientMap E)))
        (quotient_precomp_head_exact E)
        (quotient_tail_exact E)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the last arrow of the quotient extension is the original terminal
arrow, hence remains an epimorphism. -/
private theorem quotient_lastMap_epi {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    Epi ((((E.obj.δ₀.δ₀).precomp (quotientMap E)).map' n (n + 1)) ≫ eqToHom E.rightEq) := by
  -- Route correction: normalize the successor index once, then the terminal map is the original
  -- last map by definition of `Precomp.map`.
  cases' n with n hn
  cases n with
  | zero => cases hn
  | succ n =>
      -- After normalizing the positive index, the target is definitionally the original last map.
      change Epi E.lastMap
      infer_instance

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: quotienting the first map of a positive-degree Yoneda extension
produces another Yoneda extension one degree lower. -/
private theorem quotient_property {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    IsYonedaExtension (cokernel E.firstMap) B n ((E.obj.δ₀.δ₀).precomp (quotientMap E)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · -- The right endpoint is unchanged by forgetting the first two arrows and re-precomposing.
    simpa using E.rightEq
  · -- The new first map is the quotient map, already known to be mono.
    simpa [quotientMap] using quotientMap_mono E
  · -- The head exactness now comes from the image-factorization identification.
    exact quotient_exact E
  · -- The terminal arrow is literally the original last map.
    exact quotient_lastMap_epi E

omit [HasExt C] in
private noncomputable def quotient {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    YonedaExtension (cokernel E.firstMap) B n where
  obj := (E.obj.δ₀.δ₀).precomp (quotientMap E)
  property := quotient_property E

omit [HasExt C] in
private theorem firstShortExact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.cokernelSequence E.firstMap).ShortExact := by
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact E.firstMap)
    (show Mono E.firstMap from inferInstance) inferInstance

private noncomputable def toExtAux (n : ℕ+) :
    ∀ {X Y : C}, YonedaExtension X Y n → Ext Y X n :=
  @PNat.recOn n
    (fun m ↦ ∀ {X Y : C}, YonedaExtension X Y m → Ext Y X m)
    (fun {X Y} (F : YonedaExtension X Y 1) ↦
      ExtensionClass.toExt (⟦F.toExtension⟧ : ExtensionClass X Y))
    (fun n ih {X Y} (F : YonedaExtension X Y (n + 1)) ↦
      (ih (quotient F)).comp (firstShortExact F).extClass rfl)

/-- Lemma 13.27.5: the canonical comparison map from degree `n` Yoneda extensions of `B` by `A`
to `Ext B A n`, defined recursively on the actual positive Yoneda degree by peeling off the
leftmost short exact sequence and using the Chapter `12` degree-`1` bridge
`ExtensionClass.toExt (⟦E.toExtension⟧ : ExtensionClass A B)` as the base case. -/
noncomputable def toExt {n : ℕ+} (E : YonedaExtension A B n) : Ext B A n :=
  toExtAux n E

/-- Surjectivity part of Lemma 13.27.5 for the canonical comparison map `YonedaExtension.toExt`. -/
theorem toExt_surjective (n : ℕ+) :
    Function.Surjective (toExt : YonedaExtension A B n → Ext B A n) := by
  -- TODO: follow the source proof via a roof `L• ⟶ B[0]` and `L• ⟶ A[i]`, then build the
  -- induced Yoneda extension and compare its recursive `toExt` with the given `Ext` class.
  sorry

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: in degree `1`, an endpoint-fixing ladder induces an isomorphism of
the underlying short exact sequences. -/
private theorem toExtension_isomorphic_of_endpoint_ladder {E F : YonedaExtension A B 1}
    (φ : E ⟶ F)
    (hφ₀ : app' φ.hom 0 = eqToHom (E.leftEq.trans F.leftEq.symm))
    (hφ₂ : app' φ.hom 2 = eqToHom (E.rightEq.trans F.rightEq.symm)) :
    Extension.Isomorphic E.toExtension F.toExtension := by
  let φ₁ : E.obj.obj' 1 ⟶ F.obj.obj' 1 := app' φ.hom 1 (by decide)
  have hnat₀₁ :
      E.obj.map' 0 1 (by decide) (by decide) ≫ φ₁ =
        app' φ.hom 0 (by decide) ≫ F.obj.map' 0 1 (by decide) (by decide) := by
    simpa [φ₁] using naturality' φ.hom 0 1 (by decide) (by decide)
  have hnat₁₂ :
      φ₁ ≫ F.obj.map' 1 2 (by decide) (by decide) =
        E.obj.map' 1 2 (by decide) (by decide) ≫ app' φ.hom 2 (by decide) := by
    simpa [φ₁] using naturality' φ.hom 1 2 (by decide) (by decide)
  have hcomm₁₂ : E.firstMap ≫ φ₁ = F.firstMap := by
    -- Precompose the left square with the chosen identification of the left endpoint with `A`.
    calc
      E.firstMap ≫ φ₁
          = eqToHom E.leftEq.symm ≫
              (E.obj.map' 0 1 (by decide) (by decide) ≫ φ₁) := by
                simp [YonedaExtension.firstMap, Category.assoc]
      _ = eqToHom E.leftEq.symm ≫
            (app' φ.hom 0 (by decide) ≫ F.obj.map' 0 1 (by decide) (by decide)) := by
              rw [hnat₀₁]
      _ = eqToHom E.leftEq.symm ≫
            (eqToHom (E.leftEq.trans F.leftEq.symm) ≫
              F.obj.map' 0 1 (by decide) (by decide)) := by rw [hφ₀]
      _ = F.firstMap := by simp [YonedaExtension.firstMap, Category.assoc]
  have hcomm₂₃ : φ₁ ≫ F.lastMap = E.lastMap := by
    -- Postcompose the right square with the chosen identification of the right endpoint with `B`.
    calc
      φ₁ ≫ F.lastMap
          = φ₁ ≫ (F.obj.map' 1 2 (by decide) (by decide) ≫ eqToHom F.rightEq) := by
              simp [YonedaExtension.lastMap, Category.assoc]
      _ = (φ₁ ≫ F.obj.map' 1 2 (by decide) (by decide)) ≫ eqToHom F.rightEq := by
            simp [Category.assoc]
      _ = (E.obj.map' 1 2 (by decide) (by decide) ≫ app' φ.hom 2 (by decide)) ≫
            eqToHom F.rightEq := by rw [hnat₁₂]
      _ = E.lastMap := by
            rw [hφ₂]
            calc
              (E.obj.map' 1 2 (by decide) (by decide) ≫
                  eqToHom (E.rightEq.trans F.rightEq.symm)) ≫
                    eqToHom F.rightEq
                  =
                E.obj.map' 1 2 (by decide) (by decide) ≫
                  (eqToHom (E.rightEq.trans F.rightEq.symm) ≫ eqToHom F.rightEq) := by
                      simp [Category.assoc]
              _ = E.lastMap := by
                    simp [YonedaExtension.lastMap, Category.assoc]
  let ψ : E.toExtension.toShortComplex ⟶ F.toExtension.toShortComplex :=
    ShortComplex.homMk
      (𝟙 A)
      φ₁
      (𝟙 B)
      (by
        -- The first short-complex square is exactly the endpoint-normalized left square.
        simpa using hcomm₁₂.symm
      )
      (by
        -- The second short-complex square is exactly the endpoint-normalized right square.
        simpa using hcomm₂₃
      )
  have hIso₂ : IsIso φ₁ := by
    -- The short exact five-lemma upgrades the middle component to an isomorphism.
    change IsIso ψ.τ₂
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' ψ E.toExtension.shortExact
      F.toExtension.shortExact
      (by
        dsimp [ψ]
        infer_instance)
      (by
        dsimp [ψ]
        infer_instance)
  refine ⟨asIso φ₁, ?_, ?_⟩
  · -- The left compatibility is exactly the normalized first square.
    simpa using hcomm₁₂
  · -- The right compatibility is exactly the normalized second square.
    simpa using hcomm₂₃

/-- Helper for Lemma 13.27.5: in degree `1`, an endpoint-fixing ladder induces the same
`Ext¹`-class because it is an isomorphism of the underlying short exact sequences. -/
private theorem toExt_eq_of_endpoint_ladder_one {E F : YonedaExtension A B 1}
    (φ : E ⟶ F)
    (hφ₀ : app' φ.hom 0 = eqToHom (E.leftEq.trans F.leftEq.symm))
    (hφ₂ : app' φ.hom 2 = eqToHom (E.rightEq.trans F.rightEq.symm)) :
    toExt E = toExt F := by
  -- Package the ladder as an isomorphism of short exact sequences, then use the Chapter `12`
  -- bridge from extension isomorphisms to equality of `Ext¹`-classes.
  let hIso : Extension.Isomorphic E.toExtension F.toExtension :=
    toExtension_isomorphic_of_endpoint_ladder φ hφ₀ hφ₂
  change ExtensionClass.toExt (⟦E.toExtension⟧ : ExtensionClass A B) =
      ExtensionClass.toExt (⟦F.toExtension⟧ : ExtensionClass A B)
  rw [ExtensionClass.mk_eq_mk_of_isomorphic hIso]

/-- Helper for Lemma 13.27.5: in degree `1`, equivalent Yoneda extensions already have the same
class because both endpoint-fixing ladders identify the same short exact sequence class. -/
private theorem equivalent_implies_toExt_eq_one {E F : YonedaExtension A B 1}
    (h : Equivalent E F) :
    toExt E = toExt F := by
  rcases h with ⟨G, φ, ψ, hφ, hψ⟩
  rcases hφ with ⟨hφ₀, hφ₂⟩
  rcases hψ with ⟨hψ₀, hψ₂⟩
  -- Compare both extensions with the common refinement `G`.
  calc
    toExt E = toExt G := by
      symm
      exact toExt_eq_of_endpoint_ladder_one φ hφ₀ hφ₂
    _ = toExt F := by
      exact toExt_eq_of_endpoint_ladder_one ψ hψ₀ hψ₂

/-- Equality in `Ext` detects Yoneda equivalence for the canonical comparison map
`YonedaExtension.toExt`. -/
theorem equivalent_iff_toExt_eq {n : ℕ+} (E E' : YonedaExtension A B n) :
    Equivalent E E' ↔ toExt E = toExt E' := by
  -- Route correction: the degree-`1` ladder case is now handled by short-exact naturality.
  -- TODO: descend endpoint-fixing ladders through `quotient` for the forward implication, then
  -- use the canonical-roof/common-refinement argument for the converse implication.
  sorry

end YonedaExtension

end CategoryTheory

/-! ### Lemma_13_27_6 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe w v u

namespace CategoryTheory.Abelian.Ext

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (A B : C)

/- Domain-style sampling for Lemma 13.27.6:
- primary domain: degree-one `Ext` in an abelian category and its classification by extension
  classes;
- sampled owner declarations:
  `ExtensionClass`,
  `ExtensionClass.toExt`,
  `ExtensionClass.toExtAddEquiv`,
  `Ext B A 1`;
- best owner abstraction: the canonical owner is `Ext B A 1`, while the source-facing extension
  group is `ExtensionClass A B`; the correct bridge for this lemma is the additive equivalence
  `ExtensionClass.toExtAddEquiv`;
- primitive-vs-derived split:
  primitive data: the ambient abelian category with `HasExt` and the objects `A`, `B`;
  derived API: the additive identification of the Chapter 12 extension group with `Ext B A 1`.

Source/core/bridge triage:
- `source-facing`: `ExtensionClass A B`;
- `core/canonical`: `Ext B A 1`;
- `bridge/view`: `ExtensionClass.toExtAddEquiv`.

This file should therefore stay at the bridge layer: it recalls the canonical additive
identification between the source-facing extension group and the owner `Ext¹`, without introducing
any parallel local alias.
-/

/- Lemma 13.27.6: in an abelian category, the extension group constructed from short exact
sequences is canonically identified with `Ext^1_{\mathcal A}(B, A)` by
`ExtensionClass.toExtAddEquiv`. -/
recall ExtensionClass.toExtAddEquiv

end

end CategoryTheory.Abelian.Ext

/-! ### Lemma_13_27_7 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open ShortComplex.ShortExact

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {A B C : 𝒜}

/- Domain-style sampling for Lemma 13.27.7:
- primary domain: short exact sequences in an abelian category, their Yoneda composition in
  `Ext²`, and the `3 × 3` pullback comparison between short exact sequences;
- inspected owner declarations:
  `Extension`,
  `Extension.Isomorphic`,
  `ExtensionClass.pullback`,
  `DistinguishedThreeByThreeExtension`;
- best owner abstraction:
  `source-facing`: a commutative exact `3 × 3` extension diagram over fixed rows
    `S : Extension A B` and `T : Extension B C`;
  `core/canonical`: the degree-`1` owner `ExtensionClass A T.E`;
  `bridge/view`: the pullback equation
    `ExtensionClass.pullback T.f (⟦U⟧ : ExtensionClass A T.E) = ⟦S⟧`.

Primitive data are the middle short exact row `0 ⟶ A ⟶ W ⟶ T.E ⟶ 0`, a comparison morphism
`S.E ⟶ W`, and the pullback square over `T.f : B ⟶ T.E`. The extension-class pullback identity is
derived bridge API from that source-facing diagram data, not the main owner.
-/

-- Proof sketch: apply the contravariant long exact sequence in `Ext(-, A)` to the short exact
-- sequence `T : 0 ⟶ B ⟶ T.E ⟶ C ⟶ 0`. The vanishing of the Yoneda product means that the class of
-- `S : 0 ⟶ A ⟶ S.E ⟶ B ⟶ 0` lifts to an element of `Ext¹(T.E, A)`, and such a lift is represented
-- by a short exact sequence `0 ⟶ A ⟶ W ⟶ T.E ⟶ 0` whose pullback along `B ⟶ T.E` recovers `S`,
-- equivalently giving the claimed exact `3 × 3` diagram.
namespace Extension

/-- Source-facing `3 × 3` extension data for Lemma 13.27.7. This is the exact diagrammatic owner:
the top row is `S`, the bottom row is `T`, the middle row is a short exact sequence
`0 ⟶ A ⟶ W ⟶ T.E ⟶ 0`, and the right-hand square is a pullback. In an abelian category this is an
exact canonical equivalent of the textbook commutative exact `3 × 3` diagram. -/
structure ThreeByThree (S : Extension A B) (T : Extension B C) where
  middleRow : Extension A T.E
  middleColumnMap : S.E ⟶ middleRow.E
  left_comm : S.f ≫ middleColumnMap = middleRow.f
  right_pullback : IsPullback S.g middleColumnMap T.f middleRow.g

namespace ThreeByThree

variable {S : Extension A B} {T : Extension B C}

@[simp]
theorem right_comm (D : ThreeByThree S T) :
    S.g ≫ T.f = D.middleColumnMap ≫ D.middleRow.g :=
  D.right_pullback.w

end ThreeByThree

end Extension

/-- The source-facing `3 × 3` extension data of `Extension.ThreeByThree` is equivalent to the
bridge/view statement that the middle row has pullback extension class `⟦S⟧`. -/
theorem nonempty_threeByThree_iff_exists_pullback_extClass_eq
    (S : Extension A B) (T : Extension B C) :
    Nonempty (Extension.ThreeByThree S T) ↔
      ∃ U : Extension A T.E,
        ExtensionClass.pullback T.f (⟦U⟧ : ExtensionClass A T.E) = ⟦S⟧ := sorry

variable [HasExt.{w} 𝒜]

/-- Lemma 13.27.7: for short exact sequences `S : 0 ⟶ A ⟶ E ⟶ B ⟶ 0` and
`T : 0 ⟶ B ⟶ E' ⟶ C ⟶ 0` in an abelian category, the Yoneda product of their classes in
`Ext²(C, A)` is zero if and only if there exists a commutative `3 × 3` diagram with exact
rows and columns whose middle row is `0 ⟶ A ⟶ W ⟶ E' ⟶ 0` and whose middle column is
`0 ⟶ E ⟶ W ⟶ C ⟶ 0`. -/
theorem comp_extClass_eq_zero_iff_exists_exact_three_by_three_diagram
    (S : Extension A B) (T : Extension B C) :
    (extClass T.shortExact).comp (extClass S.shortExact) rfl = 0 ↔
      Nonempty (Extension.ThreeByThree S T) := by
  rw [nonempty_threeByThree_iff_exists_pullback_extClass_eq]
  sorry

end

end CategoryTheory

/-! ### Lemma_13_27_8 (from Chap13) -/
universe w v u

namespace CategoryTheory

open Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/- Domain-style sampling for Lemma 13.27.8:
- primary domain: injective-dimension bounds in an abelian category, expressed through vanishing of
  higher `Ext` groups;
- sampled owner declarations:
  `CategoryTheory.HasInjectiveDimensionLT`,
  `CategoryTheory.HasInjectiveDimensionLT.mk`,
  `CategoryTheory.HasInjectiveDimensionLT.subsingleton`,
  `CategoryTheory.hasInjectiveDimensionLT_of_enoughProjectives`;
- best owner abstraction: `HasInjectiveDimensionLT A p` is the canonical owner for the statement
  that all `Ext B A i` vanish for `i ≥ p`; the long exact sequence operators and
  `YonedaExtension.toExt` remain proof infrastructure rather than public API;
- primitive data: the degree `p` and the uniform degree-`p` vanishing hypothesis
  `hExt : ∀ A B, Subsingleton (Ext B A p)`;
- derived API: objectwise injective-dimension bounds, together with the fixed-target owner bridge
  `HasInjectiveDimensionLT.of_ext_vanishing`.

Source/core/bridge triage:
- `source-facing`: uniform higher-degree `Ext`-vanishing from vanishing in degree `p`;
- `core/canonical`: `HasInjectiveDimensionLT A p`;
- `bridge/view`: the fixed-target vanishing hypothesis `∀ B, Subsingleton (Ext B A p)` and the
  Yoneda/long-exact-sequence proof infrastructure that turns it into `HasInjectiveDimensionLT A p`.
-/

namespace HasInjectiveDimensionLT

-- Proof sketch: represent any class in `Ext B A i` for `i > p` by a Yoneda extension using
-- Lemma 13.27.5, split that extension at degree `p`, and factor the class through an element of
-- `Ext B C p`, which is zero by the hypothesis.
/-- Companion bridge: if the degree-`p` `Ext` groups into `A` vanish for every source object,
then `A` has injective dimension `< p`. -/
theorem of_ext_vanishing
    (A : C) (p : ℕ) (hExt : ∀ B : C, Subsingleton (Ext B A p)) :
    HasInjectiveDimensionLT A p := by
  sorry

end HasInjectiveDimensionLT

/-- Lemma 13.27.8: if the degree-`p` Ext groups in an abelian category vanish for every pair of
objects, then every object has injective dimension `< p`. -/
theorem hasInjectiveDimensionLT_of_uniform_vanishing
    (p : ℕ) (hExt : ∀ A B : C, Subsingleton (Ext B A p)) (A : C) :
    HasInjectiveDimensionLT A p :=
  HasInjectiveDimensionLT.of_ext_vanishing A p (hExt A)

end CategoryTheory

/-! ### Lemma_13_27_9 (from Chap13) -/
open CategoryTheory Limits
open CategoryTheory.Abelian
open DerivedCategory
open scoped CategoryTheory DerivedExt

universe w v u

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜] [HasExt.{w} 𝒜]

/- Domain-style sampling for bounded derived decompositions:
- primary domain: objects of `D(𝒜)`, their cohomology objects in `𝒜`, and finite biproduct
  realizations of the intrinsic shifted-cohomology family over bounded integer intervals;
- sampled owner declarations:
  `CategoryTheory.derivedCategory_t_bounded_iff`,
  `DerivedCategory.isGE_iff`,
  `DerivedCategory.isLE_iff`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.singleFunctor`,
  `Set.Icc`,
  `CategoryTheory.Abelian.Ext`;
- best owner abstraction: the intrinsic family `i ↦ H^i(K)[-i]` is attached directly to
  `K : D(𝒜)`, while explicit bounds `a ≤ * ≤ b` belong only to the bridge that realizes a finite
  subfamily as a biproduct for bounded-amplitude objects;
- primitive data: the derived object `K : D(𝒜)` and the canonical cohomology owners `H^i`;
- derived API: the intrinsic family `shiftedCohomology 𝒜 K`, the interval restriction
  `shiftedCohomologyOn 𝒜 K a b`, the bounded-amplitude splitting theorem with hypotheses
  `K.IsGE a` and `K.IsLE b`, and the bounded-derived specialization obtained from
  `derivedCategory_t_bounded_iff`.

Source/core/bridge triage:
- `source-facing`: the bounded-derived splitting statement for `K : Dᵇ(𝒜)` and the intrinsic
  shifted-cohomology family `i ↦ H^i(K)[-i]`;
- `core/canonical`: `D(𝒜)`, `Set.Icc`, `H^i`, `singleFunctor`,
  `CategoryTheory.derivedCategory_t_bounded_iff`, `DerivedCategory.isGE_iff`,
  `DerivedCategory.isLE_iff`, `CategoryTheory.Abelian.Ext`;
- `bridge/view`: the explicit interval restriction in `D(𝒜)` with bounds `a b` and the bounded
  finite-biproduct realization hypotheses `K.IsGE a`, `K.IsLE b`.
-/

/-- The intrinsic shifted cohomology family `i ↦ H^i(K)[-i]` attached to `K : D(𝒜)`. -/
noncomputable abbrev shiftedCohomology (K : DerivedCategory 𝒜) :
    ℤ → DerivedCategory 𝒜 :=
  fun i ↦ (singleFunctor 𝒜 i).obj ((H^i).obj K)

/-- The restriction of the shifted cohomology family of `K` to the finite interval `[a, b]`. -/
noncomputable abbrev shiftedCohomologyOn (K : DerivedCategory 𝒜) (a b : ℤ) :
    Set.Icc a b → DerivedCategory 𝒜 :=
  fun i ↦ shiftedCohomology 𝒜 K i

-- Proof sketch: choose bounds `a ≤ i ≤ b` for the cohomological amplitude of `K` and induct on
-- `b - a`; use the truncation triangle for the top degree, show that its connecting morphism
-- vanishes because it lies in a higher `Ext` group from `H^b(K)` to the lower cohomologies,
-- split the triangle, and iterate.
/-- Once explicit cohomological bounds are fixed, the shifted cohomology pieces of `K` split off
as a finite biproduct over that interval. -/
theorem isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing_of_isGE_isLE
    (K : DerivedCategory 𝒜) (a b : ℤ) (hGE : K.IsGE a) (hLE : K.IsLE b)
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((H^i).obj K) ((H^j).obj K) n)) :
    Nonempty (K ≅ ⨁ shiftedCohomologyOn 𝒜 K a b) := sorry

/-- Lemma 13.27.9: if all higher extension groups in `𝒜` from higher cohomology to lower
cohomology vanish in degrees `n ≥ 2`, then any bounded derived object is isomorphic to the
biproduct of its shifted cohomology objects over some interval containing its cohomological
support. -/
theorem isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing
    (K : Dᵇ(𝒜))
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((H^i).obj K.obj) ((H^j).obj K.obj) n)) :
    ∃ a b : ℤ, Nonempty (K.obj ≅ ⨁ shiftedCohomologyOn 𝒜 K.obj a b) := by
  rcases (derivedCategory_t_bounded_iff K.obj).1 K.property with
    ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hGE : K.obj.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact ha i hi
  have hLE : K.obj.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hb i hi
  exact ⟨a, b,
    isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing_of_isGE_isLE
      𝒜 K.obj a b hGE hLE hExt⟩

end

/-! ### Lemma_13_27_10 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open DerivedCategory
open Abelian.Ext
open scoped CategoryTheory

universe w v u

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜] [HasExt.{w} 𝒜]

/- Domain-style sampling for bounded derived decompositions:
- primary domain: bounded objects in `D(𝒜)`, their cohomology objects, and the Ext-vanishing
  criteria that force splitting;
- sampled owner declarations:
  `Dᵇ(𝒜)`,
  `shiftedCohomology`,
  `shiftedCohomologyOn`,
  `isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing`,
  `CategoryTheory.hasInjectiveDimensionLT_of_uniform_vanishing`,
  `CategoryTheory.HasInjectiveDimensionLT.of_ext_vanishing`;
- best owner abstraction: the source-facing input is a bounded derived object `K : Dᵇ(𝒜)`, while
  `shiftedCohomology` is the intrinsic family `i ↦ H^i(K)[-i]` on `D(𝒜)`, its finite interval
  restriction `shiftedCohomologyOn` is only the bounded-realization bridge from `Lemma_13_27_9`,
  and the degree-two vanishing hypothesis is converted pointwise into the canonical owner
  `HasInjectiveDimensionLT`;
- primitive data: the bounded derived object `K` and the degree-two vanishing hypothesis on `Ext`;
- derived API: the resulting source-facing injective-dimension bridge
  `CategoryTheory.hasInjectiveDimensionLT_of_uniform_vanishing`, together with the owner-level
  pointwise `Ext`-vanishing consequence furnished by `CategoryTheory.HasInjectiveDimensionLT`.

Source/core/bridge triage:
- `source-facing`: the textbook splitting statement for bounded derived objects under uniform
  degree-two Ext vanishing;
- `core/canonical`: `Dᵇ(𝒜)`, `shiftedCohomology`,
  `isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing`,
  `CategoryTheory.HasInjectiveDimensionLT`;
- `bridge/view`: the interval restriction `shiftedCohomologyOn` and the reduction from degree-two
  Ext vanishing on objects of `𝒜` to the general higher-degree cohomology-Ext hypothesis
  required by `13.27.9`.
-/

-- Proof sketch: apply Lemma 13.27.8 to each cohomology object `H^j(K)` to get the canonical
-- owner `HasInjectiveDimensionLT _ 2`, then feed the resulting higher `Ext`-vanishing into
-- Lemma 13.27.9 for the chosen cohomological bounds `[a, b]` of `K`.
/-- Lemma 13.27.10: if the degree-two `Ext` groups in an abelian category vanish for every pair
of objects, then any bounded derived object is isomorphic to the biproduct of its shifted
cohomology objects over some interval containing its cohomological support. -/
theorem isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing
    (K : Dᵇ(𝒜))
    (hExt₂ : ∀ A B : 𝒜, Subsingleton (Ext B A 2)) :
    ∃ a b : ℤ, Nonempty (K.obj ≅ ⨁ shiftedCohomologyOn 𝒜 K.obj a b) := by
  refine isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing 𝒜 K ?_
  intro n hn i j hij
  letI : HasInjectiveDimensionLT ((H^j).obj K.obj) 2 :=
    hasInjectiveDimensionLT_of_uniform_vanishing 2 hExt₂ ((H^j).obj K.obj)
  exact HasInjectiveDimensionLT.subsingleton ((H^j).obj K.obj) 2 n hn ((H^i).obj K.obj)

end
