import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.Limits

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_154_1 (from Chap10) -/
open CategoryTheory MorphismProperty
open CommRingCat
open scoped TensorProduct

universe u

namespace RingHom

section

variable {R : Type u} {A : Type u} {R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/- Domain-style sampling for Lemma 10.154.1:
* primary domain: filtered-colimit closure of étale morphisms in `CommRingCat`;
* sampled owner declarations:
  - `CommRingCat.etale`, the chapter owner for étale morphisms in `CommRingCat`;
  - `CategoryTheory.MorphismProperty.ind`, the canonical filtered-colimit owner;
  - `RingHom.IsFilteredColimitOfEtale`, the chapter source-facing owner that hides the
    same-universe `ULift` presentation;
  - `RingHom.Etale.isStableUnderBaseChange`, the ring-hom base-change theorem for étaleness;
  - `CommRingCat.isPushout_tensorProduct`, the canonical tensor-product pushout square.
* best owner abstraction: `RingHom.IsFilteredColimitOfEtale` as a ring-hom property, with its
  base-change witness `RingHom.IsFilteredColimitOfEtale.isStableUnderBaseChange`;
* primitive data: the owner-level filtered-colimit-of-étale hypothesis on the structural map;
* derived API: the tensor-product corollary `filteredColimitOfEtale_baseChange`.

Source/core/bridge triage:
* `source-facing`: the tensor-product base-change corollary
  `filteredColimitOfEtale_baseChange`;
* `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
* `bridge/view`: the hidden same-universe `ULift` presentation used by
  `RingHom.IsFilteredColimitOfEtale`.
-/

private instance etale_isStableUnderCobaseChange : CommRingCat.etale.IsStableUnderCobaseChange := by
  simpa [CommRingCat.etale, RingHom.toMorphismProperty] using
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2
      RingHom.Etale.isStableUnderBaseChange

namespace IsFilteredColimitOfEtale

-- Proof sketch: unfold the chapter owner into the categorical owner
-- `ind CommRingCat.etale` on the `ULift`ed same-universe presentation of the map, lift the given
-- pushout square through the canonical `ULift` ring isomorphisms, and apply cobase-change
-- stability of `ind CommRingCat.etale`.
/-- Filtered colimits of étale ring maps are stable under base change. -/
theorem isStableUnderBaseChange : RingHom.IsStableUnderBaseChange RingHom.IsFilteredColimitOfEtale := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _ hRS
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift R) (ULift S) := ULift.algebra' R (ULift S)
  let _ : Algebra R (ULift R') := ULift.algebra
  let _ : Algebra (ULift R) (ULift R') := ULift.algebra' R (ULift R')
  let _ : Algebra S (ULift S') := ULift.algebra
  let _ : Algebra (ULift S) (ULift S') := ULift.algebra' S (ULift S')
  let _ : Algebra R' (ULift S') := ULift.algebra
  let _ : Algebra (ULift R') (ULift S') := ULift.algebra' R' (ULift S')
  dsimp [RingHom.IsFilteredColimitOfEtale] at hRS ⊢
  let sq₀ : IsPushout
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (algebraMap S S'))
      (CommRingCat.ofHom (algebraMap R' S')) :=
    CommRingCat.isPushout_of_isPushout R S R' S'
  let eR : CommRingCat.of R ≅ CommRingCat.of (ULift R) :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : R ≃+* ULift R)
  let eS : CommRingCat.of S ≅ CommRingCat.of (ULift S) :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : S ≃+* ULift S)
  let eR' : CommRingCat.of R' ≅ CommRingCat.of (ULift R') :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : R' ≃+* ULift R')
  let eS' : CommRingCat.of S' ≅ CommRingCat.of (ULift S') :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : S' ≃+* ULift S')
  let sq : IsPushout
      (CommRingCat.ofHom (algebraMap (ULift R) (ULift S)))
      (CommRingCat.ofHom (algebraMap (ULift R) (ULift R')))
      (CommRingCat.ofHom (algebraMap (ULift S) (ULift S')))
      (CommRingCat.ofHom (algebraMap (ULift R') (ULift S'))) :=
    sq₀.of_iso eR eS eR' eS'
      (by ext x; rfl) (by ext x; rfl) (by ext x; rfl) (by ext x; rfl)
  exact of_isPushout sq.flip hRS

end IsFilteredColimitOfEtale

-- Proof sketch: equip `R' ⊗[R] A` with the canonical tensor-product pushout data and specialize
-- the owner-level base-change theorem above.
/-- Lemma 10.154.1: if `A` is a filtered colimit of étale `R`-algebras, then after any base
change `R → R'`, the canonical map `R' → R' ⊗[R] A` is again a filtered colimit of étale ring
maps. -/
theorem filteredColimitOfEtale_baseChange
    (hA : (algebraMap R A).IsFilteredColimitOfEtale) :
    (algebraMap R' (R' ⊗[R] A)).IsFilteredColimitOfEtale := by
  let _ : Algebra A (R' ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra R' (R' ⊗[R] A) := Algebra.TensorProduct.leftAlgebra
  let _ : IsScalarTower R A (R' ⊗[R] A) := by infer_instance
  let _ : IsScalarTower R R' (R' ⊗[R] A) := by infer_instance
  let _ : Algebra.IsPushout R A R' (R' ⊗[R] A) := by infer_instance
  exact IsFilteredColimitOfEtale.isStableUnderBaseChange R A R' (R' ⊗[R] A) hA

end

end RingHom

/-! ### Lemma_10_154_2 (from Chap10) -/
universe u v w

namespace RingHom

section

/- Domain-style sampling:
* primary domain: composition closure for ind-étale morphisms in commutative algebra;
* owner declarations inspected:
  - `CategoryTheory.MorphismProperty.ind`;
  - `CategoryTheory.MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads`;
  - `CommRingCat.etale`;
  - `RingHom.IsFilteredColimitOfEtale`.
* owner decision:
  - `source-facing`: `RingHom.isFilteredColimitOfEtale_comp`;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the `ULift`-based same-universe presentation hidden inside
    `RingHom.IsFilteredColimitOfEtale`.

Primitive data are just the composable ring maps `f`, `g` and their owner-level ind-étale
hypotheses. The universe-lift bookkeeping is derived bridge data and should stay hidden in the
source-facing owner rather than reappearing as a same-universe restriction on `A`, `B`, and `C`.
-/

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]

-- Proof sketch: present `B` as a filtered colimit of étale `A`-algebras and `C` as a filtered
-- colimit of étale `B`-algebras. For a finitely presented `A`-algebra mapping to `C`, first factor
-- through some étale `B`-stage by finite presentation, then descend that stage to an étale
-- `A`-algebra by the base-change descent result of Lemma `10.143.3`. The factorization criterion
-- from Lemma `10.127.4` then shows that `A → C` is a filtered colimit of étale maps.
/-- Lemma 10.154.2: the composite of two ring maps that are filtered colimits of étale ring maps
is again a filtered colimit of étale ring maps. -/
theorem isFilteredColimitOfEtale_comp
    (f : A →+* B) (g : B →+* C)
    (hf : f.IsFilteredColimitOfEtale)
    (hg : g.IsFilteredColimitOfEtale) :
    (g.comp f).IsFilteredColimitOfEtale := sorry

end

end RingHom

/-! ### Lemma_10_154_3 (from Chap10) -/
open CategoryTheory MorphismProperty Limits
open CommRingCat

universe u v w

namespace CommRingCat

/-- The morphism property on `CommRingCat` consisting of étale ring maps. -/
abbrev etale : MorphismProperty CommRingCat.{u} :=
  fun _ _ f ↦ f.hom.Etale

instance etale_respectsIso : CommRingCat.etale.RespectsIso := by
  simpa [CommRingCat.etale] using
    (RingHom.toMorphismProperty_respectsIso_iff (P := RingHom.Etale)).1 RingHom.Etale.respectsIso

end CommRingCat

/-- Helper for Lemma 10.154.3: a finitely presented `R`-algebra in the under category is
finitely presentable for any requested filtered-index universe. -/
lemma under_isFinitelyPresentable_of_finitePresentation_of_size
    {R : Type u} [CommRing R] (S : Under (CommRingCat.of R))
    (hS : S.hom.hom.FinitePresentation) :
    IsFinitelyPresentable.{w} S := by
  -- TODO: compare `IsFinitelyPresentable.{u}` and `IsFinitelyPresentable.{w}` by transporting the
  -- owner theorem `CommRingCat.isFinitelyPresentable_under` through
  -- `isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj` and the cross-universe
  -- monotonicity lemma `Functor.isCardinalAccessible_of_le` for `κ = ℵ₀`.
  sorry

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- An `R`-algebra map `f : R →+* A` is a filtered colimit of étale `R`-algebras. This thin
source-facing wrapper hides the universe-lift bookkeeping needed to express the canonical owner
`CategoryTheory.MorphismProperty.ind CommRingCat.etale`. -/
abbrev IsFilteredColimitOfEtale (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  ind.{max u v, max u v, max u v + 1} CommRingCat.etale
    (ofHom (algebraMap (ULift.{v} R) (ULift A)))

end

section

variable {R A : Type u} [CommRing R] [CommRing A]
variable [Algebra R A]
variable {J : Type v} [Category.{v} J] [IsFiltered J]

-- Proof sketch: for each stage `A_i`, choose a filtered diagram of étale `R`-algebras presenting
-- it. Since étale maps are finitely presented, Lemma `10.127.3` factors each transition map
-- between outer stages through a later inner étale stage. The Grothendieck construction on these
-- stagewise filtered diagrams is again filtered, and its colimit identifies with `A`.
--
-- Layering for this item:
-- * source-facing: a filtered diagram of commutative `R`-algebras in `Under (CommRingCat.of R)`;
-- * core/canonical owner: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
-- * bridge/view: identifying the cocone point with a chosen `R`-algebra via an isomorphism in
--   `Under (CommRingCat.of R)`.

/-- Helper for Lemma 10.154.3: an étale map in `CommRingCat` is finitely presentable as a
morphism in the corresponding under category, for any requested filtered-index size. -/
lemma etale_isFinitelyPresentable {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (hf : CommRingCat.etale f) :
    MorphismProperty.isFinitelyPresentable.{w} CommRingCat f := by
  -- Unpack étaleness to the finite-presentation component supplied by the owner theorem.
  rw [CommRingCat.etale] at hf
  have hfp : f.hom.FinitePresentation :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).2.2
  -- Then move from the under-category object to the corresponding morphism property.
  exact under_isFinitelyPresentable_of_finitePresentation_of_size (Under.mk f) hfp

/-- Helper for Lemma 10.154.3: an `ind`-étale morphism in `CommRingCat` yields a filtered
presentation in the under category whose stages are étale. -/
lemma ind_under_presentation_of_ind_etale {S : Under (CommRingCat.of R)}
    (hS : ind.{v, u, u + 1} CommRingCat.etale S.hom) :
    ∃ (K : Type v) (_ : SmallCategory K) (_ : IsFiltered K)
      (pres : ColimitPresentation K S), ∀ k, CommRingCat.etale (pres.diag.obj k).hom := by
  -- Translate the morphism-level `ind` witness to the object-level under-category owner.
  rw [MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale) (f := S.hom)] at hS
  simpa [CategoryTheory.ObjectProperty.ind, CategoryTheory.MorphismProperty.underObj] using hS

/-- Helper for Lemma 10.154.3: binding a filtered presentation of `X` with filtered presentations
of each stage by étale `R`-algebras gives a single filtered étale presentation of `X`. -/
lemma bound_under_presentation_mem_ind_etale
    {X : Under (CommRingCat.of R)} {K : J → Type v} [∀ j, SmallCategory (K j)]
    [∀ j, IsFiltered (K j)] (outer : ColimitPresentation J X)
    (inner : ∀ j, ColimitPresentation (K j) (outer.diag.obj j))
    (hEtale : ∀ j k, CommRingCat.etale ((inner j).diag.obj k).hom) :
    ObjectProperty.ind.{v} CommRingCat.etale.underObj X := by
  -- TODO: replace the raw `bind` total category by a source-faithful small-model construction
  -- whose morphisms stay in the outer index universe `v`; the direct `Total inner` route raises
  -- the hom universe to that of `Under (CommRingCat.of R)`.
  sorry

/-- Helper for Lemma 10.154.3: the raw owner on `algebraMap R A` is equivalent, up to the
canonical `ULift` isomorphisms, to the source-facing wrapper `RingHom.IsFilteredColimitOfEtale`. -/
lemma raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale :
    ind.{u, u, u + 1} CommRingCat.etale (CommRingCat.ofHom (algebraMap R A)) ↔
      (algebraMap R A).IsFilteredColimitOfEtale := by
  -- Transport the raw owner along the canonical source and target `ULift` isomorphisms.
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{u} R) (ULift A) := ULift.algebra' R (ULift A)
  let eR : CommRingCat.of R ≅ CommRingCat.of (ULift R) :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : R ≃+* ULift R)
  let eA : CommRingCat.of A ≅ CommRingCat.of (ULift A) :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : A ≃+* ULift A)
  constructor
  · intro h
    have h' :
        ind.{u, u, u + 1} CommRingCat.etale
          (eR.inv ≫ CommRingCat.ofHom (algebraMap R A) ≫ eA.hom) := by
      exact MorphismProperty.RespectsIso.precomp _ eR.inv _
        (MorphismProperty.RespectsIso.postcomp _ eA.hom _ h)
    dsimp [RingHom.IsFilteredColimitOfEtale]
    simpa [eR, eA] using h'
  · intro h
    dsimp [RingHom.IsFilteredColimitOfEtale] at h
    have h' :
        ind.{u, u, u + 1} CommRingCat.etale
          (eR.hom ≫ CommRingCat.ofHom (algebraMap (ULift R) (ULift A)) ≫ eA.inv) := by
      exact MorphismProperty.RespectsIso.precomp _ eR.hom _
        (MorphismProperty.RespectsIso.postcomp _ eA.inv _ h)
    simpa [eR, eA] using h'

/-- Helper for Lemma 10.154.3: an arbitrary-size raw `ind` witness for `algebraMap R A` can be
reconstructed as the same-universe witness used by `RingHom.IsFilteredColimitOfEtale`. -/
lemma raw_ind_etale_algebraMap_of_size
    (h : ind.{v, u, u + 1} CommRingCat.etale (CommRingCat.ofHom (algebraMap R A))) :
    (algebraMap R A).IsFilteredColimitOfEtale := by
  -- TODO: shrink the filtered witness category to the same-universe wrapper without using
  -- `MorphismProperty.ind_iff_exists`; the current blocker is the missing finitely accessible
  -- owner for `Under (CommRingCat.of R)`.
  sorry

/-- Lemma 10.154.3: if `A` is a filtered colimit of `R`-algebras and each stage is itself a
filtered colimit of étale `R`-algebras, then `A` is a filtered colimit of étale `R`-algebras. -/
theorem isFilteredColimitOfEtale_of_isColimit_filtered_system
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, ind.{v, u, u + 1} CommRingCat.etale (F.obj j).hom) :
    ind.{v, u, u + 1} CommRingCat.etale c.pt.hom := by
  -- Route correction: flatten the outer filtered system and the stagewise filtered systems
  -- directly in `Under (CommRingCat.of R)`.
  let outer : ColimitPresentation J c.pt :=
    { diag := F
      ι := c.ι
      isColimit := hc }
  -- Convert each stage hypothesis to a concrete under-category presentation by étale stages.
  have hPresentations : ∀ j, ∃ (K : Type v) (_ : SmallCategory K) (_ : IsFiltered K)
      (pres : ColimitPresentation K (F.obj j)), ∀ k, CommRingCat.etale (pres.diag.obj k).hom := by
    intro j
    exact ind_under_presentation_of_ind_etale (R := R) (hF j)
  choose K hKcat hKfiltered inner hEtale using hPresentations
  letI (j : J) : SmallCategory (K j) := hKcat j
  letI (j : J) : IsFiltered (K j) := hKfiltered j
  -- Translate the bound presentation back to the morphism-level `ind` owner.
  rw [MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale) (f := c.pt.hom)]
  simpa [show c.pt = CategoryTheory.Under.mk c.pt.hom from rfl] using
    bound_under_presentation_mem_ind_etale (R := R) (J := J) (K := K) outer inner hEtale

/-- Companion form of Lemma 10.154.3 stated through the source-facing owner
`RingHom.IsFilteredColimitOfEtale`. -/
theorem algebraMap_isFilteredColimitOfEtale_of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, ind.{v, u, u + 1} CommRingCat.etale (F.obj j).hom) :
    (algebraMap R A).IsFilteredColimitOfEtale := by
  -- First obtain the raw `ind` statement on the cocone point from the fixed-source theorem.
  have hraw_pt :
      ind.{v, u, u + 1} CommRingCat.etale c.pt.hom :=
    isFilteredColimitOfEtale_of_isColimit_filtered_system F c hc hF
  -- The isomorphism `e` only changes the target object in the under category, so postcompose.
  have hraw :
      ind.{v, u, u + 1} CommRingCat.etale (CommRingCat.ofHom (algebraMap R A)) := by
    have hpost :
        ind.{v, u, u + 1} CommRingCat.etale (c.pt.hom ≫ e.hom.right) :=
      MorphismProperty.RespectsIso.postcomp (P := ind CommRingCat.etale) e.hom.right c.pt.hom
        hraw_pt
    rw [Under.w e.hom] at hpost
    exact hpost
  -- Rebuild the same-universe raw witness and translate it to the source-facing wrapper.
  exact raw_ind_etale_algebraMap_of_size hraw

end

end RingHom

/-! ### Lemma_10_154_4 (from Chap10) -/
open CategoryTheory Limits
open CommRingCat
open CommRingCat.Hom

universe u v

namespace RingHom

section

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/- Domain-style sampling for Lemma 10.154.4:
* primary domain: filtered-colimit closure of ind-étale morphisms in the arrow category of
  commutative rings;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfEtale`, the chapter source-facing owner for ind-étale ring maps;
  - `RingHom.filteredColimitOfEtale_baseChange`, the owner-level base-change theorem;
  - `RingHom.isFilteredColimitOfEtale_of_isColimit_filtered_system`, the fixed-source colimit
    theorem;
  - `CategoryTheory.MorphismProperty.ind`, the core filtered-colimit owner behind the wrapper.
* owner decision:
  - `source-facing`: `RingHom.isFilteredColimitOfEtale_colimit_of_directed_ringMap_system`;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the wrapper `RingHom.IsFilteredColimitOfEtale`, which hides the same-universe
    `ULift` presentation of the core owner.
* primitive data: a directed diagram of ring maps in `Arrow CommRingCat` and the owner-level
  ind-étale hypothesis on each stage map;
* derived API: the induced owner-level ind-étale statement for the colimit map.

Since Lemma `10.154.3` already introduced `RingHom.IsFilteredColimitOfEtale` as the source-facing
owner, this file should use that owner directly instead of repeating the raw
`ind CommRingCat.etale` presentation in its public theorem surface.
-/

-- Proof sketch: view the directed system of ring maps as a diagram in `Arrow CommRingCat`. For
-- each stage, base change its étale presentation along the map from the source ring to the colimit
-- source using Lemma `10.154.1`. These base-changed presentations assemble into a filtered diagram
-- over the colimit source, and Lemma `10.154.3` upgrades the resulting filtered colimit
-- decomposition of the colimit target map to one by étale algebras.
/-- Lemma 10.154.4: if a directed system of commutative ring maps has the property that each stage
map is a filtered colimit of étale algebras over its source, then the colimit map from the
colimit of the source rings to the colimit of the target rings is also a filtered colimit of
étale algebras. -/
theorem isFilteredColimitOfEtale_colimit_of_directed_ringMap_system
    (F : I ⥤ Arrow CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, (hom (F.obj i).hom).IsFilteredColimitOfEtale) :
    (hom c.pt.hom).IsFilteredColimitOfEtale := sorry

end

end RingHom

/-! ### Lemma_10_154_5 (from Chap10) -/
universe u v w

namespace RingHom

section

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/- Domain-style sampling for Lemma 10.154.5:
* primary domain: filtered-colimit closure of étale ring maps in commutative algebra, specialized
  to a common-base comparison map `A → B`;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfEtale`, the chapter source-facing owner for ind-étale ring maps;
  - `RingHom.filteredColimitOfEtale_baseChange`, the owner-level base-change theorem;
  - `RingHom.isFilteredColimitOfEtale_comp`, the owner-level composition theorem;
  - `Algebra.etale_of_etale_over_common_base`, the stagewise common-base étale owner.
* owner decision:
  - `source-facing`: the Stacks lemma for the structural map `A → B` under common-base
    ind-étale hypotheses over `R`;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the wrapper `RingHom.IsFilteredColimitOfEtale`, which hides the `ULift`
    presentation of the categorical owner across possibly different universes.
* primitive data: only the owner-level ind-étale hypotheses on `R → A` and `R → B`, together with
  the given `A`-algebra structure on `B`;
* derived API: the induced owner-level ind-étale statement for `A → B`.

This file should therefore speak directly through `RingHom.IsFilteredColimitOfEtale` rather than
repeating the raw `ind CommRingCat.etale (ofHom ...)` presentation or reintroducing an unnecessary
same-universe restriction in its public theorem surface.
-/

-- Proof sketch: write `A` and `B` as filtered colimits of étale `R`-algebras. For each étale
-- stage `Aᵢ → A`, finite presentation factors the composite `Aᵢ → B` through some étale
-- `R`-stage `Bⱼ → B`. By Lemma `10.143.8`, the induced map `Aᵢ → Bⱼ` is étale, and then base
-- change along `Aᵢ → A` keeps it étale over `A`. These tensor-product stages form a filtered
-- system whose colimit is `B`, yielding the desired presentation over `A`.
/-- Lemma 10.154.5: if `A` and `B` are filtered colimits of étale `R`-algebras and `B` is an
`A`-algebra over `R`, then `A → B` is a filtered colimit of étale `A`-algebras. -/
theorem isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base
    (hA : (algebraMap R A).IsFilteredColimitOfEtale)
    (hB : (algebraMap R B).IsFilteredColimitOfEtale) :
    (algebraMap A B).IsFilteredColimitOfEtale := sorry

end

end RingHom

/-! ### Lemma_10_154_6 (from Chap10) -/
universe u

open IsLocalRing
open RingHom

section

variable {R : Type u} {A : Type u} {S : Type u}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [HenselianLocalRing S]

/-
Domain-style sampling:
- primary domain: henselian local rings, residue-field maps at primes, and ind-étale
  `R`-algebras;
- sampled owner declarations in the local chapter/domain:
  `RingHom.IsFilteredColimitOfEtale`,
  `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`,
  `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`,
  `HenselianLocalRing`;
- best owner abstraction: the ind-étale presentation should use the chapter owner
  `RingHom.IsFilteredColimitOfEtale`, while the present theorem remains the source-facing
  henselian lifting statement built on top of that owner and the residue-field API;
- primitive data vs. derived API:
  the primitive inputs are the `R`-algebra map `R → A`, its ind-étale presentation, the prime
  `q`, and the compatible residue-field map `τ`;
  the derived API is the unique `R`-algebra map `A → S` with prescribed maximal-ideal fiber and
  residue-field action.

Source/core/bridge triage:
- `source-facing`: the present ind-étale lifting theorem;
- `core/canonical`: `HenselianLocalRing S`, `RingHom.IsFilteredColimitOfEtale`, and
  `Ideal.ResidueField.map`;
- `bridge/view`: the compatibility condition on `τ` and the resulting unique `R`-algebra point
  of `A` valued in `S`.
-/

-- Proof sketch: write `A` as a filtered colimit of étale `R`-algebras using `hA`. For each étale
-- stage, restrict `q` and `τ`, then apply Lemma `10.153.11` to obtain a unique compatible map from
-- that stage to `S`. The uniqueness clause makes these stage maps compatible, so they glue along
-- the colimit to a unique `R`-algebra map `A → S` with the prescribed inverse image of
-- `maximalIdeal S` and induced residue-field map.
/-- Lemma 10.154.6: let `R → S` be a ring map with `S` henselian local. If `A` is a filtered
colimit of étale `R`-algebras, `q` is a prime of `A` whose contraction is the contraction of
`maximalIdeal S`, and `τ : κ(q) → S / maximalIdeal S` is compatible with the induced map from the
common residue field `κ(q ∩ R)`, then there exists a unique `R`-algebra map `f : A → S` whose
inverse image of `maximalIdeal S` is `q` and which induces `τ` on residue fields. -/
lemma existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap
    (hA : (algebraMap R A).IsFilteredColimitOfEtale) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ := sorry

end

/-! ### Lemma_10_154_7 (from Chap10) -/
open IsLocalRing
open RingHom

universe u

section

variable {R S S' K : Type u}
variable [CommRing R] [CommRing S] [CommRing S'] [Field K]
variable [Algebra R S] [Algebra R S'] [Algebra R K]
variable [Algebra S K] [Algebra S' K]
variable [IsScalarTower R S K] [IsScalarTower R S' K]
variable [HenselianLocalRing S] [HenselianLocalRing S']
variable [IsLocalHom (algebraMap S K)] [IsLocalHom (algebraMap S' K)]

/- Domain-style sampling:
- primary domain: henselian local rings, filtered colimits of étale algebras, and residue-field
  comparisons through maps to a common field;
- sampled owner declarations of the same kind:
  `HenselianLocalRing`,
  `RingHom.IsFilteredColimitOfEtale`,
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`,
  `ResidueField.lift`;
- best owner abstraction: the canonical owners here are `HenselianLocalRing`,
  `IsLocalHom`, and `RingHom.IsFilteredColimitOfEtale`; the present lemma stays
  `source-facing`, since it adds the extra mathematical content of comparing two henselian local
  `R`-algebras through a common residue field target `K`;
- primitive data vs. derived API:
  the primitive inputs are the two ind-étale `R`-algebra structures and the two bijective
  residue-field comparison maps to `K`;
  the derived API is the unique compatible `R`-algebra equivalence `S ≃ₐ[R] S'`.

Source/core/bridge triage:
- `source-facing`: the present uniqueness statement for two henselian local `R`-algebras with a
  common residue-field identification;
- `core/canonical`: `HenselianLocalRing`, `IsLocalHom`, `RingHom.IsFilteredColimitOfEtale`, and
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`;
- `bridge/view`: the chosen field `K` and the bijectivity of `ResidueField.lift` for the two
  structural maps.
-/

-- Proof sketch: apply Lemma `10.154.6` with `A = S` and target `S'`, using the map
-- `ResidueField.lift (algebraMap S K)` composed with the inverse of
-- `ResidueField.lift (algebraMap S' K)` to obtain a unique `R`-algebra map `S → S'`
-- compatible with the maps to `K`, and similarly a unique map `S' → S`. The two composites are
-- the unique endomorphisms compatible with the corresponding maps to `K`, so they are identities;
-- hence the two maps are inverse `R`-algebra isomorphisms, unique by the same compatibility
-- condition.
/-- Lemma 10.154.7: given a commutative diagram `S → K ← S'` over `R` in which `S` and `S'` are
henselian local rings, both are filtered colimits of étale `R`-algebras, and the maps to the
field `K` identify `K` with the residue field of each source, there exists a unique
`R`-algebra isomorphism `S ≃ₐ[R] S'` compatible with the maps to `K`. -/
lemma existsUnique_algEquiv_of_henselianLocal_of_filteredColimitOfEtale_of_common_residueField
    (hS : (algebraMap R S).IsFilteredColimitOfEtale)
    (hS' : (algebraMap R S').IsFilteredColimitOfEtale)
    (hκ : Function.Bijective (ResidueField.lift (algebraMap S K)))
    (hκ' : Function.Bijective (ResidueField.lift (algebraMap S' K))) :
    ∃! e : S ≃ₐ[R] S', (algebraMap S' K).comp (e : S →+* S') = algebraMap S K := sorry

end

/-! ### Lemma_10_154_8 (from Chap10) -/
universe u v

section

open IsLocalRing Polynomial

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (R : I → Type u) [∀ i, CommRing (R i)]
variable (φ : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (φ · · ·)]
variable [∀ i j hij, IsLocalHom (φ i j hij)]

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ φ i j h)

/-- Helper for Lemma 10.154.8: any finite family of elements of the direct limit already appears at
one stage. -/
lemma exists_stage_family :
    ∀ n : ℕ, ∀ a : Fin n → R∞, ∃ i, ∃ b : Fin n → R i, ∀ m, Ring.DirectLimit.of R (φ · · ·) i (b m) = a m
  | 0, a => by
      let i : I := Classical.arbitrary I
      refine ⟨i, fun m => Fin.elim0 m, ?_⟩
      intro m
      exact Fin.elim0 m
  | n + 1, a => by
      -- Descend the tail first, then enlarge to a common upper bound with the head coefficient.
      obtain ⟨i, b, hb⟩ := exists_stage_family n (fun m : Fin n ↦ a m.succ)
      obtain ⟨j, x, hx⟩ := Ring.DirectLimit.exists_of (G := R) (f := fun i j h ↦ φ i j h) (a 0)
      obtain ⟨k, hjk, hik⟩ := exists_ge_ge j i
      refine ⟨k, Fin.cons (φ j k hjk x) (fun m ↦ φ i k hik (b m)), ?_⟩
      intro m
      refine Fin.cases ?_ ?_ m
      · simpa using (show Ring.DirectLimit.of R (φ · · ·) k (φ j k hjk x) = a 0 by
          rw [Ring.DirectLimit.of_f, hx])
      · intro m
        simpa using (show Ring.DirectLimit.of R (φ · · ·) k (φ i k hik (b m)) = a m.succ by
          rw [Ring.DirectLimit.of_f, hb m])

/-- Helper for Lemma 10.154.8: a monic polynomial over the direct limit is already defined over one
stage by a monic polynomial. -/
lemma exists_stage_monic_polynomial (f : R∞[X]) (hf : f.Monic) :
    ∃ i, ∃ f_i : (R i)[X], f_i.Monic ∧ Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) f_i = f := by
  -- Descend the coefficients below the top degree and rebuild the stage polynomial via
  -- `Monic.as_sum`, which preserves monicity by construction.
  let n := f.natDegree
  obtain ⟨i, c, hc⟩ := exists_stage_family R φ n (fun m ↦ f.coeff m)
  let f_i : (R i)[X] := X ^ n + Finset.univ.sum (fun m : Fin n ↦ C (c m) * X ^ (m : ℕ))
  refine ⟨i, f_i, ?_, ?_⟩
  · -- The lower-degree tail has degree `< n`, so adjoining `X ^ n` yields a monic polynomial.
    have hdeg :
        degree (∑ m : Fin n, C (c m) * X ^ (m : ℕ)) < n :=
      degree_sum_fin_lt (fun m ↦ c m)
    dsimp [f_i]
    exact monic_X_pow_add hdeg
  · -- Map the rebuilt stage polynomial to the direct limit and compare with `Monic.as_sum`.
    dsimp [f_i]
    calc
      Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i)
          (X ^ n + Finset.univ.sum (fun m : Fin n ↦ C (c m) * X ^ (m : ℕ)))
          = X ^ n + Finset.univ.sum (fun m : Fin n ↦ C (f.coeff (m : ℕ)) * X ^ (m : ℕ)) := by
              simp [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
                hc]
      _ = X ^ n + Finset.sum (Finset.range n) (fun m ↦ C (f.coeff m) * X ^ m) := by
            simpa using
              ((Fin.sum_univ_eq_sum_range (fun m ↦ C (f.coeff m) * X ^ m)) n)
      _ = f := by
            simpa [n] using hf.as_sum.symm

section ResidueField

variable [∀ i, IsLocalRing (R i)]

/-- Helper for Lemma 10.154.8: the induced maps on stage residue fields form a directed system. -/
instance residueFieldDirectedSystem :
    DirectedSystem (fun i : I => ResidueField (R i))
      (fun i j hij => IsLocalRing.ResidueField.map (φ i j hij)) where
  map_self := by
    intro i x
    have hφ : φ i i le_rfl = RingHom.id (R i) := by
      ext y
      simpa using (DirectedSystem.map_self' (f := φ) y)
    simpa [hφ] using (IsLocalRing.ResidueField.map_id_apply (R := R i) x)
  map_map := by
    intro k j i hij hjk x
    have hφ :
        (φ j k hjk).comp (φ i j hij) = φ i k (hij.trans hjk) := by
      ext y
      simpa using (DirectedSystem.map_map' (f := φ) hij hjk y)
    calc
      IsLocalRing.ResidueField.map (φ j k hjk) (IsLocalRing.ResidueField.map (φ i j hij) x)
          = IsLocalRing.ResidueField.map ((φ j k hjk).comp (φ i j hij)) x := by
              simpa using (IsLocalRing.ResidueField.map_map (φ i j hij) (φ j k hjk) x)
      _ = IsLocalRing.ResidueField.map (φ i k (hij.trans hjk)) x := by
            simpa [hφ]

/-- Helper for Lemma 10.154.8: every residue-field element of the direct limit comes from one stage
residue field. -/
lemma exists_stage_residue_field_element (a₀ : ResidueField R∞) :
    ∃ i, ∃ a_i : ResidueField (R i),
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) a_i = a₀ := by
  -- Lift the residue-field element to the direct-limit ring, then descend that ring element.
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a₀
  obtain ⟨i, x_i, hx_i⟩ := Ring.DirectLimit.exists_of (G := R) (f := fun i j h ↦ φ i j h) x
  refine ⟨i, IsLocalRing.residue (R i) x_i, ?_⟩
  calc
    IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) (IsLocalRing.residue (R i) x_i)
        = IsLocalRing.residue R∞ (Ring.DirectLimit.of R (φ · · ·) i x_i) := by
            exact IsLocalRing.ResidueField.map_residue
              (Ring.DirectLimit.of R (φ · · ·) i) x_i
    _ = IsLocalRing.residue R∞ x := by rw [hx_i]

/-- Helper for Lemma 10.154.8: every polynomial over the direct-limit residue field is already
defined over one stage residue field. -/
lemma exists_stage_residue_polynomial (g : (ResidueField R∞)[X]) :
    ∃ i, ∃ g_i : (ResidueField (R i))[X],
      Polynomial.map (IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)) g_i = g := by
  -- Descend coefficients by polynomial induction, combining stages via directedness.
  induction g using Polynomial.induction_on with
  | C a =>
      obtain ⟨i, a_i, ha_i⟩ := exists_stage_residue_field_element R φ a
      refine ⟨i, C a_i, ?_⟩
      simpa [ha_i]
  | add g₁ g₂ ih₁ ih₂ =>
      obtain ⟨i₁, g₁i, hg₁i⟩ := ih₁
      obtain ⟨i₂, g₂i, hg₂i⟩ := ih₂
      obtain ⟨i, h₁i, h₂i⟩ := exists_ge_ge i₁ i₂
      let g_i : (ResidueField (R i))[X] :=
        g₁i.map (IsLocalRing.ResidueField.map (φ i₁ i h₁i))
          + g₂i.map (IsLocalRing.ResidueField.map (φ i₂ i h₂i))
      have hcomp₁ :
          (Ring.DirectLimit.of R (φ · · ·) i).comp (φ i₁ i h₁i)
            = Ring.DirectLimit.of R (φ · · ·) i₁ := by
        ext x
        simp [Ring.DirectLimit.of_f]
      have hcomp₂ :
          (Ring.DirectLimit.of R (φ · · ·) i).comp (φ i₂ i h₂i)
            = Ring.DirectLimit.of R (φ · · ·) i₂ := by
        ext x
        simp [Ring.DirectLimit.of_f]
      refine ⟨i, g_i, ?_⟩
      dsimp [g_i]
      have hrescomp₁ :
          (IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)).comp
              (IsLocalRing.ResidueField.map (φ i₁ i h₁i))
            = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i₁) := by
        ext x
        calc
          IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
              (IsLocalRing.ResidueField.map (φ i₁ i h₁i) x)
              = IsLocalRing.ResidueField.map
                  ((Ring.DirectLimit.of R (φ · · ·) i).comp (φ i₁ i h₁i)) x := by
                    simpa using (IsLocalRing.ResidueField.map_map
                      (φ i₁ i h₁i) (Ring.DirectLimit.of R (φ · · ·) i) x)
          _ = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i₁) x := by
                simpa [hcomp₁]
      have hrescomp₂ :
          (IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)).comp
              (IsLocalRing.ResidueField.map (φ i₂ i h₂i))
            = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i₂) := by
        ext x
        calc
          IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
              (IsLocalRing.ResidueField.map (φ i₂ i h₂i) x)
              = IsLocalRing.ResidueField.map
                  ((Ring.DirectLimit.of R (φ · · ·) i).comp (φ i₂ i h₂i)) x := by
                    simpa using (IsLocalRing.ResidueField.map_map
                      (φ i₂ i h₂i) (Ring.DirectLimit.of R (φ · · ·) i) x)
          _ = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i₂) x := by
                simpa [hcomp₂]
      rw [Polynomial.map_add, Polynomial.map_map, Polynomial.map_map, hrescomp₁, hrescomp₂, hg₁i, hg₂i]
  | monomial n a _ =>
      obtain ⟨i, a_i, ha_i⟩ := exists_stage_residue_field_element R φ a
      refine ⟨i, C a_i * X ^ (n + 1), ?_⟩
      simp [ha_i, Polynomial.map_mul, Polynomial.map_pow]

/-- Helper for Lemma 10.154.8: simple roots over the residue field of the direct limit descend to
one stage and lift there. -/
lemma directedSystem_directLimit_simple_root_lift
    [∀ i, HenselianLocalRing (R i)] :
    ∀ f : R∞[X], f.Monic → ∀ a₀ : ResidueField R∞, aeval a₀ f = 0 →
      aeval a₀ (Polynomial.derivative f) ≠ 0 →
      ∃ a : R∞, f.IsRoot a ∧ IsLocalRing.residue R∞ a = a₀ := by
  intro f hf a₀ ha₀ hderiv
  -- Descend the monic polynomial and the residue-field root to a common stage.
  obtain ⟨i_f, f_i, hf_i_monic, hf_i⟩ := exists_stage_monic_polynomial R φ f hf
  obtain ⟨i_a, a_i, ha_i⟩ := exists_stage_residue_field_element R φ a₀
  obtain ⟨i, hfi, hai⟩ := exists_ge_ge i_f i_a
  let f_stage : (R i)[X] := f_i.map (φ i_f i hfi)
  let a_stage : ResidueField (R i) := IsLocalRing.ResidueField.map (φ i_a i hai) a_i
  have hcomp_f :
      (Ring.DirectLimit.of R (φ · · ·) i).comp (φ i_f i hfi)
        = Ring.DirectLimit.of R (φ · · ·) i_f := by
    ext x
    simp [Ring.DirectLimit.of_f]
  have hcomp_a :
      (Ring.DirectLimit.of R (φ · · ·) i).comp (φ i_a i hai)
        = Ring.DirectLimit.of R (φ · · ·) i_a := by
    ext x
    simp [Ring.DirectLimit.of_f]
  have hf_stage :
      Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) f_stage = f := by
    dsimp [f_stage]
    rw [Polynomial.map_map, hcomp_f, hf_i]
  have ha_stage :
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) a_stage = a₀ := by
    dsimp [a_stage]
    calc
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
          (IsLocalRing.ResidueField.map (φ i_a i hai) a_i)
          = IsLocalRing.ResidueField.map
              ((Ring.DirectLimit.of R (φ · · ·) i).comp (φ i_a i hai)) a_i := by
                simpa using (IsLocalRing.ResidueField.map_map
                  (φ i_a i hai) (Ring.DirectLimit.of R (φ · · ·) i) a_i)
      _ = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i_a) a_i := by
            simpa [hcomp_a]
      _ = a₀ := ha_i
  have hψ_injective :
      Function.Injective
        (IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)) :=
    RingHom.injective _
  have hroot_stage_map :
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) (aeval a_stage f_stage) = 0 := by
    have hroot_stage_eq :
        IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) (aeval a_stage f_stage)
          = aeval a₀ f := by
      simpa [hf_stage, ha_stage] using
        (Polynomial.map_aeval_eq_aeval_map
          (φ := Ring.DirectLimit.of R (φ · · ·) i)
          (ψ := IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i))
          (h := (IsLocalRing.ResidueField.map_comp_residue
            (Ring.DirectLimit.of R (φ · · ·) i)).symm)
          (p := f_stage) (a := a_stage))
    exact hroot_stage_eq.trans ha₀
  have hroot_stage : aeval a_stage f_stage = 0 := by
    apply hψ_injective
    simpa using hroot_stage_map
  have hderiv_stage_map :
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
        (aeval a_stage (Polynomial.derivative f_stage))
        = aeval a₀ (Polynomial.derivative f) := by
    have hderiv_stage_eq :
        IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
          (aeval a_stage (Polynomial.derivative f_stage))
          = aeval a₀ (Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i)
              (Polynomial.derivative f_stage)) := by
      simpa [ha_stage] using
      (Polynomial.map_aeval_eq_aeval_map
        (φ := Ring.DirectLimit.of R (φ · · ·) i)
        (ψ := IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i))
        (h := (IsLocalRing.ResidueField.map_comp_residue
          (Ring.DirectLimit.of R (φ · · ·) i)).symm)
        (p := Polynomial.derivative f_stage) (a := a_stage))
    have hmap_deriv :
        Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) (Polynomial.derivative f_stage)
          = Polynomial.derivative f := by
      calc
        Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) (Polynomial.derivative f_stage)
            = Polynomial.derivative (Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) f_stage) := by
                simpa using
                  (Polynomial.derivative_map
                    (p := f_stage) (f := Ring.DirectLimit.of R (φ · · ·) i))
        _ = Polynomial.derivative f := by rw [hf_stage]
    calc
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
        (aeval a_stage (Polynomial.derivative f_stage))
          = aeval a₀ (Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i)
              (Polynomial.derivative f_stage)) := hderiv_stage_eq
      _ = aeval a₀ (Polynomial.derivative f) := by rw [hmap_deriv]
  have hderiv_stage : aeval a_stage (Polynomial.derivative f_stage) ≠ 0 := by
    intro hzero
    apply hderiv
    rw [← hderiv_stage_map, hzero, map_zero]
  have hstage_lift :
      ∀ g : (R i)[X], g.Monic → ∀ b : ResidueField (R i), aeval b g = 0 →
        aeval b (Polynomial.derivative g) ≠ 0 →
        ∃ x : R i, g.IsRoot x ∧ IsLocalRing.residue (R i) x = b :=
    ((HenselianLocalRing.TFAE (R i)).out 0 1).mp
      (show HenselianLocalRing (R i) from inferInstance)
  obtain ⟨x_i, hx_i, hres_i⟩ := hstage_lift f_stage (hf_i_monic.map (φ i_f i hfi))
    a_stage hroot_stage hderiv_stage
  refine ⟨Ring.DirectLimit.of R (φ · · ·) i x_i, ?_, ?_⟩
  · -- Map the lifted stage root forward to the direct limit.
    rw [← hf_stage]
    exact hx_i.map
  · -- Compare residues through the induced residue-field map of the canonical cocone map.
    calc
      IsLocalRing.residue R∞ (Ring.DirectLimit.of R (φ · · ·) i x_i)
          = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
              (IsLocalRing.residue (R i) x_i) := by
                symm
                exact IsLocalRing.ResidueField.map_residue
                  (Ring.DirectLimit.of R (φ · · ·) i) x_i
      _ = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) a_stage := by
            rw [hres_i]
      _ = a₀ := ha_stage

/-- Helper for Lemma 10.154.8: if every stage is strictly henselian, then the residue field of the
direct limit is separably algebraically closed. -/
lemma isSepClosed_residueField_directLimit
    [∀ i, StrictHenselianLocalRing (R i)] : IsSepClosed (ResidueField R∞) := by
  -- Descend one separable polynomial to a stage, solve it there, and map the root forward.
  refine (IsSepClosed.of_exists_root (k := ResidueField R∞)) ?_
  intro p hpmonic hpirr hpsep
  obtain ⟨i, p_i, hp_i⟩ := exists_stage_residue_polynomial R φ p
  let ψ : ResidueField (R i) →+* ResidueField R∞ :=
    IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
  have hψ_injective : Function.Injective ψ := RingHom.injective ψ
  have hpdeg_i : p_i.degree ≠ 0 := by
    intro hpzero
    have hpzero' : p.degree = 0 := by
      rw [← hp_i, Polynomial.degree_map_eq_of_injective hψ_injective, hpzero]
    exact (degree_pos_of_irreducible hpirr).ne' hpzero'
  have hpsep_i : p_i.Separable := by
    have hpsep_map : (p_i.map ψ).Separable := by simpa [ψ, hp_i] using hpsep
    exact (Polynomial.separable_map ψ).mp hpsep_map
  obtain ⟨x_i, hx_i⟩ := IsSepClosed.exists_root p_i hpdeg_i hpsep_i
  refine ⟨ψ x_i, ?_⟩
  have hx_map : (p_i.map ψ).eval (ψ x_i) = 0 := by
    calc
      (p_i.map ψ).eval (ψ x_i) = ψ (p_i.eval x_i) := by
        simpa using (Polynomial.eval_map_apply (p := p_i) ψ x_i)
      _ = 0 := by rw [hx_i, map_zero]
  simpa [ψ, hp_i] using hx_map

end ResidueField

-- Proof sketch: reuse the upstream direct-limit local-ring instance from Lemma `10.106.8` to put
-- a local-ring structure on `R∞`. For Hensel lifting, descend a monic polynomial over `R∞` and a
-- simple root in the residue field to a sufficiently large stage, apply the henselian property
-- there, and map the lifted root forward to the colimit.
/-- Lemma 10.154.8 (1): a filtered colimit of henselian local rings along local homomorphisms is
henselian. -/
instance directedSystem_directLimit_henselianLocalRing
    [∀ i, HenselianLocalRing (R i)] : HenselianLocalRing R∞ := by
  -- Use the residue-field formulation of Hensel's lemma and the direct stagewise descent above.
  exact ((HenselianLocalRing.TFAE R∞).out 1 0).mp
    (directedSystem_directLimit_simple_root_lift R φ)

-- Proof sketch: identify the residue field of `R∞` with the filtered colimit of the stage residue
-- fields along the induced maps; then every separable polynomial over the colimit residue field is
-- defined over some stage residue field, where it already splits because that field is separably
-- algebraically closed. Together with part (1), this gives the canonical Chapter 10 owner
-- `StrictHenselianLocalRing`.
/-- Lemma 10.154.8 (2): if the stage local rings are strictly henselian, then the filtered colimit
is strictly henselian; equivalently, its residue field is separably algebraically closed. -/
instance directedSystem_directLimit_strictHenselianLocalRing
    [∀ i, StrictHenselianLocalRing (R i)] : StrictHenselianLocalRing R∞ := by
  refine { toHenselianLocalRing := inferInstance, toIsSepClosed := ?_ }
  -- The strictness reduces to separable closedness of the direct-limit residue field.
  exact isSepClosed_residueField_directLimit R φ

end
