import Mathlib
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.Limits

-- Declarations for this item will be appended below by the statement pipeline.

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
