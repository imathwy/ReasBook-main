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

universe u v

namespace CommRingCat

/-- The morphism property on `CommRingCat` consisting of étale ring maps. -/
abbrev etale : MorphismProperty CommRingCat.{u} :=
  fun _ _ f ↦ f.hom.Etale

end CommRingCat

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
/-- Lemma 10.154.3: if `A` is a filtered colimit of `R`-algebras and each stage is itself a
filtered colimit of étale `R`-algebras, then `A` is a filtered colimit of étale `R`-algebras. -/
theorem isFilteredColimitOfEtale_of_isColimit_filtered_system
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, ind.{v, u, u + 1} CommRingCat.etale (F.obj j).hom) :
    ind.{v, u, u + 1} CommRingCat.etale c.pt.hom := sorry

/-- Companion form of Lemma 10.154.3 stated through the source-facing owner
`RingHom.IsFilteredColimitOfEtale`. -/
theorem algebraMap_isFilteredColimitOfEtale_of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, ind.{v, u, u + 1} CommRingCat.etale (F.obj j).hom) :
    (algebraMap R A).IsFilteredColimitOfEtale := sorry

end

end RingHom
