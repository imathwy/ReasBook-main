import Mathlib
import stacks_project.Chap20.Lemma_20_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]

/-- The finite intersection attached to a Čech multi-index of the cover `𝒰`. -/
abbrev cechCoverIntersection (𝒰 : ι → Opens X.carrier) {p : ℕ} (σ : Fin (p + 1) → ι) :
    Opens X.carrier :=
  ⨅ a, 𝒰 (σ a)

-- Proof sketch: apply the Čech-to-hypercohomology spectral sequence from Lemma `20.25.1`. The
-- hypothesis says that for every fixed internal degree `q`, the higher cohomology of `K.X q` on
-- every finite intersection of the cover vanishes, so the spectral sequence is concentrated on the
-- `p = 0` row. Therefore the edge comparison from the total Čech complex to derived global
-- sections is an isomorphism.
/-- Lemma 20.25.2: if every positive-degree cohomology group of each term `\mathcal F^q` of a
bounded-below complex vanishes on every finite intersection of the open cover `𝒰`, then the total
Čech complex of the cover is canonically isomorphic to the bounded-below derived global sections
`RΓ(X, \mathcal F^\bullet)`. -/
theorem moduleCechDerivedFunctor_obj_isomorphic_derivedGlobalSections_of_acyclic_on_intersections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (K : CochainComplex.Plus (RingedSpace.Modules X))
    (hacyclic : ∀ (i : ℕ), 0 < i → ∀ (p : ℕ) (σ : Fin (p + 1) → ι) (q : ℤ),
      IsZero (((moduleUnderlyingAdditiveSheaf X).obj (K.obj.X q)).H' i
        (cechCoverIntersection 𝒰 σ))) :
    IsIsomorphic ((moduleCechDerivedFunctor X 𝒰).obj K)
      ((moduleDerivedGlobalSectionsFunctor X).obj K) := sorry

end AlgebraicGeometry.RingedSpace
