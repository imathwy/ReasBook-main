import Mathlib
import StacksProject_2024.Chap10.Definition_10_70_1
import StacksProject_2024.Chap31.Definition_31_34_1

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry AffineBlowupChart

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical Rees-algebra / `Proj` owners
-- `reesAlgebra` and `AlgebraicGeometry.Proj`, while local project search verified that the affine
-- blowup algebra is already owned by Chapter 10's `affineBlowupChart` and the scheme-level blowup
-- hypothesis is already owned by Chapter 31's `IsBlowup`. The source is therefore split into one
-- scheme-level affine-open blowup/Proj comparison and two ring-level chart statements for the
-- affine-cover clause.

section

variable {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]

/-- Lemma 31.32.2: if `b : X' ⟶ X` is the blowup of `X` in a quasi-coherent ideal sheaf `I`, then
for every affine open `U ⊆ X` the inverse-image open subscheme `b⁻¹(U)` is canonically isomorphic
to the homogeneous spectrum of the Rees algebra `⊕_{d ≥ 0} (I(U))^d`. -/
theorem blowup_preimage_affineOpen_iso_proj_reesAlgebra
    (U : X.affineOpens) :
    Nonempty ((b ⁻¹ᵁ (U : X.Opens)).toScheme ≅ Proj (reesAlgebraGrade (I.ideal U))) := sorry

end

section

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- The basic chart of the Rees-algebra `Proj` cut out by a degree-one generator is the spectrum
of the corresponding affine blowup algebra. -/
theorem proj_reesAlgebra_basicOpen_isoSpec_affineBlowupChart
    (a : J) :
    Nonempty
      ((Proj.basicOpen (reesAlgebraGrade J) (reesAlgebraDegreeOne J a)).toScheme ≅
        Spec (.of (affineBlowupChart J a))) := sorry

/-- The Rees-algebra `Proj` admits an affine open cover by spectra of affine blowup algebras. -/
theorem proj_reesAlgebra_exists_affineOpenCover_spec_affineBlowupChart :
    ∃ 𝒰 : (Proj (reesAlgebraGrade J)).AffineOpenCover,
      ∀ i : 𝒰.I₀, ∃ a : J,
        Nonempty
          (((𝒰.openCover.f i).opensRange).toScheme ≅
            Spec (.of (affineBlowupChart J a))) := sorry

end

end AlgebraicGeometry
