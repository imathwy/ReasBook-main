import Mathlib
import stacks_project.Chap21.Definition_21_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat)]

variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type (max u v)} (family : ι → Over U)

/-- A functorial package for the spectral sequence computing sheaf cohomology over `U` from the
Čech cohomology of the cohomology presheaves attached to the covering family `family`. -/
structure CechToSheafCohomologySpectralSequence
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat]
    [HasExt (Sheaf J AddCommGrpCat)]
    (U : C) [HasFiniteProducts (Over U)] {ι : Type (max u v)} (family : ι → Over U) where
  /-- The cohomological spectral sequence attached to each abelian sheaf, functorially in the
  sheaf and starting on the `E₂`-page. -/
  spectralSequenceFunctor :
    Sheaf J AddCommGrpCat ⥤ E₂CohomologicalSpectralSequenceNat AddCommGrpCat
  /-- The `E₂`-page is the Čech cohomology of the cohomology presheaf `\underline{H}^q(F)`. -/
  pageTwoIso :
    ∀ (F : Sheaf J AddCommGrpCat) (p q : ℕ),
      ((spectralSequenceFunctor.obj F).page 2).X (p, q) ≅
        cechCohomology U family (F.cohomologyPresheaf q) p
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : Sheaf J AddCommGrpCat → ℕ → AddCommGrpCat
  /-- The abutment identifies with sheaf cohomology of `F` over `U`. -/
  targetIso :
    ∀ (F : Sheaf J AddCommGrpCat) (n : ℕ),
      abutment F n ≅
        F.H' n U

-- Proof sketch: apply the Grothendieck spectral sequence to the composite of the left exact
-- inclusion `sheafToPresheaf J AddCommGrpCat` with degree-zero Čech cohomology for `family`.
-- Lemma `21.8.2` identifies degree-zero Čech cohomology with sections over `U`, Lemma `21.10.2`
-- shows that injective abelian sheaves are Čech-acyclic for the cover, Lemma `21.9.6`
-- identifies higher Čech cohomology with the right derived functors of degree zero, and Lemma
-- `21.10.5` identifies the right derived functors of the inclusion with the cohomology
-- presheaves. The naturality of the Grothendieck construction yields functoriality in `F`.
/-- Lemma 21.10.6: for a covering family `family : ι → Over U` on the slice site `(C / U, J.over
U)`, there is a cohomological spectral sequence functorial in an abelian sheaf `F` whose
`E_2^{p,q}`-term is `\check H^p(family, \underline{H}^q(F))` and whose abutment is the sheaf
cohomology `H^{p+q}(U, F)`. -/
theorem exists_cechToSheafCohomologySpectralSequence :
    Nonempty (CechToSheafCohomologySpectralSequence J U family) := sorry

end

end CategoryTheory
