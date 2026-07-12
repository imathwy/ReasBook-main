import Mathlib
import StacksProject_2024.Chap24.Lemma_24_13_2

open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

namespace DifferentialGradedModule

local notation "DGAO" => _root_.SheafOfModules.RingedSite.DifferentialGradedAlgebra
  (C := C) (J := J) (𝒪 := 𝒪)

-- Semantic recall hits: `HomotopyCategory.instIsTriangulatedIntUp` and
-- `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` are the canonical owners
-- for the triangulated structure on a homotopy category and for distinguished triangles coming
-- from degreewise split short complexes. Local precedent `Definition_22_8_2` packages the
-- source's admissible-short-exact-sequence wording using `CochainComplex.trianglehOfDegreewiseSplit`.

/-- Proposition 24.22.4: for a ringed site `(\mathcal C, \mathcal O)` and a sheaf of
differential graded algebras `\mathcal A` on it, the homotopy category
`K(\textit{Mod}(\mathcal A, d))` is triangulated. In the current formalization this is the
canonical triangulated structure on `HomotopyCategory (moduleCategory 𝒜) (up ℤ)`, whose shift
functors are the standard integer shifts on the homotopy category. -/
@[stacks 0FS7, instance]
instance homotopyCategoryIsTriangulated (𝒜 : DGAO) :
    IsTriangulated (HomotopyCategory (moduleCategory 𝒜) (up ℤ)) := sorry

/-- Distinguished triangles in `K(\textit{Mod}(\mathcal A, d))` are exactly those isomorphic to
the triangle attached to a degreewise split short exact sequence of differential graded
`\mathcal A`-modules, i.e. to the source's admissible short exact sequence construction. -/
@[stacks 0FS7]
theorem mem_distTriang_iff_exists_iso_trianglehOfAdmissibleShortExact
    (𝒜 : DGAO) (T : Triangle (HomotopyCategory (moduleCategory 𝒜) (up ℤ))) :
    T ∈ distTriang (HomotopyCategory (moduleCategory 𝒜) (up ℤ)) ↔
      ∃ (S : ShortComplex (CochainComplex (moduleCategory 𝒜) ℤ)) (_hS : S.ShortExact)
        (σ : ∀ n : ℤ, (S.map (eval (moduleCategory 𝒜) (up ℤ) n)).Splitting),
        Nonempty (T ≅ CochainComplex.trianglehOfDegreewiseSplit S σ) := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
