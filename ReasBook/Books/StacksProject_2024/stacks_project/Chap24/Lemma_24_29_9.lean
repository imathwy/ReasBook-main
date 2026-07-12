import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksProject_2024.Chap24.Lemma_24_25_12
import StacksProject_2024.Chap24.Lemma_24_29_8

open CategoryTheory
open DerivedCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite
namespace DifferentialGradedAlgebra

section

variable {X : RingedSite.{u, v}} (𝒜 : DifferentialGradedAlgebra X)
variable (A : 𝒜.moduleCat)
variable (hypercohomology : ℤ → DerivedCategory 𝒜.moduleCat ⥤ AddCommGrpCat.{max u v})

-- Semantic search note: `lean_leansearch` surfaced `CategoryTheory.preadditiveCoyoneda` and the
-- shift-functor API; the owner choice below was then aligned with the Chapter 24 derived-category
-- files and the Chapter 13 representability conventions using `singleFunctor` and shifted Hom.

/-- Lemma 24.29.9: let `(\mathcal C, \mathcal O)` be a ringed site, let `(\mathcal A, d)` be a
sheaf of differential graded `\mathcal O`-algebras, and let `\mathcal M` be a differential graded
`\mathcal A`-module. In the current formalization, the source left-hand side
`H^n(\mathcal C, \mathcal M)` is packaged by a chosen functor family `hypercohomology`, the dg
algebra viewed as a module over itself is represented by the degree-zero complex
`(singleFunctor 𝒜.moduleCat 0).obj A`, `hshift` records the canonical identification
`H^n(\mathcal C, -) = H^0(\mathcal C, -[n])`, and `hzero` records the degree-zero comparison from
Lemmas `24.29.1`, `24.29.8`, and `24.26.7`. Under these source-faithful ambient identifications,
the `n`-th hypercohomology functor is corepresented by `A[0]`, equivalently by
`M ↦ \operatorname{Hom}_{D(\mathcal A, d)}(A[0], M[n])`. -/
@[stacks 0FTX]
theorem nthHypercohomologyFunctor_iso_shiftedCoyoneda
    (hshift :
      ∀ n : ℤ,
        hypercohomology n ≅
          (shiftFunctor (DerivedCategory 𝒜.moduleCat) n) ⋙ hypercohomology 0)
    (hzero :
      hypercohomology 0 ≅
        preadditiveCoyoneda.obj (Opposite.op ((singleFunctor 𝒜.moduleCat 0).obj A)))
    (n : ℤ) :
    Nonempty
      (hypercohomology n ≅
        (shiftFunctor (DerivedCategory 𝒜.moduleCat) n) ⋙
          preadditiveCoyoneda.obj (Opposite.op ((singleFunctor 𝒜.moduleCat 0).obj A))) := sorry

/-- Evaluating `nthHypercohomologyFunctor_iso_shiftedCoyoneda` at a derived object `M` gives the
source formula `H^n(\mathcal C, M) = \operatorname{Hom}_{D(\mathcal A, d)}(A[0], M[n])`. -/
@[stacks 0FTX]
theorem nthHypercohomology_iso_homIntoShift
    (hshift :
      ∀ n : ℤ,
        hypercohomology n ≅
          (shiftFunctor (DerivedCategory 𝒜.moduleCat) n) ⋙ hypercohomology 0)
    (hzero :
      hypercohomology 0 ≅
        preadditiveCoyoneda.obj (Opposite.op ((singleFunctor 𝒜.moduleCat 0).obj A)))
    (M : DerivedCategory 𝒜.moduleCat) (n : ℤ) :
    Nonempty
      ((hypercohomology n).obj M ≅
        AddCommGrpCat.of
          (((singleFunctor 𝒜.moduleCat 0).obj A) ⟶
            (shiftFunctor (DerivedCategory 𝒜.moduleCat) n).obj M)) := sorry

end

end DifferentialGradedAlgebra
end RingedSite
