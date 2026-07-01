import Mathlib
import stacks_project.Chap17.Definition_17_17_1
import stacks_project.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

-- Proof sketch: choose the compatible upper-truncation resolution tower from Lemma `20.26.11`.
-- Each stage is bounded above and has flat terms because its terms are coproducts of
-- `j_{U!}\mathcal O_U`, which are flat by Lemma `17.17.6`; hence every stage is K-flat by
-- Lemma `20.26.9`. Apply Lemma `20.26.10` to the sequential colimit of the tower. The comparison
-- map from that colimit to `\mathcal G^\bullet` is a quasi-isomorphism and degreewise epi by the
-- construction in Lemma `20.26.11`, and each term of the colimit remains flat because it is a
-- direct sum of flat modules.
/-- Lemma 20.26.12: every complex `\mathcal G^\bullet` of `\mathcal O_X`-modules on a ringed
space `(X, \mathcal O_X)` admits a quasi-isomorphism from a K-flat complex whose terms are flat
`\mathcal O_X`-modules, and this quasi-isomorphism is termwise surjective. -/
theorem exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex (RingedSpace.Modules X) ℤ) :
    ∃ (K : CochainComplex (RingedSpace.Modules X) ℤ) (hK : IsKFlat K)
      (hFlat : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n))
      (α : K ⟶ 𝒢), QuasiIso α ∧ ∀ n : ℤ, Epi (α.f n) := sorry

end AlgebraicGeometry.RingedSpace
