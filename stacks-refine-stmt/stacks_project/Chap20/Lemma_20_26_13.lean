import Mathlib
import stacks_project.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape MonoidalCategory
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [Abelian (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules X)))]

-- Proof sketch: choose a quasi-isomorphism `K^• ⟶ F^•` from a K-flat complex using Lemma
-- `20.26.12`. Tensoring this comparison with either `P^•` or `Q^•` gives quasi-isomorphisms on
-- the vertical arrows by Lemma `20.26.3`, while tensoring `α` with the K-flat complex `K^•`
-- gives a quasi-isomorphism on the top horizontal map. The commutative square then forces the
-- bottom horizontal map to be a quasi-isomorphism.
/-- Lemma 20.26.13: if `α : \mathcal P^\bullet \to \mathcal Q^\bullet` is a quasi-isomorphism
between K-flat complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, then
for every complex `\mathcal F^\bullet` of `\mathcal O_X`-modules the induced map
`\mathrm{Tot}(\mathrm{id}_{\mathcal F^\bullet} \otimes \alpha) :
\mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X} \mathcal P^\bullet) ⟶
\mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X} \mathcal Q^\bullet)` is a
quasi-isomorphism. -/
lemma quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat
    (F P Q : CochainComplex (RingedSpace.Modules X) ℤ)
    (hP : CochainComplex.IsKFlat P) (hQ : CochainComplex.IsKFlat Q)
    (α : P ⟶ Q) (hα : QuasiIso α) :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 F) α) := sorry

end AlgebraicGeometry.RingedSpace
