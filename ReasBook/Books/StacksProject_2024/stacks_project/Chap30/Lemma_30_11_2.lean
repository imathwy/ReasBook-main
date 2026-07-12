import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.Chap30.Definition_30_11_1
import StacksProject_2024.Chap30.Lemma_30_9_1
import StacksProject_2024.Chap30.Lemma_30_9_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [MonoidalClosed X.Modules]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsCoherent]

attribute [local instance] isCoherent_internalHom

-- Semantic recall: `lean_leansearch` surfaced the existing scheme-module owner
-- `AlgebraicGeometry.Scheme.Modules`, the locally Noetherian stalk-ring instance, and the
-- internal-Hom owner `ihom`; local Chapter 30 precedent states depth conditions with
-- `moduleDepth (X.presheaf.stalk x) RingedSpace.stalkModuleCat _ x)`. The source proof uses
-- the Chapter 17 stalk comparison as the bridge from sheaf internal-Hom to stalkwise linear maps.

/-- Lemma 30.11.2 (1): if the stalk `𝒢_x` has depth at least `1`, then the stalk of the internal
Hom sheaf `\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F,\mathcal G)` at `x` has depth at
least `1`. -/
@[stacks 0EBC]
theorem moduleDepth_internalHom_stalk_ge_one_of_moduleDepth_stalk_ge_one
    (x : X)
    (h𝒢x : (1 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat 𝒢 x)) :
    (1 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x)
        (RingedSpace.stalkModuleCat ((ihom ℱ).obj 𝒢) x) := sorry

/-- Lemma 30.11.2 (2): if the stalk `𝒢_x` has depth at least `2`, then the stalkwise ordinary
Hom module `Hom_{\mathcal O_{X,x}}(\mathcal F_x,\mathcal G_x)` has depth at least `2`. Via the
finite-presentation comparison for coherent sheaves, this is the source statement for the stalk
of `\operatorname{Hom}_{\mathcal O_X}(\mathcal F,\mathcal G)`. -/
@[stacks 0EBC]
theorem moduleDepth_linearMap_stalk_ge_two_of_moduleDepth_stalk_ge_two
    (x : X)
    (h𝒢x : (2 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat 𝒢 x)) :
    (2 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x)
        (RingedSpace.stalkModuleCat ℱ x →ₗ[X.presheaf.stalk x]
          (RingedSpace.stalkModuleCat 𝒢 x) := sorry

end AlgebraicGeometry.Scheme.Modules
