import Mathlib
import StacksProject_2024.Chap18.Lemma_18_40_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

-- Proof sketch: apply Lemma `18.40.5 (1)` to the localization functor
-- `Over.forget U : C/U ⥤ C`; its inverse image on commutative ring sheaves is exactly the
-- restricted structure sheaf `\mathcal O_U`.
/-- Lemma 18.40.12 (1): if `(\mathcal C, \mathcal O)` is a locally ringed site and `U` is an
object of `\mathcal C`, then the localization `(\mathcal C/U, \mathcal O_U)` is a locally
ringed site. -/
theorem localization_isLocallyRingedSite
    (U : C) [IsLocallyRingedSite 𝒪] :
    IsLocallyRingedSite ((J.overPullback CommRingCat.{max u v} U).obj 𝒪) := sorry

end

end CategoryTheory
