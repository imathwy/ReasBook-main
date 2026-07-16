import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Definition_18_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

/- Lemma 18.21.5: after identifying the representable localizations
`(j_ℱ, j_ℱ^♯) = (j_U, j_U^♯)` and `(j_𝒢, j_𝒢^♯) = (j_V, j_V^♯)` from Lemma 18.21.3, the
inverse-image square of Lemma 18.21.4 is the same canonical pullback square as in Lemma 18.19.5.
The underlying topos-level comparison is the standard slice-topos isomorphism
`Over.star ℱ ⋙ Over.pullback s ≅ Over.star 𝒢`. -/
recall Over.starPullbackIsoStar

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v}) (U : C)

/- Companion recall: under the identifications of Lemma 18.21.3, the structure-sheaf component
`j_U^♯` is the canonical representable localization map on sheaves of rings. This is the `j^♯`
appearing in the ringed refinement of Lemma 18.21.5. -/
#check (RingedSite.representableLocalizationStructureMap 𝒪 U)

end
