import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe uA uAU vA vAU

namespace SheafOfModules.RingedSite

section

variable {ModGrA : Type uA} [Category.{vA} ModGrA]
variable {ModGrAU : Type uAU} [Category.{vAU} ModGrAU]
variable (jShriek : ModGrAU ⥤ ModGrA) (jStar : ModGrA ⥤ ModGrAU)
variable (hAdj : jShriek ⊣ jStar)
variable (ℳ : ModGrAU) (𝒩 : ModGrA)

-- Owner/API choice note: this item is checked against the local differential graded analogue
-- `Chap24/Lemma_24_19_1.lean`, which packages the textbook Hom-set bijection as a source-facing
-- abbrev over the canonical adjunction equivalence.

/- Source/core/bridge triage for Lemma 24.10.1:
- `source-facing`: the graded extension-by-zero/restriction Hom-set bijection
  `Hom(j_! \mathcal M, \mathcal N) ≃ Hom(\mathcal M, j^* \mathcal N)`;
- `core/canonical`: the generic adjunction equivalence `Adjunction.homEquiv`;
- `bridge/view`: the specialization `hAdj.homEquiv ℳ 𝒩`.

This item is therefore a direct specialization of the canonical adjunction owner, not a new local
owner. -/

/- Lemma 24.10.1: in the localized graded-module situation above, the displayed Hom-set bijection
is exactly the canonical adjunction equivalence `Adjunction.homEquiv`. -/
recall Adjunction.homEquiv

/-- Lemma 24.10.1: in the localized graded-module situation above, morphisms
`j_! \mathcal M \to \mathcal N` are in canonical bijection with morphisms
`\mathcal M \to j^* \mathcal N`. -/
noncomputable abbrev gradedExtensionByZeroRestrictionHomEquiv :
    (jShriek.obj ℳ ⟶ 𝒩) ≃ (ℳ ⟶ jStar.obj 𝒩) :=
  hAdj.homEquiv ℳ 𝒩

/-- Applying `gradedExtensionByZeroRestrictionHomEquiv` is definitionally the adjunction hom-set
equivalence for extension by zero and restriction on graded modules. -/
theorem gradedExtensionByZeroRestrictionHomEquiv_apply (φ : jShriek.obj ℳ ⟶ 𝒩) :
    gradedExtensionByZeroRestrictionHomEquiv jShriek jStar hAdj ℳ 𝒩 φ = hAdj.homEquiv ℳ 𝒩 φ :=
  rfl

end

end SheafOfModules.RingedSite
