import Mathlib.CategoryTheory.Adjunction.Basic

open CategoryTheory

noncomputable section

universe uA uAU vA vAU

namespace SheafOfModules.RingedSite

section

variable {DGModA : Type uA} [Category.{vA} DGModA]
variable {DGModAU : Type uAU} [Category.{vAU} DGModAU]
variable (jShriek : DGModAU ⥤ DGModA) (jStar : DGModA ⥤ DGModAU)
variable (hAdj : jShriek ⊣ jStar)
variable (ℳ : DGModAU) (𝒩 : DGModA)

-- Semantic search note: `lean_leansearch` only surfaced general adjunction-hom infrastructure, so
-- the owner/API choice here was checked against the local graded predecessor
-- `Chap24/Lemma_24_10_1.lean` and the DG pullback/pushforward adjunction surface in
-- `Chap24/Lemma_24_18_1.lean`.

/- Source/core/bridge triage for Lemma 24.19.1:
- `source-facing`: the differential graded extension-by-zero/restriction Hom-set bijection
  `Hom(j_! \mathcal M, \mathcal N) ≃ Hom(\mathcal M, j^* \mathcal N)`;
- `core/canonical`: the generic adjunction equivalence `Adjunction.homEquiv`;
- `bridge/view`: the specialization `hAdj.homEquiv ℳ 𝒩`.

This item is therefore a direct specialization of the canonical adjunction owner, not a new local
owner. -/

/-
Lemma 24.19.1: in the localized differential graded-module situation above, the displayed
Hom-set bijection is exactly the specialized canonical adjunction equivalence `hAdj.homEquiv ℳ 𝒩`.
-/
#check hAdj.homEquiv ℳ 𝒩

/-- Lemma 24.19.1: in the localized differential graded-module situation above, morphisms
`j_! \mathcal M \to \mathcal N` are in canonical bijection with morphisms
`\mathcal M \to j^* \mathcal N`. -/
noncomputable abbrev dgExtensionByZeroRestrictionHomEquiv
    (hAdj : jShriek ⊣ jStar) (ℳ : DGModAU) (𝒩 : DGModA) :
    (jShriek.obj ℳ ⟶ 𝒩) ≃ (ℳ ⟶ jStar.obj 𝒩) :=
  hAdj.homEquiv ℳ 𝒩

/-- Applying `dgExtensionByZeroRestrictionHomEquiv` is definitionally the adjunction hom-set
equivalence for differential graded extension by zero and restriction. -/
@[simp] theorem dgExtensionByZeroRestrictionHomEquiv_apply (φ : jShriek.obj ℳ ⟶ 𝒩) :
    dgExtensionByZeroRestrictionHomEquiv hAdj ℳ 𝒩 φ = hAdj.homEquiv ℳ 𝒩 φ :=
  rfl

/-- Applying the inverse of `dgExtensionByZeroRestrictionHomEquiv` is definitionally the inverse
adjunction hom-set equivalence for differential graded extension by zero and restriction. -/
@[simp] theorem dgExtensionByZeroRestrictionHomEquiv_symm_apply
    (φ : ℳ ⟶ jStar.obj 𝒩) :
    (dgExtensionByZeroRestrictionHomEquiv hAdj ℳ 𝒩).symm φ =
      (hAdj.homEquiv ℳ 𝒩).symm φ :=
  rfl

end

end SheafOfModules.RingedSite
