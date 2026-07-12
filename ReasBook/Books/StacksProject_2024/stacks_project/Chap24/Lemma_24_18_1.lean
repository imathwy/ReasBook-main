import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe uA uB vA vB

namespace SheafOfModules.RingedSite

section

variable {DGModA : Type uA} [Category.{vA} DGModA]
variable {DGModB : Type uB} [Category.{vB} DGModB]
variable (fPush : DGModA ⥤ DGModB) (fPull : DGModB ⥤ DGModA)
variable (hAdj : fPull ⊣ fPush)
variable (𝒩 : DGModB) (ℳ : DGModA)

-- Semantic search note: `lean_leansearch` is unavailable in this runner, so the owner/API choice
-- was checked against the local graded predecessor `Chap24/Lemma_24_9_1.lean` and the module
-- pullback/pushforward adjunction owner `Chap18/Lemma_18_13_2.lean`.

/-- Lemma 24.18.1: in the differential graded pullback/pushforward situation above, morphisms
`\mathcal N \to f_* \mathcal M` in `\textit{Mod}^{dg}(\mathcal B, \text{d})` are in canonical
bijection with morphisms `f^* \mathcal N \to \mathcal M` in
`\textit{Mod}^{dg}(\mathcal A, \text{d})`. -/
noncomputable abbrev dgPullbackPushforwardHomEquiv :
    (𝒩 ⟶ fPush.obj ℳ) ≃ (fPull.obj 𝒩 ⟶ ℳ) :=
  (hAdj.homEquiv 𝒩 ℳ).symm

/-- Applying `dgPullbackPushforwardHomEquiv` is definitionally the inverse adjunction hom-set
equivalence on differential graded modules. -/
theorem dgPullbackPushforwardHomEquiv_apply (φ : 𝒩 ⟶ fPush.obj ℳ) :
    dgPullbackPushforwardHomEquiv fPush fPull hAdj 𝒩 ℳ φ =
      (hAdj.homEquiv 𝒩 ℳ).symm φ := sorry

end

end SheafOfModules.RingedSite
