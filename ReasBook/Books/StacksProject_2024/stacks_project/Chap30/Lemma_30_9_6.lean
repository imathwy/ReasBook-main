import Mathlib
import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.restrictStalkNatIso`; together
-- with local Chapter 17 precedent `RingedSpace.moduleStalkMap`, this gives the right source-
-- facing statement surface for extending a stalk morphism to a morphism on a neighborhood.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Lemma 30.9.6: let `X` be a locally Noetherian scheme. Let `\mathcal{F}`, `\mathcal{G}` be
coherent `\mathcal{O}_ X`-modules. Let `x \in X`. Suppose
`\psi : \mathcal{G}_ x \to \mathcal{F}_ x` is a map of `\mathcal{O}_{X, x}`-modules. Then there
exists an open neighbourhood `U \subset X` of `x` and a map
`\varphi : \mathcal{G}|_ U \to \mathcal{F}|_ U` such that `\varphi _ x = \psi`. -/
@[stacks 01Y4]
theorem exists_open_neighborhood_restriction_hom_of_stalk_hom
    {𝒢 ℱ : X.Modules} [𝒢.IsCoherent] [ℱ.IsCoherent]
    (x : X) (ψ : RingedSpace.stalkModuleCat 𝒢 x ⟶ RingedSpace.stalkModuleCat ℱ x) :
    ∃ (U : X.Opens) (hxU : x ∈ U)
      (φ : ((Scheme.Modules.restrictFunctor U.ι).obj 𝒢) ⟶
        ((Scheme.Modules.restrictFunctor U.ι).obj ℱ)),
      let xU : (↑U : Scheme) := ⟨x, hxU⟩
      RingedSpace.moduleStalkMap xU φ ≫
          (Scheme.Modules.restrictStalkNatIso U.ι xU).hom.app ℱ =
        ((Scheme.Modules.restrictStalkNatIso U.ι xU).hom.app 𝒢) ≫
          (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map ψ :=
  sorry

end AlgebraicGeometry.Scheme.Modules
