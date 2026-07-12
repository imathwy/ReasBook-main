import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap06.Lemma_6_30_13

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable {B : Set (Opens Y)} (hB : Opens.IsBasis B)

private abbrev moduleBasisRestriction (hB : Opens.IsBasis B) :
    SheafOfModules (RingedSpace.ringCatSheaf Y) ⥤
      SheafOfModules
        (((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
          (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y)).obj
          (RingedSpace.ringCatSheaf Y)) :=
  SheafOfModules.pushforward
    (𝟙 (((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y)).obj
        (RingedSpace.ringCatSheaf Y)))

-- Proof sketch: restricting sheaves of modules on `Y` to a basis `B` is an equivalence by
-- Lemma `6.30.13`. Hence any morphism between the basis restrictions of `𝒢` and `f_* ℱ`
-- extends uniquely to a global morphism `𝒢 ⟶ f_* ℱ`. Unpacked sectionwise, this is exactly the
-- compatible family of `\mathcal O_Y(V)`-linear maps on basis opens appearing in the Stacks
-- statement.
/-- Lemma 6.30.15: let `f : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)` be a morphism of ringed
spaces, let `ℱ` be a sheaf of `\mathcal{O}_X`-modules, let `𝒢` be a sheaf of
`\mathcal{O}_Y`-modules, and let `B` be a basis of `Y`. A morphism between the restrictions of
`𝒢` and `f_* ℱ` to the basis site attached to `B` extends uniquely to a global morphism
`𝒢 ⟶ f_* ℱ`; equivalently, a compatible family of `\mathcal O_Y(V)`-linear maps
`𝒢(V) ⟶ ℱ(f^{-1}(V))` for `V ∈ B` comes from a unique `f`-map. -/
theorem existsUnique_module_pushforward_hom_of_basis_restriction
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
    (𝒢 : SheafOfModules ((RingedSpace.ringCatSheaf Y)))
    (φB : (moduleBasisRestriction hB).obj 𝒢 ⟶
      (moduleBasisRestriction hB).obj ((f _*).obj ℱ)) :
    ∃! φ : 𝒢 ⟶ (f _*).obj ℱ,
      (moduleBasisRestriction hB).map φ = φB := by
  let F := moduleBasisRestriction hB
  letI : Functor.IsEquivalence F :=
    restrictSheafOfModulesToBasis_isEquivalence hB ((RingedSpace.ringCatSheaf Y))
  refine ⟨F.preimage φB, by simpa [F] using F.map_preimage φB, ?_⟩
  intro φ hφ
  exact F.map_injective <| hφ.trans <| by simpa [F] using (F.map_preimage φB).symm

end

end AlgebraicGeometry
