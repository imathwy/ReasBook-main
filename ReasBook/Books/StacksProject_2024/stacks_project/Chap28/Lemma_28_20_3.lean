import StacksProject_2024.stacks_project.Chap28.Lemma_28_20_2

open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` confirmed the scheme-level reducedness owner
-- `AlgebraicGeometry.IsReduced`. Local precedent in Lemma 28.20.2 fixes the five existing
-- locally-free conditions and the fiber-rank expression, so this item adds only the reduced-case
-- finite-type plus locally-constant-rank condition to that TFAE.

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- The condition that a scheme module is of finite type and has locally constant fiber-rank
function. -/
@[stacks 0FWH]
class FiniteTypeRankLocallyConstant : Prop extends ℱ.IsFiniteType where
  rank_locallyConstant :
    IsLocallyConstant
      (fun x : X ↦
        (Module.finrank
          (IsLocalRing.ResidueField (X.presheaf.stalk x))
          ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[X.presheaf.stalk x]
            ↑(RingedSpace.stalkModuleCat ℱ x)) : ℤ))

/-- A finite-type module with locally constant fiber rank is of finite type. -/
instance instIsFiniteTypeOfFiniteTypeRankLocallyConstant
    [h : FiniteTypeRankLocallyConstant ℱ] :
    ℱ.IsFiniteType :=
  h.toIsFiniteType

/-- A finite-type module with locally constant fiber rank has locally constant fiber-rank
function. -/
theorem rankLocallyConstant_of_finiteTypeRankLocallyConstant
    [h : FiniteTypeRankLocallyConstant ℱ] :
    IsLocallyConstant
      (fun x : X ↦
        (Module.finrank
          (IsLocalRing.ResidueField (X.presheaf.stalk x))
          ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[X.presheaf.stalk x]
            ↑(RingedSpace.stalkModuleCat ℱ x)) : ℤ)) := sorry

/-- Lemma 28.20.3: if `X` is reduced and `\mathcal F` is a quasi-coherent
`\mathcal O_X`-module, then the equivalent conditions of Lemma 28.20.2 are also equivalent to
`\mathcal F` being of finite type and the fiber-rank function
`x \mapsto \dim_{\kappa(x)} \mathcal F_x \otimes_{\mathcal O_{X,x}} \kappa(x)` being locally
constant in the Zariski topology. -/
@[stacks 0FWH]
theorem finiteLocallyFree_tfae_of_isReduced [IsReduced X] :
    List.TFAE [
      FinitePresentationFlat ℱ,
      FinitePresentationStalkwiseFree ℱ,
      LocallyFreeFiniteType ℱ,
      SheafOfModules.IsFiniteLocallyFree ℱ,
      FiniteTypeStalkwiseFreeRankLocallyConstant ℱ,
      FiniteTypeRankLocallyConstant ℱ
    ] := sorry

end AlgebraicGeometry.Scheme.Modules
