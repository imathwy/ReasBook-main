import Mathlib
import StacksProject_2024.Chap21.Situation_21_38_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable {D : RingedSite.{u, v}} (S : inherited_ringed_topos_situation D)
variable (U' : S.C'.S)

local notation "U" => S.u.G.obj U'
local notation "V" => S.C.p.obj U

/-- The localized projection functor `\mathcal C'/U' \to \mathcal D/V` induced by `p'`, after
identifying `V = p(u(U'))` with `p'(U')`. -/
abbrev sourceSliceProjectionFunctor : Over U' ⥤ Over V :=
  let uFun := S.u.G
  let pFun := S.C.p
  let pFun' := S.C'.p
  let hcomm : uFun ⋙ pFun = pFun' := S.u.w
  let hbase : V = pFun'.obj U' := congrArg (fun F ↦ F.obj U') hcomm
  cast (congrArg (fun X ↦ Over U' ⥤ Over X) hbase.symm) (Over.post pFun')

/-- Bundles the section and inverse-image identities for a localized comparison morphism over the
object `U'` of `\mathcal C'`. -/
class IsLocalizedComparisonSection
    (πU' : MorphismOfTopoiIn (D.siteTopology.over V)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U'))
    (g' : MorphismOfTopoiIn
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U'))
    (πU : MorphismOfTopoiIn (D.siteTopology.over V)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U))
    (σ' : MorphismOfTopoiIn
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U')
      (D.siteTopology.over V)) : Prop where
  /-- `\pi'_{U'} \circ \sigma'` is the identity on `\operatorname{Sh}(\mathcal D/V)`. -/
  piU'_comp_sigma'_eq_id :
    MorphismOfTopoiIn.comp πU' σ' = MorphismOfTopoiIn.id (D.siteTopology.over V)
  /-- `\pi_U \circ g' \circ \sigma'` is the identity on `\operatorname{Sh}(\mathcal D/V)`. -/
  piU_comp_comparison_comp_sigma'_eq_id :
    MorphismOfTopoiIn.comp πU (MorphismOfTopoiIn.comp g' σ') =
      MorphismOfTopoiIn.id (D.siteTopology.over V)
  /-- The inverse-image functor of `\sigma'` is `\pi'_{U', *}`. -/
  sigma'_inverseImage_eq :
    σ'.inverseImage = πU'.pushforward
  /-- The inverse-image functor of `g' \circ \sigma'` is `\pi_{U, *}`. -/
  comparison_comp_sigma'_inverseImage_eq :
    (MorphismOfTopoiIn.comp g' σ').inverseImage = πU.pushforward

/-- A localized comparison morphism satisfies the bundled section identities once the four
defining equalities are specified. -/
instance
    {πU' : MorphismOfTopoiIn (D.siteTopology.over V)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U')}
    {g' : MorphismOfTopoiIn
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U')}
    {πU : MorphismOfTopoiIn (D.siteTopology.over V)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U)}
    {σ' : MorphismOfTopoiIn
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U')
      (D.siteTopology.over V)}
    (h₁ : MorphismOfTopoiIn.comp πU' σ' = MorphismOfTopoiIn.id (D.siteTopology.over V))
    (h₂ : MorphismOfTopoiIn.comp πU (MorphismOfTopoiIn.comp g' σ') =
      MorphismOfTopoiIn.id (D.siteTopology.over V))
    (h₃ : σ'.inverseImage = πU'.pushforward)
    (h₄ : (MorphismOfTopoiIn.comp g' σ').inverseImage = πU.pushforward) :
    IsLocalizedComparisonSection S U' πU' g' πU σ' := sorry

-- Proof sketch: apply Lemma `21.38.2` to the fibred category `S.C'` and the object `U'` to obtain
-- a section `σ'` of `π'_{U'}` whose inverse image is `π'_{U', *}`. Compose with the localized
-- comparison morphism `g'`; because `u` is a morphism of fibred categories over `D`, it preserves
-- strongly cartesian morphisms, so this composite is the section supplied by the same construction
-- for `S.C` and `U = u(U')`, giving both the second section identity and the pushforward formula
-- for the composite inverse image.
/-- Lemma 21.38.4: for `U' \in \mathcal C'`, with `U = u(U')` and `V = p'(U')`, let
`\pi'_{U'} : \operatorname{Sh}(\mathcal C'/U') \to \operatorname{Sh}(\mathcal D/V)`,
`g' : \operatorname{Sh}(\mathcal C'/U') \to \operatorname{Sh}(\mathcal C/U)`, and
`\pi_U : \operatorname{Sh}(\mathcal C/U) \to \operatorname{Sh}(\mathcal D/V)` be the induced
localized morphisms of topoi. Then there exists a morphism
`\sigma' : \operatorname{Sh}(\mathcal D/V) \to \operatorname{Sh}(\mathcal C'/U')` such that
`\pi'_{U'} \circ \sigma' = \mathrm{id}`, `\pi_U \circ g' \circ \sigma' = \mathrm{id}`,
`(\sigma')^{-1} = \pi'_{U', *}`, and `(g' \circ \sigma')^{-1} = \pi_{U, *}`. -/
theorem localized_comparison_morphism_has_section
    [Functor.IsContinuous (sourceSliceProjectionFunctor S U')
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U')
      (D.siteTopology.over V)]
    [Functor.IsContinuous (Over.post S.u.G)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U')
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U)]
    [Functor.IsContinuous (Over.post S.C.p)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U)
      (D.siteTopology.over V)]
    (πU' : MorphismOfTopoiIn (D.siteTopology.over V)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U'))
    (hπU' :
      πU'.inverseImage =
        (sourceSliceProjectionFunctor S U').sheafPushforwardContinuous
          (Type (max u v))
          ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U')
          (D.siteTopology.over V))
    (g' : MorphismOfTopoiIn
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U'))
    (hg' :
      g'.inverseImage =
        (Over.post S.u.G : Over U' ⥤ Over U).sheafPushforwardContinuous
          (Type (max u v))
          ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U')
          ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U))
    (πU : MorphismOfTopoiIn (D.siteTopology.over V)
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U))
    (hπU :
      πU.inverseImage =
        (Over.post S.C.p : Over U ⥤ Over V).sheafPushforwardContinuous
          (Type (max u v))
          ((FibredCategoryOver.inheritedTopology D.siteTopology S.C).over U)
          (D.siteTopology.over V)) :
    ∃ σ' : MorphismOfTopoiIn
      ((FibredCategoryOver.inheritedTopology D.siteTopology S.C').over U')
      (D.siteTopology.over V),
      IsLocalizedComparisonSection S U' πU' g' πU σ' := sorry

end

end FibredCategoryOver
end CategoryTheory
