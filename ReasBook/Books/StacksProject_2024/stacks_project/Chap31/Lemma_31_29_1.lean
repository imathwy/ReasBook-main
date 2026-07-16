import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_78_1
import StacksProject_2024.stacks_project.Chap28.Definition_28_7_1
import StacksProject_2024.stacks_project.Chap30.Lemma_30_9_4
import StacksProject_2024.stacks_project.Chap31.Definition_31_12_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_12_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `Module.IsReflexive` and the module-level
-- `dualTensorHomEquiv`; local Chapter 31 precedent fixes the sheaf-side owners as
-- `Scheme.Modules.reflexiveHull`, `Scheme.Modules.IsReflexive`, and internal Hom `ihom`.

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

/-- The tensor unit in `X.Modules` is coherent on a locally Noetherian scheme. This is a local
helper for using the internal-Hom dual `\mathcal H\!\mathit{om}(\mathcal F,\mathcal O_X)` with
the monoidal tensor unit model of `\mathcal O_X`. -/
theorem tensorUnit_isCoherent_of_isLocallyNoetherian :
    (𝟙_ (X.Modules)).IsCoherent := sorry

/-- A coherent module has rank one at the generic point when its generic stalk is finite locally
free of rank `1` over the generic local ring. -/
abbrev isRankOneAtGenericPoint (ℱ : X.Modules) : Prop :=
  Module.FiniteLocallyFreeOfRank (X.presheaf.stalk (genericPoint X))
    ↑(RingedSpace.stalkModuleCat ℱ (genericPoint X)) 1

/-- The object property selecting rank-one coherent reflexive `\mathcal O_X`-modules. -/
abbrev rankOneReflexiveModuleProperty : ObjectProperty X.Modules :=
  fun ℱ ↦ ∃ hcoh : ℱ.IsCoherent,
    IsReflexive ℱ ∧ isRankOneAtGenericPoint X ℱ

/-- The full subcategory of rank-one coherent reflexive `\mathcal O_X`-modules. -/
abbrev RankOneReflexiveModule :=
  (rankOneReflexiveModuleProperty X).FullSubcategory

/-- The set-level type of isomorphism classes of rank-one coherent reflexive
`\mathcal O_X`-modules, represented by the skeleton of the full subcategory. -/
@[stacks 0EBL]
abbrev RankOneReflexiveIsoClass :=
  Skeleton (RankOneReflexiveModule X)

variable {X}

/-- The isomorphism class of a rank-one coherent reflexive `\mathcal O_X`-module. -/
noncomputable def rankOneReflexiveIsoClassOf
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ]
    (hrank : isRankOneAtGenericPoint X ℱ) :
    RankOneReflexiveIsoClass X :=
  toSkeleton (⟨ℱ, ⟨inferInstance, inferInstance, hrank⟩⟩ : RankOneReflexiveModule X)

/-- The raw tensor-to-internal-Hom morphism
`\mathcal H\!\mathit{om}(\mathcal F,\mathcal O_X) \otimes \mathcal G \to
\mathcal H\!\mathit{om}(\mathcal F,\mathcal G)`, obtained by currying evaluation. -/
noncomputable def dualTensorToInternalHom (ℱ 𝒢 : X.Modules) :
    (((ihom ℱ).obj (𝟙_ (X.Modules))) ⊗ 𝒢 : X.Modules) ⟶ (ihom ℱ).obj 𝒢 :=
  MonoidalClosed.curry (
    (α_ ℱ ((ihom ℱ).obj (𝟙_ (X.Modules))) 𝒢).inv ≫
    tensorHom ((ihom.ev ℱ).app (𝟙_ (X.Modules))) (𝟙 𝒢) ≫
    (λ_ 𝒢).hom)

/-- The displayed double-dual comparison morphism from
`(\mathcal H\!\mathit{om}(\mathcal F,\mathcal O_X) \otimes \mathcal G)^{**}` to
`\mathcal H\!\mathit{om}(\mathcal F,\mathcal G)`. -/
@[stacks 0EBL]
noncomputable def reflexiveHullDualTensorToInternalHom
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    [((((ihom ℱ).obj (𝟙_ (X.Modules))) ⊗ 𝒢 : X.Modules)).IsCoherent]
    [(((ihom ℱ).obj 𝒢)).IsCoherent] [IsReflexive ((ihom ℱ).obj 𝒢)] :
    reflexiveHull ((((ihom ℱ).obj (𝟙_ (X.Modules))) ⊗ 𝒢 : X.Modules)) ⟶
      (ihom ℱ).obj 𝒢 :=
  reflexiveHullMap (dualTensorToInternalHom ℱ 𝒢) ≫
    inv (toReflexiveHull ((ihom ℱ).obj 𝒢))

/-- Lemma 31.29.1 (1): let `X` be an integral locally Noetherian normal scheme. For coherent
reflexive `\mathcal O_X`-modules `\mathcal F` and `\mathcal G`, the canonical map
`(\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F,\mathcal O_X) \otimes_{\mathcal O_X}
\mathcal G)^{**} \to
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F,\mathcal G)` is an isomorphism. -/
@[stacks 0EBL]
theorem isIso_reflexiveHullDualTensorToInternalHom
    (hXnormal : X.isNormal)
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    [IsReflexive ℱ] [IsReflexive 𝒢] :
    letI : (𝟙_ (X.Modules)).IsCoherent := tensorUnit_isCoherent_of_isLocallyNoetherian X
    letI : (((ihom ℱ).obj (𝟙_ (X.Modules)))).IsCoherent := isCoherent_internalHom
    letI : ((((ihom ℱ).obj (𝟙_ (X.Modules))) ⊗ 𝒢 : X.Modules)).IsCoherent :=
      isCoherent_tensor
    letI : (((ihom ℱ).obj 𝒢)).IsCoherent := isCoherent_internalHom
    IsIso (reflexiveHullDualTensorToInternalHom ℱ 𝒢) := sorry

/-- Lemma 31.29.1 (2): for an integral locally Noetherian normal scheme `X`, the rule
`\mathcal F, \mathcal G \mapsto
(\mathcal F \otimes_{\mathcal O_X} \mathcal G)^{**}` defines an abelian group law on the
isomorphism classes of rank-one coherent reflexive `\mathcal O_X`-modules. -/
@[stacks 0EBL]
theorem exists_addCommGroup_rankOneReflexiveIsoClass_tensor_reflexiveHull
    (hXnormal : X.isNormal) :
    ∃ groupLaw : AddCommGroup (RankOneReflexiveIsoClass X),
      ∀ (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
        [IsReflexive ℱ] [IsReflexive 𝒢]
        (hℱrank : isRankOneAtGenericPoint X ℱ)
        (h𝒢rank : isRankOneAtGenericPoint X 𝒢),
        ∃ hTensorCoh : ((ℱ ⊗ 𝒢 : X.Modules)).IsCoherent,
          letI : ((ℱ ⊗ 𝒢 : X.Modules)).IsCoherent := hTensorCoh
          ∃ hHullCoh : (reflexiveHull (ℱ ⊗ 𝒢 : X.Modules)).IsCoherent,
            letI : (reflexiveHull (ℱ ⊗ 𝒢 : X.Modules)).IsCoherent := hHullCoh
            ∃ hHullRef : IsReflexive (reflexiveHull (ℱ ⊗ 𝒢 : X.Modules)),
              letI : IsReflexive (reflexiveHull (ℱ ⊗ 𝒢 : X.Modules)) := hHullRef
              ∃ hHullRank :
                isRankOneAtGenericPoint X (reflexiveHull (ℱ ⊗ 𝒢 : X.Modules)),
                letI : AddCommGroup (RankOneReflexiveIsoClass X) := groupLaw
                rankOneReflexiveIsoClassOf (reflexiveHull (ℱ ⊗ 𝒢 : X.Modules)) hHullRank =
                  rankOneReflexiveIsoClassOf ℱ hℱrank +
                    rankOneReflexiveIsoClassOf 𝒢 h𝒢rank := sorry

end AlgebraicGeometry.Scheme.Modules
