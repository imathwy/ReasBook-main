import StacksProject_2024.stacks_project.Chap07.Definition_7_17_4
import StacksProject_2024.stacks_project.Chap07.Lemma_7_17_5
import StacksProject_2024.stacks_project.Chap07.Lemma_7_17_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe wI v u

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 21.16.2:
- primary domain: filtered-colimit comparison for sheaf cohomology on a Grothendieck site, using
  source-facing test sets of set-valued sheaves;
- sampled owner declarations:
  `GrothendieckTopology.IsQuasiCompactTestSet`,
  `GrothendieckTopology.globalSectionsColimitComparison_bijective_of_quasiCompactTestSet`,
  `Sheaf.isQuasiCompactObject_of_isLocallySurjective`,
  `Sheaf.cohomologyFunctor`;
- best owner abstraction: the Chapter 7 owner `IsQuasiCompactTestSet` for the terminal-lift and
  quasi-compact-self-product consequences;
- primitive data here: the stronger source-facing surjective-cover, refinement, product,
  equalizer, and quasi-compactness hypotheses;
- derived API here: the canonical bridge from `IsCohomologyColimitTestSet` to
  `IsQuasiCompactTestSet`.

Source/core/bridge triage:
- `source-facing`: `IsCohomologyColimitTestSet`;
- `core/canonical`: `IsQuasiCompactTestSet`;
- `bridge/view`: the instance below reusing the Chapter 7 owner instead of a parallel local API.
-/

/-- A subset of sheaves satisfying the surjective-cover, product, equalizer, and
quasi-compactness hypotheses used to commute global sheaf cohomology with filtered colimits. -/
@[mk_iff isCohomologyColimitTestSet_iff]
class IsCohomologyColimitTestSet
    (S : Set (Sheaf J (Type (max u v)))) : Prop where
  exists_surjective_to_terminal :
    ∃ K : Sheaf J (Type (max u v)), K ∈ S ∧ IsLocallySurjective (terminal.from K)
  refine_surjection
      {F K : Sheaf J (Type (max u v))} (π : F ⟶ K)
      (hK : K ∈ S) (hπ : IsLocallySurjective π) :
      ∃ K' : Sheaf J (Type (max u v)), K' ∈ S ∧
        ∃ κ : K' ⟶ F, IsLocallySurjective (κ ≫ π)
  surjective_product
      {K K' : Sheaf J (Type (max u v))} (hK : K ∈ S) (hK' : K' ∈ S) :
      ∃ K'' : Sheaf J (Type (max u v)), K'' ∈ S ∧
        ∃ π : K'' ⟶ K ⨯ K', IsLocallySurjective π
  surjective_equalizer
      {K K' : Sheaf J (Type (max u v))} (a b : K ⟶ K')
      (hK : K ∈ S) (hK' : K' ∈ S) :
      ∃ K'' : Sheaf J (Type (max u v)), K'' ∈ S ∧
        ∃ π : K'' ⟶ equalizer a b, IsLocallySurjective π
  quasiCompact
      {K : Sheaf J (Type (max u v))} (hK : K ∈ S) :
      K.IsQuasiCompactObject

/-- The stronger cohomology-colimit test-set hypotheses imply the Chapter `7`
quasi-compact test-set criterion. -/
instance instIsQuasiCompactTestSetOfIsCohomologyColimitTestSet
    (S : Set (Sheaf J (Type (max u v)))) [IsCohomologyColimitTestSet J S] :
    IsQuasiCompactTestSet J S := by
  sorry

-- Proof sketch: for a surjection `F ⟶ *`, first choose the distinguished cover `K ⟶ *` from the
-- stronger test-set data and refine the pullback `F ×_* K ⟶ K` through another object of `S`,
-- giving the lifting clause required by Lemma `7.17.8 (4)`. For quasi-compact self-products, use
-- the product-surjection clause to produce `K'' ⟶ K × K` with `K'' ∈ S`, then descend
-- quasi-compactness along this locally surjective map via Lemma `7.17.5 (2)`.
variable {I : Type wI} [Category.{wI} I] [IsFiltered I]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I AddCommGrpCat.{v}]

-- Proof sketch: proceed by induction on `p`. The case `p = 0` reduces to Lemma `7.17.8 (4)`
-- using the weaker quasi-compact test-set extracted above. For the induction step, choose a
-- surjection `K ⟶ *` with `K ∈ S`, apply the Čech-to-cohomology spectral sequence of Lemma
-- `21.13.2`, and use the source hypotheses on products, equalizers, and quasi-compactness to show
-- that every localized site over `K^(n + 1)` again satisfies the same test-set condition. Then
-- filtered colimits commute with the lower-degree terms by the induction hypothesis, forcing the
-- injective-colimit term to be acyclic in degree `p + 1`.
/-- Lemma 21.16.2: if a site admits a subset `S` of sheaves of sets satisfying the source
surjectivity, product, equalizer, and quasi-compactness hypotheses, then for every filtered
diagram `ℱ` of abelian sheaves and every degree `p`, the canonical comparison morphism
`colimit.post ℱ (Sheaf.cohomologyFunctor J p)` is an isomorphism. -/
@[stacks 0GN3]
theorem siteCohomologyColimitComparison_isIso_of_isCohomologyColimitTestSet
    (S : Set (Sheaf J (Type (max u v))))
    [IsCohomologyColimitTestSet J S]
    (ℱ : I ⥤ Sheaf J AddCommGrpCat.{v}) (p : ℕ) :
    IsIso (colimit.post ℱ (Sheaf.cohomologyFunctor J p)) := sorry

end CategoryTheory.GrothendieckTopology
