import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksProject_2024.stacks_project.Chap07.Definition_7_8_1
import StacksProject_2024.stacks_project.Chap08.Definition_8_11_1
import StacksProject_2024.stacks_project.Chap08.Lemma_8_11_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open SemiRepresentableFamily.Over

noncomputable section

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.11.1:
- primary domain: gerbes and their bands on a site, together with cofinal covering families on the
  slice site `(C / U, J.over U)` and cohomology vanishing on members of those families;
- sampled owner declarations:
  `IsGerbe`,
  `HasAbelianAutomorphismSheaves`,
  `IsGerbeBand`,
  `GrothendieckTopology.CoversTop`,
  `Sheaf.over`,
  `Sheaf.H`,
  `SemiRepresentableFamily.Over.Refines`,
  `SemiRepresentableFamily.Over.ofArrows`;
- best owner abstraction:
  `source-facing`: the cofinal vanishing-on-terms-and-overlaps hypothesis for the band sheaf over
    `U`;
  `core/canonical`: the gerbe owners `IsGerbe`, `HasAbelianAutomorphismSheaves`, `IsGerbeBand`,
    together with the slice-site cover owner `GrothendieckTopology.CoversTop`, the localized
    sheaf owner `Sheaf.over`, and the slice-site cohomology owner `Sheaf.H`;
  `bridge/view`: the indexed-arrow presentation of slice families through `ofArrows`, used with
    the chapter refinement owner `Refines`.

Primitive data versus derived API:
- primitive data: an indexed covering family `V : ι → Over U`, a refining family `W : κ → Over U`
  together with a refinement `Refines ... ...`, and cohomology vanishing on the terms `W i` and
  their pairwise overlaps;
- derived API: the unpacking theorem for the cofinal hypothesis and the gerbe section-existence
  consequence.

The refinement therefore keeps the source-facing cofinal-vanishing predicate on the same owner
level as the adjacent Chapter 21 cofinal-covering lemmas, while simplifying only the downstream
API shape that is genuinely redundant.
-/

namespace Sheaf

/-- A sheaf of abelian groups has a cofinal system of coverings of `U` on which the first
cohomology vanishes on every member of the cover and on every pairwise overlap. -/
def HasCofinalCoveringsWithVanishingH1OnTermsAndOverlaps
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{max u v}) (U : C)
    [Limits.HasFiniteProducts (Over U)]
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v}]
    [∀ X : C, HasExt (Sheaf (J.over X) AddCommGrpCat.{max u v})] : Prop :=
  ∀ (ι : Type w) (V : ι → Over U), (J.over U).CoversTop V →
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Refines
          (ofArrows (fun i ↦ (W i).left) fun i ↦ (W i).hom)
          (ofArrows (fun i ↦ (V i).left) fun i ↦ (V i).hom) ∧
        (∀ i : κ, IsZero <| AddCommGrpCat.of ((G.over (W i).left).H 1)) ∧
        ∀ i j : κ, IsZero <| AddCommGrpCat.of ((G.over ((Limits.prod (W i) (W j)).left)).H 1)

-- Proof sketch: this is the defining expansion of
-- `HasCofinalCoveringsWithVanishingH1OnTermsAndOverlaps`; apply the hypothesis to the chosen
-- covering family.
/-- Unfolding the cofinal vanishing hypothesis yields a refining covering whose members and
pairwise overlaps all have trivial first cohomology. -/
theorem hasCofinalCoveringsWithVanishingH1OnTermsAndOverlaps_exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)]
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v}]
    [∀ X : C, HasExt (Sheaf (J.over X) AddCommGrpCat.{max u v})]
    {G : Sheaf J AddCommGrpCat.{max u v}}
    (hG : G.HasCofinalCoveringsWithVanishingH1OnTermsAndOverlaps U)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Refines
          (ofArrows (fun i ↦ (W i).left) fun i ↦ (W i).hom)
          (ofArrows (fun i ↦ (V i).left) fun i ↦ (V i).hom) ∧
        (∀ i : κ, IsZero <| AddCommGrpCat.of ((G.over (W i).left).H 1)) ∧
        ∀ i j : κ, IsZero <| AddCommGrpCat.of ((G.over ((Limits.prod (W i) (W j)).left)).H 1) :=
  sorry

end Sheaf

-- Proof sketch: choose a covering of `U` carrying local objects by the gerbe condition, then
-- refine it using the cofinal vanishing hypothesis so that the band has vanishing `H¹` on each
-- member and each overlap. The resulting local isomorphism torsors are trivial, so one can choose
-- descent isomorphisms. Their failure to satisfy the cocycle condition is a Čech `2`-cocycle with
-- values in the band; the vanishing of `H²(U, band.sheaf)` and the Čech-to-sheaf-cohomology
-- comparison make this cocycle a coboundary, so the descent datum can be corrected and then
-- glued by stack descent.
/-- Lemma 21.11.1: let `𝒮` be a gerbe on `(C, J)` with abelian automorphism sheaves, and let
`G` be the abelian band sheaf constructed from those automorphism sheaves. If `G` has a cofinal
system of coverings of `U` on which the first cohomology vanishes on every member and every
pairwise overlap, and if `H^2(U, G) = 0`, then the gerbe `𝒮` has an object lying over `U`. -/
@[stacks 0CK0]
theorem gerbe_has_section_of_cofinal_H1_vanishing_and_H2_vanishing
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v}]
    [∀ X : C, HasExt (Sheaf (J.over X) AddCommGrpCat.{max u v})]
    (𝒮 : StackInGroupoidsOver J) (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (G : Sheaf J AddCommGrpCat.{max u v}) (hband : IsGerbeBand hAbelian G)
    (U : C) [Limits.HasFiniteProducts (Over U)]
    (hcofinal : G.HasCofinalCoveringsWithVanishingH1OnTermsAndOverlaps U)
    (hH2 : IsZero <| AddCommGrpCat.of ((G.over U).H 2)) :
    Nonempty (𝒮.p.Fiber U) := sorry

end CategoryTheory
