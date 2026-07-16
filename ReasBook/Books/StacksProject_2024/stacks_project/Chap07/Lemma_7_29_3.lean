import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_29_2
import StacksProject_2024.stacks_project.Chap07.Lemma_7_28_1
import StacksProject_2024.stacks_project.Chap07.Lemma_7_28_4
-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.29.3:
- primary domain: comparison-lemma style sheaf equivalences for dense subsites and their slice-site
  localizations;
- sampled owner API:
  `Functor.IsDenseSubsite`,
  `Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension`,
  `Over.post`;
- source/core/bridge triage:
  `source-facing`: the localized dense-subsite instance for `Over.post u`;
  `core/canonical`: the dense-subsite direct-image equivalence instance for
  `G.sheafPushforwardCocontinuous`;
  `bridge/view`: the slice-site specialization obtained by instantiating that canonical instance at
  `G := Over.post u`.

Primitive data here are only the functor `u`, the object `U`, and the owner instance
`u.IsDenseSubsite J K`. The sheaf-equivalence statement is derived API from that
owner together with separate pointwise right Kan extension hypotheses on `Over.post u`, so this
file should keep only the localized owner instance and recall the bridge theorem directly rather
than introducing a parallel theorem wrapper.
-/

/-- Lemma 7.29.3, source-facing owner layer: a dense-subsite functor remains a dense subsite
after passage to any slice site. -/
instance overPost_isDenseSubsite
    (u : C ⥤ D) (U : C) [u.IsDenseSubsite J K] :
    (Over.post u).IsDenseSubsite (J.over U) (K.over (u.obj U)) := by
  letI : Functor.IsSourceLocallyFaithful (Over.post u) (J.over U) := by
    sorry
  letI : Functor.IsSourceLocallyFull (Over.post u) (J.over U) := by
    sorry
  letI : (Over.post u).IsCoverDense (K.over (u.obj U)) := by
    sorry
  exact sourceLocal_isDenseSubsite (Over.post u)

/- Lemma 7.29.3, bridge/view recall: once `overPost_isDenseSubsite` upgrades `Over.post u`
to the canonical dense-subsite owner on slice sites, the induced cocontinuous direct image
on sheaves of sets is an equivalence after supplying the needed pointwise right Kan extensions. -/
variable (u : C ⥤ D) (U : C) [u.IsDenseSubsite J K]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂),
  (Over.post u).op.HasPointwiseRightKanExtension P]

#synth
  ((Over.post u).sheafPushforwardCocontinuous (Type (max u₁ u₂ v₁ v₂)) (J.over U)
    (K.over (u.obj U))).IsEquivalence

end CategoryTheory
