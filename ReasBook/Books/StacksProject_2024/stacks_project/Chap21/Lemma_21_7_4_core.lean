import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1_core

open CategoryTheory

noncomputable section

universe u v

namespace RingedSite.Hom

/-- The `i`-th higher direct image of a sheaf of modules along a morphism of ringed sites. -/
abbrev higherDirectImageModule {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
    [Functor.Additive f.modulePushforward]
    [HasInjectiveResolutions (ModuleCat X)]
    (ℱ : ModuleCat X) (i : ℕ) :
    ModuleCat Y :=
  (f.modulePushforward.rightDerived i).obj ℱ

/- Lean surface notation for the higher direct image `R^i f_*(\mathcal F)`. A thin macro keeps
instance search at use sites instead of forcing it during notation elaboration. -/
scoped macro:max "R^{" i:term "}_[" f:term "](" F:term ")" : term =>
  `(@higherDirectImageModule _ _ $f _ _ $F $i)

end RingedSite.Hom
