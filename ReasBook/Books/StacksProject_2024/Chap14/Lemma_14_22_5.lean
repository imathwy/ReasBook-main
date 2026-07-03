import Mathlib
import StacksProject_2024.Chap14.Lemma_14_21_3
import StacksProject_2024.Chap14.Lemma_14_21_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A]

section

variable [HasFiniteColimits A]

/- Domain-style sampling for Lemma 14.22.5:
- primary domain: simplicial-object skeletons in a category with finite colimits, organized into the canonical
  sequential diagram whose colimit recovers the original simplicial object;
- sampled owner declarations:
  `sk`,
  `skAdj`,
  `Functor.ofSequence`,
  `evaluationJointlyReflectsColimits`,
  `Functor.IsEventuallyConstantFrom.isColimitOfIsIso`;
- best owner abstraction:
  `source-facing`: the sequence `n ↦ (sk n).obj V` together with its canonical cocone into `V`;
  `core/canonical`: the skeleton endofunctors `sk n`, the counits `(skAdj n).counit.app V`, and
    the sequence/cocone owners `Functor.ofSequence`, `NatTrans.ofSequence`, and
    `evaluationJointlyReflectsColimits`;
  `bridge/view`: the successor map from `(sk n).obj V` to `(sk (n + 1)).obj V`, obtained by
    transporting the unit of `skAdj (n + 1)` across truncation, together with the degreewise
    eventual-constancy bridge to `Functor.IsEventuallyConstantFrom.isColimitOfIsIso`.
- primitive data: the simplicial object `V` and the canonical counit maps from each skeleton to
  `V`;
- derived API: the sequential diagram of skeletons, its cocone into `V`, the monomorphism
  property of transition maps, and the colimit witness.

Source/core/bridge triage:
- `source-facing`: `skeletonSequence V` and `skeletonSequenceCocone V`;
- `core/canonical`: `sk`, `skAdj`, `Functor.ofSequence`, and `NatTrans.ofSequence`;
- `bridge/view`: the local successor-map construction below. -/

/-- The canonical map from the `n`-skeleton of a simplicial object to its `(n + 1)`-skeleton. -/
private noncomputable def skeletonSuccMap (V : SimplicialObject A) (n : ℕ) :
    (sk n).obj V ⟶ (sk (n + 1)).obj V :=
  ((skAdj n).homEquiv ((truncation n).obj V) ((sk (n + 1)).obj V)).symm
    (((truncationCompTrunc (Nat.le_succ n)).app V).inv ≫
      (Truncated.trunc A (n + 1) n).map
        ((skAdj (n + 1)).unit.app ((truncation (n + 1)).obj V)) ≫
      ((truncationCompTrunc (Nat.le_succ n)).app
        ((sk (n + 1)).obj V)).hom)

/-- The sequential diagram of the simplicial skeletons of `V`. -/
noncomputable def skeletonSequence (V : SimplicialObject A) : ℕ ⥤ SimplicialObject A :=
  Functor.ofSequence (skeletonSuccMap V)

-- Proof sketch: `skeletonSuccMap V n` is defined by adjunction from the truncation comparison
-- induced by the unit of `skAdj (n + 1)`. Unwinding that adjunction and the triangle identities
-- shows that composing with the counit to `V` recovers the counit from the `n`-skeleton.
/-- The maps in the skeleton sequence are compatible with the canonical inclusions into `V`. -/
private theorem skeletonSuccMap_comp_counit (V : SimplicialObject A) (n : ℕ) :
    skeletonSuccMap V n ≫ (skAdj (n + 1)).counit.app V = (skAdj n).counit.app V := sorry

/-- The canonical cocone from the sequence of skeletons of `V` to `V`. -/
noncomputable def skeletonSequenceCocone (V : SimplicialObject A) :
    Cocone (skeletonSequence V) where
  pt := V
  ι := NatTrans.ofSequence
    (fun n ↦ (skAdj n).counit.app V)
    (fun n ↦ by
      simpa [skeletonSequence, skeletonSuccMap_comp_counit] using
        skeletonSuccMap_comp_counit V n)

private theorem skeletonSequenceEvaluation_isEventuallyConstantFrom
    (V : SimplicialObject A) (m : ℕ) :
    Functor.IsEventuallyConstantFrom
      (skeletonSequence V ⋙ (evaluation _ A).obj (op (SimplexCategory.mk m))) m := by
  let ev : SimplicialObject A ⥤ A := (evaluation _ A).obj (op (SimplexCategory.mk m))
  intro j f
  let ε :
      ∀ n : ℕ,
        ((skeletonSequence V ⋙ ev).obj n ⟶ V.obj (op (SimplexCategory.mk m))) :=
    fun n ↦ ((skeletonSequenceCocone V).ι.app n).app (op (SimplexCategory.mk m))
  haveI : IsIso (ε m) := by
    simpa [ε, skeletonSequenceCocone] using
      truncatedSkeleton_counit_app_isIso_of_le m V (le_rfl : m ≤ m)
  haveI : IsIso (ε j) := by
    simpa [ε, skeletonSequenceCocone] using
      truncatedSkeleton_counit_app_isIso_of_le j V (leOfHom f)
  have hε :
      (skeletonSequence V ⋙ ev).map f ≫ ε j = ε m := by
    simpa [ε] using
      (ev.mapCocone (skeletonSequenceCocone V)).w f
  have hmap :
      (skeletonSequence V ⋙ ev).map f = ε m ≫ (asIso (ε j)).inv := by
    apply (cancel_mono (ε j)).1
    calc
      (skeletonSequence V ⋙ ev).map f ≫ ε j = ε m :=
        hε
      _ = (ε m ≫ (asIso (ε j)).inv) ≫ ε j := by simp [Category.assoc]
  rw [hmap]
  infer_instance

private noncomputable def skeletonSequenceEvaluation_isColimit
    (V : SimplicialObject A) (m : ℕ) :
    IsColimit
      (((evaluation _ A).obj (op (SimplexCategory.mk m))).mapCocone
        (skeletonSequenceCocone V)) := by
  let ev : SimplicialObject A ⥤ A := (evaluation _ A).obj (op (SimplexCategory.mk m))
  let h :
      Functor.IsEventuallyConstantFrom
        (skeletonSequence V ⋙ ev) m :=
    skeletonSequenceEvaluation_isEventuallyConstantFrom V m
  haveI :
      IsIso ((ev.mapCocone (skeletonSequenceCocone V)).ι.app m) := by
    simpa [skeletonSequenceCocone] using
      truncatedSkeleton_counit_app_isIso_of_le m V (le_rfl : m ≤ m)
  exact h.isColimitOfIsIso (ev.mapCocone (skeletonSequenceCocone V))

-- Proof sketch: evaluation at degree `m` preserves colimits in the functor category of simplicial
-- objects, and for every `m` the evaluated sequence is eventually constant because
-- `((sk n).obj V).obj (op ⦋m⦌) = V.obj (op ⦋m⦌)` once `n ≥ m`. Thus the canonical cocone
-- `skeletonSequenceCocone V` is degreewise colimiting, hence colimiting in `SimplicialObject A`.
/-- Lemma 14.22.5: for a simplicial object `V` in a category with finite colimits, the canonical sequential
diagram of skeletons
`(sk 0).obj V ⟶ (sk 1).obj V ⟶ (sk 2).obj V ⟶ ⋯`
has colimit cocone `skeletonSequenceCocone V`, so `V` is the colimit of its skeletons. The
companion theorem `skeletonSequence_map_mono` records under abelian hypotheses that all transition
maps are monomorphisms.
-/
noncomputable def skeletonSequence_isColimit (V : SimplicialObject A) :
    IsColimit (skeletonSequenceCocone V) :=
  evaluationJointlyReflectsColimits (skeletonSequenceCocone V) fun Δ ↦ by
    cases Δ with
    | op Δ =>
        cases Δ with
        | mk m =>
            simpa using skeletonSequenceEvaluation_isColimit V m

end

section

variable [Abelian A]

-- Proof sketch: the cocone identity for `skeletonSequenceCocone V` gives
-- `(skeletonSequence V).map (homOfLE h) ≫ (skAdj j).counit.app V = (skAdj i).counit.app V`.
-- Both counits are mono by Lemma 14.21.10, so the left factor is mono by cancellation.
/-- Every transition morphism in the skeleton sequence of `V` is monomorphic. -/
theorem skeletonSequence_map_mono (V : SimplicialObject A) {i j : ℕ} (h : i ≤ j) :
    Mono ((skeletonSequence V).map (homOfLE h)) := by
  haveI : Mono ((skAdj i).counit.app V) := truncatedSkeleton_counit_mono i V
  let fac :
      (skeletonSequence V).map (homOfLE h) ≫ (skAdj j).counit.app V = (skAdj i).counit.app V := by
    simpa [skeletonSequenceCocone] using (skeletonSequenceCocone V).w (homOfLE h)
  refine ⟨?_⟩
  intro Z f g hfg
  apply (cancel_mono ((skAdj i).counit.app V)).1
  calc
    f ≫ (skAdj i).counit.app V
        = (f ≫ (skeletonSequence V).map (homOfLE h)) ≫ (skAdj j).counit.app V := by
            rw [Category.assoc, fac]
    _ = (g ≫ (skeletonSequence V).map (homOfLE h)) ≫ (skAdj j).counit.app V := by
          rw [hfg]
    _ = g ≫ (skAdj i).counit.app V := by
          rw [Category.assoc, fac]

end

end CategoryTheory
