import stacks_proof.stacks_project.Chap08.Lemma_8_11_3.Index
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open BasedFunctor
open Functor
open Functor.Fiber
open Functor.IsStronglyCartesian
open FibredCategoryOver

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver.{u₁, v₁, max u₁ v₁, v₁} J}

-- Proof sketch: the stack field is supplied by the inherited-topology theorem for fibred
-- morphisms, while the two gerbe local fields are transported through the strict factorization
-- and the equivalence on source fibers.
/-- Lemma 8.11.3: let `F : Xₛ ⟶ Yₛ` be a morphism of stacks in groupoids over `(C, J)`, and let
`a : Xₛ ⥤ᵇ X'` be an equivalence over `C` such that `a ⋙ F' = toBasedFunctor F`, where
`F' : X' ⟶ Yₛ` is fibred in groupoids over `Yₛ`. Then `F'`, viewed over the topology on `Yₛ`
inherited from `(C, J)`, is a gerbe if and only if `F` is locally essentially surjective on
objects and locally lifts fiber morphisms after passing to a cover. -/
@[stacks 06P1]
theorem isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms_of_factorization
    (F : Xₛ ⟶ Yₛ)
    {X' : BasedCategory.{v₁, max u₁ v₁} C}
    (a : Xₛ.toBasedCategory ⥤ᵇ X')
    (F' : X' ⥤ᵇ Yₛ.toBasedCategory)
    [IsFibredInGroupoids F'.toFunctor]
    (ha : a.IsEquivalenceOverBase)
    (hfactor : a ⋙ F' = toBasedFunctor F) :
    IsGerbe (inheritedTopology J Yₛ) F'.toFunctor ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F := by
  let Ftarget := fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)
  let Fsource := fibredInGroupoidsFactorizationFromSource (toBasedFunctor F)
  letI : IsFibredInGroupoids Ftarget.toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids (toBasedFunctor F)
  have hsourceEquiv : Fsource.IsEquivalenceOverBase :=
    fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase (toBasedFunctor F)
  letI : IsStackInGroupoids (inheritedTopology J Yₛ) F'.toFunctor :=
    factorizationProjection_isStackInGroupoidsOverInheritedTopology
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) a F' ha
  letI : IsStackInGroupoids (inheritedTopology J Yₛ) Ftarget.toFunctor :=
    factorizationProjection_isStackInGroupoidsOverInheritedTopology
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) Fsource Ftarget hsourceEquiv
  obtain ⟨h, hEquiv, _hCompC, _hCompY⟩ :=
    exists_equivalence_over_target_between_fibred_groupoid_factorizations_of_strict_comm
      (F := toBasedFunctor F)
      (a := Fsource)
      (f := Ftarget)
      (b := a)
      (g := F')
      hsourceEquiv
      ha
      (fibredInGroupoidsFactorization_comp (toBasedFunctor F))
      hfactor
  let arbitraryStack : StackInGroupoidsOver (inheritedTopology J Yₛ) :=
    StackInGroupoidsOver.ofProjection (inheritedTopology J Yₛ) F'.toFunctor
  let canonicalStack : StackInGroupoidsOver (inheritedTopology J Yₛ) :=
    StackInGroupoidsOver.ofProjection (inheritedTopology J Yₛ) Ftarget.toFunctor
  let H : arbitraryStack ⟶ canonicalStack :=
    StackInGroupoidsOver.Hom.ofBasedFunctor h
  have hH : H.IsEquivalenceOverBase := by
    -- The Chapter 4 comparison is already an equivalence over the inherited target base.
    change h.IsEquivalenceOverBase
    exact hEquiv
  have hGerbeTransport :
      IsGerbe (inheritedTopology J Yₛ) F'.toFunctor ↔
        IsGerbe (inheritedTopology J Yₛ) Ftarget.toFunctor := by
    -- Transport gerbes across the equivalence of the two strict factorizations over `Yₛ`.
    simpa [arbitraryStack, canonicalStack, StackInGroupoidsOver.p] using
      (gerbe_iff_of_equivalenceOverBase (K := inheritedTopology J Yₛ) H hH)
  exact
    hGerbeTransport.trans
      (canonicalFactorizationToTarget_isGerbeOverInheritedTopology_iff_localConditions
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F)

-- Proof sketch: apply the main factorization-independent statement to the canonical explicit
-- factorization `X ×_{F,Y,\mathrm{id}} Y ⟶ Y`, where the source comparison
-- `X ⟶ X ×_{F,Y,\mathrm{id}} Y` is an equivalence over `C` by Lemma `4.35.16`.
/-- Canonical specialization of Lemma 8.11.3 to the explicit factorization
`X ×_{F,Y,\mathrm{id}} Y ⟶ Y`. This is the bridge from the source-facing factorization statement
to the chapter's canonical factorization owner. -/
theorem factorizationToTarget_isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms
    (F : Xₛ ⟶ Yₛ) :
    IsGerbe (inheritedTopology J Yₛ)
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F := by
  letI :
      IsFibredInGroupoids
        (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids (toBasedFunctor F)
  exact
    canonicalFactorizationToTarget_isGerbeOverInheritedTopology_iff_localConditions
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F

end

end StackInGroupoidsOver.Hom

end CategoryTheory
