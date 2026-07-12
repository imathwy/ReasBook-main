import Mathlib
import StacksProject_2024.Chap12.Lemma_12_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

universe w v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u} [Category.{w} D]
variable {W : MorphismProperty C} (L : C ⥤ D) [L.IsLocalization W]

private theorem instPreadditiveUnop_eq (A : Type u) [Category.{v} A] [P : Preadditive A] :
    letI : Preadditive Aᵒᵖ := inferInstance
    instPreadditiveUnop A = P := by
  apply Preadditive.ext
  funext X Y
  apply AddCommGroup.ext
  ext f g
  simp only [Equiv.add_def]
  let e : (X ⟶ Y) ≃ ((opOp A).obj X ⟶ (opOp A).obj Y) :=
    (Functor.FullyFaithful.ofFullyFaithful (opOp A)).homEquiv
  have h : e f + e g = e (f + g) := by
    change f.op.op + g.op.op = (f + g).op.op
    simp
  change e.symm (e f + e g) = f + g
  rw [h, e.symm_apply_apply]

namespace Localization

/- Source/core/bridge triage for Lemma 12.8.1:
- source-facing: the main item states existence and uniqueness of a preadditive structure on a
  localization making the localization functor additive
- core/canonical owner: for left fractions, the owner is `Localization.preadditive L W` together
  with `Localization.functor_additive L W`
- bridge/view: for right fractions, pass to `L.op : Cᵒᵖ ⥤ Dᵒᵖ`, use the left-fraction owner there,
  and transport the resulting preadditive structure back along the chapter owner
  `instPreadditiveUnop` from Lemma 12.5.2. -/
/-- The preadditive structure on `D` induced from the opposite localization when `W` has a right
calculus of fractions. -/
@[reducible] noncomputable def preadditiveOfHasRightCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.HasRightCalculusOfFractions] :
    Preadditive D :=
  letI : Preadditive Dᵒᵖ := preadditive L.op W.op
  instPreadditiveUnop D

lemma functor_additive_of_hasRightCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.HasRightCalculusOfFractions] :
    letI := preadditiveOfHasRightCalculusOfFractions L W
    L.Additive := by
  letI : Preadditive Dᵒᵖ := preadditive L.op W.op
  letI : Preadditive D :=
    Preadditive.ofFullyFaithful ((opOpEquivalence D).symm.fullyFaithfulFunctor)
  letI : L.op.Additive := functor_additive L.op W.op
  letI : Functor.Additive (L.op.rightOp) := inferInstance
  letI : (unopUnop D).Additive := by
    simpa using Equivalence.additive_inverse_of_FullyFaithful ((opOpEquivalence D).symm)
  have hAdd : (L.op.rightOp ⋙ unopUnop D).Additive := inferInstance
  rw [preadditiveOfHasRightCalculusOfFractions, instPreadditiveUnop]
  convert hAdd using 1
  congr
  exact Subsingleton.elim _ _

end Localization

private lemma localization_preadditive_unique
    {A : Type*} [Category A] [Preadditive A]
    {B : Type*} [Category B] (S : MorphismProperty A) (F : A ⥤ B) [F.IsLocalization S]
    [S.HasLeftCalculusOfFractions]
    (P Q : Preadditive B)
    (hP : letI := P; F.Additive)
    (hQ : letI := Q; F.Additive) :
    P = Q := by
  letI := P
  letI : F.Additive := hP
  let B' := InducedCategory B id
  letI : Category B' := inferInstance
  letI : Preadditive B' := by
    letI := Q
    infer_instance
  let G : B ⥤ B' :=
    { obj := id
      map := fun f ↦ InducedCategory.homMk f }
  have hFG : (F ⋙ G).Additive := by
    letI := Q
    letI : F.Additive := hQ
    refine ⟨?_⟩
    intro X Y f g
    ext
    exact F.map_add
  have hG : G.Additive := (Localization.functor_additive_iff F S G).2 hFG
  apply Preadditive.ext
  funext X Y
  apply AddCommGroup.ext
  ext f g
  simpa [G] using congrArg InducedCategory.Hom.hom G.map_add

section LeftCalculusOfFractions

private lemma localization_existsUnique_preadditive_of_hasLeftCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.HasLeftCalculusOfFractions] :
    ∃! P : Preadditive D, letI := P; L.Additive := by
  let P₀ : Preadditive D := Localization.preadditive L W
  have hP₀ : letI := P₀; L.Additive := by
    simpa [P₀] using (Localization.functor_additive L W)
  refine ⟨P₀, ?_, ?_⟩
  · exact hP₀
  · intro P hP
    exact localization_preadditive_unique W L P P₀ hP hP₀

end LeftCalculusOfFractions

section RightCalculusOfFractions

private lemma localization_existsUnique_preadditive_of_hasRightCalculusOfFractions
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.HasRightCalculusOfFractions] :
    ∃! P : Preadditive D, letI := P; L.Additive := by
  let P₀ : Preadditive D := Localization.preadditiveOfHasRightCalculusOfFractions L W
  refine ⟨P₀, ?_, ?_⟩
  · simpa [P₀] using Localization.functor_additive_of_hasRightCalculusOfFractions L W
  · intro P hP
    letI := P
    letI : L.Additive := hP
    let transport : Preadditive Dᵒᵖ → Preadditive D := fun R ↦
      letI : Preadditive Dᵒᵖ := R
      show Preadditive D from instPreadditiveUnop D
    have hP_op : letI := instPreadditiveOpposite D; L.op.Additive := by
      infer_instance
    have hP₀_op : instPreadditiveOpposite D = Localization.preadditive L.op W.op := by
      exact localization_preadditive_unique W.op L.op (instPreadditiveOpposite D)
        (Localization.preadditive L.op W.op) hP_op
        (Localization.functor_additive L.op W.op)
    have htransport : transport (instPreadditiveOpposite D) =
        transport (Localization.preadditive L.op W.op) := by
      exact congrArg transport hP₀_op
    have htransport_left : transport (instPreadditiveOpposite D) = P := by
      simpa [transport] using (instPreadditiveUnop_eq D)
    have htransport_right : transport (Localization.preadditive L.op W.op) = P₀ := by
      rfl
    calc
      P = transport (instPreadditiveOpposite D) := htransport_left.symm
      _ = transport (Localization.preadditive L.op W.op) := htransport
      _ = P₀ := htransport_right

end RightCalculusOfFractions

-- Proof sketch: in the left-fraction case, use the canonical construction
-- `CategoryTheory.Localization.preadditive L W` together with
-- `CategoryTheory.Localization.functor_additive L W`. In the right-fraction case, pass to the
-- opposite localization, apply the left-fraction construction there, and transfer the resulting
-- preadditive structure back across opposites.
/-- Lemma 12.8.1: if `C` is preadditive and `W` is a left or right multiplicative system, then
any localization functor `L : C ⥤ D` carries a unique preadditive structure on `D` for which `L`
is additive. -/
@[stacks 05QD]
theorem localization_existsUnique_preadditive
    (hW : W.HasLeftCalculusOfFractions ∨ W.HasRightCalculusOfFractions) :
    ∃! P : Preadditive D, letI := P; L.Additive := by
  rcases hW with hW | hW
  · letI := hW
    exact localization_existsUnique_preadditive_of_hasLeftCalculusOfFractions L W
  · letI := hW
    exact localization_existsUnique_preadditive_of_hasRightCalculusOfFractions L W

end CategoryTheory
