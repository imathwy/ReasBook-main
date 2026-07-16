import Mathlib
import stacks_proof.stacks_project.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open SSet.modelCategoryQuillen

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

private theorem limitProjection_ofSequence_hasLiftingProperty
    {X : ℕ → C} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)
    [HasLimit (Functor.ofOpSequence f)] {A B : C} (g : A ⟶ B)
    (hf : ∀ n : ℕ, HasLiftingProperty g (f n)) :
    HasLiftingProperty g (limit.π (Functor.ofOpSequence f) (op 0)) := by
  let F := Functor.ofOpSequence f
  refine ⟨fun {u v} sq ↦ ?_⟩
  let successorSq (n : ℕ) (prev : B ⟶ X n)
      (hprev : u ≫ limit.π F (op n) = g ≫ prev) :
      CommSq (u ≫ limit.π F (op (n + 1))) g (f n) prev := by
    have hπ :
        limit.π F (op (n + 1)) ≫ f n = limit.π F (op n) := by
      simpa [F] using limit.w F (homOfLE (Nat.le_add_right n 1)).op
    have hsucc :
        u ≫ limit.π F (op (n + 1)) ≫ f n = u ≫ limit.π F (op n) := by
      exact congrArg (fun k ↦ u ≫ k) hπ
    exact CommSq.mk (by simpa [Category.assoc] using hsucc.trans hprev)
  let stage₀ : { l : B ⟶ X 0 // u ≫ limit.π F (op 0) = g ≫ l } :=
    ⟨v, sq.w⟩
  let succStage (n : ℕ)
      (prev : { l : B ⟶ X n // u ≫ limit.π F (op n) = g ≫ l }) :
      { l : B ⟶ X (n + 1) // u ≫ limit.π F (op (n + 1)) = g ≫ l } := by
    let hsq := successorSq n prev.1 prev.2
    let _ : hsq.HasLift := (hf n).sq_hasLift hsq
    exact ⟨hsq.lift, (CommSq.fac_left hsq).symm⟩
  have succStage_w (n : ℕ)
      (prev : { l : B ⟶ X n // u ≫ limit.π F (op n) = g ≫ l }) :
      prev.1 = (succStage n prev).1 ≫ f n := by
    let hsq := successorSq n prev.1 prev.2
    let _ : hsq.HasLift := (hf n).sq_hasLift hsq
    simpa only [succStage] using (CommSq.fac_right hsq).symm
  let stage : (n : ℕ) → { l : B ⟶ X n // u ≫ limit.π F (op n) = g ≫ l } :=
    Nat.rec stage₀ (fun n prev ↦ succStage n prev)
  let c : Cone F := {
    pt := B
    π := NatTrans.ofOpSequence (fun n ↦ (stage n).1) (fun n ↦ by
      simpa [stage, F] using succStage_w n (stage n))
  }
  refine CommSq.HasLift.mk' ?_
  refine ⟨limit.lift F c, ?_, ?_⟩
  · apply limit.hom_ext
    intro n
    rw [Category.assoc, limit.lift_π]
    simpa [c] using (stage n.unop).2.symm
  · rw [limit.lift_π]
    rfl

namespace MorphismProperty

/-- The projection from the inverse limit of a countable tower of morphisms in `T.rlp` again lies
in `T.rlp`. -/
theorem rlp_limitProjection_ofSequence (T : MorphismProperty C)
    {X : ℕ → C} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)
    [HasLimit (Functor.ofOpSequence f)] (hf : ∀ n : ℕ, T.rlp (f n)) :
    T.rlp (limit.π (Functor.ofOpSequence f) (Opposite.op 0)) :=
  fun _ _ g hg ↦ limitProjection_ofSequence_hasLiftingProperty f g (fun n ↦ hf n g hg)

end MorphismProperty

end CategoryTheory

variable {X : ℕ → SSet.{u}} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)

/- Domain-style sampling for Lemma 14.30.5:
- primary domain: lifting properties of inverse-limit projections for sequential diagrams,
  specialized to simplicial sets.
- inspected owner declarations:
  `CategoryTheory.MorphismProperty.rlp`,
  `CategoryTheory.MorphismProperty.rlp_limitProjection_ofSequence`,
  `CategoryTheory.Functor.ofOpSequence`,
  `boundaryInclusions_rlp_hasLiftingProperty`.
- best owner abstraction: the morphism-property theorem
  `CategoryTheory.MorphismProperty.rlp_limitProjection_ofSequence`, specialized here to the
  Chapter 14 owner property `I.rlp`.
- primitive-vs-derived split:
  primitive data: the inverse sequence `f` and the stagewise owner property `I.rlp (f n)`;
  derived API: the source-facing specialized interface for trivial Kan fibrations.

Source/core/bridge triage:
- `source-facing`: the textbook statement about inverse limits of trivial Kan fibrations.
- `core/canonical`: the owner theorem
  `CategoryTheory.MorphismProperty.rlp_limitProjection_ofSequence`.
- `bridge/view`: Definition 14.30.1, which identifies the textbook notion with `I.rlp`. -/

/- Lemma 14.30.5: for a countable inverse sequence of trivial Kan fibrations of simplicial sets,
equivalently of morphisms having the right lifting property with respect to all boundary
inclusions, the canonical projection from the inverse limit to the initial term again has that
right lifting property. In the refined API this source-facing statement is used directly as the
owner specialization `I.rlp_limitProjection_ofSequence f`. -/
#check (I.rlp_limitProjection_ofSequence f :
  ∀ [HasLimit (Functor.ofOpSequence f)],
    (∀ n : ℕ, I.rlp (f n)) → I.rlp (limit.π (Functor.ofOpSequence f) (Opposite.op 0)))
