import Mathlib
import stacks_project.Chap13.Definition_13_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.41.3:
- primary domain: low-length Postnikov systems in a pretriangulated category;
- inspected canonical owner declarations:
  `PostnikovSystem`,
  `PostnikovSystemMorphism`,
  `CommSq`,
  `PostnikovSystem.mk₀`,
  `ComposableArrows.homMk₀` / `ComposableArrows.hom_ext₀`,
  `ComposableArrows.homMk₁` / `ComposableArrows.hom_ext₁`;
- best owner abstraction: the source-facing objects remain `PostnikovSystem X` and
  `PostnikovSystemMorphism P P' φ`, while the core/canonical low-length bookkeeping is handled by
  the existing `ComposableArrows` owners and the triangle API from `Definition_13_41_1`;
- primitive-vs-derived split:
  primitive data: a Postnikov system and a morphism of Postnikov systems;
  derived API: the length-`0` and length-`1` componentwise descriptions coming from the canonical
    `ComposableArrows` small-length API, the triangle view of a stage of a Postnikov system, and
    the induced complexness of the underlying `ComposableArrows` object.

Source/core/bridge triage:
- source-facing: the existence and uniqueness statements about `PostnikovSystem` and
  `PostnikovSystemMorphism`;
- core/canonical: `ComposableArrows` in lengths `0`, `1`, and `2`, together with the
  distinguished-triangle API;
- bridge/view: identifying the length-`1` case with extending an arrow to a distinguished triangle
  and the length-`0` case with the unique component map on the sole auxiliary object.
-/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

-- Proof sketch: a length-`0` complex is just one object, so the source-facing owner
-- `PostnikovSystem X` is given directly by the canonical base constructor `PostnikovSystem.mk₀`.
/-- Lemma 13.41.3 (1): every length-`0` complex in a triangulated category admits a Postnikov
system. -/
theorem length_zero_postnikovSystem_exists (X : ComposableArrows D 0) :
    Nonempty (PostnikovSystem X) :=
  ⟨PostnikovSystem.mk₀ (X.obj 0) (𝟙 (X.obj 0))⟩

-- Proof sketch: for `n = 0`, the only square to satisfy is the compatibility with
-- `Y₀ ⟶ X₀`, so the extension problem is governed by the unique component map in
-- `ComposableArrows D 0`.
/-- Lemma 13.41.3 (2): for length `0`, every morphism of complexes extends to a morphism of
Postnikov systems. -/
theorem length_zero_morphism_extension_exists
    {X X' : ComposableArrows D 0} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') : Nonempty (PostnikovSystemMorphism P P' φ) := by
  let e : P' 0 ≅ X'.obj 0 := by
    simpa using asIso (P'.toX (Fin.last 0))
  let yMap : (i : Fin (0 + 1)) → P i ⟶ P' i := fun i ↦
    match i with
    | ⟨0, _⟩ => P.toX 0 ≫ φ.app 0 ≫ e.inv
  refine ⟨{
    yMap := yMap
    comm_toX := ?_
    comm_toNext := fun i ↦ Fin.elim0 i
    comm_connecting := fun i ↦ Fin.elim0 i
  }⟩
  intro i
  fin_cases i
  refine CommSq.mk ?_
  simp [yMap, e]

-- Proof sketch: for `n = 0`, a morphism of Postnikov systems is determined by its only component
-- on `Y₀`, and the compatibility with `Y₀ ⟶ X₀` forces that component uniquely.
/-- Lemma 13.41.3 (3): for length `0`, the extension of a morphism of complexes to Postnikov
systems is unique. -/
theorem length_zero_morphism_extension_subsingleton
    {X X' : ComposableArrows D 0} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') : Subsingleton (PostnikovSystemMorphism P P' φ) := by
  let e : P' 0 ≅ X'.obj 0 := by
    simpa using asIso (P'.toX (Fin.last 0))
  refine ⟨?_⟩
  intro ψ ψ'
  have h0 : ψ.yMap 0 = ψ'.yMap 0 := by
    have hcomm : ψ.yMap 0 ≫ P'.toX 0 = ψ'.yMap 0 ≫ P'.toX 0 := by
      simpa using (ψ.comm_toX 0).w.symm.trans (ψ'.comm_toX 0).w
    have := congrArg (fun f ↦ f ≫ e.inv) hcomm
    simpa [Category.assoc, e] using this
  have hy : ψ.yMap = ψ'.yMap := by
    funext i
    fin_cases i
    exact h0
  cases ψ
  cases ψ'
  cases hy
  simp

-- Proof sketch: every arrow in a triangulated category extends to a distinguished triangle, and
-- that core triangle owner is exactly the data of a length-`1` Postnikov system.
/-- Lemma 13.41.3 (4): every length-`1` complex in a triangulated category admits a Postnikov
system. -/
theorem length_one_postnikovSystem_exists (X : ComposableArrows D 1) :
    Nonempty (PostnikovSystem X) := sorry

-- Proof sketch: after choosing distinguished triangles for the two length-`1` Postnikov systems,
-- TR3 extends the given morphism of arrows to a morphism of triangles, hence to a morphism of
-- Postnikov systems.
/-- Lemma 13.41.3 (5): for length `1`, every morphism of complexes extends to a morphism of
Postnikov systems. -/
theorem length_one_morphism_extension_exists
    {X X' : ComposableArrows D 1} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') : Nonempty (PostnikovSystemMorphism P P' φ) := sorry

-- Proof sketch: choose a Postnikov system for the tail `X₁ ⟶ X₀`, factor `X₂ ⟶ X₁` through the
-- auxiliary object using the vanishing of the composite `X₂ ⟶ X₁ ⟶ X₀`, and complete that factor
-- to a distinguished triangle.
/-- Lemma 13.41.3 (6): every length-`2` complex in a triangulated category admits a Postnikov
system. This is the first non-formal existence step beyond the vacuous length-`0` and triangle
length-`1` owner cases. -/
theorem length_two_postnikovSystem_exists (X : ComposableArrows D 2) (hX : X.IsComplex) :
    Nonempty (PostnikovSystem X) := sorry

end

-- Proof sketch: the textbook statement is a non-universality claim. One exhibits a triangulated
-- category, two length-`2` complexes with chosen Postnikov systems, and a morphism of complexes
-- for which no compatible morphism of Postnikov systems exists.
/-- Lemma 13.41.3 (7): for length `2`, it is not true in general that every morphism of complexes
extends to a morphism of Postnikov systems. -/
theorem length_two_morphism_extension_not_universal :
    ¬ ∀ {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D] {X X' : ComposableArrows D 2}
        (P : PostnikovSystem X) (P' : PostnikovSystem X') (φ : X ⟶ X'),
          Nonempty (PostnikovSystemMorphism P P' φ) := sorry

-- Proof sketch: for each `n > 2`, one uses a standard counterexample showing that some
-- length-`n` complex in a triangulated category does not admit any Postnikov system.
/-- Lemma 13.41.3 (8): for every `n > 2`, it is not true in general that every length-`n` complex
in a triangulated category admits a Postnikov system. -/
theorem length_gt_two_postnikovSystem_existence_not_universal (n : ℕ) (hn : 2 < n) :
    ¬ ∀ {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D] (X : ComposableArrows D n)
        (hX : X.IsComplex), Nonempty (PostnikovSystem X) := sorry

end CategoryTheory
