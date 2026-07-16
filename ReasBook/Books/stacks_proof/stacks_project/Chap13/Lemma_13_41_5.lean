import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_41_1
import stacks_proof.stacks_project.Chap13.Lemma_13_4_8
import stacks_proof.stacks_project.Chap13.Lemma_13_41_3
import stacks_proof.stacks_project.Chap13.Lemma_13_41_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Helper for Lemma 13.41.5: a morphism of Postnikov systems is determined by its component maps
on the auxiliary objects. -/
theorem postnikovSystemMorphism_ext_of_yMap_eq
    {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X} {P' : PostnikovSystem X'}
    {φ : X ⟶ X'} {ψ ψ' : PostnikovSystemMorphism P P' φ}
    (h : ∀ i, ψ.yMap i = ψ'.yMap i) :
    ψ = ψ' := by
  -- Proof comment: after unpacking the two structures, the `yMap` field is the only free data;
  -- the square fields are propositions determined by proof irrelevance.
  cases ψ
  cases ψ'
  simp at h
  have hy : yMap✝¹ = yMap✝ := funext h
  subst hy
  rfl

namespace PostnikovSystemMorphism

/-- Helper for Lemma 13.41.5: the morphism of finite rows induced on the recursive tails is built
from the successor components of the original ladder morphism. -/
def delta0_map
    {n : ℕ} {X X' : ComposableArrows D (n + 2)} (φ : X ⟶ X') :
    X.δ₀ ⟶ X'.δ₀ := sorry

/-- Helper for Lemma 13.41.5: a morphism of Postnikov systems restricts to a morphism on the
recursive tails. -/
def tail
    {n : ℕ} {X X' : ComposableArrows D (n + 2)} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} (ψ : PostnikovSystemMorphism P P' φ) :
    PostnikovSystemMorphism P.tail P'.tail (delta0_map φ) := sorry

end PostnikovSystemMorphism

/-- Helper for Lemma 13.41.5: the cross-vanishing hypothesis restricts to the recursive tails. -/
theorem cross_vanishing_tail
    {n : ℕ} {X X' : ComposableArrows D (n + 2)}
    (h :
      ∀ ⦃a b : Fin (n + 3)⦄, b < a →
        Subsingleton (ShiftedHom (X.obj a) (X'.obj b) ((a.1 : ℤ) - b.1 - 1)) ∧
          Subsingleton (ShiftedHom (X.obj b) (X'.obj a) ((b.1 : ℤ) - a.1))) :
    ∀ ⦃a b : Fin (n + 2)⦄, b < a →
      Subsingleton
          (ShiftedHom ((X.δ₀).obj a) ((X'.δ₀).obj b) ((a.1 : ℤ) - b.1 - 1)) ∧
        Subsingleton (ShiftedHom ((X.δ₀).obj b) ((X'.δ₀).obj a) ((b.1 : ℤ) - a.1)) := by
  intro a b hab
  -- Proof comment: after removing the leftmost object, the tail indices are exactly successors of
  -- the original indices, and the shift formula is unchanged.
  simpa using h (a := a.succ) (b := b.succ) (show b.succ < a.succ by simpa using hab)

/-- Helper for Lemma 13.41.5: subsingletonness of an ordinary Hom set transports backward across
an isomorphism on the source. -/
theorem subsingleton_hom_source_of_iso
    {A B C : D} (e : A ≅ B) (hsub : Subsingleton (B ⟶ C)) :
    Subsingleton (A ⟶ C) := by
  -- Proof comment: compare maps after precomposing with the forward isomorphism and cancel the
  -- inverse on the left.
  refine ⟨fun f g ↦ ?_⟩
  have hfg : e.hom ≫ f = e.hom ≫ g := hsub.elim (e.hom ≫ f) (e.hom ≫ g)
  simpa [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) hfg

/-- Helper for Lemma 13.41.5: subsingletonness of a shifted Hom group transports backward across
an isomorphism on the target. -/
theorem subsingleton_shiftedHom_target_of_iso
    {A B C : D} (e : B ≅ C) (m : ℤ)
    (hsub : Subsingleton (ShiftedHom A C m)) :
    Subsingleton (ShiftedHom A B m) := by
  -- Proof comment: postcompose with the shifted isomorphism and cancel it on the right.
  refine ⟨fun f g ↦ ?_⟩
  have hfg :
      f ≫ ((shiftFunctor D m).map e.hom) = g ≫ ((shiftFunctor D m).map e.hom) :=
    hsub.elim _ _
  exact (cancel_mono ((shiftFunctor D m).map e.hom)).1 <| by
    simpa [ShiftedHom, Category.assoc] using hfg

/-- Helper for Lemma 13.41.5: subsingletonness of a shifted Hom group transports backward across
an isomorphism on the source. -/
theorem subsingleton_shiftedHom_source_of_iso
    {A B C : D} (e : A ≅ B) (m : ℤ)
    (hsub : Subsingleton (ShiftedHom B C m)) :
    Subsingleton (ShiftedHom A C m) := by
  -- Proof comment: compare maps after precomposing with the forward isomorphism and cancel the
  -- inverse on the left.
  refine ⟨fun f g ↦ ?_⟩
  have hfg : e.hom ≫ f = e.hom ≫ g := hsub.elim (e.hom ≫ f) (e.hom ≫ g)
  simpa [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) hfg

/-- Helper for Lemma 13.41.5: subsingletonness of maps `A ⟦-1⟧ ⟶ B⟦m⟧` follows from
subsingletonness of maps `A ⟶ B⟦m + 1⟧` by shifting once and cancelling the canonical
comparison isomorphisms. -/
theorem subsingleton_hom_shift_neg_one_source_of_shifted
    {A B : D} (m : ℤ) (hsub : Subsingleton (ShiftedHom A B (m + 1))) :
    Subsingleton (A⟦(-1 : ℤ)⟧ ⟶ B⟦m⟧) := by
  -- TODO: transport the degree-`m + 1` subsingleton statement through the canonical shift
  -- equivalences `A ≅ A⟦-1⟧⟦1⟧` and `(B⟦m⟧)⟦1⟧ ≅ B⟦m + 1⟧`, then cancel the shifted
  -- isomorphisms.
  sorry

namespace PostnikovSystem

/-- Helper for Lemma 13.41.5: the successor index is the previous shift degree plus one. -/
private theorem succ_val_eq_add_one
    {n : ℕ} (i : Fin n) :
    ((i.1 : ℤ) + 1) = i.succ.1 := by
  -- Proof comment: this is the arithmetic normalization needed by the shift-add comparison in
  -- `to_zero_shifted`.
  norm_num [Fin.succ]

/-- Helper for Lemma 13.41.5: the canonical composite from the `i`th auxiliary object to the
extreme auxiliary object `P 0`, shifted by the stage number `i`. -/
def to_zero_shifted
    {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) :
    ∀ i : Fin (n + 1), P i ⟶ (P 0)⟦(i.1 : ℤ)⟧ := sorry

/-- Helper for Lemma 13.41.5: at the extreme stage, `to_zero_shifted` is the identity. -/
@[simp] theorem to_zero_shifted_zero
    {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.to_zero_shifted 0 = 𝟙 (P 0) := by
  -- TODO: unfold `PostnikovSystem.to_zero_shifted` at the zero stage and normalize the `0`-shift.
  sorry

/-- Helper for Lemma 13.41.5: the successor-stage `to_zero_shifted` map is the connecting map
followed by the recursively constructed composite to the extreme auxiliary object. -/
@[simp] theorem to_zero_shifted_succ
    {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) (i : Fin (n + 1)) :
    P.to_zero_shifted i.succ =
      P.connecting i ≫ (P.to_zero_shifted i.castSucc)⟦(1 : ℤ)⟧' ≫
        ((shiftFunctorAdd' D (i.1 : ℤ) (1 : ℤ) i.succ.1
          (succ_val_eq_add_one i)).app (P 0)).symm.hom := by
  -- TODO: unfold `PostnikovSystem.to_zero_shifted` at a successor index and simplify the
  -- successor arithmetic in the shift-add comparison.
  sorry

end PostnikovSystem

namespace PostnikovSystemMorphism

/-- Helper for Lemma 13.41.5: the canonical composites from a stage to the extreme auxiliary
object commute with any morphism of Postnikov systems. -/
theorem comm_to_zero_shifted
    {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X} {P' : PostnikovSystem X'}
    {φ : X ⟶ X'} (ψ : PostnikovSystemMorphism P P' φ) :
    ∀ i : Fin (n + 1),
      P.to_zero_shifted i ≫ (ψ.yMap 0)⟦(i.1 : ℤ)⟧' = ψ.yMap i ≫ P'.to_zero_shifted i := by
  -- TODO: prove this by induction on `i`, using `PostnikovSystem.to_zero_shifted_succ`,
  -- the naturality of `shiftFunctorAdd'`, and the stagewise compatibility
  -- `ψ.comm_connecting_w`.
  sorry

end PostnikovSystemMorphism

/-- Helper for Lemma 13.41.5: equality of the tail morphisms gives equality of all successor
components of the original Postnikov-system morphisms. -/
theorem postnikovSystemMorphism_yMap_succ_eq_of_tail_eq
    {n : ℕ} {X X' : ComposableArrows D (n + 2)} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ ψ' : PostnikovSystemMorphism P P' φ}
    (htail : PostnikovSystemMorphism.tail ψ = PostnikovSystemMorphism.tail ψ') :
    ∀ i : Fin (n + 2), ψ.yMap i.succ = ψ'.yMap i.succ := by
  -- Proof comment: the tail morphism stores exactly the successor-stage components.
  intro i
  simpa [PostnikovSystemMorphism.tail] using congrArg
    (fun θ : PostnikovSystemMorphism P.tail P'.tail (PostnikovSystemMorphism.delta0_map φ) ↦
      θ.yMap i)
    htail

/-- Helper for Lemma 13.41.5: one inverse-rotated stage step propagates fixed-target vanishing
from the row object and the later auxiliary object to the current auxiliary object. -/
theorem postnikov_fixed_target_stage_step
    {m : ℕ} {X : ComposableArrows D m} (P : PostnikovSystem X) (W : D) (i : Fin m)
    (hX : Subsingleton (ShiftedHom (X.obj i.castSucc) W (i.castSucc.1 : ℤ)))
    (hSucc : Subsingleton (ShiftedHom (P i.succ) W (i.succ.1 : ℤ))) :
    Subsingleton (ShiftedHom (P i.castSucc) W (i.castSucc.1 : ℤ)) := by
  -- TODO: inverse-rotate the stage triangle and use exactness plus the two subsingleton
  -- hypotheses to kill maps out of `P i.castSucc`.
  sorry

/-- Helper for Lemma 13.41.5: fixed-target vanishing for the row objects propagates by reverse
induction to all positive-stage auxiliary objects. -/
theorem postnikov_fixed_target_stage_subsingleton
    {m : ℕ} {X : ComposableArrows D m} (P : PostnikovSystem X) (W : D)
    (hW : ∀ ⦃b : Fin (m + 1)⦄, 0 < b.1 →
      Subsingleton (ShiftedHom (X.obj b) W (b.1 : ℤ))) :
    ∀ ⦃b : Fin (m + 1)⦄, 0 < b.1 →
      Subsingleton (ShiftedHom (P b) W (b.1 : ℤ)) := by
  -- TODO: run reverse induction on `b`, using `postnikov_fixed_target_stage_step` and the last
  -- stage isomorphism `P.toX (Fin.last m)`.
  sorry

/-- Helper for Lemma 13.41.5: one exactness step propagates fixed-source vanishing from the row
object and the later auxiliary object to the current auxiliary object. -/
theorem postnikov_fixed_source_stage_step
    {m : ℕ} {X : ComposableArrows D m} (P : PostnikovSystem X) (W : D) (i : Fin m)
    (hX :
      Subsingleton (ShiftedHom W (X.obj i.castSucc) (-((i.castSucc.1 : ℤ)))))
    (hSucc :
      Subsingleton (ShiftedHom W (P i.succ) (-((i.succ.1 : ℤ))))) :
    Subsingleton (ShiftedHom W (P i.castSucc) (-((i.castSucc.1 : ℤ)))) := by
  -- TODO: factor maps through the connecting morphism using
  -- `PostnikovSystem.stage_shiftedHom_exact₁_factor`, then kill the factor with `hSucc`.
  sorry

/-- Helper for Lemma 13.41.5: fixed-source vanishing for the row objects propagates by reverse
induction to all positive-stage auxiliary objects. -/
theorem postnikov_fixed_source_stage_subsingleton
    {m : ℕ} {X : ComposableArrows D m} (P : PostnikovSystem X) (W : D)
    (hW : ∀ ⦃b : Fin (m + 1)⦄, 0 < b.1 →
      Subsingleton (ShiftedHom W (X.obj b) (-((b.1 : ℤ))))) :
    ∀ ⦃b : Fin (m + 1)⦄, 0 < b.1 →
      Subsingleton (ShiftedHom W (P b) (-((b.1 : ℤ)))) := by
  -- TODO: run reverse induction on `b`, using `postnikov_fixed_source_stage_step` and the last
  -- stage isomorphism `P.toX (Fin.last m)`.
  sorry

/-- Helper for Lemma 13.41.5: the cross-vanishing hypothesis propagates to the two head-step
vanishing conditions needed for the inverse-rotated head-triangle comparison. -/
theorem head_step_hom_vanishing_of_cross_vanishing
    {n : ℕ} {X X' : ComposableArrows D (n + 2)} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (hcross :
      ∀ ⦃a b : Fin (n + 3)⦄, b < a →
        Subsingleton (ShiftedHom (X.obj a) (X'.obj b) ((a.1 : ℤ) - b.1 - 1)) ∧
          Subsingleton (ShiftedHom (X.obj b) (X'.obj a) ((b.1 : ℤ) - a.1))) :
    Subsingleton (P 1 ⟶ X'.obj 0) ∧ Subsingleton (ShiftedHom (X.obj 0) (P' 1) (-1)) := by
  -- TODO: combine the fixed-target and fixed-source reverse-induction families with the `a = 0`
  -- specialization of `hcross` to obtain the two head-step vanishing conditions.
  sorry

/-- Helper for Lemma 13.41.5: the extreme-target vanishing hypothesis restricts to the target
tail hypothesis needed for the recursive call in textbook case `(1)`. -/
theorem postnikov_target_auxiliary_vanishing_of_extreme_target
    {n : ℕ} {X X' : ComposableArrows D (n + 1)} (P' : PostnikovSystem X')
    (htarget :
      ∀ a : Fin (n + 1), Subsingleton (ShiftedHom (X.obj a.castSucc) (P' 0) (a.1 : ℤ))) :
    ∀ a : Fin n,
      Subsingleton (ShiftedHom ((X.δ₀).obj a.castSucc) (P'.tail 0) (a.1 : ℤ)) := by
  intro a
  -- TODO: this is the mixed target-side bridge from the source proof. One exactness step on the
  -- head triangle `P' 0 ⟶ X'.obj 0 ⟶ P' 1 ⟶ P' 0[1]`, together with the degree `a.succ`
  -- hypothesis from `htarget`, should produce the exact recursive tail hypothesis.
  sorry

/-- Helper for Lemma 13.41.5: the extreme-source vanishing hypothesis restricts to the source
tail hypothesis needed for the recursive call in textbook case `(2)`. -/
theorem postnikov_source_tail_vanishing_of_extreme_source
    {n : ℕ} {X X' : ComposableArrows D (n + 1)} (P : PostnikovSystem X)
    (hsource :
      ∀ a : Fin (n + 1), Subsingleton (ShiftedHom (P 0) (X'.obj a.succ) (-((a.1 : ℤ) + 1)))) :
    ∀ a : Fin n,
      Subsingleton (ShiftedHom (P.tail 0) ((X'.δ₀).obj a.succ) (-((a.1 : ℤ) + 1))) := by
  intro a
  -- TODO: this is the mixed source-side bridge from the source proof. Use the head triangle of
  -- `P`, inverse-rotated exactness, and the source-extreme family `hsource` to move the fixed
  -- source from `P 0` down to `P.tail 0 = P 1`.
  sorry

/-- Helper for Lemma 13.41.5: case `(1)` of the textbook proof, where maps from each shifted row
object into the extreme target auxiliary object vanish. -/
theorem postnikovSystemMorphism_subsingleton_of_target_extreme_vanishing :
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X')
    (htarget : ∀ a : Fin n, Subsingleton (ShiftedHom (X.obj a.castSucc) (P' 0) (a.1 : ℤ))) :
    Subsingleton (PostnikovSystemMorphism P P' φ) := by
  -- TODO: recurse on the tails using `postnikov_target_auxiliary_vanishing_of_extreme_target`,
  -- then compare the inverse-rotated head triangles with Lemma 13.4.8, alternative `(2)`.
  sorry

/-- Helper for Lemma 13.41.5: case `(2)` of the textbook proof, where maps from the extreme
source auxiliary object to each shifted row object vanish. -/
theorem postnikovSystemMorphism_subsingleton_of_source_extreme_vanishing :
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X')
    (hsource :
      ∀ a : Fin n, Subsingleton (ShiftedHom (P 0) (X'.obj a.succ) (-((a.1 : ℤ) + 1)))) :
    Subsingleton (PostnikovSystemMorphism P P' φ) := by
  -- TODO: recurse on the tails using `postnikov_source_tail_vanishing_of_extreme_source`, then
  -- compare the inverse-rotated head triangles with Lemma 13.4.8, alternative `(1)`.
  sorry

/-- Helper for Lemma 13.41.5: case `(3)` of the textbook proof, where the paired cross-vanishing
hypothesis forces uniqueness by tail induction and one inverse-rotated head comparison. -/
theorem postnikovSystemMorphism_subsingleton_of_cross_vanishing :
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X')
    (hcross :
      ∀ ⦃a b : Fin (n + 1)⦄, b < a →
        Subsingleton (ShiftedHom (X.obj a) (X'.obj b) ((a.1 : ℤ) - b.1 - 1)) ∧
          Subsingleton (ShiftedHom (X.obj b) (X'.obj a) ((b.1 : ℤ) - a.1))) :
    Subsingleton (PostnikovSystemMorphism P P' φ) := by
  -- TODO: recurse on the tails using `cross_vanishing_tail`, obtain the head-step vanishing pair
  -- from `head_step_hom_vanishing_of_cross_vanishing`, and compare the inverse-rotated head
  -- triangles.
  sorry

/- Domain-style sampling for Lemma 13.41.5:
- primary domain: uniqueness of morphisms of Postnikov systems in a pretriangulated category under
  Hom-vanishing hypotheses;
- inspected owner declarations:
  `ShiftedHom`,
  `shifted_hom_vanishes_above_successor`,
  `PostnikovSystemMorphism`,
  `PostnikovSystemMorphism.triangleMorphism`,
  `triangleMorphism_eq_of_outer_eq_of_hom_vanishing`;
- best owner abstraction:
  `source-facing`: the three global textbook Hom-vanishing alternatives for Postnikov systems,
  `core/canonical`: the triangle category owner together with the stagewise uniqueness theorem
    `triangleMorphism_eq_of_outer_eq_of_hom_vanishing`, the shifted-Hom owner `ShiftedHom`, and
    the chapter-level familywise vanishing owner `shifted_hom_vanishes_above_successor`,
  `bridge/view`: the stagewise triangle morphisms `ψ.triangleMorphism i` and the canonical
    translation between the source-facing index formulas and those owner-level shifted-Hom
    vanishing predicates;
- primitive-vs-derived split:
  primitive data: the two Postnikov systems and the source-facing global vanishing alternative,
  derived API: the induced triangle-level uniqueness statements obtained by applying
    `triangleMorphism_eq_of_outer_eq_of_hom_vanishing` to the stage triangles. The third
  alternative remains source-facing here, rather than being repackaged, because this file does
    not yet have an upstream owner predicate for the paired cross-vanishing hypothesis. -/

-- Proof sketch: argue by induction on the length of the Postnikov systems. In the first two
-- vanishing cases, the successive maps to or from the extreme auxiliary object are forced stage by
-- stage by the distinguished triangles of the Postnikov systems. In the third case, compare two
-- candidate morphisms on the top distinguished triangles and apply
-- `triangleMorphism_eq_of_outer_eq_of_hom_vanishing`, using the stated cross-vanishing together
-- with the inductive description of the auxiliary objects exactly as in Lemmas 13.41.4 and 13.4.8.
/-- Lemma 13.41.5: if any one of the three textbook Hom-vanishing hypotheses holds for two
Postnikov systems over a morphism `φ : X ⟶ X'`, then there exists at most one morphism of
Postnikov systems lying over `φ`. -/
-- TODO for Lemma 13.41.5: split the proof into the three textbook vanishing alternatives. Cases
-- (1) and (2) need stagewise exactness against the extreme auxiliary object, while case (3) uses
-- `PostnikovSystemMorphism.tail`, `cross_vanishing_tail`, and a head-step comparison via
-- `triangleMorphism_eq_of_outer_eq_of_hom_vanishing` on the inverse-rotated head triangles.
theorem postnikovSystemMorphism_subsingleton_of_hom_vanishing
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X')
    (hvan :
      (∀ a : Fin n, Subsingleton (ShiftedHom (X.obj a.castSucc) (P' 0) (a.1 : ℤ))) ∨
        (∀ a : Fin n,
          Subsingleton (ShiftedHom (P 0) (X'.obj a.succ) (-((a.1 : ℤ) + 1)))) ∨
          (∀ ⦃a b : Fin (n + 1)⦄, b < a →
            Subsingleton (ShiftedHom (X.obj a) (X'.obj b) ((a.1 : ℤ) - b.1 - 1)) ∧
              Subsingleton (ShiftedHom (X.obj b) (X'.obj a) ((b.1 : ℤ) - a.1)))) :
    Subsingleton (PostnikovSystemMorphism P P' φ) := by
  -- Proof comment: split into the three textbook vanishing alternatives and handle each one with
  -- its own source-faithful recursive argument.
  rcases hvan with htarget | hvan
  · exact postnikovSystemMorphism_subsingleton_of_target_extreme_vanishing P P' φ htarget
  rcases hvan with hsource | hcross
  · exact postnikovSystemMorphism_subsingleton_of_source_extreme_vanishing P P' φ hsource
  · exact postnikovSystemMorphism_subsingleton_of_cross_vanishing P P' φ hcross

end

end CategoryTheory
