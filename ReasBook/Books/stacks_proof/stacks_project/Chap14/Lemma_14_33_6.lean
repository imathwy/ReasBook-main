import Mathlib
import stacks_proof.stacks_project.Chap14.Lemma_14_33_2
import stacks_proof.stacks_project.Chap14.Lemma_14_33_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject.Augmented
open scoped IteratedEndofunctor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IteratedEndofunctorResolutionWhiskerNotation

/- Source-facing notation for the two standard horizontal whiskerings of an endomorphism
`f : 𝟭 C ⟶ 𝟭 C` with a simplicial endofunctor object `X`. These are the simplicial maps whose
degreewise components are `f ⋆ 1_X` and `1_X ⋆ f`. -/
set_option quotPrecheck false in
scoped notation:81 f:81 " ⋆ₗ " X:82 =>
  Functor.whiskerLeft X ((whiskeringLeft C C C).map f)

set_option quotPrecheck false in
scoped notation:81 X:82 " ⋆ᵣ " f:81 =>
  Functor.whiskerLeft X ((whiskeringRight C C C).map f)

end IteratedEndofunctorResolutionWhiskerNotation

open scoped IteratedEndofunctorResolutionWhiskerNotation

/- Domain-style sampling for Lemma 14.33.6:
- primary domain: simplicial objects of endofunctors, augmented simplicial objects, whiskering of
  natural transformations by endofunctors, and the zigzag homotopy relation on simplicial maps;
- sampled same-kind declarations:
  `Functor.whiskeringLeft`,
  `Functor.whiskeringRight`,
  `Functor.id_hcomp`,
  `Functor.hcomp_id`,
  `prePostcomposeAugmented`,
  `SimplicialObject.Augmented.whiskeringObj`,
  `prePostcomposeAugmentedMap_homotopic`,
  `SimplicialObject.Augmented`;
- best owner abstraction: the primitive owner is the canonical whiskering action of the functors
  `whiskeringLeft C C C` and `whiskeringRight C C C` on the endofunorphism `f : 𝟭 C ⟶ 𝟭 C`; the
  source-facing simplicial maps are obtained by whiskering a simplicial object `X` by those owner
  maps, and for Lemma 14.33.6 the relevant `X` is the canonical iterated endofunctor resolution
  from `Lemma_14_33_2`, while the final homotopy statement is a specialization of the chapter-level
  theorem `prePostcomposeAugmentedMap_homotopic`;
- primitive data: the simplicial identities `hσδ₀`, `hσδ₁`, `hσσ` defining the canonical
  resolution, together with a natural endomorphism `f : 𝟭 C ⟶ 𝟭 C`;
- derived API: the source-facing simplicial endomorphisms
  `f ⋆ₗ X` and `X ⋆ᵣ f`, corresponding degreewise to `f ⋆ 1_X` and `1_X ⋆ f`, the canonical
  augmentation-compatibility squares for the iterated resolution, and the resulting homotopy
  statement.

Source/core/bridge triage:
- `source-facing`: the endomorphisms `f ⋆ 1_X` and `1_X ⋆ f` of the canonical simplicial
  endofunctor resolution arising from the iterated endofunctor construction;
- `core/canonical`: the functorial owner maps `(whiskeringLeft C C C).map f`,
  `(whiskeringRight C C C).map f`, whiskering by `X`, and the augmented pre/postcomposition owner
  API from `Lemma_14_33_5`;
- `bridge/view`: the notation-level source-facing whiskered maps `f ⋆ₗ X` and `X ⋆ᵣ f`, together
  with their augmentation-compatibility squares, which supply the augmented morphisms whose
  induced simplicial maps are obtained directly by `whiskeringObj.map ... |>.left`.
-/

/-- Helper for Lemma 14.33.6: whiskering a simplicial object of endofunctors on the left by the
identity functor does not change its face maps. -/
@[simp] private theorem whiskeringLeft_id_delta
    (X : SimplicialObject (C ⥤ C)) {n : ℕ} (i : Fin (n + 2)) :
    SimplicialObject.δ (X ⋙ (whiskeringLeft C C C).obj (𝟭 C)) i = SimplicialObject.δ X i := by
  -- Evaluate the whiskered natural transformations componentwise; `𝟭 C` acts trivially on every
  -- endofunctor morphism.
  ext Z
  simp [SimplicialObject.δ]

/-- Helper for Lemma 14.33.6: whiskering a simplicial object of endofunctors on the left by the
identity functor does not change its degeneracy maps. -/
@[simp] private theorem whiskeringLeft_id_sigma
    (X : SimplicialObject (C ⥤ C)) {n : ℕ} (i : Fin (n + 1)) :
    SimplicialObject.σ (X ⋙ (whiskeringLeft C C C).obj (𝟭 C)) i = SimplicialObject.σ X i := by
  -- The same componentwise calculation shows that degeneracy maps are unchanged as well.
  ext Z
  simp [SimplicialObject.σ]

private theorem prePostcomposeAugmented_id_id_hom
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    :
    (prePostcomposeAugmented (𝟭 C) (𝟭 C) ε).hom = ε := by
  ext n
  simp [prePostcomposeAugmented]

private def leftStarAugmentedHom
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    prePostcomposeAugmented (𝟭 C) (𝟭 C) ε ⟶
      prePostcomposeAugmented (𝟭 C) (𝟭 C) ε :=
  ((SimplicialObject.Augmented.whiskering (C ⥤ C) (C ⥤ C)).map
    ((whiskeringLeft C C C).map f)).app
      { left := X, right := 𝟭 C, hom := ε }

@[simp] private theorem leftStarAugmentedHom_left
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (leftStarAugmentedHom X ε f).left = f ⋆ₗ X := by
  simp [leftStarAugmentedHom]

@[simp] private theorem leftStarAugmentedHom_right
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (leftStarAugmentedHom X ε f).right = f := by
  ext Z
  simp [leftStarAugmentedHom]

private def rightStarAugmentedHom
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    prePostcomposeAugmented (𝟭 C) (𝟭 C) ε ⟶
      prePostcomposeAugmented (𝟭 C) (𝟭 C) ε :=
  ((SimplicialObject.Augmented.whiskering (C ⥤ C) (C ⥤ C)).map
    ((whiskeringRight C C C).map f)).app
      { left := X, right := 𝟭 C, hom := ε }

@[simp] private theorem rightStarAugmentedHom_left
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (rightStarAugmentedHom X ε f).left = X ⋆ᵣ f := by
  simp [rightStarAugmentedHom]

@[simp] private theorem rightStarAugmentedHom_right
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (rightStarAugmentedHom X ε f).right = f := by
  ext Z
  simp [rightStarAugmentedHom]

section IteratedResolution

variable {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
local notation "X⦅" n:max "⦆" => Y⦅n⦆
local notation "d^⦅" n ", " j "⦆" => d[Y, d]⦅n, j⦆
local notation "s^⦅" n ", " j "⦆" => s[Y, s]⦅n, j⦆

/-- Helper for Lemma 14.33.6: split `Y⦅n + 1⦆` into the left block `Y⦅n - i⦆` and the right
block `Y⦅i⦆` exactly as in the source proof. -/
private noncomputable def iteratedEndofunctorSplitIso (n : ℕ) (i : Fin (n + 1)) :
    X⦅(n + 1)⦆ ≅ X⦅(n - i.1)⦆ ⋙ X⦅i.1⦆ :=
  eqToIso (by rw [Nat.sub_add_cancel i.is_le]) ≪≫ iteratedEndofunctorCompIso Y (n - i.1) i.1

/-- Helper for Lemma 14.33.6: a nonterminal iterated face map is the smaller face map whiskered
on the right by `Y`. -/
@[simp] private theorem iterated_faceMap_castSucc
    (n : ℕ) (j : Fin (n + 2)) :
    d^⦅n + 1, j.castSucc⦆ = Functor.whiskerRight d^⦅n, j⦆ Y := by
  -- This is the recursive nonterminal branch of `iteratedFaceMap`.
  simp [iteratedFaceMap]

/-- Helper for Lemma 14.33.6: the terminal iterated face map is the right-unitor branch of the
recursive definition. -/
@[simp] private theorem iterated_faceMap_last
    (n : ℕ) :
    d^⦅n + 1, Fin.last (n + 2)⦆ =
      Functor.whiskerLeft X⦅(n + 1)⦆ d ≫ (Functor.rightUnitor X⦅(n + 1)⦆).hom := by
  -- This is the recursive terminal branch of `iteratedFaceMap`.
  simp [iteratedFaceMap]
  rfl

/-- Helper for Lemma 14.33.6: the degree-`0` first face map is the branch that inserts `d`
in the left factor of `Y ⋙ Y`. -/
private theorem iterated_faceMap_zero_first :
    d^⦅0, (0 : Fin 2)⦆ = Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom := by
  -- Identify the nonterminal branch of `iteratedFaceMap` in degree `0`.
  have h :
      Fin.lastCases
          (motive := fun _ : Fin 2 => X⦅1⦆ ⟶ X⦅0⦆)
          (Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom)
          (fun _ : Fin 1 => Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom)
          (Fin.castSucc 0)
        = Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom := by
    simpa using
      (Fin.lastCases_castSucc
        (motive := fun _ : Fin 2 => X⦅1⦆ ⟶ X⦅0⦆)
        (last := Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom)
        (cast := fun _ : Fin 1 => Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom)
        0)
  simpa [iteratedFaceMap] using h

/-- Helper for Lemma 14.33.6: the degree-`0` last face map is the branch that inserts `d`
in the right factor of `Y ⋙ Y`. -/
private theorem iterated_faceMap_zero_last :
    d^⦅0, (1 : Fin 2)⦆ = Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom := by
  -- Identify the terminal branch of `iteratedFaceMap` in degree `0`.
  have h :
      Fin.lastCases
          (motive := fun _ : Fin 2 => X⦅1⦆ ⟶ X⦅0⦆)
          (Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom)
          (fun _ : Fin 1 => Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom)
          (Fin.last 1)
        = Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom := by
    simpa using
      (Fin.lastCases_last
        (motive := fun _ : Fin 2 => X⦅1⦆ ⟶ X⦅0⦆)
        (last := Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom)
        (cast := fun _ : Fin 1 => Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom))
  simpa [iteratedFaceMap] using h

/-- Helper for Lemma 14.33.6: a nonterminal iterated degeneracy map is the smaller degeneracy map
whiskered on the right by `Y`. -/
@[simp] private theorem iterated_degeneracyMap_castSucc
    (n : ℕ) (j : Fin (n + 1)) :
    s^⦅n + 1, j.castSucc⦆ = Functor.whiskerRight s^⦅n, j⦆ Y := by
  -- This is the recursive nonterminal branch of `iteratedDegeneracyMap`.
  simp [iteratedDegeneracyMap]

/-- Helper for Lemma 14.33.6: the terminal iterated degeneracy map is the associator branch of
the recursive definition. -/
@[simp] private theorem iterated_degeneracyMap_last
    (n : ℕ) :
    s^⦅n + 1, Fin.last (n + 1)⦆ =
      Functor.whiskerLeft X⦅n⦆ s ≫ (Functor.associator X⦅n⦆ Y Y).inv := by
  -- This is the recursive terminal branch of `iteratedDegeneracyMap`.
  simp [iteratedDegeneracyMap]
  rfl

/-- Helper for Lemma 14.33.6: the terminal face map component evaluates `d` on the current
iterate `X⦅n⦆.obj Z`. -/
private theorem iterated_faceMap_last_app
    (n : ℕ) (Z : C) :
    d^⦅n, Fin.last (n + 1)⦆.app Z = d.app (X⦅n⦆.obj Z) := by
  -- Split off the degree-`0` base case; afterwards the terminal recursive branch is already in
  -- the required pointwise form.
  cases n with
  | zero =>
      rw [show (Fin.last 1 : Fin 2) = (1 : Fin 2) by rfl]
      rw [iterated_faceMap_zero_last]
      simpa [iteratedEndofunctor, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.rightUnitor_hom_app]
  | succ n =>
      rw [iterated_faceMap_last]
      simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]

/-- Helper for Lemma 14.33.6: the terminal degeneracy map component evaluates `s` on the current
iterate `X⦅n⦆.obj Z`. -/
private theorem iterated_degeneracyMap_last_app
    (n : ℕ) (Z : C) :
    s^⦅n + 1, Fin.last (n + 1)⦆.app Z = s.app (X⦅n⦆.obj Z) := by
  -- The associator branch becomes the functorial image of `s.app` because the associator is the
  -- identity on objects.
  rw [iterated_degeneracyMap_last]
  simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app]

/-- Helper for Lemma 14.33.6: the terminal adjacent `σδ` composites are exactly left-whiskered
copies of the degree-`0` composites `s ≫ d₀` and `s ≫ d₁`. -/
private theorem terminal_adjacent_face_map_normalization
    (n : ℕ) :
    s^⦅n + 1, Fin.last (n + 1)⦆ ≫ d^⦅n + 1, (Fin.last (n + 1)).castSucc⦆ =
      Functor.whiskerLeft X⦅n⦆ (s^⦅0, 0⦆ ≫ d^⦅0, (0 : Fin 2)⦆) ∧
      s^⦅n + 1, Fin.last (n + 1)⦆ ≫ d^⦅n + 1, (Fin.last (n + 1)).succ⦆ =
        Functor.whiskerLeft X⦅n⦆ (s^⦅0, 0⦆ ≫ d^⦅0, (1 : Fin 2)⦆) := by
  constructor
  · -- Evaluate the terminal/castSucc composite pointwise; both sides are the same left-whiskered
    -- copy of `s ≫ d^⦅0, 0⦆`.
    rw [iterated_degeneracyMap_last, iterated_faceMap_castSucc]
    ext Z
    simp [NatTrans.comp_app, iteratedDegeneracyMap, iterated_faceMap_zero_first,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app]
    rw [iterated_faceMap_last_app]
    rfl
  · -- The terminal/terminal composite likewise matches the left-whiskered copy of
    -- `s ≫ d^⦅0, 1⦆`.
    rw [iterated_degeneracyMap_last, Fin.succ_last, iterated_faceMap_last]
    ext Z
    simp [NatTrans.comp_app, iteratedDegeneracyMap, iterated_faceMap_zero_last,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app]
    simp [iteratedEndofunctor]

/-- Helper for Lemma 14.33.6: right-whiskering preserves the adjacent `σδ` identities from the
previous degree. -/
private theorem iterated_adjacent_face_map_comp_degeneracy_map_castSucc
    {n : ℕ} {j : Fin (n + 1)}
    (hcast : s^⦅n, j⦆ ≫ d^⦅n, j.castSucc⦆ = 𝟙 X⦅n⦆)
    (hsucc : s^⦅n, j⦆ ≫ d^⦅n, j.succ⦆ = 𝟙 X⦅n⦆) :
    s^⦅n + 1, j.castSucc⦆ ≫ d^⦅n + 1, j.castSucc.castSucc⦆ = 𝟙 X⦅(n + 1)⦆ ∧
      s^⦅n + 1, j.castSucc⦆ ≫ d^⦅n + 1, j.succ.castSucc⦆ = 𝟙 X⦅(n + 1)⦆ := by
  constructor
  · -- All three maps are right-whiskered copies of the degree-`n` composite, so pointwise
    -- functoriality of `Y.map` transports the smaller identity.
    rw [iterated_degeneracyMap_castSucc, iterated_faceMap_castSucc]
    ext Z
    have hcast_app := congrArg (fun k ↦ k.app Z) hcast
    simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp] using
      congrArg (fun k ↦ Y.map k) hcast_app
  · -- The same right-whiskering argument applies to the `j.succ` branch.
    rw [iterated_degeneracyMap_castSucc, iterated_faceMap_castSucc]
    ext Z
    have hsucc_app := congrArg (fun k ↦ k.app Z) hsucc
    simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp,
      Fin.castSucc_succ] using
      congrArg (fun k ↦ Y.map k) hsucc_app

/-- Helper for Lemma 14.33.6: the adjacent face-degeneracy identities are exactly the two
assumptions involving `d` and `s`, propagated by whiskering. -/
private theorem iterated_adjacent_face_map_comp_degeneracy_map
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (n : ℕ) (j : Fin (n + 1)) :
    s^⦅n, j⦆ ≫ d^⦅n, j.castSucc⦆ = 𝟙 X⦅n⦆ ∧
      s^⦅n, j⦆ ≫ d^⦅n, j.succ⦆ = 𝟙 X⦅n⦆ := by
  induction n with
  | zero =>
      -- In degree `0`, the two required identities are exactly the hypotheses.
      fin_cases j
      exact ⟨hσδ₀, hσδ₁⟩
  | succ n ih =>
      -- Split off the terminal branch; the remaining branch is the right-whiskered induction
      -- hypothesis.
      refine Fin.lastCases ?_ ?_ j
      ·
        rcases terminal_adjacent_face_map_normalization (Y := Y) (d := d) (s := s) n with
          ⟨hcast, hsucc⟩
        have hwhisker_id : Functor.whiskerLeft (X⦅n⦆) (𝟙 (X⦅0⦆)) = 𝟙 (X⦅(n + 1)⦆) := by
          simp [iteratedEndofunctor]
        constructor
        · -- The first adjacent branch is the left-whiskered copy of `hσδ₀`.
          rw [hcast, hσδ₀]
          simpa [iteratedEndofunctor] using hwhisker_id
        · -- The second adjacent branch is the left-whiskered copy of `hσδ₁`.
          rw [hsucc, hσδ₁]
          simpa [iteratedEndofunctor] using hwhisker_id
      · intro j
        exact iterated_adjacent_face_map_comp_degeneracy_map_castSucc (Y := Y) (d := d)
          (s := s) (hcast := (ih j).1) (hsucc := (ih j).2)

/-- Helper for Lemma 14.33.6: splitting off a zero right block gives the identity map. -/
@[simp] private theorem iteratedEndofunctorSplitIso_zero_hom
    (n : ℕ) :
    (iteratedEndofunctorSplitIso (Y := Y) n (0 : Fin (n + 1))).hom = 𝟙 X⦅(n + 1)⦆ := by
  -- The zero split is the base case of `iteratedEndofunctorCompIso`.
  simp [iteratedEndofunctorSplitIso, iteratedEndofunctorCompIso]

/-- Helper for Lemma 14.33.6: splitting off a zero right block gives the identity inverse map. -/
@[simp] private theorem iteratedEndofunctorSplitIso_zero_inv
    (n : ℕ) :
    (iteratedEndofunctorSplitIso (Y := Y) n (0 : Fin (n + 1))).inv = 𝟙 X⦅(n + 1)⦆ := by
  -- The zero split is the base case of `iteratedEndofunctorCompIso`.
  simp [iteratedEndofunctorSplitIso, iteratedEndofunctorCompIso]

/-- Helper for Lemma 14.33.6: increasing the split index by one lowers the left block degree by
one. -/
@[simp] private theorem split_left_degree_succ
    (n : ℕ) (i : Fin (n + 1)) :
    n + 1 - i.succ.1 = n - i.1 := by
  -- This is the arithmetic identity behind every recursive split-transport step.
  exact Nat.succ_sub_succ_eq_sub n i.1

/-- Helper for Lemma 14.33.6: casting a split index with `castSucc` does not change the left
block degree. -/
@[simp] private theorem split_left_degree_castSucc
    (n : ℕ) (i : Fin (n + 1)) :
    n - i.castSucc.1 = n - i.1 := by
  -- `castSucc` preserves the underlying natural number.
  rfl

/-- Helper for Lemma 14.33.6: the zero split leaves the entire degree in the left block. -/
@[simp] private theorem split_left_degree_zero
    (n : ℕ) :
    n - (0 : Fin (n + 1)).1 = n := by
  -- The zero split removes no terms from the left block.
  simp

/-- Helper for Lemma 14.33.6: the last split leaves no left block. -/
@[simp] private theorem split_left_degree_last
    (n : ℕ) :
    n - (Fin.last n).1 = 0 := by
  -- Splitting off the maximal right block exhausts the left block.
  simp

/-- Helper for Lemma 14.33.6: the recursive successor split has the expected source object after
viewing the final factor as a right whisker by `Y`. -/
private theorem split_succ_source_obj_eq
    (n : ℕ) (i : Fin (n + 1)) :
    X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y := by
  -- Normalize the source as one more iterate on the right block and solve the remaining index
  -- equality arithmetically.
  have h : n = n - i.1 + i.1 := by
    simpa using (Nat.sub_add_cancel i.is_le).symm
  simpa [iteratedEndofunctor, split_left_degree_succ] using
    congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h

/-- Helper for Lemma 14.33.6: the recursive successor split has the expected target object after
reassociating the right block with one extra copy of `Y`. -/
@[simp] private theorem split_succ_target_obj_eq
    (n : ℕ) (i : Fin (n + 1)) :
    X⦅(n + 1 - i.succ.1)⦆ ⋙ (X⦅i.1⦆ ⋙ Y) = X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆ := by
  -- This is definitionally the recursive clause `X⦅i + 1⦆ = X⦅i⦆ ⋙ Y`.
  rfl

/-- Helper for Lemma 14.33.6: the target-side successor split transport is the identity
natural transformation. -/
@[simp] private theorem split_succ_target_obj_eqToHom
    (n : ℕ) (i : Fin (n + 1)) :
    eqToHom (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)) = 𝟙 _ := by
  -- After substituting the definitional target equality, the cast is `eqToHom rfl`.
  ext Z
  cases split_succ_target_obj_eq (Y := Y) (n := n) (i := i)
  rfl

/-- Helper for Lemma 14.33.6: the inverse target-side successor split transport is the identity
natural transformation. -/
@[simp] private theorem split_succ_target_obj_eq_symm_eqToHom
    (n : ℕ) (i : Fin (n + 1)) :
    eqToHom (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)).symm = 𝟙 _ := by
  -- The symmetric cast is also `eqToHom rfl` after substituting the equality proof.
  ext Z
  cases split_succ_target_obj_eq (Y := Y) (n := n) (i := i)
  rfl

/-- Helper for Lemma 14.33.6: the objectwise successor target transport is the identity map. -/
@[simp] private theorem split_succ_target_obj_eq_obj_eqToHom
    (n : ℕ) (i : Fin (n + 1)) (Z : C) :
    eqToHom
        (congrArg (fun F : C ⥤ C ↦ F.obj Z)
          (split_succ_target_obj_eq (Y := Y) (n := n) (i := i))) =
      𝟙 _ := by
  -- After evaluating the target equality at `Z`, the cast is again reflexive.
  cases split_succ_target_obj_eq (Y := Y) (n := n) (i := i)
  rfl

/-- Helper for Lemma 14.33.6: the inverse objectwise successor target transport is the identity
map. -/
@[simp] private theorem split_succ_target_obj_eq_symm_obj_eqToHom
    (n : ℕ) (i : Fin (n + 1)) (Z : C) :
    eqToHom
        (congrArg (fun F : C ⥤ C ↦ F.obj Z)
          (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)).symm) =
      𝟙 _ := by
  -- The symmetric componentwise cast collapses in the same way.
  cases split_succ_target_obj_eq (Y := Y) (n := n) (i := i)
  rfl

/-- Helper for Lemma 14.33.6: any objectwise successor target cast coming from the recursive split
is the identity map. -/
@[simp] private theorem split_succ_target_obj_any_eqToHom
    (n : ℕ) (i : Fin (n + 1)) (Z : C)
    (p :
      (X⦅(n + 1 - i.succ.1)⦆ ⋙ (X⦅i.1⦆ ⋙ Y)).obj Z =
        (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z) :
    eqToHom p = 𝟙 _ := by
  -- All proofs of this definitional component equality induce the same identity map.
  have hp :
      p =
        ((by
          rfl :
            (X⦅(n + 1 - i.succ.1)⦆ ⋙ (X⦅i.1⦆ ⋙ Y)).obj Z =
              (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z)) := Subsingleton.elim _ _
  cases hp
  rfl

/-- Helper for Lemma 14.33.6: after applying the final `Y`, any successor target component cast
from the recursive split is still the identity map. -/
@[simp] private theorem split_succ_target_obj_after_Y_any_eqToHom
    (n : ℕ) (i : Fin (n + 1)) (Z : C)
    (p :
      Y.obj (X⦅i.1⦆.obj (X⦅(n + 1 - i.succ.1)⦆.obj Z)) =
        (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z) :
    eqToHom p = 𝟙 _ := by
  -- The recursive target equality remains definitional after evaluating the final `Y`.
  have hp :
      p =
        ((by
          rfl :
            Y.obj (X⦅i.1⦆.obj (X⦅(n + 1 - i.succ.1)⦆.obj Z)) =
              (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z)) := Subsingleton.elim _ _
  cases hp
  rfl

/-- Helper for Lemma 14.33.6: the symmetric componentwise cast from the recursive successor split
is also the identity map. -/
@[simp] private theorem split_succ_target_obj_after_Y_any_symm_eqToHom
    (n : ℕ) (i : Fin (n + 1)) (Z : C)
    (p :
      (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z =
        Y.obj (X⦅i.1⦆.obj (X⦅(n + 1 - i.succ.1)⦆.obj Z))) :
    eqToHom p = 𝟙 _ := by
  -- The inverse associator component is the same definitional equality in the opposite direction.
  have hp :
      p =
        ((by
          rfl :
            (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z =
              Y.obj (X⦅i.1⦆.obj (X⦅(n + 1 - i.succ.1)⦆.obj Z)))) := Subsingleton.elim _ _
  cases hp
  rfl

/-- Helper for Lemma 14.33.6: the leading source-side successor cast is the explicit block-split
transport. -/
@[simp] private theorem split_succ_source_obj_eqToHom
    (n : ℕ) (i : Fin (n + 1)) :
    eqToHom
        ((by
          have h : n = n - i.1 + i.1 := by
            simpa using (Nat.sub_add_cancel i.is_le).symm
          simpa [iteratedEndofunctor, split_left_degree_succ] using
            congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h) :
          X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y) =
      eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)) := by
  -- Both source casts encode the same arithmetic rewrite of the recursive successor split.
  simpa using congrArg eqToHom
    (Subsingleton.elim
      (((by
          have h : n = n - i.1 + i.1 := by
            simpa using (Nat.sub_add_cancel i.is_le).symm
          simpa [iteratedEndofunctor, split_left_degree_succ] using
            congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h) :
          X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y))
      (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)))

/-- Helper for Lemma 14.33.6: the inverse leading source-side successor cast is the explicit
block-split transport. -/
@[simp] private theorem split_succ_source_obj_eq_symm_eqToHom
    (n : ℕ) (i : Fin (n + 1)) :
    eqToHom
        (((by
          have h : n = n - i.1 + i.1 := by
            simpa using (Nat.sub_add_cancel i.is_le).symm
          simpa [iteratedEndofunctor, split_left_degree_succ] using
            congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h) :
          X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y).symm) =
      eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)).symm := by
  -- The symmetric source casts agree by the same object equality.
  simpa using congrArg (fun h ↦ eqToHom h.symm)
    (Subsingleton.elim
      (((by
          have h : n = n - i.1 + i.1 := by
            simpa using (Nat.sub_add_cancel i.is_le).symm
          simpa [iteratedEndofunctor, split_left_degree_succ] using
            congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h) :
          X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y))
      (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)))

/-- Helper for Lemma 14.33.6: the successor split isomorphism forward map is the recursive split
map, with the source and target transports made explicit by named casts. -/
private theorem iterated_split_iso_succ_hom_transport_with_named_casts
    (n : ℕ) (i : Fin (n + 1)) :
    (iteratedEndofunctorSplitIso (Y := Y) (n + 1) i.succ).hom =
      eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)) ≫
        Functor.whiskerRight
          (iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).hom Y ≫
          (Functor.associator X⦅(n + 1 - i.succ.1)⦆ X⦅i.1⦆ Y).hom ≫
            eqToHom (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)) :=
by
  -- Unfold one recursive layer of the split isomorphism and rewrite the source/target casts by
  -- the named transport lemmas.
  rw [split_succ_source_obj_eqToHom, split_succ_target_obj_eqToHom]
  let g :
      X⦅(n + 2)⦆ ⟶ X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆ :=
    eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)) ≫
      Functor.whiskerRight
        (iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).hom Y ≫
      (Functor.associator X⦅(n + 1 - i.succ.1)⦆ X⦅i.1⦆ Y).hom
  -- After the source and target casts are named, only the terminal identity needs normalization.
  simp [iteratedEndofunctorSplitIso, iteratedEndofunctorCompIso]
  simpa [g, iteratedEndofunctor] using (Category.comp_id g).symm

/-- Helper for Lemma 14.33.6: the successor split isomorphism inverse map is the recursive
unsplit map, with the source and target transports made explicit by named casts. -/
private theorem iterated_split_iso_succ_inv_transport_with_named_casts
    (n : ℕ) (i : Fin (n + 1)) :
    (iteratedEndofunctorSplitIso (Y := Y) (n + 1) i.succ).inv =
      eqToHom (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)).symm ≫
        (Functor.associator X⦅(n + 1 - i.succ.1)⦆ X⦅i.1⦆ Y).inv ≫
          Functor.whiskerRight
            (iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).inv Y ≫
            eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)).symm :=
by
  -- The inverse recursion normalizes in the same way, now using the symmetric source and target
  -- casts.
  rw [split_succ_target_obj_eq_symm_eqToHom]
  simp [iteratedEndofunctorSplitIso, iteratedEndofunctorCompIso]
  let g :
      X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆ ⟶ X⦅(n + 2)⦆ :=
    (Functor.associator X⦅(n + 1 - i.succ.1)⦆ X⦅i.1⦆ Y).inv ≫
      Functor.whiskerRight
        (iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).inv Y ≫
        eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)).symm
  exact (Category.id_comp g).symm

/-- Helper for Lemma 14.33.6: after evaluating the successor split transport at an object `Z`,
the target-side cast disappears and one is left with the concrete recursive split map. -/
private theorem iterated_split_iso_succ_app_cast_cleanup
    (n : ℕ) (i : Fin (n + 1)) (Z : C) :
    (((iteratedEndofunctorSplitIso (Y := Y) (n + 1) i.succ).hom).app Z =
        eqToHom
            (congrArg (fun F : C ⥤ C ↦ F.obj Z)
              (split_succ_source_obj_eq (Y := Y) (n := n) (i := i))) ≫
          Y.map ((iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).hom.app Z) ≫
            eqToHom
              ((by
                rfl :
                  Y.obj (X⦅i.1⦆.obj (X⦅(n + 1 - i.succ.1)⦆.obj Z)) =
                    (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z))) ∧
      (((iteratedEndofunctorSplitIso (Y := Y) (n + 1) i.succ).inv).app Z =
        eqToHom
            ((by
              rfl :
                (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z =
                  Y.obj (X⦅i.1⦆.obj (X⦅(n + 1 - i.succ.1)⦆.obj Z)))) ≫
          Y.map ((iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).inv.app Z) ≫
            eqToHom
              (congrArg (fun F : C ⥤ C ↦ F.obj Z)
                (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)).symm)) := by
  constructor
  · -- Evaluate the named forward split formula at `Z`; the terminal target cast becomes `𝟙`.
    have h :=
      congrArg (fun η ↦ η.app Z)
        (iterated_split_iso_succ_hom_transport_with_named_casts (Y := Y) (n := n) (i := i))
    simpa [NatTrans.comp_app, Category.assoc] using h
  · -- Evaluate the named inverse split formula at `Z`; the leading target cast also becomes `𝟙`.
    have h :=
      congrArg (fun η ↦ η.app Z)
        (iterated_split_iso_succ_inv_transport_with_named_casts (Y := Y) (n := n) (i := i))
    simpa [NatTrans.comp_app, Category.assoc] using h

/-- Helper for Lemma 14.33.6: the realization equation for face maps can be read in the
source-proof direction by moving the object transport to the right. -/
private theorem realization_delta_symm
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U)
    {n : ℕ} (i : Fin (n + 2)) :
    eqToHom (hU.obj_eq (n + 1)).symm ≫ U.δ i =
      d^⦅n, i⦆ ≫ eqToHom (hU.obj_eq n).symm := by
  -- Insert the identity transport on the right, rewrite the middle composite by `δ_eq`, and then
  -- collapse the inverse transports.
  calc
    eqToHom (hU.obj_eq (n + 1)).symm ≫ U.δ i =
        eqToHom (hU.obj_eq (n + 1)).symm ≫ (U.δ i ≫ eqToHom (hU.obj_eq n)) ≫
          eqToHom (hU.obj_eq n).symm := by
            simp [Category.assoc]
    _ = eqToHom (hU.obj_eq (n + 1)).symm ≫
          (eqToHom (hU.obj_eq (n + 1)) ≫ d^⦅n, i⦆) ≫ eqToHom (hU.obj_eq n).symm := by
            rw [hU.δ_eq]
    _ = d^⦅n, i⦆ ≫ eqToHom (hU.obj_eq n).symm := by
          simp [Category.assoc]

/-- Helper for Lemma 14.33.6: the realization equation for degeneracy maps can be read in the
source-proof direction by moving the object transport to the right. -/
private theorem realization_sigma_symm
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U)
    {n : ℕ} (i : Fin (n + 1)) :
    eqToHom (hU.obj_eq n).symm ≫ U.σ i =
      s^⦅n, i⦆ ≫ eqToHom (hU.obj_eq (n + 1)).symm := by
  -- The same transport maneuver rewrites the degeneracy realization identity in source-proof
  -- orientation.
  calc
    eqToHom (hU.obj_eq n).symm ≫ U.σ i =
        eqToHom (hU.obj_eq n).symm ≫ (U.σ i ≫ eqToHom (hU.obj_eq (n + 1))) ≫
          eqToHom (hU.obj_eq (n + 1)).symm := by
            simp [Category.assoc]
    _ = eqToHom (hU.obj_eq n).symm ≫
          (eqToHom (hU.obj_eq n) ≫ s^⦅n, i⦆) ≫ eqToHom (hU.obj_eq (n + 1)).symm := by
            rw [hU.σ_eq]
    _ = s^⦅n, i⦆ ≫ eqToHom (hU.obj_eq (n + 1)).symm := by
          simp [Category.assoc]

/-- Helper for Lemma 14.33.6: after evaluating the realization face identity at `Z`, any
composable prefix can be carried across the final object transport. -/
private theorem iterated_endofunctor_realization_delta_app_tail
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U)
    {n : ℕ} (i : Fin (n + 2)) (Z : C)
    {A : C} (p : A ⟶ X⦅(n + 1)⦆.obj Z) :
    p ≫ (eqToHom (hU.obj_eq (n + 1)).symm).app Z ≫ (U.δ i).app Z =
      p ≫ d^⦅n, i⦆.app Z ≫ (eqToHom (hU.obj_eq n).symm).app Z := by
  -- Evaluate the realization face identity at `Z`, then precompose by the chosen prefix.
  have hdelta_app :
      (eqToHom (hU.obj_eq (n + 1)).symm).app Z ≫ (U.δ i).app Z =
        d^⦅n, i⦆.app Z ≫ (eqToHom (hU.obj_eq n).symm).app Z := by
    simpa [NatTrans.comp_app] using
      congrArg (fun η ↦ η.app Z) (realization_delta_symm (d := d) (s := s) (hU := hU) (i := i))
  exact congrArg (fun k ↦ p ≫ k) hdelta_app

/-- Helper for Lemma 14.33.6: after evaluating the realization degeneracy identity at `Z`, any
composable prefix can be carried across the final object transport. -/
private theorem iterated_endofunctor_realization_sigma_app_tail
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U)
    {n : ℕ} (i : Fin (n + 1)) (Z : C)
    {A : C} (p : A ⟶ X⦅n⦆.obj Z) :
    p ≫ (eqToHom (hU.obj_eq n).symm).app Z ≫ (U.σ i).app Z =
      p ≫ s^⦅n, i⦆.app Z ≫ (eqToHom (hU.obj_eq (n + 1)).symm).app Z := by
  -- The degeneracy transport behaves identically after evaluation at `Z`.
  have hsigma_app :
      (eqToHom (hU.obj_eq n).symm).app Z ≫ (U.σ i).app Z =
        s^⦅n, i⦆.app Z ≫ (eqToHom (hU.obj_eq (n + 1)).symm).app Z := by
    simpa [NatTrans.comp_app] using
      congrArg (fun η ↦ η.app Z) (realization_sigma_symm (d := d) (s := s) (hU := hU) (i := i))
  exact congrArg (fun k ↦ p ≫ k) hsigma_app

-- Proof sketch: specialize the generic left-whiskering compatibility square to the canonical
-- iterated endofunctor resolution and its canonical augmentation.
/-- Lemma 14.33.6 (compatibility for `f ⋆ 1_X`): the left-whiskered endomorphism of the canonical
iterated endofunctor resolution is compatible with the augmentation via `f`. -/
@[stacks 0G5S]
theorem iterated_endofunctor_left_star_augmentation_compatible
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    CommSq
      (f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ)
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      ((SimplicialObject.const (C ⥤ C)).map f) := by
  let X := iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ
  let ε := iteratedEndofunctorAugmentation d s
    (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ)
  simpa [X, ε, prePostcomposeAugmented_id_id_hom] using
    CommSq.mk (leftStarAugmentedHom X ε f).w

-- Proof sketch: specialize the generic right-whiskering compatibility square to the canonical
-- iterated endofunctor resolution and its canonical augmentation.
/-- Lemma 14.33.6 (compatibility for `1_X ⋆ f`): the right-whiskered endomorphism of the canonical
iterated endofunctor resolution is compatible with the augmentation via `f`. -/
@[stacks 0G5S]
theorem iterated_endofunctor_right_star_augmentation_compatible
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    CommSq
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f)
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      ((SimplicialObject.const (C ⥤ C)).map f) := by
  let X := iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ
  let ε := iteratedEndofunctorAugmentation d s
    (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ)
  simpa [X, ε, prePostcomposeAugmented_id_id_hom] using
    CommSq.mk (rightStarAugmentedHom X ε f).w

/-- Helper for Lemma 14.33.6: the directed homotopy component `h_{n,i}` is obtained by inserting
one extra copy of `Y`, splitting `Y⦅n + 1⦆` into the left block `Y⦅i⦆` and right block
`Y⦅n - i⦆`, applying the middle whisker `1_i ⋆ f ⋆ 1_{n - i}`, and transporting back to the
canonical realization. -/
private noncomputable def iterated_endofunctor_middle_whisker_component
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C)
    (n : ℕ) (i : Fin (n + 1)) :
    (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ).obj
        (Opposite.op (SimplexCategory.mk n)) ⟶
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ).obj
        (Opposite.op (SimplexCategory.mk (n + 1))) :=
  let X := iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ
  let hX := iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ
  let j : Fin (n + 1) := ⟨n - i.1, lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self n)⟩
  eqToHom (hX.obj_eq n) ≫
    s^⦅n, j⦆ ≫
      (iteratedEndofunctorSplitIso (Y := Y) n j).hom ≫
        Functor.whiskerLeft X⦅(n - j.1)⦆ (Functor.whiskerRight f X⦅j.1⦆) ≫
          (iteratedEndofunctorSplitIso (Y := Y) n j).inv ≫
            eqToHom (hX.obj_eq (n + 1)).symm

/-- Helper for Lemma 14.33.6: the source-proof family `h_{n,i}` already has the dependent type
required by `SimplicialObject.Homotopy.mk`. -/
private noncomputable def iterated_endofunctor_middle_whisker_family
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    {n : ℕ} → (i : Fin (n + 1)) →
      ((iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ).obj
          (Opposite.op (SimplexCategory.mk n)) ⟶
        (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ).obj
          (Opposite.op (SimplexCategory.mk (n + 1)))) :=
  fun {n} i ↦
    iterated_endofunctor_middle_whisker_component
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f n i

/-- Helper for Lemma 14.33.6: in the endpoint `i = 0`, the internal split index is `Fin.last n`. -/
@[simp] private theorem iterated_endofunctor_middle_whisker_zero_split_index
    (n : ℕ) :
    (⟨n - (0 : Fin (n + 1)).1,
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self n)⟩ : Fin (n + 1)) = Fin.last n := by
  -- The endpoint `i = 0` leaves the whole degree on the right block.
  ext
  simp

/-- Helper for Lemma 14.33.6: in the endpoint `i = Fin.last n`, the internal split index is `0`. -/
@[simp] private theorem iterated_endofunctor_middle_whisker_last_split_index
    (n : ℕ) :
    (⟨n - (Fin.last n).1,
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self n)⟩ : Fin (n + 1)) = 0 := by
  -- The endpoint `i = Fin.last n` leaves nothing on the right block.
  ext
  simp

/-- Helper for Lemma 14.33.6: the explicit zero split index written as `⟨n - n, _⟩` is `0`. -/
@[simp] private theorem iterated_endofunctor_zero_split_index_normalization
    (n : ℕ) :
    (⟨n - n,
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self n)⟩ : Fin (n + 1)) = 0 := by
  -- This is the arithmetic normalization of the complementary endpoint split index.
  ext
  simp

/-- Helper for Lemma 14.33.6: after pushing the `i = 0` endpoint through the realization
face map, the remaining `Z`-component is the explicit terminal split composite from the source
proof. -/
private theorem iterated_endofunctor_middle_whisker_last_endpoint_core_app
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C)
    (n : ℕ) (Z : C) :
    ((iterated_endofunctor_middle_whisker_family
          (d := d) (s := s) hσδ₀ hσδ₁ hσσ f (0 : Fin (n + 1)) ≫
        SimplicialObject.δ
          (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
            (whiskeringLeft C C C).obj (𝟭 C))
          0).app Z) =
      (eqToHom
          ((iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ).obj_eq n)).app Z ≫
        s^⦅n, Fin.last n⦆.app Z ≫
          ((iteratedEndofunctorSplitIso (Y := Y) n (Fin.last n)).hom.app Z) ≫
            (Functor.whiskerLeft X⦅(n - (Fin.last n).1)⦆
              (Functor.whiskerRight f X⦅(Fin.last n).1⦆)).app Z ≫
              ((iteratedEndofunctorSplitIso (Y := Y) n (Fin.last n)).inv.app Z) ≫
                d^⦅n, 0⦆.app Z ≫
                  (eqToHom
                    ((iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ).obj_eq n).symm).app Z := by
  let hX := iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ
  -- Replace the owner face map by the realization face formula, leaving the explicit terminal
  -- split composite from the source proof.
  rw [whiskeringLeft_id_delta]
  have htail :=
    iterated_endofunctor_realization_delta_app_tail (d := d) (s := s) hX (i := (0 : Fin (n + 2))) Z
      (p :=
        (eqToHom (hX.obj_eq n)).app Z ≫
          s^⦅n, Fin.last n⦆.app Z ≫
            ((iteratedEndofunctorSplitIso (Y := Y) n (Fin.last n)).hom.app Z) ≫
              (Functor.whiskerLeft X⦅(n - (Fin.last n).1)⦆
                (Functor.whiskerRight f X⦅(Fin.last n).1⦆)).app Z ≫
                ((iteratedEndofunctorSplitIso (Y := Y) n (Fin.last n)).inv.app Z))
  -- Unfold the family only up to the point where the split index is identified with `Fin.last n`.
  simpa [iterated_endofunctor_middle_whisker_family, iterated_endofunctor_middle_whisker_component,
    iterated_endofunctor_middle_whisker_zero_split_index, NatTrans.comp_app, Category.assoc]
    using htail

/-- Helper for Lemma 14.33.6: the terminal split core appearing in the `i = 0` endpoint
normalizes to the right-whiskered endpoint map. -/
private theorem iterated_endofunctor_split_last_endpoint_factorization_app
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C)
    (n : ℕ) (Z : C) :
    (eqToHom
        ((iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ).obj_eq n)).app Z ≫
      s^⦅n, Fin.last n⦆.app Z ≫
        ((iteratedEndofunctorSplitIso (Y := Y) n (Fin.last n)).hom.app Z) ≫
          (Functor.whiskerLeft X⦅(n - (Fin.last n).1)⦆
            (Functor.whiskerRight f X⦅(Fin.last n).1⦆)).app Z ≫
            ((iteratedEndofunctorSplitIso (Y := Y) n (Fin.last n)).inv.app Z) ≫
              d^⦅n, 0⦆.app Z ≫
                (eqToHom
                  ((iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ).obj_eq n).symm).app Z =
      ((iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f).app
        (Opposite.op (SimplexCategory.mk n))).app Z := by
  -- TODO: normalize the `j = Fin.last n` split conjugation to the right-whiskered copy of
  -- `s^⦅0, 0⦆ ≫ d^⦅0, 0⦆`, then collapse it with `hσδ₀` and the right-whiskered endpoint formula.
  sorry

/-- Helper for Lemma 14.33.6: the `Z`-component of the `i = 0` endpoint collapses to the
right-whiskered map after rewriting the terminal split and the `s ≫ d₁` identity. -/
private theorem iterated_endofunctor_middle_whisker_last_endpoint_component_app
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C)
    (n : ℕ) (Z : C) :
    ((iterated_endofunctor_middle_whisker_family
          (d := d) (s := s) hσδ₀ hσδ₁ hσσ f (0 : Fin (n + 1)) ≫
        SimplicialObject.δ
          (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
            (whiskeringLeft C C C).obj (𝟭 C))
          0).app Z) =
    ((iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f).app
        (Opposite.op (SimplexCategory.mk n))).app Z := by
  -- The endpoint proof now splits cleanly into the realization-tail rewrite and the extremal
  -- split normalization isolated below.
  have hcore :=
    iterated_endofunctor_middle_whisker_last_endpoint_core_app
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f n Z
  have hfactor :=
    iterated_endofunctor_split_last_endpoint_factorization_app
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f n Z
  exact hcore.trans hfactor

/-- Helper for Lemma 14.33.6: after pushing the `i = Fin.last n` endpoint through the terminal
face map, the remaining `Z`-component is the explicit zero-split composite from the source proof. -/
private theorem iterated_endofunctor_zero_split_middle_whisker_app
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C)
    (n : ℕ) (Z : C) :
    ((iteratedEndofunctorSplitIso (Y := Y) n (0 : Fin (n + 1))).hom.app Z) ≫
        (Functor.whiskerLeft X⦅n⦆ (Functor.whiskerRight f X⦅0⦆)).app Z ≫
          ((iteratedEndofunctorSplitIso (Y := Y) n (0 : Fin (n + 1))).inv.app Z) =
      Y.map (f.app (X⦅n⦆.obj Z)) := by
  -- The zero split is the identity, so the middle whisker is already the pointwise map
  -- `Y.map (f.app (X⦅n⦆.obj Z))`.
  simp [iteratedEndofunctorSplitIso_zero_hom, iteratedEndofunctorSplitIso_zero_inv,
    iteratedEndofunctor, NatTrans.comp_app, Category.assoc, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]

/-- Helper for Lemma 14.33.6: after pushing the `i = Fin.last n` endpoint through the terminal
face map, the remaining `Z`-component is the explicit zero-split composite from the source proof. -/
private theorem iterated_endofunctor_middle_whisker_zero_endpoint_core_app
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C)
    (n : ℕ) (Z : C) :
    ((iterated_endofunctor_middle_whisker_family
          (d := d) (s := s) hσδ₀ hσδ₁ hσσ f (Fin.last n) ≫
        SimplicialObject.δ
          (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
            (whiskeringLeft C C C).obj (𝟭 C))
          (Fin.last (n + 1))).app Z) =
      (eqToHom
          ((iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ).obj_eq n)).app Z ≫
        s^⦅n, (0 : Fin (n + 1))⦆.app Z ≫
          Y.map (f.app (X⦅n⦆.obj Z)) ≫
            d^⦅n, Fin.last (n + 1)⦆.app Z ≫
              (eqToHom
                ((iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ).obj_eq n).symm).app Z := by
  -- TODO: rewrite the family index to the explicit zero split, collapse the middle whisker by
  -- `iterated_endofunctor_zero_split_middle_whisker_app`, and then apply the realization-tail
  -- identity for `δ (Fin.last (n + 1))`.
  sorry

/-- Helper for Lemma 14.33.6: the zero split core appearing in the `i = Fin.last n` endpoint
normalizes to the left-whiskered endpoint map. -/
private theorem iterated_endofunctor_split_zero_endpoint_factorization_app
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C)
    (n : ℕ) (Z : C) :
    (eqToHom
        ((iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ).obj_eq n)).app Z ≫
      s^⦅n, (0 : Fin (n + 1))⦆.app Z ≫
        Y.map (f.app (X⦅n⦆.obj Z)) ≫
          d^⦅n, Fin.last (n + 1)⦆.app Z ≫
            (eqToHom
              ((iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ).obj_eq n).symm).app Z =
      ((f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ).app
        (Opposite.op (SimplexCategory.mk n))).app Z := by
  -- TODO: normalize the `j = 0` split conjugation to the left-whiskered copy of
  -- `s^⦅0, 0⦆ ≫ d^⦅0, 1⦆`, then collapse it with `hσδ₁` and the left-whiskered endpoint formula.
  sorry

/-- Helper for Lemma 14.33.6: the `Z`-component of the `i = Fin.last n` endpoint collapses to the
left-whiskered map after rewriting the zero split and the `s ≫ d₁` identity. -/
private theorem iterated_endofunctor_middle_whisker_zero_endpoint_component_app
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C)
    (n : ℕ) (Z : C) :
    ((iterated_endofunctor_middle_whisker_family
          (d := d) (s := s) hσδ₀ hσδ₁ hσσ f (Fin.last n) ≫
        SimplicialObject.δ
          (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
            (whiskeringLeft C C C).obj (𝟭 C))
          (Fin.last (n + 1))).app Z) =
    ((f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ).app
        (Opposite.op (SimplexCategory.mk n))).app Z := by
  -- The complementary endpoint now follows the same two-step pattern: first remove the
  -- realization tail, then normalize the extremal zero split.
  have hcore :=
    iterated_endofunctor_middle_whisker_zero_endpoint_core_app
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f n Z
  have hfactor :=
    iterated_endofunctor_split_zero_endpoint_factorization_app
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f n Z
  exact hcore.trans hfactor

/-- Helper for Lemma 14.33.6: the `i = 0` and `i = n + 1` endpoint composites of the explicit
middle-whisker family agree with `1_X ⋆ f` and `f ⋆ 1_X`. -/
private theorem iterated_endofunctor_middle_whisker_endpoints
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    (∀ n,
        iterated_endofunctor_middle_whisker_family
            (d := d) (s := s) hσδ₀ hσδ₁ hσσ f (0 : Fin (n + 1)) ≫
          SimplicialObject.δ
            (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
              (whiskeringLeft C C C).obj (𝟭 C))
            0 =
          (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f).app
            (Opposite.op (SimplexCategory.mk n))) ∧
      (∀ n,
        iterated_endofunctor_middle_whisker_family
            (d := d) (s := s) hσδ₀ hσδ₁ hσσ f (Fin.last n) ≫
          SimplicialObject.δ
            (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
              (whiskeringLeft C C C).obj (𝟭 C))
            (Fin.last (n + 1)) =
          (f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ).app
            (Opposite.op (SimplexCategory.mk n))) := by
  -- The raw family already lands in the owner expected by `Homotopy.mk`; the remaining endpoint
  -- work is to normalize the `j = Fin.last n` and `j = 0` split formulas and then apply the two
  -- base identities `hσδ₀` and `hσδ₁`.
  constructor
  · intro n
    -- Evaluate the endpoint at an object and use the dedicated terminal-branch normalization.
    ext Z
    exact iterated_endofunctor_middle_whisker_last_endpoint_component_app
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f n Z
  · intro n
    -- The complementary endpoint is the zero-split branch normalized objectwise.
    ext Z
    exact iterated_endofunctor_middle_whisker_zero_endpoint_component_app
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f n Z

/-- Helper for Lemma 14.33.6: the explicit middle-whisker family satisfies the five branchwise
simplicial identities required to assemble a directed simplicial homotopy. -/
private theorem iterated_endofunctor_middle_whisker_simplicial_relations
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    (∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)),
        i ≤ j.castSucc →
          iterated_endofunctor_middle_whisker_family
              (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j.succ ≫
            SimplicialObject.δ
              (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
                (whiskeringLeft C C C).obj (𝟭 C))
              i.castSucc =
            SimplicialObject.δ
              (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
                (whiskeringLeft C C C).obj (𝟭 C))
              i ≫
              iterated_endofunctor_middle_whisker_family
                (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j) ∧
      (∀ {n : ℕ} (j : Fin (n + 1)),
        iterated_endofunctor_middle_whisker_family
            (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j.succ ≫
          SimplicialObject.δ
            (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
              (whiskeringLeft C C C).obj (𝟭 C))
            j.castSucc.succ =
          iterated_endofunctor_middle_whisker_family
            (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j.castSucc ≫
            SimplicialObject.δ
              (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
                (whiskeringLeft C C C).obj (𝟭 C))
              j.castSucc.succ) ∧
      (∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)),
        j.castSucc < i →
          iterated_endofunctor_middle_whisker_family
              (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j.castSucc ≫
            SimplicialObject.δ
              (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
                (whiskeringLeft C C C).obj (𝟭 C))
              i.succ =
            SimplicialObject.δ
              (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
                (whiskeringLeft C C C).obj (𝟭 C))
              i ≫
              iterated_endofunctor_middle_whisker_family
                (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j) ∧
      (∀ {n : ℕ} (i j : Fin (n + 1)),
        i ≤ j →
          iterated_endofunctor_middle_whisker_family
              (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j ≫
            SimplicialObject.σ
              (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
                (whiskeringLeft C C C).obj (𝟭 C))
              i.castSucc =
            SimplicialObject.σ
              (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
                (whiskeringLeft C C C).obj (𝟭 C))
              i ≫
              iterated_endofunctor_middle_whisker_family
                (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j.succ) ∧
      (∀ {n : ℕ} (i j : Fin (n + 1)),
        j ≤ i →
          iterated_endofunctor_middle_whisker_family
              (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j ≫
            SimplicialObject.σ
              (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
                (whiskeringLeft C C C).obj (𝟭 C))
              i.succ =
            SimplicialObject.σ
              (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋙
                (whiskeringLeft C C C).obj (𝟭 C))
              i ≫
              iterated_endofunctor_middle_whisker_family
                (d := d) (s := s) hσδ₀ hσδ₁ hσσ f j.castSucc) := by
  -- After expanding the common owner object, each branch is the source-proof check obtained by
  -- pushing the relevant face or degeneracy into the correct block and comparing the same middle
  -- whisker on both sides.
  -- TODO: first replace the outer owner maps by the explicit `d^⦅n, i⦆` and `s^⦅n, i⦆` using
  -- `whiskeringLeft_id_delta`, `whiskeringLeft_id_sigma`, `realization_delta_symm`, and
  -- `realization_sigma_symm`. Then use the split transport lemmas for successor indices to move
  -- the chosen face or degeneracy into the appropriate block and finish with the source
  -- equalities from `Lemma_14_33_2`.
  sorry

/-- Helper for Lemma 14.33.6: bundling the explicit middle-whisker components gives the directed
simplicial homotopy whose endpoints are `f ⋆ 1_X` and `1_X ⋆ f`. -/
private noncomputable def iterated_endofunctor_left_star_right_star_directed_homotopy
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    SimplicialObject.Homotopy
      (f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ)
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f) :=
  let hendpoints :=
    iterated_endofunctor_middle_whisker_endpoints
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f
  let hsimplicial :=
    iterated_endofunctor_middle_whisker_simplicial_relations
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f
  -- The source-proof family already has the dependent type expected by `Homotopy.mk`; the
  -- remaining obligations are isolated into the endpoint and simplicial-relation helpers above.
  SimplicialObject.Homotopy.mk
    (iterated_endofunctor_middle_whisker_family
      (d := d) (s := s) hσδ₀ hσδ₁ hσσ f)
    hendpoints.1
    hendpoints.2
    hsimplicial.1
    hsimplicial.2.1
    hsimplicial.2.2.1
    hsimplicial.2.2.2.1
    hsimplicial.2.2.2.2

-- Proof sketch: specialize `prePostcomposeAugmentedMap_homotopy` to the augmented simplicial
-- object coming from the canonical iterated endofunctor resolution, taking both source and
-- target functors to be `𝟭 C`. The two required augmented morphisms are the ones determined by
-- the public compatibility theorems above; after identifying the whiskering owners at `𝟭 C` with the
-- original simplicial endofunctor object, the two resulting simplicial maps are
-- `f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ` and
-- `iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f`.
/-- Lemma 14.33.6: for the simplicial endofunctor object arising from `Example 14.33.1` and
`Lemma 14.33.2`, the endomorphisms `f ⋆ 1_X` and `1_X ⋆ f` are homotopic in the zigzag sense. -/
@[stacks 0G5S]
theorem iterated_endofunctor_left_star_right_star_homotopic
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    SimplicialObject.Homotopic
      (f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ)
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f) := by
  -- Route correction: specializing Lemma 14.33.5 only compares the two composite orders
  -- `(f ⋆ₗ X) ≫ (X ⋆ᵣ f)` and `(X ⋆ᵣ f) ≫ (f ⋆ₗ X)`, so the textbook middle-whisker homotopy
  -- must be built directly on the canonical iterated resolution.
  exact
    SimplicialObject.Homotopic.of_homotopy
      (iterated_endofunctor_left_star_right_star_directed_homotopy
        (d := d) (s := s) hσδ₀ hσδ₁ hσσ f)

end IteratedResolution

end CategoryTheory
