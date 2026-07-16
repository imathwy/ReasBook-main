import Mathlib
import StacksProject_2024.stacks_project.Chap14.Example_14_33_1
import StacksProject_2024.stacks_project.Chap14.Lemma_14_2_4
import StacksProject_2024.stacks_project.Chap14.Lemma_14_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open scoped Simplicial
open scoped IteratedEndofunctor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section

variable {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)

/-
Domain-style sampling:
- primary domain: augmentations of simplicial objects of endofunctors, built from the iterated
  endofunctor formulas of `Example 14.33.1`;
- sampled owner declarations:
  `Definition_14_20_1`,
  `SimplicialObject.augment`,
  `SimplicialObject.augmentHomEquivZeroSimplex`,
  `SimplicialObject.augment_hom_zero`,
  `iteratedFaceMap`;
- best owner abstraction: for fixed `U` and target `𝟭 C`, the chapter's source-facing owner is the
  augmentation morphism `U ⟶ (const (C ⥤ C)).obj (𝟭 C)` from `Definition_14_20_1`; its canonical
  owner construction is `SimplicialObject.augment`, while the chapter bridge
  `SimplicialObject.augmentHomEquivZeroSimplex` repackages the same construction in terms of the
  primitive degree-`0` datum and its two-face relation;
- source/core/bridge triage:
  - `source-facing`: `IteratedEndofunctorRealization` and the existence/uniqueness statement for a
    simplicial object realizing the explicit formulas, together with the augmentation morphism
    `U ⟶ (const (C ⥤ C)).obj (𝟭 C)`;
  - `core/canonical`: `SimplicialObject.augment`;
  - `bridge/view`: `SimplicialObject.augmentHomEquivZeroSimplex`, together with the
    realization-specific degree-`0` map and its face-condition theorem;
- primitive data vs. derived API:
  primitive data are the realization equations and the degree-`0` map
  `U _⦋0⦌ ⟶ 𝟭 C`; the full augmentation morphism and higher-degree compatibility are derived from
  `SimplicialObject.augment`.
-/

local notation "X⦅" n:max "⦆" => Y⦅n⦆
local notation "d^⦅" n ", " j "⦆" => d[Y, d]⦅n, j⦆
local notation "s^⦅" n ", " j "⦆" => s[Y, s]⦅n, j⦆

/-- Helper for Lemma 14.33.2: the degree-`0` first face map is the branch that inserts `d`
in the left factor of `Y ⋙ Y`. -/
private theorem iterated_face_map_zero_first :
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

/-- Helper for Lemma 14.33.2: the degree-`0` last face map is the branch that inserts `d`
in the right factor of `Y ⋙ Y`. -/
private theorem iterated_face_map_zero_last :
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

/-- The two degree-`0` iterated face maps become equal after postcomposition by `d`. -/
theorem iterated_face_map_comp_counit_eq :
    d^⦅0, (0 : Fin 2)⦆ ≫ d = d^⦅0, (1 : Fin 2)⦆ ≫ d := by
  -- Rewrite the two branches explicitly and compare them by naturality of `d`.
  rw [iterated_face_map_zero_first, iterated_face_map_zero_last]
  ext X
  simp [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  simpa using d.naturality (d.app X)

/-- Helper for Lemma 14.33.2: a nonterminal iterated face map is obtained by whiskering the
smaller face map on the right by `Y`. -/
@[simp] private theorem iterated_face_map_castSucc
    (n : ℕ) (j : Fin (n + 2)) :
    d^⦅n + 1, j.castSucc⦆ = Functor.whiskerRight d^⦅n, j⦆ Y := by
  -- Unfold the recursive nonterminal branch of `iteratedFaceMap`.
  simp [iteratedFaceMap]

/-- Helper for Lemma 14.33.2: the last iterated face map is the recursive right-unitor branch. -/
@[simp] private theorem iterated_face_map_last
    (n : ℕ) :
    d^⦅n + 1, Fin.last (n + 2)⦆ =
      Functor.whiskerLeft X⦅(n + 1)⦆ d ≫ (Functor.rightUnitor X⦅(n + 1)⦆).hom := by
  -- Unfold the terminal branch of the recursive definition.
  simp [iteratedFaceMap]
  rfl

/-- Helper for Lemma 14.33.2: the degree-`0` terminal `δ-δ` branch is the naturality square for
the smaller face map against `d`. -/
private theorem terminal_face_face_normalization_zero
    (i : Fin 2) :
    d^⦅1, Fin.last 2⦆ ≫ d^⦅0, i⦆ =
      d^⦅1, i.castSucc⦆ ≫ d^⦅0, Fin.last 1⦆ := by
  -- Expand the terminal and nonterminal branches, then read the equality pointwise as
  -- naturality of the smaller face map with respect to the counit `d`.
  have hlast :
      d^⦅0, Fin.last 1⦆ = Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom := by
    simpa using (iterated_face_map_zero_last (Y := Y) (d := d))
  rw [iterated_face_map_last, iterated_face_map_castSucc, hlast]
  ext X
  simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app]
  simpa using (d.naturality (d^⦅0, i⦆.app X)).symm

/-- Helper for Lemma 14.33.2: every positive-degree terminal `δ-δ` branch is the naturality square
for the smaller face map against `d`. -/
private theorem terminal_face_face_normalization_succ
    (n : ℕ) (i : Fin (n + 3)) :
    d^⦅n + 2, Fin.last (n + 3)⦆ ≫ d^⦅n + 1, i⦆ =
      d^⦅n + 2, i.castSucc⦆ ≫ d^⦅n + 1, Fin.last (n + 2)⦆ := by
  -- Expand the terminal and nonterminal recursive branches, then pointwise naturality of the
  -- smaller face map gives the required whiskering normalization.
  rw [iterated_face_map_last, iterated_face_map_castSucc, iterated_face_map_last]
  ext X
  simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app]
  simpa using (d.naturality (d^⦅n + 1, i⦆.app X)).symm

/-- Helper for Lemma 14.33.2: a nonterminal iterated degeneracy map is obtained by whiskering the
smaller degeneracy map on the right by `Y`. -/
@[simp] private theorem iterated_degeneracy_map_castSucc
    (n : ℕ) (j : Fin (n + 1)) :
    s^⦅n + 1, j.castSucc⦆ = Functor.whiskerRight s^⦅n, j⦆ Y := by
  -- Unfold the recursive nonterminal branch of `iteratedDegeneracyMap`.
  simp [iteratedDegeneracyMap]

/-- Helper for Lemma 14.33.2: the last iterated degeneracy map is the recursive associator
branch. -/
@[simp] private theorem iterated_degeneracy_map_last
    (n : ℕ) :
    s^⦅n + 1, Fin.last (n + 1)⦆ =
      Functor.whiskerLeft X⦅n⦆ s ≫ (Functor.associator X⦅n⦆ Y Y).inv := by
  -- Unfold the terminal branch of the recursive definition.
  simp [iteratedDegeneracyMap]
  rfl

/-- Helper for Lemma 14.33.2: the terminal face map component evaluates `d` on the current
iterate `X⦅n⦆.obj Z`. -/
private theorem iterated_face_map_last_app
    (n : ℕ) (Z : C) :
    d^⦅n, Fin.last (n + 1)⦆.app Z = d.app (X⦅n⦆.obj Z) := by
  -- Split off the degree-`0` base case; afterwards the terminal recursive branch is already in
  -- the required pointwise form.
  cases n with
  | zero =>
      have hlast : (Fin.last 1 : Fin 2) = (1 : Fin 2) := rfl
      rw [hlast, iterated_face_map_zero_last]
      simpa [iteratedEndofunctor, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.rightUnitor_hom_app]
  | succ n =>
      rw [iterated_face_map_last]
      simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]

/-- Helper for Lemma 14.33.2: the terminal degeneracy map component evaluates `s` on the current
iterate `X⦅n⦆.obj Z`. -/
private theorem iterated_degeneracy_map_last_app
    (n : ℕ) (Z : C) :
    s^⦅n + 1, Fin.last (n + 1)⦆.app Z = s.app (X⦅n⦆.obj Z) := by
  -- The associator branch becomes the functorial image of `s.app` because the associator is the
  -- identity on objects.
  rw [iterated_degeneracy_map_last]
  simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app]

/-- Helper for Lemma 14.33.2: the terminal adjacent `δσ` composites are exactly left-whiskered
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
    rw [iterated_degeneracy_map_last, iterated_face_map_castSucc]
    ext Z
    simp [NatTrans.comp_app, iteratedDegeneracyMap, iterated_face_map_zero_first,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app]
    rw [iterated_face_map_last_app]
    rfl
  · -- The terminal/terminal composite likewise matches the left-whiskered copy of
    -- `s ≫ d^⦅0, 1⦆`.
    rw [iterated_degeneracy_map_last, Fin.succ_last, iterated_face_map_last]
    ext Z
    simp [NatTrans.comp_app, iteratedDegeneracyMap, iterated_face_map_zero_last,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app]
    simp [iteratedEndofunctor]

/-- Helper for Lemma 14.33.2: the unique degree-`1` nonterminal `δδ` branch is the image under
`Y.map` of the naturality square for `d` against itself. -/
private theorem initial_nonterminal_face_map_normalization :
    d^⦅1, ((0 : Fin 2)).succ⦆ ≫ d^⦅0, (0 : Fin 2)⦆ =
      d^⦅1, ((0 : Fin 2)).castSucc⦆ ≫ d^⦅0, (0 : Fin 2)⦆ := by
  -- Rewrite the degree-`1` faces into right-whiskered degree-`0` faces, then push the
  -- naturality square for `d.app Z` through `Y.map`.
  have hs : (((0 : Fin 2).succ : Fin 3)) = (Fin.last 1).castSucc := rfl
  rw [hs, iterated_face_map_castSucc, iterated_face_map_castSucc]
  ext Z
  simp [NatTrans.comp_app, Functor.whiskerRight_app, iterated_face_map_zero_last,
    iterated_face_map_zero_first, Functor.whiskerLeft_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app]
  simpa [Functor.map_comp] using
    congrArg (fun k ↦ Y.map k) ((d.naturality (d.app Z)).symm)

/-- The explicit iterated face maps satisfy the simplicial face-face relation. -/
theorem iterated_face_map_comp_face_map
    (n : ℕ) {i j : Fin (n + 2)} (hij : i ≤ j) :
    d^⦅n + 1, j.succ⦆ ≫ d^⦅n, i⦆ = d^⦅n + 1, i.castSucc⦆ ≫ d^⦅n, j⦆ := by
  induction n with
  | zero =>
      -- In degree `0`, the terminal branch is already normalized, and the only nonterminal
      -- branch is the isolated degree-`1` computation above.
      refine Fin.lastCases
        (motive := fun j : Fin 2 ↦
          ∀ {i : Fin 2}, i ≤ j →
            d^⦅1, j.succ⦆ ≫ d^⦅0, i⦆ = d^⦅1, i.castSucc⦆ ≫ d^⦅0, j⦆)
        ?_ ?_ j hij
      · intro i hij
        simpa using terminal_face_face_normalization_zero (Y := Y) (d := d) i
      · intro j
        fin_cases j
        intro i hij
        fin_cases i
        · simpa using initial_nonterminal_face_map_normalization (Y := Y) (d := d)
        · simp at hij
  | succ n ih =>
      -- Split first on whether the outer face is terminal. The terminal branch is one of the
      -- already normalized `δδ` squares; the nonterminal branch is a right-whiskered copy of the
      -- smaller simplicial relation.
      refine Fin.lastCases
        (motive := fun j : Fin (n + 3) ↦
          ∀ {i : Fin (n + 3)}, i ≤ j →
            d^⦅n + 2, j.succ⦆ ≫ d^⦅n + 1, i⦆ = d^⦅n + 2, i.castSucc⦆ ≫ d^⦅n + 1, j⦆)
        ?_ ?_ j hij
      · intro i hij
        simpa [Fin.succ_last] using
          terminal_face_face_normalization_succ (Y := Y) (d := d) (n := n) i
      · intro j i hij
        refine Fin.lastCases
          (motive := fun i : Fin (n + 3) ↦
            i ≤ j.castSucc →
              d^⦅n + 2, j.castSucc.succ⦆ ≫ d^⦅n + 1, i⦆ =
                d^⦅n + 2, i.castSucc⦆ ≫ d^⦅n + 1, j.castSucc⦆)
          ?_ ?_ i hij
        · -- The terminal `i` case is impossible because a terminal index cannot lie below a
          -- nonterminal one.
          intro hij
          exfalso
          exact (not_le_of_gt (Fin.castSucc_lt_last j)) hij
        · intro i hij
          have hij' : i ≤ j := by
            simpa using hij
          -- Rewrite every face map as a right-whiskered smaller face map, then transport the
          -- smaller equality pointwise through `Y.map`.
          rw [← Fin.castSucc_succ j, iterated_face_map_castSucc, iterated_face_map_castSucc,
            iterated_face_map_castSucc, iterated_face_map_castSucc]
          ext Z
          have h_app :=
            congrArg (fun k ↦ k.app Z)
              (ih (i := i) (j := j) hij')
          simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp] using
            congrArg (fun k ↦ Y.map k) h_app

/-- Helper for Lemma 14.33.2: in the terminal `δσ` branch with `i < j + 1`, the terminal
degeneracy and the nonterminal face form the naturality square of the smaller face map against
`s`. -/
private theorem terminal_degeneracy_comp_face_castSucc
    (n : ℕ) (i : Fin (n + 2)) :
    s^⦅n + 2, Fin.last (n + 2)⦆ ≫ d^⦅n + 2, i.castSucc.castSucc⦆ =
      d^⦅n + 1, i.castSucc⦆ ≫ s^⦅n + 1, Fin.last (n + 1)⦆ := by
  -- Expand the terminal degeneracy and the two nonterminal face branches, then read the equality
  -- pointwise as naturality of `s` against the smaller face component.
  rw [iterated_degeneracy_map_last, iterated_face_map_castSucc, iterated_face_map_castSucc,
    iterated_degeneracy_map_last]
  ext Z
  simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app]
  simpa [Functor.comp_map] using (s.naturality (d^⦅n, i⦆.app Z)).symm

/-- Helper for Lemma 14.33.2: in the terminal `δσ` branch with `i > j + 1`, the nonterminal
degeneracy and the terminal face form the naturality square of the smaller degeneracy against
`d`. -/
private theorem nonterminal_degeneracy_comp_last_face
    (n : ℕ) (j : Fin (n + 2)) :
    s^⦅n + 2, j.castSucc⦆ ≫ d^⦅n + 2, Fin.last (n + 3)⦆ =
      d^⦅n + 1, Fin.last (n + 2)⦆ ≫ s^⦅n + 1, j⦆ := by
  -- Unfold the nonterminal degeneracy branch and the terminal face branch.
  rw [iterated_degeneracy_map_castSucc, iterated_face_map_last]
  -- Compare the two composites pointwise; this is exactly naturality of `d` for the smaller
  -- degeneracy component.
  ext Z
  simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app]
  simpa [Functor.comp_map] using d.naturality (s^⦅n + 1, j⦆.app Z)

/-- Helper for Lemma 14.33.2: the explicit face and degeneracy maps satisfy the nonadjacent
`i < j` simplicial identity. -/
private theorem iterated_face_map_comp_degeneracy_map_of_le
    (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)} (hij : i ≤ j.castSucc) :
    s^⦅n + 1, j.succ⦆ ≫ d^⦅n + 1, i.castSucc⦆ = d^⦅n, i⦆ ≫ s^⦅n, j⦆ := by
  induction n with
  | zero =>
      -- In degree `0`, only the unique nonadjacent branch remains.
      fin_cases j
      fin_cases i
      · have hbase :
            s^⦅1, Fin.last 1⦆ ≫ d^⦅1, ((0 : Fin 2).castSucc)⦆ =
              d^⦅0, (0 : Fin 2)⦆ ≫ s^⦅0, (0 : Fin 1)⦆ := by
            rw [iterated_degeneracy_map_last, iterated_face_map_castSucc, iterated_face_map_zero_first]
            ext Z
            simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
              Functor.associator_inv_app, Functor.leftUnitor_hom_app]
            simpa [Functor.comp_map] using (s.naturality (d.app Z)).symm
        simpa using hbase
      · simp at hij
  | succ n ih =>
      -- Split first on the outer degeneracy index. The terminal branch is the isolated
      -- naturality square above, and the nonterminal branch is a right-whiskered smaller
      -- relation.
      cases j using Fin.lastCases with
      | last =>
          cases i using Fin.lastCases with
          | last =>
              exfalso
              simpa using hij
          | cast i =>
              simpa [Fin.succ_last] using
                terminal_degeneracy_comp_face_castSucc (Y := Y) (d := d) (s := s) (n := n) i
      | cast j =>
          cases i using Fin.lastCases with
          | last =>
              exfalso
              simpa using hij
          | cast i =>
              have hij' : i ≤ j.castSucc := by
                simpa using hij
              rw [← Fin.castSucc_succ j, iterated_degeneracy_map_castSucc,
                iterated_face_map_castSucc, iterated_face_map_castSucc,
                iterated_degeneracy_map_castSucc]
              ext Z
              have h_app :=
                congrArg (fun k ↦ k.app Z)
                  (ih (i := i) (j := j) hij')
              simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp,
                Fin.castSucc_succ] using
                congrArg (fun k ↦ Y.map k) h_app

/-- Helper for Lemma 14.33.2: the explicit face and degeneracy maps satisfy the nonadjacent
`i > j + 1` simplicial identity. -/
private theorem iterated_face_map_comp_degeneracy_map_of_gt
    (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)} (hji : j.castSucc < i) :
    s^⦅n + 1, j.castSucc⦆ ≫ d^⦅n + 1, i.succ⦆ = d^⦅n, i⦆ ≫ s^⦅n, j⦆ := by
  induction n with
  | zero =>
      -- In degree `0`, only the unique `i > j + 1` branch remains.
      fin_cases j
      fin_cases i
      · simp at hji
      · have hbase :
            s^⦅1, ((0 : Fin 1).castSucc)⦆ ≫ d^⦅1, Fin.last 2⦆ =
              d^⦅0, (1 : Fin 2)⦆ ≫ s^⦅0, (0 : Fin 1)⦆ := by
            rw [iterated_degeneracy_map_castSucc, iterated_face_map_last, iterated_face_map_zero_last]
            ext Z
            simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
              Functor.rightUnitor_hom_app]
            simpa [Functor.comp_map] using d.naturality (s.app Z)
        simpa [Fin.succ_last] using hbase
  | succ n ih =>
      -- Split on whether the outer face is terminal. The terminal branch is the isolated
      -- naturality square `nonterminal_degeneracy_comp_last_face`, and the nonterminal branch is
      -- a right-whiskered smaller relation.
      cases i using Fin.lastCases with
      | last =>
          simpa [Fin.succ_last] using
            nonterminal_degeneracy_comp_last_face (Y := Y) (d := d) (s := s) (n := n) j
      | cast i =>
          cases j using Fin.lastCases with
          | last =>
              exfalso
              exact (not_lt_of_ge (Fin.le_last i)) hji
          | cast j =>
              have hji' : j.castSucc < i := by
                simpa using hji
              rw [iterated_degeneracy_map_castSucc, ← Fin.castSucc_succ i,
                iterated_face_map_castSucc, iterated_face_map_castSucc,
                iterated_degeneracy_map_castSucc]
              ext Z
              have h_app :=
                congrArg (fun k ↦ k.app Z)
                  (ih (i := i) (j := j) hji')
              simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp,
                Fin.castSucc_succ] using
                congrArg (fun k ↦ Y.map k) h_app

/-- Helper for Lemma 14.33.2: the adjacent face-degeneracy identities are exactly the two
assumptions involving `d` and `s`, propagated by whiskering. -/
private theorem iterated_adjacent_face_map_comp_degeneracy_map_castSucc
    {n : ℕ} {j : Fin (n + 1)}
    (hcast : s^⦅n, j⦆ ≫ d^⦅n, j.castSucc⦆ = 𝟙 X⦅n⦆)
    (hsucc : s^⦅n, j⦆ ≫ d^⦅n, j.succ⦆ = 𝟙 X⦅n⦆) :
    s^⦅n + 1, j.castSucc⦆ ≫ d^⦅n + 1, j.castSucc.castSucc⦆ = 𝟙 X⦅(n + 1)⦆ ∧
      s^⦅n + 1, j.castSucc⦆ ≫ d^⦅n + 1, j.succ.castSucc⦆ = 𝟙 X⦅(n + 1)⦆ := by
  constructor
  · -- All three maps are right-whiskered copies of the degree-`n` composite, so pointwise functoriality of
    -- `Y.map` transports the smaller identity.
    rw [iterated_degeneracy_map_castSucc, iterated_face_map_castSucc]
    ext Z
    have hcast_app := congrArg (fun k ↦ k.app Z) hcast
    simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp] using
      congrArg (fun k ↦ Y.map k) hcast_app
  · -- The same right-whiskering argument applies to the `j.succ` branch.
    rw [iterated_degeneracy_map_castSucc, iterated_face_map_castSucc]
    ext Z
    have hsucc_app := congrArg (fun k ↦ k.app Z) hsucc
    simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp,
      Fin.castSucc_succ] using
      congrArg (fun k ↦ Y.map k) hsucc_app

/-- Helper for Lemma 14.33.2: the adjacent face-degeneracy identities are exactly the two
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
      -- Split off the terminal branch; the remaining branch is just the right-whiskered induction
      -- hypothesis.
      refine Fin.lastCases ?_ ?_ j
      ·
          rcases terminal_adjacent_face_map_normalization (Y := Y) (d := d) (s := s) n with
            ⟨hcast, hsucc⟩
          have hwhisker_id : Functor.whiskerLeft (X⦅n⦆) (𝟙 (X⦅0⦆)) = 𝟙 (X⦅(n + 1)⦆) := by
            simp [iteratedEndofunctor]
          constructor
          · rw [hcast, hσδ₀]
            simpa [iteratedEndofunctor] using hwhisker_id
          · rw [hsucc, hσδ₁]
            simpa [iteratedEndofunctor] using hwhisker_id
      · intro j
        exact iterated_adjacent_face_map_comp_degeneracy_map_castSucc (Y := Y) (d := d)
          (s := s) (hcast := (ih j).1) (hsucc := (ih j).2)

/-- Helper for Lemma 14.33.2: the explicit degeneracy maps satisfy the simplicial
degeneracy-degeneracy relation. -/
private theorem terminal_degeneracy_comp_degeneracy_castSucc
    (n : ℕ) (i : Fin (n + 1)) :
    s^⦅n + 1, Fin.last (n + 1)⦆ ≫ s^⦅n + 2, i.castSucc.castSucc⦆ =
      s^⦅n + 1, i.castSucc⦆ ≫ s^⦅n + 2, Fin.last (n + 2)⦆ := by
  -- Expand the terminal and the two nonterminal degeneracies, then read the equality pointwise
  -- as naturality of `s` against the smaller degeneracy component.
  rw [iterated_degeneracy_map_last, iterated_degeneracy_map_castSucc,
    iterated_degeneracy_map_castSucc, iterated_degeneracy_map_last]
  ext Z
  simp [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app]
  simpa [Functor.comp_map] using (s.naturality (s^⦅n, i⦆.app Z)).symm

/-- Helper for Lemma 14.33.2: the equal-index terminal `σσ` composites are exactly left-whiskered
copies of the degree-`0` composites `s ≫ s₀` and `s ≫ s₁`. -/
private theorem terminal_equal_degeneracy_map_normalization
    (n : ℕ) :
    s^⦅n + 1, Fin.last (n + 1)⦆ ≫ s^⦅n + 2, (Fin.last (n + 1)).castSucc⦆ =
      Functor.whiskerLeft X⦅n⦆ (s^⦅0, 0⦆ ≫ s^⦅1, (0 : Fin 2)⦆) ∧
      s^⦅n + 1, Fin.last (n + 1)⦆ ≫ s^⦅n + 2, (Fin.last (n + 1)).succ⦆ =
        Functor.whiskerLeft X⦅n⦆ (s^⦅0, 0⦆ ≫ s^⦅1, (1 : Fin 2)⦆) := by
  constructor
  · -- The terminal/castSucc composite is the left-whiskered copy of the degree-`1` branch that
    -- inserts `s` in the first factor.
    have hfirst : s^⦅1, (0 : Fin 2)⦆ = Functor.whiskerRight s Y := by
      simpa using
        (iterated_degeneracy_map_castSucc (Y := Y) (s := s) (n := 0) (j := (0 : Fin 1)))
    rw [hfirst, iterated_degeneracy_map_last, iterated_degeneracy_map_castSucc]
    ext Z
    simp [NatTrans.comp_app, iteratedDegeneracyMap, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app]
    have hmap :
        Y.map (𝟙 (Y.obj (Y.obj (Y⦅n⦆.obj Z)))) =
          𝟙 (Y.obj (Y.obj (Y.obj (Y⦅n⦆.obj Z)))) := by
      simpa using (Y.map_id (Y.obj (Y.obj (Y⦅n⦆.obj Z))))
    have htail :
        s.app (Y⦅n⦆.obj Z) ≫ Y.map (s.app (Y⦅n⦆.obj Z)) ≫
            Y.map (𝟙 (Y.obj (Y.obj (Y⦅n⦆.obj Z)))) =
          s.app (Y⦅n⦆.obj Z) ≫ Y.map (s.app (Y⦅n⦆.obj Z)) ≫
            𝟙 (Y.obj (Y.obj (Y.obj (Y⦅n⦆.obj Z)))) := by
      simpa [hmap]
    have hid :
        s.app (Y⦅n⦆.obj Z) ≫ Y.map (s.app (Y⦅n⦆.obj Z)) ≫
            𝟙 (Y.obj (Y.obj (Y.obj (Y⦅n⦆.obj Z)))) =
          s.app (Y⦅n⦆.obj Z) ≫ Y.map (s.app (Y⦅n⦆.obj Z)) := by
      simpa [Functor.comp_obj] using
        (Category.comp_id
          (s.app (Y⦅n⦆.obj Z) ≫ Y.map (s.app (Y⦅n⦆.obj Z))))
    exact htail.trans hid
  · -- The terminal/terminal composite is the left-whiskered copy of the degree-`1` terminal
    -- degeneracy composite.
    have hlast : s^⦅1, (1 : Fin 2)⦆ = Functor.whiskerLeft Y s ≫ (Functor.associator Y Y Y).inv := by
      simpa [Fin.succ_last] using (iterated_degeneracy_map_last (Y := Y) (s := s) (n := 0))
    rw [hlast, iterated_degeneracy_map_last, Fin.succ_last, iterated_degeneracy_map_last]
    ext Z
    simp [NatTrans.comp_app, iteratedDegeneracyMap, Functor.whiskerLeft_app,
      Functor.associator_inv_app]
    simp [iteratedEndofunctor]

/-- Helper for Lemma 14.33.2: the explicit degeneracy maps satisfy the simplicial
degeneracy-degeneracy relation. -/
private theorem iterated_degeneracy_map_comp_degeneracy_map
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    s^⦅n, j⦆ ≫ s^⦅n + 1, i.castSucc⦆ = s^⦅n, i⦆ ≫ s^⦅n + 1, j.succ⦆ := by
  induction n with
  | zero =>
      -- In degree `0`, the only branch is the source hypothesis `hσσ`.
      fin_cases i
      fin_cases j
      simpa using hσσ
  | succ n ih =>
      -- Split first on the outer degeneracy index. The terminal branch separates into the strict
      -- terminal and equal-index terminal branches; the nonterminal branch is a right-whiskered
      -- smaller relation.
      cases j using Fin.lastCases with
      | last =>
          cases i using Fin.lastCases with
          | last =>
              rcases terminal_equal_degeneracy_map_normalization (Y := Y) (s := s) n with
                ⟨hcast, hsucc⟩
              rw [hcast, hsucc]
              simpa [iteratedEndofunctor] using congrArg (Functor.whiskerLeft X⦅n⦆) hσσ
          | cast i =>
              simpa [Fin.succ_last] using
                terminal_degeneracy_comp_degeneracy_castSucc (Y := Y) (s := s) (n := n) i
      | cast j =>
          cases i using Fin.lastCases with
          | last =>
              exfalso
              exact (not_le_of_gt (Fin.castSucc_lt_last j)) hij
          | cast i =>
              have hij' : i ≤ j := by
                simpa using hij
              rw [iterated_degeneracy_map_castSucc, iterated_degeneracy_map_castSucc,
                iterated_degeneracy_map_castSucc, ← Fin.castSucc_succ j,
                iterated_degeneracy_map_castSucc]
              ext Z
              have h_app :=
                congrArg (fun k ↦ k.app Z)
                  (ih (i := i) (j := j) hij')
              simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp,
                Fin.castSucc_succ] using
                congrArg (fun k ↦ Y.map k) h_app

/-- A simplicial object realizes the iterated endofunctor construction when its objects, face
maps, and degeneracy maps agree with the explicit formulas from `Example 14.33.1`. -/
structure IteratedEndofunctorRealization (U : SimplicialObject (C ⥤ C)) : Prop where
  /-- The degree-`n` term of `U` is `X⦅n⦆ = Y⦅n⦆`. -/
  obj_eq (n : ℕ) : U _⦋n⦌ = X⦅n⦆
  /-- The face maps of `U` are the explicit maps `d^⦅n, i⦆` obtained by inserting `d`. -/
  δ_eq {n : ℕ} (i : Fin (n + 2)) :
    eqToHom (obj_eq (n + 1)) ≫ d^⦅n, i⦆ =
      U.δ i ≫ eqToHom (obj_eq n)
  /-- The degeneracy maps of `U` are the explicit maps `s^⦅n, i⦆` obtained by inserting `s`. -/
  σ_eq {n : ℕ} (i : Fin (n + 1)) :
    eqToHom (obj_eq n) ≫ s^⦅n, i⦆ =
      U.σ i ≫ eqToHom (obj_eq (n + 1))

private theorem iteratedEndofunctorAugmentation_zeroSimplex_face_condition
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U) :
    U.δ 0 ≫ eqToHom (hU.obj_eq 0) ≫ d =
      U.δ 1 ≫ eqToHom (hU.obj_eq 0) ≫ d := by
  -- Transport both composites to the explicit degree-`0` face maps from `Example 14.33.1`.
  calc
    U.δ 0 ≫ eqToHom (hU.obj_eq 0) ≫ d =
        eqToHom (hU.obj_eq 1) ≫ d^⦅0, (0 : Fin 2)⦆ ≫ d := by
          calc
            U.δ 0 ≫ eqToHom (hU.obj_eq 0) ≫ d =
                (U.δ 0 ≫ eqToHom (hU.obj_eq 0)) ≫ d := by
                  rw [Category.assoc]
            _ = (eqToHom (hU.obj_eq 1) ≫ d^⦅0, (0 : Fin 2)⦆) ≫ d := by
                  exact congrArg (fun k ↦ k ≫ d) ((hU.δ_eq (n := 0) (0 : Fin 2)).symm)
            _ = eqToHom (hU.obj_eq 1) ≫ d^⦅0, (0 : Fin 2)⦆ ≫ d := by
                  rw [Category.assoc]
    _ = eqToHom (hU.obj_eq 1) ≫ d^⦅0, (1 : Fin 2)⦆ ≫ d := by
          simpa only [Category.assoc] using
            congrArg (fun k ↦ eqToHom (hU.obj_eq 1) ≫ k)
              (iterated_face_map_comp_counit_eq (Y := Y) (d := d))
    _ = U.δ 1 ≫ eqToHom (hU.obj_eq 0) ≫ d := by
          calc
            eqToHom (hU.obj_eq 1) ≫ d^⦅0, (1 : Fin 2)⦆ ≫ d =
                (eqToHom (hU.obj_eq 1) ≫ d^⦅0, (1 : Fin 2)⦆) ≫ d := by
                  rw [Category.assoc]
            _ = (U.δ 1 ≫ eqToHom (hU.obj_eq 0)) ≫ d := by
                  exact congrArg (fun k ↦ k ≫ d) (hU.δ_eq (n := 0) (1 : Fin 2))
            _ = U.δ 1 ≫ eqToHom (hU.obj_eq 0) ≫ d := by
                  rw [Category.assoc]

/-- Helper for Lemma 14.33.2: the explicit iterated face and degeneracy maps define the
presentation-side functor on `SimplexCategoryGenRel`, valued in the opposite endofunctor
category so that the simplicial identities match the generators-and-relations orientation. -/
private noncomputable def iteratedEndofunctor_source_functor
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆) :
    SimplexCategoryGenRel ⥤ (C ⥤ C)ᵒᵖ :=
  CategoryTheory.Quotient.lift _
    (Paths.lift
      { obj := fun n ↦ op X⦅n⦆
        map := fun f ↦
          match f with
          | @FreeSimplexQuiver.Hom.δ n i => (d^⦅n, i⦆).op
          | @FreeSimplexQuiver.Hom.σ n i => (s^⦅n, i⦆).op })
    (fun _ _ _ _ h ↦
      match h with
      | .δ_comp_δ H => by
          simpa using congrArg Quiver.Hom.op
            (iterated_face_map_comp_face_map (Y := Y) (d := d) _ H)
      | .δ_comp_σ_of_le H => by
          simpa using congrArg Quiver.Hom.op
            (iterated_face_map_comp_degeneracy_map_of_le
              (Y := Y) (d := d) (s := s) _ H)
      | .δ_comp_σ_self => by
          simpa using congrArg Quiver.Hom.op
            (iterated_adjacent_face_map_comp_degeneracy_map
              (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ _ _).1
      | .δ_comp_σ_succ => by
          simpa using congrArg Quiver.Hom.op
            (iterated_adjacent_face_map_comp_degeneracy_map
              (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ _ _).2
      | .δ_comp_σ_of_gt H => by
          simpa using congrArg Quiver.Hom.op
            (iterated_face_map_comp_degeneracy_map_of_gt
              (Y := Y) (d := d) (s := s) _ H)
      | .σ_comp_σ H => by
          simpa using congrArg Quiver.Hom.op
            (iterated_degeneracy_map_comp_degeneracy_map
              (Y := Y) (s := s) hσσ _ H))

/-- Helper for Lemma 14.33.2: the source presentation functor sends a face generator to the
corresponding explicit face map. -/
@[simp] private theorem iteratedEndofunctor_source_functor_map_delta
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    {n : ℕ} (i : Fin (n + 2)) :
    (iteratedEndofunctor_source_functor
      (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ).map (SimplexCategoryGenRel.δ i) =
      (d^⦅n, i⦆).op := by
  -- Unfold the generator abbreviation until the quotient-lift map lemma applies, then evaluate
  -- the single-edge path through `Paths.lift`.
  simpa [iteratedEndofunctor_source_functor, SimplexCategoryGenRel.δ] using
    (CategoryTheory.Quotient.lift_map_functor_map
      (r := FreeSimplexQuiver.homRel)
      (F := CategoryTheory.Paths.lift
        { obj := fun n ↦ op X⦅n⦆
          map := fun f ↦
            match f with
            | @FreeSimplexQuiver.Hom.δ n i => (d^⦅n, i⦆).op
            | @FreeSimplexQuiver.Hom.σ n i => (s^⦅n, i⦆).op })
      (H := fun _ _ _ _ h ↦
        match h with
        | .δ_comp_δ H => by
            simpa using congrArg Quiver.Hom.op
              (iterated_face_map_comp_face_map (Y := Y) (d := d) _ H)
        | .δ_comp_σ_of_le H => by
            simpa using congrArg Quiver.Hom.op
              (iterated_face_map_comp_degeneracy_map_of_le
                (Y := Y) (d := d) (s := s) _ H)
        | .δ_comp_σ_self => by
            simpa using congrArg Quiver.Hom.op
              (iterated_adjacent_face_map_comp_degeneracy_map
                (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ _ _).1
        | .δ_comp_σ_succ => by
            simpa using congrArg Quiver.Hom.op
              (iterated_adjacent_face_map_comp_degeneracy_map
                (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ _ _).2
        | .δ_comp_σ_of_gt H => by
            simpa using congrArg Quiver.Hom.op
              (iterated_face_map_comp_degeneracy_map_of_gt
                (Y := Y) (d := d) (s := s) _ H)
        | .σ_comp_σ H => by
            simpa using congrArg Quiver.Hom.op
              (iterated_degeneracy_map_comp_degeneracy_map
                (Y := Y) (s := s) hσσ _ H))
      ((CategoryTheory.Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.Hom.δ i)))

/-- Helper for Lemma 14.33.2: the source presentation functor sends a degeneracy generator to the
corresponding explicit degeneracy map. -/
@[simp] private theorem iteratedEndofunctor_source_functor_map_sigma
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    {n : ℕ} (i : Fin (n + 1)) :
    (iteratedEndofunctor_source_functor
      (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ).map (SimplexCategoryGenRel.σ i) =
      (s^⦅n, i⦆).op := by
  -- Unfold the generator abbreviation until the quotient-lift map lemma applies, then evaluate
  -- the single-edge path through `Paths.lift`.
  simpa [iteratedEndofunctor_source_functor, SimplexCategoryGenRel.σ] using
    (CategoryTheory.Quotient.lift_map_functor_map
      (r := FreeSimplexQuiver.homRel)
      (F := CategoryTheory.Paths.lift
        { obj := fun n ↦ op X⦅n⦆
          map := fun f ↦
            match f with
            | @FreeSimplexQuiver.Hom.δ n i => (d^⦅n, i⦆).op
            | @FreeSimplexQuiver.Hom.σ n i => (s^⦅n, i⦆).op })
      (H := fun _ _ _ _ h ↦
        match h with
        | .δ_comp_δ H => by
            simpa using congrArg Quiver.Hom.op
              (iterated_face_map_comp_face_map (Y := Y) (d := d) _ H)
        | .δ_comp_σ_of_le H => by
            simpa using congrArg Quiver.Hom.op
              (iterated_face_map_comp_degeneracy_map_of_le
                (Y := Y) (d := d) (s := s) _ H)
        | .δ_comp_σ_self => by
            simpa using congrArg Quiver.Hom.op
              (iterated_adjacent_face_map_comp_degeneracy_map
                (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ _ _).1
        | .δ_comp_σ_succ => by
            simpa using congrArg Quiver.Hom.op
              (iterated_adjacent_face_map_comp_degeneracy_map
                (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ _ _).2
        | .δ_comp_σ_of_gt H => by
            simpa using congrArg Quiver.Hom.op
              (iterated_face_map_comp_degeneracy_map_of_gt
                (Y := Y) (d := d) (s := s) _ H)
        | .σ_comp_σ H => by
            simpa using congrArg Quiver.Hom.op
              (iterated_degeneracy_map_comp_degeneracy_map
                (Y := Y) (s := s) hσσ _ H))
      ((CategoryTheory.Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.Hom.σ i)))

/-- Helper for Lemma 14.33.2: the source presentation functor has the expected skeletal objects. -/
@[simp] private theorem iteratedEndofunctor_source_functor_obj_mk
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (n : ℕ) :
    (iteratedEndofunctor_source_functor
      (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ).obj (SimplexCategoryGenRel.mk n) =
      op X⦅n⦆ := rfl

/-- Helper for Lemma 14.33.2: any simplicial morphism can be canonically rewritten between the
skeletal simplices `⦋len⦌`, which is the shape needed to apply
`SimplexCategoryGenRel.toSimplexCategory.preimage`. -/
private def simplexCategoryCanonicalHom
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    SimplexCategory.mk Δ'.unop.len ⟶ SimplexCategory.mk Δ.unop.len :=
  eqToHom (SimplexCategory.mk_len Δ'.unop) ≫ θ.unop ≫
    eqToHom (SimplexCategory.mk_len Δ.unop).symm

/-- Helper for Lemma 14.33.2: canonicalization does nothing to a coface generator. -/
private theorem simplexCategoryCanonicalHom_delta
    {n : ℕ} (i : Fin (n + 2)) :
    simplexCategoryCanonicalHom (θ := (SimplexCategory.δ i).op) = SimplexCategory.δ i := by
  simp [simplexCategoryCanonicalHom]

/-- Helper for Lemma 14.33.2: canonicalization does nothing to a codegeneracy generator. -/
private theorem simplexCategoryCanonicalHom_sigma
    {n : ℕ} (i : Fin (n + 1)) :
    simplexCategoryCanonicalHom (θ := (SimplexCategory.σ i).op) = SimplexCategory.σ i := by
  simp [simplexCategoryCanonicalHom]

/-- Helper for Lemma 14.33.2: canonicalization turns an identity in `SimplexCategoryᵒᵖ` into the
skeletal identity on the corresponding `[n]`. -/
private theorem simplexCategoryCanonicalHom_id
    (Δ : SimplexCategoryᵒᵖ) :
    simplexCategoryCanonicalHom (θ := 𝟙 Δ) = 𝟙 (SimplexCategory.mk Δ.unop.len) := by
  cases Δ using Opposite.rec
  simp [simplexCategoryCanonicalHom]

/-- Helper for Lemma 14.33.2: canonicalization reverses composition exactly as required for the
opposite simplicial indexing category. -/
private theorem simplexCategoryCanonicalHom_comp
    {Δ₀ Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (θ₁ : Δ₀ ⟶ Δ₁) (θ₂ : Δ₁ ⟶ Δ₂) :
    simplexCategoryCanonicalHom (θ := θ₁ ≫ θ₂) =
      simplexCategoryCanonicalHom (θ := θ₂) ≫ simplexCategoryCanonicalHom (θ := θ₁) := by
  cases Δ₀ using Opposite.rec
  cases Δ₁ using Opposite.rec
  cases Δ₂ using Opposite.rec
  simp [simplexCategoryCanonicalHom]

/-- Helper for Lemma 14.33.2: the canonicalized simplex morphism has a chosen lift through the
generators-and-relations presentation. -/
private noncomputable def simplexCategoryCanonicalPreimage
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    SimplexCategoryGenRel.mk Δ'.unop.len ⟶ SimplexCategoryGenRel.mk Δ.unop.len :=
  SimplexCategoryGenRel.toSimplexCategory.preimage (simplexCategoryCanonicalHom θ)

/-- Helper for Lemma 14.33.2: the chosen preimage of an identity simplex morphism is the identity
presentation morphism. -/
private theorem simplexCategoryCanonicalPreimage_id
    (Δ : SimplexCategoryᵒᵖ) :
    simplexCategoryCanonicalPreimage (θ := 𝟙 Δ) =
      𝟙 (SimplexCategoryGenRel.mk Δ.unop.len) := by
  apply SimplexCategoryGenRel.toSimplexCategory.map_injective
  simp [simplexCategoryCanonicalPreimage, simplexCategoryCanonicalHom_id]

/-- Helper for Lemma 14.33.2: the chosen preimages compose in the same order as the canonicalized
simplex morphisms. -/
private theorem simplexCategoryCanonicalPreimage_comp
    {Δ₀ Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (θ₁ : Δ₀ ⟶ Δ₁) (θ₂ : Δ₁ ⟶ Δ₂) :
    simplexCategoryCanonicalPreimage (θ := θ₁ ≫ θ₂) =
      simplexCategoryCanonicalPreimage (θ := θ₂) ≫
        simplexCategoryCanonicalPreimage (θ := θ₁) := by
  apply SimplexCategoryGenRel.toSimplexCategory.map_injective
  simp [simplexCategoryCanonicalPreimage, simplexCategoryCanonicalHom_comp]

/-- Helper for Lemma 14.33.2: canonical preimages of coface generators are the corresponding
presentation generators. -/
private theorem simplexCategoryCanonicalPreimage_delta
    {n : ℕ} (i : Fin (n + 2)) :
    simplexCategoryCanonicalPreimage (θ := (SimplexCategory.δ i).op) =
      SimplexCategoryGenRel.δ i := by
  apply SimplexCategoryGenRel.toSimplexCategory.map_injective
  simp [simplexCategoryCanonicalPreimage, simplexCategoryCanonicalHom_delta]

/-- Helper for Lemma 14.33.2: canonical preimages of codegeneracy generators are the corresponding
presentation generators. -/
private theorem simplexCategoryCanonicalPreimage_sigma
    {n : ℕ} (i : Fin (n + 1)) :
    simplexCategoryCanonicalPreimage (θ := (SimplexCategory.σ i).op) =
      SimplexCategoryGenRel.σ i := by
  apply SimplexCategoryGenRel.toSimplexCategory.map_injective
  simp [simplexCategoryCanonicalPreimage, simplexCategoryCanonicalHom_sigma]

/-- Helper for Lemma 14.33.2: the canonical simplicial object is obtained by evaluating the
presentation functor on canonical preimages of simplex morphisms. -/
private noncomputable def iteratedEndofunctor_simplicial_object
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆) :
    SimplicialObject (C ⥤ C) :=
  { obj := fun Δ ↦ X⦅Δ.unop.len⦆
    map := fun θ ↦
      ((iteratedEndofunctor_source_functor
        (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ).map
          (simplexCategoryCanonicalPreimage θ)).unop
    map_id := by
      intro Δ
      rw [simplexCategoryCanonicalPreimage_id]
      simpa using congrArg Quiver.Hom.unop
        ((iteratedEndofunctor_source_functor
          (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ).map_id
            (SimplexCategoryGenRel.mk Δ.unop.len))
    map_comp := by
      intro Δ₀ Δ₁ Δ₂ θ₁ θ₂
      rw [simplexCategoryCanonicalPreimage_comp]
      simpa using congrArg Quiver.Hom.unop
        ((iteratedEndofunctor_source_functor
          (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ).map_comp
            (simplexCategoryCanonicalPreimage θ₂)
            (simplexCategoryCanonicalPreimage θ₁)) }

/-- Helper for Lemma 14.33.2: the canonical simplicial object satisfies the explicit realization
equations from `Example 14.33.1`. -/
private theorem iteratedEndofunctor_simplicial_object_realization :
    ∀ (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
      (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
      (hσσ :
        s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
          s^⦅0, 0⦆ ≫ s^⦅1, 1⦆),
    IteratedEndofunctorRealization d s
      (iteratedEndofunctor_simplicial_object
        (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ) := by
  intro hσδ₀ hσδ₁ hσσ
  refine
    { obj_eq := fun _ ↦ rfl
      δ_eq := ?_
      σ_eq := ?_ }
  · intro n i
    simp [iteratedEndofunctor_simplicial_object, simplexCategoryCanonicalPreimage_delta,
      SimplicialObject.δ_def]
  · intro n i
    simp [iteratedEndofunctor_simplicial_object, simplexCategoryCanonicalPreimage_sigma,
      SimplicialObject.σ_def]

/-- Helper for Lemma 14.33.2: any realization carries every presentation morphism to the
corresponding explicit iterated map after transporting along the realization object equalities. -/
private theorem iteratedEndofunctorRealization_map_eq_source
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U)
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    U.map (SimplexCategoryGenRel.toSimplexCategory.map f).op ≫ eqToHom (hU.obj_eq a.len) =
      eqToHom (hU.obj_eq b.len) ≫
        ((iteratedEndofunctor_source_functor
          (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ).map f).unop := by
  let F :=
    iteratedEndofunctor_source_functor
      (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ
  refine SimplexCategoryGenRel.hom_induction
    (P := fun {x y} g ↦
      U.map (SimplexCategoryGenRel.toSimplexCategory.map g).op ≫ eqToHom (hU.obj_eq x.len) =
        eqToHom (hU.obj_eq y.len) ≫ (F.map g).unop)
    ?_ ?_ ?_ f
  · intro n
    simp [F]
  · intro n m u i hu
    simp only [SimplexCategoryGenRel.toSimplexCategory_map_δ, Functor.map_comp, op_comp,
      Category.assoc]
    rw [hu]
    simpa [F, SimplicialObject.δ_def, Functor.map_comp, Category.assoc] using
      (congrArg (fun k ↦ k ≫ (F.map u).unop) (hU.δ_eq (n := m) i)).symm
  · intro n m u i hu
    simp only [SimplexCategoryGenRel.toSimplexCategory_map_σ, Functor.map_comp, op_comp,
      Category.assoc]
    rw [hu]
    simpa [F, SimplicialObject.σ_def, Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ k ≫ (F.map u).unop) ((hU.σ_eq (n := m) i).symm)

-- Proof sketch: the relations
-- `1_Y = (d ⋆ 1_Y) ∘ s = (1_Y ⋆ d) ∘ s` and `(s ⋆ 1) ∘ s = (1 ⋆ s) ∘ s` are precisely the degree
-- `0` and degree `1` simplicial identities for the explicit face and degeneracy maps from
-- `Example 14.33.1`. Hence those maps extend uniquely to a simplicial object with the displayed
-- realization equations.
/-- Lemma 14.33.2 (1): if the degree-`0` degeneracy composed with the two degree-`0` face maps is
the identity and the two degree-`1` degeneracy composites agree, then the iterated endofunctor
data from `Example 14.33.1` is realized by a unique simplicial object of endofunctors of `C`. -/
theorem iteratedEndofunctor_exists_unique_simplicial_object
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆) :
    ∃! U : SimplicialObject (C ⥤ C),
      IteratedEndofunctorRealization d s U := by
  refine ⟨iteratedEndofunctor_simplicial_object
      (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ,
    iteratedEndofunctor_simplicial_object_realization
      (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ, ?_⟩
  intro U hU
  refine Functor.ext (fun Δ ↦ hU.obj_eq Δ.unop.len) ?_
  intro Δ Δ' θ
  cases Δ using Opposite.rec
  rename_i Δ₀
  cases Δ' using Opposite.rec
  rename_i Δ₁
  let f : SimplexCategoryGenRel.mk Δ₁.len ⟶ SimplexCategoryGenRel.mk Δ₀.len :=
    SimplexCategoryGenRel.toSimplexCategory.preimage θ.unop
  have hf : SimplexCategoryGenRel.toSimplexCategory.map f = θ.unop := by
    simpa [f] using SimplexCategoryGenRel.toSimplexCategory.map_preimage θ.unop
  have hmap :
      U.map θ ≫ eqToHom (hU.obj_eq Δ₁.len) =
        eqToHom (hU.obj_eq Δ₀.len) ≫
          ((iteratedEndofunctor_source_functor
            (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ).map f).unop := by
    simpa [hf] using
      (iteratedEndofunctorRealization_map_eq_source
        (Y := Y) (d := d) (s := s) hσδ₀ hσδ₁ hσσ hU f)
  apply (cancel_mono (eqToHom (hU.obj_eq Δ₁.len))).1
  simp only [Category.assoc]
  rw [hmap]
  simp [iteratedEndofunctor_simplicial_object, simplexCategoryCanonicalPreimage,
    simplexCategoryCanonicalHom, f, Category.assoc]

/-- The canonical simplicial object realizing the iterated endofunctor data of
`Example 14.33.1`. -/
noncomputable def iteratedEndofunctorResolution
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆) :
    SimplicialObject (C ⥤ C) :=
  Classical.choose <|
    ExistsUnique.exists
      (iteratedEndofunctor_exists_unique_simplicial_object d s hσδ₀ hσδ₁ hσσ)

/-- The canonical iterated endofunctor resolution satisfies the realization equations. -/
theorem iteratedEndofunctorResolution_realization
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆) :
    IteratedEndofunctorRealization d s
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ) :=
  Classical.choose_spec <|
    ExistsUnique.exists
      (iteratedEndofunctor_exists_unique_simplicial_object d s hσδ₀ hσδ₁ hσσ)

/-- Any simplicial realization of the iterated endofunctor data is equal to the canonical one. -/
theorem iteratedEndofunctorResolution_eq
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U) :
    U = iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ :=
  ExistsUnique.unique
    (iteratedEndofunctor_exists_unique_simplicial_object d s hσδ₀ hσδ₁ hσσ)
    hU
    (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ)

/-- Lemma 14.33.2 (2): for any simplicial realization of the iterated endofunctor data from
`Example 14.33.1`, the map `d : Y ⟶ 𝟭 C` induces the canonical augmentation to the constant
simplicial object on the identity endofunctor. -/
def iteratedEndofunctorAugmentation
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U) :
    U ⟶ (const (C ⥤ C)).obj (𝟭 C) :=
  (augmentHomEquivZeroSimplex U (𝟭 C)).symm
    ⟨eqToHom (hU.obj_eq 0) ≫ d,
      iteratedEndofunctorAugmentation_zeroSimplex_face_condition d s hU⟩

-- Proof sketch: `iteratedEndofunctorAugmentation` is the canonical owner
-- `SimplicialObject.augment` applied to the degree-`0` map `eqToHom (hU.obj_eq 0) ≫ d`.
/-- The augmentation induced by `d` has the expected degree-`0` component. -/
@[simp]
theorem iteratedEndofunctorAugmentation_app_zero
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U) :
    (iteratedEndofunctorAugmentation d s hU).app (op ⦋0⦌) =
      eqToHom (hU.obj_eq 0) ≫ d := by
  simpa [iteratedEndofunctorAugmentation] using
    augmentHomEquivZeroSimplex_symm_apply_zero U (𝟭 C)
      ⟨eqToHom (hU.obj_eq 0) ≫ d,
        iteratedEndofunctorAugmentation_zeroSimplex_face_condition d s hU⟩

end

end CategoryTheory
