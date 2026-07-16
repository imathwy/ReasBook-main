import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_8_1
import stacks_proof.stacks_project.Chap13.Lemma_13_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open ComplexShape
open HomologicalComplex

universe v u

namespace CategoryTheory

namespace ComposableArrows

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

section

/-- Helper for Lemma 13.9.15: the object function of the row obtained by appending a final object
`B` to `T₀`. -/
abbrev extended_replacement_obj {n : ℕ} (T₀ : ComposableArrows (Comp(𝒜)) n) (B : Comp(𝒜)) :
    Fin (n + 2) → Comp(𝒜) :=
  Fin.lastCases B (fun i ↦ T₀.obj i)

/-- Helper for Lemma 13.9.15: the source object of an inherited successor map in the extended row
identifies with the corresponding old source object. -/
lemma extended_replacement_old_source_eq {n : ℕ} (T₀ : ComposableArrows (Comp(𝒜)) n)
    (B : Comp(𝒜)) (i : Fin n) :
    extended_replacement_obj T₀ B i.castSucc.castSucc = T₀.obj i.castSucc := by
  rw [extended_replacement_obj]
  simpa using
    (Fin.lastCases_castSucc
      (n := n + 1)
      (motive := fun _ : Fin (n + 2) ↦ Comp(𝒜))
      (last := B)
      (cast := fun j ↦ T₀.obj j)
      i.castSucc)

/-- Helper for Lemma 13.9.15: the target object of an inherited successor map in the extended row
identifies with the corresponding old target object. -/
lemma extended_replacement_old_target_eq {n : ℕ} (T₀ : ComposableArrows (Comp(𝒜)) n)
    (B : Comp(𝒜)) (i : Fin n) :
    extended_replacement_obj T₀ B i.castSucc.succ = T₀.obj i.succ := by
  -- Proof comment: the successor of an inherited index is still on the inherited branch of
  -- `Fin.lastCases`, after rewriting `i.castSucc.succ` as `i.succ.castSucc`.
  rw [Fin.succ_castSucc, extended_replacement_obj]
  simpa using
    (Fin.lastCases_castSucc
      (n := n + 1)
      (motive := fun _ : Fin (n + 2) ↦ Comp(𝒜))
      (last := B)
      (cast := fun j ↦ T₀.obj j)
      i.succ)

/-- Helper for Lemma 13.9.15: the rightmost object of `T₀` is its value at the last index. -/
lemma right_obj_last_eq {n : ℕ} (T₀ : ComposableArrows (Comp(𝒜)) n) :
    T₀.obj (Fin.last n) = T₀.right := by
  rfl

/-- Helper for Lemma 13.9.15: the source object of the final successor map in the extended row is
the last old object `T₀.right`. -/
lemma extended_replacement_last_source_eq {n : ℕ} (T₀ : ComposableArrows (Comp(𝒜)) n)
    (B : Comp(𝒜)) :
    extended_replacement_obj T₀ B (Fin.last n).castSucc = T₀.obj (Fin.last n) := by
  simp [extended_replacement_obj]

/-- Helper for Lemma 13.9.15: the target object of the final successor map in the extended row is
the appended object `B`. -/
lemma extended_replacement_last_target_eq {n : ℕ} (T₀ : ComposableArrows (Comp(𝒜)) n)
    (B : Comp(𝒜)) :
    extended_replacement_obj T₀ B (Fin.last n).succ = B := by
  simp

/-- Helper for Lemma 13.9.15: the old successor maps can be reused as the non-final successor maps
of the extended row, after the canonical object identifications. -/
def extended_replacement_old_map {n : ℕ} (T₀ : ComposableArrows (Comp(𝒜)) n)
    (B : Comp(𝒜)) (i : Fin n) :
    (extended_replacement_obj T₀ B i.castSucc.castSucc) ⟶
      (extended_replacement_obj T₀ B i.castSucc.succ) :=
  eqToHom (extended_replacement_old_source_eq T₀ B i) ≫
    T₀.map' i.1 (i.1 + 1) ≫
      eqToHom (extended_replacement_old_target_eq T₀ B i).symm

/-- Helper for Lemma 13.9.15: the final successor map of the extended row is the appended map
`u : T₀.right ⟶ B`, transported across the canonical object identifications. -/
def extended_replacement_last_map {n : ℕ} (T₀ : ComposableArrows (Comp(𝒜)) n)
    (B : Comp(𝒜)) (u : T₀.right ⟶ B) :
    (extended_replacement_obj T₀ B (Fin.last n).castSucc) ⟶
      (extended_replacement_obj T₀ B (Fin.last n).succ) :=
  eqToHom (extended_replacement_last_source_eq T₀ B) ≫
    eqToHom (right_obj_last_eq T₀) ≫
    u ≫
      eqToHom (extended_replacement_last_target_eq T₀ B).symm

/-- Helper for Lemma 13.9.15: append a final object `B` and a final arrow
`u : T₀.right ⟶ B` to a composable row `T₀`. -/
noncomputable def extended_replacement_row {n : ℕ}
    (T₀ : ComposableArrows (Comp(𝒜)) n) (B : Comp(𝒜)) (u : T₀.right ⟶ B) :
    ComposableArrows (Comp(𝒜)) (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (extended_replacement_obj T₀ B)
    (Fin.lastCases (extended_replacement_last_map T₀ B u)
      (fun i ↦ extended_replacement_old_map T₀ B i))

/-- Helper for Lemma 13.9.15: the extended row agrees with the old row on the initial segment. -/
@[simp] lemma extended_replacement_row_obj_castSucc {n : ℕ}
    (T₀ : ComposableArrows (Comp(𝒜)) n) (B : Comp(𝒜)) (u : T₀.right ⟶ B) (i : Fin (n + 1)) :
    (extended_replacement_row T₀ B u).obj i.castSucc = T₀.obj i := by
  simp [extended_replacement_row]

/-- Helper for Lemma 13.9.15: the final object of the extended row is the appended object `B`. -/
@[simp] lemma extended_replacement_row_obj_last {n : ℕ}
    (T₀ : ComposableArrows (Comp(𝒜)) n) (B : Comp(𝒜)) (u : T₀.right ⟶ B) :
    (extended_replacement_row T₀ B u).obj (Fin.last (n + 1)) = B := by
  simp [extended_replacement_row]

/-- Helper for Lemma 13.9.15: the last horizontal map of the extended row is the appended map
`u`, after the canonical endpoint identifications. -/
@[simp] lemma extended_replacement_row_map_last {n : ℕ}
    (T₀ : ComposableArrows (Comp(𝒜)) n) (B : Comp(𝒜)) (u : T₀.right ⟶ B) :
    (extended_replacement_row T₀ B u).map' n (n + 1) =
      extended_replacement_last_map T₀ B u := by
  unfold extended_replacement_row
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ (i := n) (hi := Nat.lt_succ_self n)]
  simp only [Fin.lastCases_last]

/-- Helper for Lemma 13.9.15: each inherited horizontal map of the extended row is the
corresponding old map from `T₀`, after the canonical endpoint identifications. -/
@[simp] lemma extended_replacement_row_map_castSucc {n : ℕ}
    (T₀ : ComposableArrows (Comp(𝒜)) n) (B : Comp(𝒜)) (u : T₀.right ⟶ B) (j : Fin n) :
    (extended_replacement_row T₀ B u).map' j.1 (j.1 + 1) =
      extended_replacement_old_map T₀ B j := by
  unfold extended_replacement_row
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ (i := j.1)
    (hi := Nat.lt_trans j.2 (Nat.lt_succ_self n))]
  simp only [Fin.lastCases_castSucc]

/-- Helper for Lemma 13.9.15: the inherited comparison maps may be viewed as component maps on the
initial segment of the extended ladder. -/
@[simp] lemma extended_replacement_cast_target_eq {n : ℕ} {S : ComposableArrows (Comp(𝒜)) (n + 1)}
    (i : Fin (n + 1)) :
    S.δlast.obj i = S.obj i.castSucc := by
  rfl

/-- Helper for Lemma 13.9.15: the inherited comparison maps may be viewed as component maps on the
initial segment of the extended ladder. -/
def extended_replacement_cast_component {n : ℕ} {T₀ : ComposableArrows (Comp(𝒜)) n}
    {S : ComposableArrows (Comp(𝒜)) (n + 1)} {B : Comp(𝒜)} {u : T₀.right ⟶ B}
    (φ₀ : T₀ ⟶ S.δlast) (i : Fin (n + 1)) :
    (extended_replacement_row T₀ B u).obj i.castSucc ⟶ S.obj i.castSucc :=
  eqToHom (extended_replacement_row_obj_castSucc T₀ B u i) ≫
    φ₀.app i ≫
      eqToHom (extended_replacement_cast_target_eq (S := S) i).symm

/-- Helper for Lemma 13.9.15: the final comparison map of the extended ladder is the chosen
projection `π : B ⟶ S.right`. -/
@[simp] lemma extended_replacement_last_component_target_eq
    {n : ℕ} {S : ComposableArrows (Comp(𝒜)) (n + 1)} :
    S.right = S.obj (Fin.last (n + 1)) := by
  rfl

/-- Helper for Lemma 13.9.15: the final comparison map of the extended ladder is the chosen
projection `π : B ⟶ S.right`. -/
def extended_replacement_last_component {n : ℕ} {T₀ : ComposableArrows (Comp(𝒜)) n}
    {S : ComposableArrows (Comp(𝒜)) (n + 1)} {B : Comp(𝒜)} {u : T₀.right ⟶ B}
    (π : B ⟶ S.right) :
    (extended_replacement_row T₀ B u).obj (Fin.last (n + 1)) ⟶ S.obj (Fin.last (n + 1)) :=
  eqToHom (extended_replacement_row_obj_last T₀ B u) ≫
    π ≫
      eqToHom (extended_replacement_last_component_target_eq (S := S)).symm

/-- Helper for Lemma 13.9.15: transporting a homotopy equivalence across the inherited endpoint
identifications yields a homotopy equivalence on the extended row. -/
lemma extended_replacement_cast_component_homotopyEquivalences
    {n : ℕ} {T₀ : ComposableArrows (Comp(𝒜)) n}
    {S : ComposableArrows (Comp(𝒜)) (n + 1)} {B : Comp(𝒜)} {u : T₀.right ⟶ B}
    (φ₀ : T₀ ⟶ S.δlast) (i : Fin (n + 1))
    (h : homotopyEquivalences 𝒜 (up ℤ) (φ₀.app i)) :
    homotopyEquivalences 𝒜 (up ℤ) (extended_replacement_cast_component (u := u) φ₀ i) := by
  rcases h with ⟨e, hEq⟩
  refine ⟨(HomotopyEquiv.ofIso (eqToIso (extended_replacement_row_obj_castSucc T₀ B u i))).trans
      (e.trans (HomotopyEquiv.ofIso (eqToIso (extended_replacement_cast_target_eq (S := S) i)).symm)),
    ?_⟩
  simpa [extended_replacement_cast_component, hEq]

/-- Helper for Lemma 13.9.15: transporting a homotopy equivalence across the final endpoint
identifications yields a homotopy equivalence on the extended row. -/
lemma extended_replacement_last_component_homotopyEquivalences
    {n : ℕ} {T₀ : ComposableArrows (Comp(𝒜)) n}
    {S : ComposableArrows (Comp(𝒜)) (n + 1)} {B : Comp(𝒜)} {u : T₀.right ⟶ B}
    (π : B ⟶ S.right) (h : homotopyEquivalences 𝒜 (up ℤ) π) :
    homotopyEquivalences 𝒜 (up ℤ) (extended_replacement_last_component (u := u) π) := by
  rcases h with ⟨e, hEq⟩
  refine ⟨(HomotopyEquiv.ofIso (eqToIso (extended_replacement_row_obj_last T₀ B u))).trans
      (e.trans
        (HomotopyEquiv.ofIso (eqToIso (extended_replacement_last_component_target_eq (S := S)).symm))),
    ?_⟩
  simpa [extended_replacement_last_component, hEq]


/-- Helper for Lemma 13.9.15: the vertical comparison maps on the extended replacement row are the
old comparison maps on the initial segment and the chosen projection on the last object. -/
def extended_replacement_components {n : ℕ} {T₀ : ComposableArrows (Comp(𝒜)) n}
    {S : ComposableArrows (Comp(𝒜)) (n + 1)} {B : Comp(𝒜)} {u : T₀.right ⟶ B}
    (φ₀ : T₀ ⟶ S.δlast) (π : B ⟶ S.right) :
    ∀ i : Fin (n + 2), (extended_replacement_row T₀ B u).obj i ⟶ S.obj i :=
  Fin.lastCases (extended_replacement_last_component (u := u) π)
    (fun i ↦ extended_replacement_cast_component (u := u) φ₀ i)

/-- Helper for Lemma 13.9.15: the extended component family restricts to the inherited component
maps on the initial segment. -/
@[simp] lemma extended_replacement_components_castSucc {n : ℕ}
    {T₀ : ComposableArrows (Comp(𝒜)) n} {S : ComposableArrows (Comp(𝒜)) (n + 1)}
    {B : Comp(𝒜)} {u : T₀.right ⟶ B} (φ₀ : T₀ ⟶ S.δlast) (π : B ⟶ S.right)
    (i : Fin (n + 1)) :
    extended_replacement_components (u := u) φ₀ π i.castSucc =
      extended_replacement_cast_component (u := u) φ₀ i := by
  simp [extended_replacement_components]

/-- Helper for Lemma 13.9.15: the final component of the extended ladder is the chosen
projection `π`. -/
@[simp] lemma extended_replacement_components_last {n : ℕ}
    {T₀ : ComposableArrows (Comp(𝒜)) n} {S : ComposableArrows (Comp(𝒜)) (n + 1)}
    {B : Comp(𝒜)} {u : T₀.right ⟶ B} (φ₀ : T₀ ⟶ S.δlast) (π : B ⟶ S.right) :
    extended_replacement_components (u := u) φ₀ π (Fin.last (n + 1)) =
      extended_replacement_last_component (u := u) π := by
  simp [extended_replacement_components]

/-- Helper for Lemma 13.9.15: once the new last square commutes, the component family on the
extended row is a morphism of composable rows. -/
lemma extended_replacement_components_natural {n : ℕ}
    {T₀ : ComposableArrows (Comp(𝒜)) n} {S : ComposableArrows (Comp(𝒜)) (n + 1)}
    (φ₀ : T₀ ⟶ S.δlast) {B : Comp(𝒜)} {u : T₀.right ⟶ B} {π : B ⟶ S.right}
    (hlast : u ≫ π = φ₀.app (Fin.last n) ≫ S.map' n (n + 1)) :
    ∀ (i : ℕ) (hi : i < n + 1),
      (extended_replacement_row T₀ B u).map' i (i + 1) ≫
          extended_replacement_components (u := u) φ₀ π ⟨i + 1, by omega⟩ =
        extended_replacement_components (u := u) φ₀ π ⟨i, by omega⟩ ≫
          S.map' i (i + 1) := by
  intro i hi
  obtain hlt | hEq := lt_or_eq_of_le (Nat.le_of_lt_succ hi)
  · let j : Fin n := ⟨i, hlt⟩
    have hiSrc : i < n + 2 := by omega
    have hiTgt : i + 1 < n + 2 := by omega
    have hsrc : (⟨i, hiSrc⟩ : Fin (n + 2)) = j.castSucc.castSucc := by
      ext
      rfl
    have htgt : (⟨i + 1, hiTgt⟩ : Fin (n + 2)) = j.succ.castSucc := by
      ext
      rfl
    -- Proof comment: on a non-final square, both comparison maps come from the inherited row and
    -- the square reduces to the already-known naturality of `φ₀`.
    have hmap :
        (extended_replacement_row T₀ B u).map' i (i + 1) =
          extended_replacement_old_map T₀ B j := by
      simpa [j] using extended_replacement_row_map_castSucc T₀ B u j
    rw [hmap]
    rw [hsrc, htgt]
    rw [extended_replacement_components_castSucc (u := u) φ₀ π j.castSucc]
    rw [extended_replacement_components_castSucc (u := u) φ₀ π j.succ]
    dsimp [extended_replacement_old_map, extended_replacement_cast_component]
    cases extended_replacement_old_source_eq T₀ B j
    cases extended_replacement_old_target_eq T₀ B j
    cases extended_replacement_row_obj_castSucc T₀ B u j.castSucc
    cases extended_replacement_row_obj_castSucc T₀ B u j
    simpa [j, Category.assoc] using
      (ComposableArrows.naturality' φ₀ i (i + 1)
        (hij := Nat.le_succ i)
        (hj := Nat.succ_le_of_lt hlt))
  · subst i
    have hsrc : (⟨n, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := by
      ext
      simp
    have htgt : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by
      ext
      simp
    -- Proof comment: on the final square, the inherited component on the source and the chosen
    -- projection on the target reduce the claim exactly to `hlast`.
    have hsrcComp :
        extended_replacement_components (u := u) φ₀ π ⟨n, by omega⟩ =
          extended_replacement_components (u := u) φ₀ π (Fin.last n).castSucc := by
      cases hsrc
      rfl
    have htgtComp :
        extended_replacement_components (u := u) φ₀ π ⟨n + 1, by omega⟩ =
          extended_replacement_components (u := u) φ₀ π (Fin.last (n + 1)) := by
      cases htgt
      rfl
    rw [hsrcComp, htgtComp]
    rw [extended_replacement_row_map_last T₀ B u]
    rw [extended_replacement_components_last (u := u) φ₀ π]
    rw [extended_replacement_components_castSucc (u := u) φ₀ π (Fin.last n)]
    dsimp [extended_replacement_last_map, extended_replacement_last_component,
      extended_replacement_cast_component]
    cases extended_replacement_last_source_eq T₀ B
    cases right_obj_last_eq T₀
    cases extended_replacement_last_target_eq T₀ B
    cases extended_replacement_row_obj_last T₀ B u
    cases extended_replacement_last_component_target_eq (S := S)
    cases extended_replacement_row_obj_castSucc T₀ B u (Fin.last n)
    cases extended_replacement_cast_target_eq (S := S) (Fin.last n)
    simpa [Category.assoc] using hlast

variable [HasBinaryBiproducts 𝒜]

/-- Helper for Lemma 13.9.15: the projection from the canonical split-mono factorization object to
its target complex is a homotopy equivalence. -/
lemma splitMono_factorization_projection_homotopy_equivalence {K L : Comp(𝒜)} :
    homotopyEquivalences 𝒜 (up ℤ)
      (biprod.fst : CochainComplex.splitMonoFactorizationObj K L ⟶ L) := by
  exact ⟨CochainComplex.splitMonoFactorizationProjectionHomotopyEquiv K L, rfl⟩

/- Domain-style sampling for Lemma 13.9.15:
- primary domain: finite composable rows of cochain complexes and commutative ladders whose
  horizontal maps are termwise split monomorphisms and whose vertical maps are homotopy
  equivalences;
- sampled owner declarations:
  `CategoryTheory.ComposableArrows`,
  `CategoryTheory.ComposableArrows.arrow`,
  `CochainComplex.splitMono_factorization_through_biproduct_mappingCone_id`,
  `HomologicalComplex.homotopyEquivalences`;
- best owner abstraction: the ladder data already lives canonically as a morphism
  `φ : T ⟶ S` in `ComposableArrows`, and the horizontal edges are canonically indexed by `Fin n`;
  the split-mono and homotopy-equivalence conditions are theorem-side properties expressed
  componentwise by the canonical owners `IsSplitMono` and `homotopyEquivalences`; the boundedness
  clauses likewise belong directly to the existing owners `CochainComplex.plus`,
  `CochainComplex.minus`, and `CochainComplex.bounded`;
- source/core/bridge triage:
  `source-facing`: existence of a replacement row with split-monomorphic horizontal maps and
    homotopy-equivalent vertical comparison maps;
  `core/canonical`: `ComposableArrows`, `IsSplitMono`, `homotopyEquivalences`, and the
    cochain-complex boundedness owners;
  `bridge/view`: the componentwise predicates imposed on the existing ladder morphism `φ`.
- primitive data: only the replacement row `T` and comparison morphism `φ : T ⟶ S`;
- derived API: the componentwise split-mono, homotopy-equivalence, and boundedness-preservation
  clauses.

This theorem should therefore quantify directly over the canonical owner `φ : T ⟶ S` instead of
introducing a separate wrapper class for these theorem-side properties.
-/

-- Proof sketch: argue by induction on the length of the composable sequence. The case of a single
-- object is trivial. For the induction step, first construct the replacement up to the penultimate
-- complex, then apply Lemma 13.9.6 to the composite from the last replacement complex to the final
-- complex to extend the diagram by one more term. The boundedness assertions are propagated at
-- each step using the corresponding boundedness clauses in Lemma 13.9.6.
/-- Lemma 13.9.15: every finite composable sequence of cochain complexes in an additive category
admits a commutative diagram from another sequence whose successive maps are termwise split
injections and whose vertical maps to the original sequence are homotopy equivalences; moreover,
if the original sequence is termwise bounded below, bounded above, or bounded, then the replacing
sequence has the same property termwise. -/
@[stacks 014M]
theorem exists_splitMono_homotopyReplacement
    {n : ℕ} (S : ComposableArrows (Comp(𝒜)) n) :
    ∃ (T : ComposableArrows (Comp(𝒜)) n) (φ : T ⟶ S),
      (∀ i : Fin n, ∀ k : ℤ, IsSplitMono ((T.map' i.1 (i.1 + 1)).f k)) ∧
      (∀ i : Fin (n + 1), homotopyEquivalences 𝒜 (up ℤ) (φ.app i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.plus 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.plus 𝒜 (T.obj i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.minus 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.minus 𝒜 (T.obj i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 (T.obj i)) := by
  induction n with
  | zero =>
      -- Proof comment: a row with no arrows already satisfies the conclusion, using the identity
      -- ladder morphism.
      refine ⟨S, 𝟙 S, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        refine ⟨HomotopyEquiv.refl (S.obj i), rfl⟩
      · intro hS i
        simpa using hS i
      · intro hS i
        simpa using hS i
      · intro hS i
        simpa using hS i
  | succ n ih =>
      -- Route correction: keep the textbook induction on `S.δlast`; the only new ingredient is
      -- the split-mono factorization of the last composite.
      obtain ⟨T₀, φ₀, hsplit₀, hhom₀, hplus₀, hminus₀, hbounded₀⟩ := ih S.δlast
      let α : T₀.right ⟶ S.right := φ₀.app (Fin.last n) ≫ S.map' n (n + 1)
      let B : Comp(𝒜) := CochainComplex.splitMonoFactorizationObj T₀.right S.right
      let u : T₀.right ⟶ B := CochainComplex.splitMonoFactorizationι α
      let π : B ⟶ S.right := biprod.fst
      have hlast : u ≫ π = φ₀.app (Fin.last n) ≫ S.map' n (n + 1) := by
        -- Proof comment: the chosen last projection is exactly the projection appearing in the
        -- canonical split-mono factorization of `α`.
        simpa only [α, u, π] using CochainComplex.splitMonoFactorizationι_comp_fst α
      let T : ComposableArrows (Comp(𝒜)) (n + 1) := extended_replacement_row T₀ B u
      let φ : T ⟶ S :=
        ComposableArrows.homMk
          (extended_replacement_components (u := u) φ₀ π)
          (extended_replacement_components_natural (φ₀ := φ₀) (B := B) (u := u) (π := π) hlast)
      refine ⟨T, φ, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · intro k
          -- Proof comment: the final horizontal map is the canonical split mono from Lemma 13.9.6.
          rw [show T.map' (↑(Fin.last n)) (↑(Fin.last n) + 1) =
              extended_replacement_last_map T₀ B u by
              simpa [T] using extended_replacement_row_map_last T₀ B u]
          dsimp [extended_replacement_last_map]
          cases extended_replacement_last_source_eq T₀ B
          cases right_obj_last_eq T₀
          cases extended_replacement_last_target_eq T₀ B
          simpa [T, B, u, α] using
            CochainComplex.splitMonoFactorizationι_f_isSplitMono α k
        · intro j k
          -- Proof comment: every inherited horizontal map is exactly the old one from `T₀`.
          rw [show T.map' (↑j.castSucc) (↑j.castSucc + 1) =
              extended_replacement_old_map T₀ B j by
              simpa [T, Fin.succ_castSucc] using
                extended_replacement_row_map_castSucc T₀ B u j]
          dsimp [extended_replacement_old_map]
          cases extended_replacement_old_source_eq T₀ B j
          cases extended_replacement_old_target_eq T₀ B j
          simpa [Category.assoc] using hsplit₀ j k
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · -- Proof comment: the last vertical map is the projection from the factorization object,
          -- which is a homotopy equivalence by Lemma 13.9.6.
          rw [show φ.app (Fin.last (n + 1)) = extended_replacement_last_component (u := u) π by
            simp [φ, extended_replacement_components]]
          exact extended_replacement_last_component_homotopyEquivalences (u := u) π <|
            (splitMono_factorization_projection_homotopy_equivalence
              (K := T₀.right) (L := S.right))
        · intro j
          -- Proof comment: inherited vertical maps are the old ones from `φ₀`, transported across
          -- definitional equalities in the extended row.
          rw [show φ.app j.castSucc = extended_replacement_cast_component (u := u) φ₀ j by
            simp [φ, extended_replacement_components]]
          exact extended_replacement_cast_component_homotopyEquivalences (u := u) φ₀ j (hhom₀ j)
      · intro hS
        have hS₀ : ∀ i : Fin (n + 1), CochainComplex.plus 𝒜 ((S.δlast).obj i) := by
          intro i
          exact hS i.castSucc
        have hT₀ : ∀ i : Fin (n + 1), CochainComplex.plus 𝒜 (T₀.obj i) := hplus₀ hS₀
        intro i
        refine Fin.lastCases ?_ ?_ i
        · -- Proof comment: bounded-below-ness of the new last object follows from the canonical
          -- factorization object boundedness lemma.
          have hTlast : CochainComplex.plus 𝒜 T₀.right := by
            simpa [right_obj_last_eq] using hT₀ (Fin.last n)
          have hSlast : CochainComplex.plus 𝒜 S.right := by
            simpa using hS (Fin.last (n + 1))
          simpa [T, B] using CochainComplex.splitMonoFactorizationObj_plus hTlast hSlast
        · intro j
          -- Proof comment: on the inherited segment, the new row reuses the old objects of `T₀`.
          simpa [T] using hT₀ j
      · intro hS
        have hS₀ : ∀ i : Fin (n + 1), CochainComplex.minus 𝒜 ((S.δlast).obj i) := by
          intro i
          exact hS i.castSucc
        have hT₀ : ∀ i : Fin (n + 1), CochainComplex.minus 𝒜 (T₀.obj i) := hminus₀ hS₀
        intro i
        refine Fin.lastCases ?_ ?_ i
        · -- Proof comment: bounded-above-ness of the new last object comes from the corresponding
          -- factorization-object lemma.
          have hTlast : CochainComplex.minus 𝒜 T₀.right := by
            simpa [right_obj_last_eq] using hT₀ (Fin.last n)
          have hSlast : CochainComplex.minus 𝒜 S.right := by
            simpa using hS (Fin.last (n + 1))
          simpa [T, B] using CochainComplex.splitMonoFactorizationObj_boundedAbove hTlast hSlast
        · intro j
          -- Proof comment: inherited objects preserve bounded-above-ness from `T₀`.
          simpa [T] using hT₀ j
      · intro hS
        have hS₀ : ∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 ((S.δlast).obj i) := by
          intro i
          exact hS i.castSucc
        have hT₀ : ∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 (T₀.obj i) := hbounded₀ hS₀
        intro i
        refine Fin.lastCases ?_ ?_ i
        · -- Proof comment: boundedness of the final object combines the bounded-below and
          -- bounded-above transfer on the split-mono factorization object.
          have hTlast : CochainComplex.bounded 𝒜 T₀.right := by
            simpa [right_obj_last_eq] using hT₀ (Fin.last n)
          have hSlast : CochainComplex.bounded 𝒜 S.right := by
            simpa using hS (Fin.last (n + 1))
          simpa [T, B] using CochainComplex.splitMonoFactorizationObj_bounded hTlast hSlast
        · intro j
          -- Proof comment: inherited objects preserve boundedness from the induction hypothesis.
          simpa [T] using hT₀ j

end

end ComposableArrows

end CategoryTheory
