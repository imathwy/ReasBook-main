import Mathlib
import StacksProject_2024.Chap19.«19_2_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open scoped CategoryTheory

/- Domain-style sampling for Example 19.2.2:
- primary domain: quotient sets in `Type`, sequential colimits, and the represented-Hom
  comparison `colimit.post B (coyoneda.obj (op A))`;
- sampled owner declarations:
  `Quotient.map`,
  `Functor.ofSequence`,
  `colimit.post`,
  `colimit_post_coyoneda_ι_app`;
- best owner abstractions:
  the source-facing quotient stage `collapsedInitialSegment n` and the canonical comparison map
  `colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ))`;
- primitive data: the quotient relation collapsing the initial segment `{0, …, n}`;
- derived API: the transition maps induced by monotonicity of the collapsed segment and the
  comparison map from `19.2.0.1`.

Source/core/bridge triage:
- `source-facing`: the sequential quotient system `B_{n + 1}` and the noninjectivity example;
- `core/canonical`: `colimit.post`;
- `bridge/view`: the monotonicity maps `B_{n + 1} → B_{m + 1}` assembling the sequential system.

The raw owner name `collapsedInitialSegment` is already short and stable on this small local API
surface, so no extra `B_n` notation is introduced here.
-/

/-- The equivalence relation on `ℕ` that identifies all elements of the initial segment
`{0, …, n}` and leaves larger elements distinct. -/
def collapsedInitialSegmentSetoid (n : ℕ) : Setoid ℕ where
  r a b := a = b ∨ a ≤ n ∧ b ≤ n
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with rfl | ⟨ha, hb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hb, ha⟩
    · intro a b c hab hbc
      rcases hab with rfl | ⟨ha, hb⟩
      · exact hbc
      · rcases hbc with rfl | ⟨_, hc⟩
        · exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩

/-- The quotient set obtained by collapsing the first `n + 1` natural numbers to a single point.
This is the Lean stage indexed by `n`, corresponding to the textbook family `B_{n + 1}`. -/
abbrev collapsedInitialSegment (n : ℕ) : Type :=
  Quotient (collapsedInitialSegmentSetoid n)

/-- For `n ≤ m`, the quotient map `B_{n + 1} → B_{m + 1}` induced by collapsing a larger initial
segment. -/
def collapsedInitialSegmentMap {n m : ℕ} (h : n ≤ m) :
    collapsedInitialSegment n → collapsedInitialSegment m :=
  Quotient.map id <| by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨Nat.le_trans ha h, Nat.le_trans hb h⟩

/-- The sequential system `B_{n + 1}` of collapsed initial segments of the natural numbers. -/
def collapsedInitialSegmentDiagram : ℕ ⥤ Type :=
  Functor.ofSequence fun n ↦ collapsedInitialSegmentMap (Nat.le_succ n)

/-- Helper for Example 19.2.2: every transition map in the collapsed-initial-segment diagram
still sends the class of `a` to the class of `a`. -/
lemma collapsedInitialSegmentDiagram_map_mk {n m : ℕ} (h : n ≤ m) (a : ℕ) :
    collapsedInitialSegmentDiagram.map (homOfLE h)
      (Quotient.mk (collapsedInitialSegmentSetoid n) a) =
        (Quotient.mk (collapsedInitialSegmentSetoid m) a : collapsedInitialSegment m) := by
  -- Reduce an arbitrary later-stage map to repeated successor maps.
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero h
      subst hn
      simp [collapsedInitialSegmentDiagram]
  | succ m ih =>
      by_cases hnm : n = m + 1
      · subst hnm
        simp [collapsedInitialSegmentDiagram]
      · have hnm' : n ≤ m := Nat.le_of_lt_succ (lt_of_le_of_ne h hnm)
        have hcomp : homOfLE h = homOfLE hnm' ≫ homOfLE (Nat.le_succ m) := by
          simpa [homOfLE_comp] using
            (Subsingleton.elim (homOfLE h) (homOfLE hnm' ≫ homOfLE (Nat.le_succ m)))
        have hsucc :
            collapsedInitialSegmentDiagram.map (homOfLE (Nat.le_succ m)) =
              collapsedInitialSegmentMap (Nat.le_succ m) := by
          simpa [collapsedInitialSegmentDiagram] using
            (Functor.ofSequence_map_homOfLE_succ
              (f := fun n ↦ collapsedInitialSegmentMap (Nat.le_succ n)) m)
        -- First move to stage `m`, then take the final successor step.
        rw [hcomp, Functor.map_comp]
        rw [hsucc]
        rw [types_comp_apply]
        rw [ih hnm']
        rfl

/-- Helper for Example 19.2.2: every stage representative becomes the collapsed base class after
passing to a sufficiently large later stage. -/
lemma collapsedInitialSegment_representative_eq_base_in_colimit (n a : ℕ) :
    colimit.ι collapsedInitialSegmentDiagram n
        (Quotient.mk (collapsedInitialSegmentSetoid n) a) =
      colimit.ι collapsedInitialSegmentDiagram (max n a)
        (Quotient.mk (collapsedInitialSegmentSetoid (max n a)) 0) := by
  -- Move the representative to the later stage `max n a`, where both `a` and `0` lie in the
  -- collapsed initial segment.
  refine Types.colimit_sound (F := collapsedInitialSegmentDiagram)
    (f := homOfLE (Nat.le_max_left n a)) ?_
  rw [collapsedInitialSegmentDiagram_map_mk (Nat.le_max_left n a) a]
  apply Quotient.sound
  right
  exact ⟨Nat.le_max_right n a, Nat.zero_le _⟩

/-- Helper for Example 19.2.2: the collapsed base class represents the same colimit point at
every stage. -/
lemma collapsedInitialSegment_base_eq_origin_in_colimit (n : ℕ) :
    colimit.ι collapsedInitialSegmentDiagram n
        (Quotient.mk (collapsedInitialSegmentSetoid n) 0) =
      colimit.ι collapsedInitialSegmentDiagram 0
        (Quotient.mk (collapsedInitialSegmentSetoid 0) 0) := by
  -- The stage-`0` base class maps to the base class at every later stage.
  symm
  refine Types.colimit_sound (F := collapsedInitialSegmentDiagram)
    (f := homOfLE (Nat.zero_le n)) ?_
  simpa using collapsedInitialSegmentDiagram_map_mk (Nat.zero_le n) 0

-- Proof sketch: every class in some stage eventually maps to the collapsed point, so in the
-- filtered colimit all representatives become equal to that distinguished class.
/-- Any two points in the colimit of the collapsed-initial-segment system are equal. -/
theorem collapsedInitialSegmentDiagram_colimit_subsingleton :
    Subsingleton (colimit collapsedInitialSegmentDiagram) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨i, xi, rfl⟩ := Types.jointly_surjective' x
  obtain ⟨j, yj, rfl⟩ := Types.jointly_surjective' y
  -- Reduce both colimit points to representatives in their quotient stages.
  refine Quotient.inductionOn xi ?_
  intro a
  refine Quotient.inductionOn yj ?_
  intro b
  -- Compare both representatives with the single global base point.
  calc
    colimit.ι collapsedInitialSegmentDiagram i
        (Quotient.mk (collapsedInitialSegmentSetoid i) a) =
      colimit.ι collapsedInitialSegmentDiagram (max i a)
        (Quotient.mk (collapsedInitialSegmentSetoid (max i a)) 0) :=
      collapsedInitialSegment_representative_eq_base_in_colimit i a
    _ =
      colimit.ι collapsedInitialSegmentDiagram 0
        (Quotient.mk (collapsedInitialSegmentSetoid 0) 0) :=
      collapsedInitialSegment_base_eq_origin_in_colimit (max i a)
    _ =
      colimit.ι collapsedInitialSegmentDiagram (max j b)
        (Quotient.mk (collapsedInitialSegmentSetoid (max j b)) 0) := by
          symm
          exact collapsedInitialSegment_base_eq_origin_in_colimit (max j b)
    _ =
      colimit.ι collapsedInitialSegmentDiagram j
        (Quotient.mk (collapsedInitialSegmentSetoid j) b) :=
      (collapsedInitialSegment_representative_eq_base_in_colimit j b).symm

/-- Helper for Example 19.2.2: the stagewise quotient projection `ℕ → B_{n + 1}`. -/
def collapsedInitialSegmentProjection (n : ℕ) : ℕ → collapsedInitialSegment n :=
  fun t ↦ Quotient.mk (collapsedInitialSegmentSetoid n) t

/-- Helper for Example 19.2.2: the stagewise constant map to the collapsed base class. -/
def collapsedInitialSegmentBaseConstant (n : ℕ) : ℕ → collapsedInitialSegment n :=
  fun _ ↦ Quotient.mk (collapsedInitialSegmentSetoid n) 0

/-- Helper for Example 19.2.2: transporting the quotient projection to a later stage still gives
the quotient projection at that later stage. -/
lemma collapsedInitialSegmentProjection_natural {n m : ℕ} (h : n ≤ m) :
    (collapsedInitialSegmentDiagram ⋙ coyoneda.obj (op ℕ)).map (homOfLE h)
      (collapsedInitialSegmentProjection n) =
    collapsedInitialSegmentProjection m := by
  -- The represented-Hom functor acts pointwise on these stagewise maps.
  funext t
  simpa [collapsedInitialSegmentProjection] using collapsedInitialSegmentDiagram_map_mk h t

/-- Helper for Example 19.2.2: transporting the constant collapsed map to a later stage still
gives the constant collapsed map. -/
lemma collapsedInitialSegmentBaseConstant_natural {n m : ℕ} (h : n ≤ m) :
    (collapsedInitialSegmentDiagram ⋙ coyoneda.obj (op ℕ)).map (homOfLE h)
      (collapsedInitialSegmentBaseConstant n) =
    collapsedInitialSegmentBaseConstant m := by
  -- The base class remains the base class after every transition map.
  funext t
  simpa [collapsedInitialSegmentBaseConstant] using collapsedInitialSegmentDiagram_map_mk h 0

/-- Helper for Example 19.2.2: equality in a sequential colimit of types can be checked after
mapping to a common later stage. -/
lemma sequential_colimit_eq_at_common_stage {F : ℕ ⥤ Type _} {i j : ℕ}
    {x : F.obj i} {y : F.obj j} (h : colimit.ι F i x = colimit.ι F j y) :
    ∃ k, ∃ hi : i ≤ k, ∃ hj : j ≤ k,
      F.map (homOfLE hi) x = F.map (homOfLE hj) y := by
  -- This is the standard filtered-colimit equality criterion specialized to `ℕ`.
  rcases (Types.FilteredColimit.colimit_eq_iff (F := F)).1 h with ⟨k, f, g, hfg⟩
  exact ⟨k, leOfHom f, leOfHom g, by simpa [homOfLE_leOfHom] using hfg⟩

/-- Helper for Example 19.2.2: at each stage, the quotient projection `ℕ → B_{m + 1}` is not
the constant map to the collapsed base class. -/
lemma collapsedInitialSegment_projection_ne_constant (m : ℕ) :
    collapsedInitialSegmentProjection m ≠ collapsedInitialSegmentBaseConstant m := by
  intro h
  have hEval := congrFun h (m + 1)
  have hClasses :
      (Quotient.mk (collapsedInitialSegmentSetoid m) (m + 1) : collapsedInitialSegment m) =
        Quotient.mk (collapsedInitialSegmentSetoid m) 0 := hEval
  have hRel : (collapsedInitialSegmentSetoid m).r (m + 1) 0 := Quotient.exact hClasses
  rcases hRel with hEq | ⟨hm, _⟩
  · exact Nat.succ_ne_zero m hEq
  · exact Nat.not_succ_le_self m hm

-- Proof sketch: compare the classes in `colim_n Mor(ℕ, B_{n + 1})` represented by the quotient
-- projections `ℕ → B_{n + 1}` and by the constant maps to the collapsed class. They remain
-- distinct in the Hom-colimit, but after composing with the colimit cocone they both become the
-- unique map from `ℕ` to the one-point colimit of the `B_{n + 1}`.
/-- Example 19.2.2: for the sequential system `B_{n + 1}` obtained by collapsing the first
`n + 1` natural numbers, the canonical comparison map
`colim_n Mor(ℕ, B_{n + 1}) → Mor(ℕ, colim_n B_{n + 1})` is not injective. -/
theorem collapsedInitialSegment_hom_colimit_comparison_not_injective :
    ¬ Function.Injective
      (colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ))) := by
  intro hInjective
  have hImages :
      (colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ)))
          (colimit.ι (collapsedInitialSegmentDiagram ⋙ coyoneda.obj (op ℕ)) 0
            (collapsedInitialSegmentProjection 0)) =
        (colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ)))
          (colimit.ι (collapsedInitialSegmentDiagram ⋙ coyoneda.obj (op ℕ)) 0
            (collapsedInitialSegmentBaseConstant 0)) := by
    letI : Subsingleton (colimit collapsedInitialSegmentDiagram) :=
      collapsedInitialSegmentDiagram_colimit_subsingleton
    -- After applying the comparison map, both representatives become the unique function to the
    -- one-point colimit.
    rw [show
      (colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ)))
          (colimit.ι (collapsedInitialSegmentDiagram ⋙ coyoneda.obj (op ℕ)) 0
            (collapsedInitialSegmentProjection 0)) =
        collapsedInitialSegmentProjection 0 ≫ colimit.ι collapsedInitialSegmentDiagram 0 by
          simpa using colimit_post_coyoneda_ι_app ℕ collapsedInitialSegmentDiagram 0
            (collapsedInitialSegmentProjection 0)]
    rw [show
      (colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ)))
          (colimit.ι (collapsedInitialSegmentDiagram ⋙ coyoneda.obj (op ℕ)) 0
            (collapsedInitialSegmentBaseConstant 0)) =
        collapsedInitialSegmentBaseConstant 0 ≫ colimit.ι collapsedInitialSegmentDiagram 0 by
          simpa using colimit_post_coyoneda_ι_app ℕ collapsedInitialSegmentDiagram 0
            (collapsedInitialSegmentBaseConstant 0)]
    funext t
    exact Subsingleton.elim _ _
  have hClasses :
      colimit.ι (collapsedInitialSegmentDiagram ⋙ coyoneda.obj (op ℕ)) 0
          (collapsedInitialSegmentProjection 0) =
        colimit.ι (collapsedInitialSegmentDiagram ⋙ coyoneda.obj (op ℕ)) 0
          (collapsedInitialSegmentBaseConstant 0) :=
    hInjective hImages
  rcases sequential_colimit_eq_at_common_stage
      (F := collapsedInitialSegmentDiagram ⋙ coyoneda.obj (op ℕ)) hClasses with
    ⟨k, hkProj, hkConst, hkEq⟩
  have hStage :
      collapsedInitialSegmentProjection k = collapsedInitialSegmentBaseConstant k := by
    -- Equality in the Hom-colimit forces equality after transport to one common stage.
    simpa [collapsedInitialSegmentProjection_natural hkProj,
      collapsedInitialSegmentBaseConstant_natural hkConst] using hkEq
  exact collapsedInitialSegment_projection_ne_constant k hStage
