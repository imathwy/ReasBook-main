import Mathlib
import stacks_proof.stacks_project.Chap19.«19_2_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

/-- The transition map between consecutive finite initial segments of `ℕ`, modeled by
`Fin (n + 1) ⟶ Fin (n + 2)`. -/
def nat_initial_segment_map (n : ℕ) : Fin (n + 1) ⟶ Fin (n + 2) :=
  Fin.castSucc

/-- The sequential diagram of finite initial segments of `ℕ` in the category of sets. -/
def nat_initial_segment_diagram : ℕ ⥤ Type :=
  Functor.ofSequence nat_initial_segment_map

/-- The map `ℕ → colimit nat_initial_segment_diagram` sending `n` to the class of the top element
of the `n`-th finite initial segment. -/
def nat_initial_segment_colimit_map : ℕ → colimit nat_initial_segment_diagram :=
  fun n ↦ colimit.ι nat_initial_segment_diagram n (Fin.last n)

/-- Helper for Example 19.2.1: the successor inclusion of finite initial segments preserves the
underlying natural number. -/
lemma nat_initial_segment_map_comp_val (n : ℕ) :
    nat_initial_segment_map n ≫ (fun i : Fin (n + 2) ↦ i.1) =
      (fun i : Fin (n + 1) ↦ i.1) := by
  rfl

/-- Helper for Example 19.2.1: the stagewise maps `Fin (n + 1) → ℕ` form a cocone over the
sequential diagram of finite initial segments. -/
lemma nat_initial_segment_nat_cocone_naturality (n : ℕ) :
    nat_initial_segment_diagram.map (homOfLE (Nat.le_succ n)) ≫
        (fun i : Fin (n + 2) ↦ i.1) =
      (fun i : Fin (n + 1) ↦ i.1) := by
  -- Reduce the diagram map to the defining successor inclusion.
  simpa [nat_initial_segment_diagram, Functor.ofSequence_map_homOfLE_succ] using
    nat_initial_segment_map_comp_val n

/-- Helper for Example 19.2.1: the colimit of the finite initial segments carries the canonical
numeric value descending the stagewise inclusions. -/
noncomputable def nat_initial_segment_nat_cocone : Cocone nat_initial_segment_diagram where
  pt := ℕ
  ι := NatTrans.ofSequence
    (fun n ↦ fun i : Fin (n + 1) ↦ i.1)
    nat_initial_segment_nat_cocone_naturality

/-- Helper for Example 19.2.1: the sequential colimit of the finite initial segments maps
canonically to `ℕ` by recording the underlying value of a stage representative. -/
noncomputable def nat_initial_segment_colimit_to_nat :
    colimit nat_initial_segment_diagram ⟶ ℕ :=
  colimit.desc nat_initial_segment_diagram nat_initial_segment_nat_cocone

/-- Helper for Example 19.2.1: the canonical map from the colimit to `ℕ` evaluates a stage
representative by its underlying natural number. -/
lemma nat_initial_segment_colimit_to_nat_apply (n : ℕ) (i : Fin (n + 1)) :
    nat_initial_segment_colimit_to_nat (colimit.ι nat_initial_segment_diagram n i) = i.1 := by
  -- Apply the universal property of the colimit to the explicit cocone to `ℕ`.
  simpa [nat_initial_segment_colimit_to_nat, nat_initial_segment_nat_cocone] using
    congrFun (colimit.ι_desc nat_initial_segment_nat_cocone n) i

/-- Helper for Example 19.2.1: the distinguished point represented by `Fin.last n` maps to the
number `n`. -/
lemma nat_initial_segment_colimit_map_value (n : ℕ) :
    nat_initial_segment_colimit_to_nat (nat_initial_segment_colimit_map n) = n := by
  -- The top element of `Fin (n + 1)` has value `n`.
  simpa [nat_initial_segment_colimit_map] using
    nat_initial_segment_colimit_to_nat_apply n (Fin.last n)

/-- The canonical map from `ℕ` to the colimit of the finite initial segments does not factor
through any single stage `Fin (m + 1)`. -/
-- Proof sketch: if such a factorization through `Fin (m + 1)` existed, the image of every natural
-- number in the colimit would already come from that finite stage, contradicting the fact that the
-- elements represented by `Fin.last n` require arbitrarily large stages.
theorem nat_initial_segment_colimit_map_not_factor_through_stage (m : ℕ) :
    ¬ ∃ f : ℕ → Fin (m + 1),
        nat_initial_segment_colimit_map = fun n ↦ colimit.ι nat_initial_segment_diagram m (f n) :=
  by
    rintro ⟨f, hf⟩
    have hvalue : m + 1 = (f (m + 1)).1 := by
      -- Compare the two descriptions of the `(m + 1)`st point after descending to `ℕ`.
      have hpoint := congrFun hf (m + 1)
      have hnat := congrArg nat_initial_segment_colimit_to_nat hpoint
      simpa [nat_initial_segment_colimit_map_value, nat_initial_segment_colimit_to_nat_apply] using
        hnat
    have hlt : (f (m + 1)).1 < m + 1 := (f (m + 1)).is_lt
    have hself : (f (m + 1)).1 < (f (m + 1)).1 := by
      simpa [← hvalue] using hlt
    exact Nat.lt_irrefl _ hself

/-- Helper for Example 19.2.1: every element of the colimit of the stagewise Hom-sets is
represented by a map to one fixed finite stage. -/
lemma hom_comparison_has_bounded_stage
    (x : colimit (nat_initial_segment_diagram ⋙ coyoneda.obj (op ℕ))) :
    ∃ m, ∃ g : ℕ → Fin (m + 1),
      (colimit.post nat_initial_segment_diagram (coyoneda.obj (op ℕ))) x =
        fun n ↦ colimit.ι nat_initial_segment_diagram m (g n) := by
  obtain ⟨m, g, rfl⟩ := Types.jointly_surjective' x
  refine ⟨m, g, ?_⟩
  -- The comparison map sends a stage representative to its postcomposition with the colimit leg.
  simpa using
    (colimit_post_coyoneda_ι_app ℕ nat_initial_segment_diagram m g)

/-- Example 19.2.1: in the category of sets, for the sequential system of finite initial
segments of `ℕ` modeled by `Fin (n + 1)`, the canonical comparison map from the colimit of the
stagewise Hom-sets `ℕ → Fin (n + 1)` to the Hom-set `ℕ → colimit nat_initial_segment_diagram` is
not surjective. -/
-- Proof sketch: apply `nat_initial_segment_colimit_map_not_factor_through_stage` to the map
-- `nat_initial_segment_colimit_map`. Any element in the image of the comparison map comes from a
-- single stage, so this specific map cannot lie in the image.
theorem nat_initial_segment_hom_colimit_comparison_not_surjective :
    ¬ Function.Surjective
      (colimit.post nat_initial_segment_diagram (coyoneda.obj (op ℕ))) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj nat_initial_segment_colimit_map
  rcases hom_comparison_has_bounded_stage x with ⟨m, g, hg⟩
  -- Any map in the image of the Hom-colimit comparison already factors through one stage.
  have hfactor :
      nat_initial_segment_colimit_map =
        fun n ↦ colimit.ι nat_initial_segment_diagram m (g n) := by
    exact hx.symm.trans hg
  exact nat_initial_segment_colimit_map_not_factor_through_stage m ⟨g, hfactor⟩
