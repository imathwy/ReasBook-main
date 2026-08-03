module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.UnitInterval

public section

universe u

/-- Helper for Theorem 70.1: a finite square grid subordinate to a two-member
open cover along a fixed-endpoint path homotopy. -/
structure OpenUnionHomotopyGrid
    {X : Type u} [TopologicalSpace X] {U V : Set X} {x y : X}
    {p q : Path x y} (F : Path.Homotopy p q) where
  n : ℕ
  point : Fin (n + 2) → unitInterval
  start : point 0 = 0
  finish : point (Fin.last (n + 1)) = 1
  monotone : Monotone point
  side : Fin (n + 1) → Fin (n + 1) → Bool
  covered : ∀ j i, Set.MapsTo F
    (Set.Icc (point j.castSucc) (point j.succ) ×ˢ
      Set.Icc (point i.castSucc) (point i.succ))
    (if side j i then V else U)

/-- Helper for Theorem 70.1: compactness supplies a finite square grid
subordinate to an open two-member cover along a path homotopy. -/
lemma exists_openUnionHomotopyGrid
    {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {x y : X} {p q : Path x y} (F : Path.Homotopy p q) :
    Nonempty (OpenUnionHomotopyGrid (U := U) (V := V) F) := by
  classical
  -- Pull the cover back through the homotopy to the compact parameter square.
  let c : Bool → Set (unitInterval × unitInterval) := fun
    | false => F ⁻¹' U
    | true => F ⁻¹' V
  have hcOpen : ∀ choice, IsOpen (c choice) := by
    intro choice
    cases choice
    · exact hU.preimage F.continuous
    · exact hV.preimage F.continuous
  have hcCover : Set.univ ⊆ ⋃ choice, c choice := by
    intro z _
    have hFz : F z ∈ U ∪ V := by
      rw [hcover]
      exact Set.mem_univ (F z)
    cases hFz with
    | inl hFzU => exact Set.mem_iUnion.mpr ⟨false, hFzU⟩
    | inr hFzV => exact Set.mem_iUnion.mpr ⟨true, hFzV⟩
  -- Truncate the common monotone sequence after an index where it is one.
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htCovered⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hcOpen hcCover
  have hmpositive : 0 < m := by
    by_contra hmnot
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmnot
    subst m
    have htone : t 0 = 1 := hm 0 le_rfl
    rw [ht0] at htone
    exact zero_ne_one htone
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpositive)
  let point : Fin (n + 2) → unitInterval := fun i ↦ t i
  choose side hside using fun j : Fin (n + 1) ↦
    fun i : Fin (n + 1) ↦ htCovered j i
  have hcells : ∀ j i, Set.MapsTo F
      (Set.Icc (point j.castSucc) (point j.succ) ×ˢ
        Set.Icc (point i.castSucc) (point i.succ))
      (if side j i then V else U) := by
    intro j i z hz
    have hzCover : z ∈ c (side j i) := hside j i hz
    cases hchoice : side j i
    · simpa only [c, hchoice, Bool.false_eq_true, if_false,
        Set.mem_preimage] using hzCover
    · simpa only [c, hchoice, Bool.true_eq, if_true,
        Set.mem_preimage] using hzCover
  -- Store the finite truncation and all cell labels in the grid interface.
  refine ⟨⟨n, point, ht0, ?_, ?_, side, hcells⟩⟩
  · exact hm (n + 1) le_rfl
  · intro i j hij
    exact htmono hij
