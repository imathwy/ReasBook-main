module

public import Topology_Munkres_2000.Book.Definition_50_7.GeneralPosition
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

public section

namespace Set

open Affine

/-- Helper for Remark 50.1: a finset with at most two points is affinely independent
when indexed by its subtype. -/
private lemma affineIndependent_coe_of_card_le_two
    {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]
    (s : Finset P) (hcard : s.card ≤ 2) :
    AffineIndependent k (fun x : s ↦ (x : P)) := by
  -- With at most one point, the subtype itself is subsingleton.
  by_cases hsmall : s.card ≤ 1
  · letI : Subsingleton s := Finset.card_le_one_iff_subsingleton_coe.mp hsmall
    exact affineIndependent_of_subsingleton k _
  -- In the remaining case, reindex the two distinct subtype elements by `Fin 2`.
  have htwo : s.card = 2 := by
    omega
  let e : s ≃ Fin 2 := s.equivFinOfCardEq htwo
  let p : Fin 2 → P := fun i ↦ (e.symm i : P)
  have hp_ne : p 0 ≠ p 1 := by
    intro hp
    have heq : e.symm 0 = e.symm 1 := Subtype.ext hp
    exact Fin.zero_ne_one (e.symm.injective heq)
  have hp_pair : p = ![p 0, p 1] := by
    funext i
    fin_cases i
    · rfl
    · rfl
  have hp_independent : AffineIndependent k p := by
    rw [hp_pair]
    exact affineIndependent_of_ne k hp_ne
  have hreindexed : AffineIndependent k (p ∘ e) :=
    (affineIndependent_equiv e).mpr hp_independent
  have hcomp : p ∘ e = fun x : s ↦ (x : P) := by
    funext x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  rw [hcomp] at hreindexed
  exact hreindexed

/-- Helper for Remark 50.1: three subtype-indexed points are affinely independent
exactly when their underlying finset is not collinear. -/
private lemma affineIndependent_coe_iff_not_collinear_of_card_eq_three
    {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]
    (s : Finset P) (hcard : s.card = 3) :
    AffineIndependent k (fun x : s ↦ (x : P)) ↔ ¬ Collinear k (s : Set P) := by
  -- The range of the subtype coercion is precisely the set represented by the finset.
  have hrange : Set.range (fun x : s ↦ (x : P)) = (s : Set P) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have htypecard : Fintype.card s = 1 + 2 := by
    simpa only [Fintype.card_coe] using hcard
  -- Both sides now use the same vector-span range, so the rank criteria coincide.
  rw [← hrange, collinear_iff_finrank_le_one,
    affineIndependent_iff_not_finrank_vectorSpan_le k _ htypecard]

/-- Helper for Remark 50.1: four subtype-indexed points are affinely independent
exactly when their underlying finset is not coplanar. -/
private lemma affineIndependent_coe_iff_not_coplanar_of_card_eq_four
    {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]
    (s : Finset P) (hcard : s.card = 4) :
    AffineIndependent k (fun x : s ↦ (x : P)) ↔ ¬ Coplanar k (s : Set P) := by
  -- As in the three-point case, normalize the geometric set to a finite range.
  have hrange : Set.range (fun x : s ↦ (x : P)) = (s : Set P) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have htypecard : Fintype.card s = 2 + 2 := by
    simpa only [Fintype.card_coe] using hcard
  -- The four-point affine-rank obstruction is exactly coplanarity.
  rw [← hrange, coplanar_iff_finrank_le_two,
    affineIndependent_iff_not_finrank_vectorSpan_le k _ htypecard]

/-- Remark 50.1: For subsets of `EuclideanSpace ℝ (Fin 3)`, general position is
equivalent to having no collinear three-point subset and no coplanar four-point subset. -/
theorem inGeneralPosition_iff_noThreeCollinear_noFourCoplanar
    {A : Set (EuclideanSpace ℝ (Fin 3))} :
    A.InGeneralPosition ↔
      (∀ s : Finset (EuclideanSpace ℝ (Fin 3)),
        (s : Set (EuclideanSpace ℝ (Fin 3))) ⊆ A →
          s.card = 3 → ¬ Collinear ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ s : Finset (EuclideanSpace ℝ (Fin 3)),
        (s : Set (EuclideanSpace ℝ (Fin 3))) ⊆ A →
          s.card = 4 → ¬ Coplanar ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))) := by
  constructor
  · intro hgeneral
    constructor
    · intro s hs hcard
      -- General position supplies affine independence for every three-point subset.
      have hbound : s.card ≤ 3 + 1 := by
        omega
      have hindependent := hgeneral.affineIndependent s hs hbound
      exact (affineIndependent_coe_iff_not_collinear_of_card_eq_three s hcard).mp
        hindependent
    · intro s hs hcard
      -- The same defining condition handles four-point subsets directly.
      have hbound : s.card ≤ 3 + 1 := by
        omega
      have hindependent := hgeneral.affineIndependent s hs hbound
      exact (affineIndependent_coe_iff_not_coplanar_of_card_eq_four s hcard).mp
        hindependent
  · rintro ⟨hthree, hfour⟩
    rw [inGeneralPosition_iff]
    intro s hs hbound
    -- Subsets with at most two points are automatically affinely independent.
    by_cases hsmall : s.card ≤ 2
    · exact affineIndependent_coe_of_card_le_two s hsmall
    -- Every remaining subset allowed by general position has exactly three or four points.
    have hcases : s.card = 3 ∨ s.card = 4 := by
      omega
    rcases hcases with hcard | hcard
    · exact (affineIndependent_coe_iff_not_collinear_of_card_eq_three s hcard).mpr
        (hthree s hs hcard)
    · exact (affineIndependent_coe_iff_not_coplanar_of_card_eq_four s hcard).mpr
        (hfour s hs hcard)

end Set
