import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling for this refine pass:
-- * primary domain: `S`-free / maximal `S`-free convex sets in `ℝ^q`
-- * core/canonical owners inspected: `is_free_of`, `is_maximal_free_of`,
--   `is_lattice_free`, `is_maximal_lattice_free`
-- * chapter lattice owner reused here: `ℤ^q` together with `mem_integerVectors_iff`
-- * source-facing owner kept here: `nonnegativeIntegerVectors` with notation `ℤ_+^q`
-- * primitive vs derived split: `nonnegativeIntegerVectors` is primitive data; the free/maximal
--   predicates remain thin specializations of the Chapter 6 generic owners; the halfspace owner is
--   stated intrinsically via the linear functional `dotProduct a`

section Exercise614

variable {q : ℕ}

local notation "R2" => Fin 2 → ℝ

open scoped IntegerVectorNotation

/-- The embedded nonnegative integer lattice `ℤ_+^q = ℤ^q ∩ ℝ_+^q ⊆ ℝ^q`. -/
def nonnegativeIntegerVectors (q : ℕ) : Set (Fin q → ℝ) :=
  ℤ^q ∩ Set.Ici (0 : Fin q → ℝ)

namespace NonnegativeIntegerVectorNotation

scoped notation "ℤ_+^" n:max => nonnegativeIntegerVectors n

end NonnegativeIntegerVectorNotation

open scoped NonnegativeIntegerVectorNotation

/-- Membership in `ℤ_+^q` is exactly membership in `ℤ^q` together with coordinatewise
nonnegativity. -/
theorem mem_nonnegativeIntegerVectors_iff
    {r : Fin q → ℝ} :
    r ∈ ℤ_+^q ↔
      r ∈ ℤ^q ∧ 0 ≤ r :=
  Iff.rfl

/-- A real vector lies in `ℤ_+^q` exactly when each coordinate is a nonnegative integer. -/
theorem mem_nonnegativeIntegerVectors_iff_forall
    {r : Fin q → ℝ} :
    r ∈ ℤ_+^q ↔
      ∀ i, r i ∈ Set.range (Int.cast : ℤ → ℝ) ∧ 0 ≤ r i := by
  constructor
  · intro hr
    rcases mem_nonnegativeIntegerVectors_iff.mp hr with ⟨hr_int, hr_nonneg⟩
    intro i
    exact ⟨(mem_integerVectors_iff_forall.mp hr_int) i, hr_nonneg i⟩
  · intro h
    exact (mem_nonnegativeIntegerVectors_iff).2
      ⟨(mem_integerVectors_iff_forall).2 (fun i ↦ (h i).1), fun i ↦ (h i).2⟩

/-- Membership in `ℤ_+^q` means being the real-valued coercion of a nonnegative integer vector. -/
theorem mem_nonnegativeIntegerVectors_iff_exists
    {r : Fin q → ℝ} :
    r ∈ ℤ_+^q ↔
      ∃ z : Fin q → ℕ, r = Nat.cast ∘ z := by
  constructor
  · rintro ⟨hr_int, hr_nonneg⟩
    rcases (mem_integerVectors_iff.mp hr_int) with ⟨z, rfl⟩
    refine ⟨fun i ↦ Int.toNat (z i), ?_⟩
    funext i
    have hzi_nonneg : 0 ≤ z i := by
      have hri : (0 : ℝ) ≤ (z i : ℝ) := by
        simpa using hr_nonneg i
      exact (Int.cast_nonneg_iff).1 hri
    change (z i : ℝ) = (Int.toNat (z i) : ℝ)
    exact_mod_cast (Int.toNat_of_nonneg hzi_nonneg).symm
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · refine (mem_integerVectors_iff).2 ⟨fun i ↦ (z i : ℤ), ?_⟩
      funext i
      simp
    · exact fun i ↦ Nat.cast_nonneg (z i)

/-- A convex set in `ℝ^q` is `ℤ_+^q`-free when its interior contains no embedded nonnegative
integer point. -/
def is_nonnegative_integer_free (K : Set (Fin q → ℝ)) : Prop :=
  is_free_of (ℤ_+^q) K

/-- `is_nonnegative_integer_free K` unfolds to the assertion that no point of `ℤ_+^q` lies in the
interior of `K`. -/
theorem is_nonnegative_integer_free_iff
    {K : Set (Fin q → ℝ)} :
    is_nonnegative_integer_free K ↔
      ∀ z : Fin q → ℕ, (Nat.cast ∘ z) ∉ interior K := by
  rw [is_nonnegative_integer_free, is_free_of_iff]
  constructor
  · intro h z
    exact h _ ((mem_nonnegativeIntegerVectors_iff_exists).2 ⟨z, rfl⟩)
  · intro h x hx
    rcases (mem_nonnegativeIntegerVectors_iff_exists).1 hx with ⟨z, rfl⟩
    exact h z

/-- If `K` is `ℤ_+^q`-free, then every embedded nonnegative integer point lies outside the
interior of `K`. -/
theorem is_nonnegative_integer_free.not_mem_interior
    {K : Set (Fin q → ℝ)}
    (hK : is_nonnegative_integer_free K)
    {x : Fin q → ℝ}
    (hx : x ∈ ℤ_+^q) :
    x ∉ interior K :=
  is_free_of.not_mem_interior hK hx

/-- A convex set in `ℝ^q` is maximal `ℤ_+^q`-free when it is `ℤ_+^q`-free and admits no strictly
larger convex `ℤ_+^q`-free superset. -/
def is_maximal_nonnegative_integer_free (K : Set (Fin q → ℝ)) : Prop :=
  is_maximal_free_of (ℤ_+^q) K

/-- `is_maximal_nonnegative_integer_free K` unfolds to convexity, `ℤ_+^q`-freeness, and
maximality among convex `ℤ_+^q`-free supersets. -/
theorem is_maximal_nonnegative_integer_free_iff
    {K : Set (Fin q → ℝ)} :
    is_maximal_nonnegative_integer_free K ↔
      Convex ℝ K ∧
        is_nonnegative_integer_free K ∧
          ∀ L : Set (Fin q → ℝ),
            K ⊆ L → Convex ℝ L → is_nonnegative_integer_free L → L = K :=
  Iff.rfl

/-- A maximal `ℤ_+^q`-free set is convex. -/
theorem is_maximal_nonnegative_integer_free.convex
    {K : Set (Fin q → ℝ)}
    (hK : is_maximal_nonnegative_integer_free K) :
    Convex ℝ K :=
  is_maximal_free_of.convex hK

/-- A maximal `ℤ_+^q`-free set is `ℤ_+^q`-free. -/
theorem is_maximal_nonnegative_integer_free.free
    {K : Set (Fin q → ℝ)}
    (hK : is_maximal_nonnegative_integer_free K) :
    is_nonnegative_integer_free K :=
  is_maximal_free_of.free hK

/-- Maximality among convex `ℤ_+^q`-free supersets gives equality with any larger convex
`ℤ_+^q`-free superset. -/
theorem is_maximal_nonnegative_integer_free.eq_of_subset
    {K : Set (Fin q → ℝ)}
    (hK : is_maximal_nonnegative_integer_free K)
    {L : Set (Fin q → ℝ)}
    (hKL : K ⊆ L)
    (hL_convex : Convex ℝ L)
    (hL_free : is_nonnegative_integer_free L) :
    L = K :=
  is_maximal_free_of.eq_of_subset hK hKL hL_convex hL_free

/-- The halfspace through the origin with outward normal `a` in `ℝ²`. -/
def nonnegative_supporting_halfspace (a : R2) : Set R2 :=
  {x : R2 | dotProduct a x ≤ 0}

/-- Exercise 6.14. A convex set in `ℝ²` is `ℤ_+^2`-free if it contains no point of `ℤ_+^2` in
its interior. The maximal `ℤ_+^2`-free convex sets that are not `ℤ²`-free are exactly the
halfspaces through the origin with a nonzero normal vector in the nonnegative orthant. -/
theorem maximal_nonnegative_integer_free_not_lattice_free_iff
    {K : Set R2} :
    is_maximal_nonnegative_integer_free K ∧ ¬ is_lattice_free K ↔
      ∃ a : R2, 0 ≤ a ∧ a ≠ 0 ∧ K = nonnegative_supporting_halfspace a := sorry

end Exercise614
