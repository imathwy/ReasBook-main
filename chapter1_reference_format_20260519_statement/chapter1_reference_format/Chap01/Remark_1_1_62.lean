import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Proof sketch: induct on the nonempty finset; the singleton case is immediate, and the
-- inductive step uses `lcm_mul_left` together with the fact that `normalize (a : ℤ) = |a|`.
/-- Remark 1.1.62: for a nonempty finite family of integers, multiplying every entry by `a`
multiplies the least common multiple by `|a|`. -/
lemma finset_int_lcm_mul_eq_abs_mul_lcm {ι : Type u} (s : Finset ι) (hs : s.Nonempty) (a : ℤ)
    (f : ι → ℤ) : s.lcm (fun i ↦ a * f i) = |a| * s.lcm f := by
  classical
  rw [Int.abs_eq_normalize]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton b =>
      simp
  | cons b t hb ht ih =>
      simp only [Finset.cons_eq_insert, Finset.lcm_insert, ih]
      have hassoc : Associated (normalize a * t.lcm f) (a * t.lcm f) :=
        (normalize_associated a).mul_right (t.lcm f)
      calc
        lcm (a * f b) (normalize a * t.lcm f) = lcm (a * f b) (a * t.lcm f) :=
          lcm_eq_of_associated_right hassoc (a * f b)
        _ = normalize a * lcm (f b) (t.lcm f) :=
          lcm_mul_left a (f b) (t.lcm f)
