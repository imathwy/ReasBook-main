import StacksProject_2024.stacks_project.Chap28.Lemma_28_4_4
import StacksProject_2024.stacks_project.Chap29.Definition_29_47_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

section

variable (A : Type u) [CommRing A]

-- Semantic recall: `lean_leansearch` surfaced the canonical reducedness owners
-- `IsReduced` for rings and schemes, while the local Chapter 29 files already fix the owners
-- `SeminormalRing`, `AbsolutelyWeaklyNormalRing`, `Scheme.Seminormal`, and
-- `Scheme.AbsolutelyWeaklyNormal`.

/-- Lemma 29.47.5 (1): a seminormal ring is reduced. -/
@[instance]
theorem isReduced_of_seminormalRing [SeminormalRing A] :
    IsReduced A := by
  refine ⟨?_⟩
  intro x hx
  rcases hx with ⟨n, hn⟩
  have huniq_zero : ∃! a : A, (0 : A) = a ^ 2 ∧ (0 : A) = a ^ 3 :=
    SeminormalRing.existsUnique_sq_cube_of_cube_eq_sq (show (0 : A) ^ 3 = (0 : A) ^ 2 by simp)
  have hstep (m : ℕ) (hm : x ^ (m + 2) = 0) : x ^ (m + 1) = 0 := by
    obtain ⟨a, -, ha⟩ := huniq_zero
    have h0 : a = 0 := by
      simpa using (ha 0 (by simp)).symm
    have hsq : (0 : A) = (x ^ (m + 1)) ^ 2 := by
      calc
        (0 : A) = x ^ ((m + 1) * 2) := by
          rw [show (m + 1) * 2 = (m + 2) + m by omega, pow_add, hm, zero_mul]
        _ = (x ^ (m + 1)) ^ 2 := by rw [pow_mul]
    have hcube : (0 : A) = (x ^ (m + 1)) ^ 3 := by
      calc
        (0 : A) = x ^ ((m + 1) * 3) := by
          rw [show (m + 1) * 3 = (m + 2) + (m + m + 1) by omega, pow_add, hm, zero_mul]
        _ = (x ^ (m + 1)) ^ 3 := by rw [pow_mul]
    have hpow : x ^ (m + 1) = a :=
      ha (x ^ (m + 1)) ⟨hsq, hcube⟩
    simpa [h0] using hpow
  cases n with
  | zero =>
      have h1 : (1 : A) = 0 := by simpa using hn
      calc
        x = x * 1 := by simp
        _ = x * 0 := by rw [h1]
        _ = 0 := by simp
  | succ n =>
      have hzero_of_pow_eq_zero : ∀ m : ℕ, x ^ (m + 1) = 0 → x = 0 := by
        intro m
        induction m with
        | zero =>
            intro hm
            simpa using hm
        | succ m ihm =>
            intro hm
            have hm' : x ^ (m + 1) = 0 := by
              simpa [Nat.add_assoc] using hstep m (by simpa [Nat.add_assoc] using hm)
            exact ihm hm'
      exact hzero_of_pow_eq_zero n hn

/-- Lemma 29.47.5 (2): an absolutely weakly normal ring is reduced. -/
theorem isReduced_of_absolutelyWeaklyNormalRing [AbsolutelyWeaklyNormalRing A] :
    IsReduced A :=
  isReduced_of_seminormalRing A

end

namespace AlgebraicGeometry.Scheme

/-- Lemma 29.47.5 (3): a seminormal scheme is reduced. -/
@[instance]
theorem isReduced_of_seminormal (X : Scheme.{u}) [Seminormal X] :
    IsReduced X := by
  refine (isReduced_iff_hasRingPropertyLocally_isReduced X).2 ?_
  refine ⟨?_⟩
  intro x
  rcases exists_affineOpen_seminormalRing X x with ⟨U, hxU, hU⟩
  let _ : SeminormalRing (Γ(X, (U : X.Opens))) := hU
  exact ⟨U, hxU, isReduced_of_seminormalRing (Γ(X, (U : X.Opens)))⟩

/-- Lemma 29.47.5 (4): an absolutely weakly normal scheme is reduced. -/
@[instance]
theorem isReduced_of_absolutelyWeaklyNormal (X : Scheme.{u}) [AbsolutelyWeaklyNormal X] :
    IsReduced X := by
  refine (isReduced_iff_hasRingPropertyLocally_isReduced X).2 ?_
  refine ⟨?_⟩
  intro x
  rcases exists_affineOpen_absolutelyWeaklyNormalRing X x with ⟨U, hxU, hU⟩
  let _ : AbsolutelyWeaklyNormalRing (Γ(X, (U : X.Opens))) := hU
  exact ⟨U, hxU, isReduced_of_absolutelyWeaklyNormalRing (Γ(X, (U : X.Opens)))⟩

end AlgebraicGeometry.Scheme
