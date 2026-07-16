import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_36_8

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

open IsIntegral

variable {ι : Type u} [Finite ι]
variable {R : ι → Type v} {S : ι → Type w}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]

/-- Lemma 10.36.10 (1): an element of the product ring lies in the integral closure of
`∏ i, R i` in `∏ i, S i` exactly when each component lies in the integral closure of `R i`
in `S i`. -/
-- Proof sketch: Rewrite membership in each integral closure using `mem_integralClosure_iff`,
-- then apply `IsIntegral.pi_iff` from Lemma 10.36.8 to pass between integrality over the
-- product ring and componentwise integrality.
theorem mem_integralClosure_pi_iff {s : Π i, S i} :
    s ∈ integralClosure (Π i, R i) (Π i, S i) ↔ ∀ i, s i ∈ integralClosure (R i) (S i) := by
  simp [mem_integralClosure_iff, IsIntegral.pi_iff]

omit [Finite ι] in
private theorem algebraMap_pi_injective_iff :
    Function.Injective (algebraMap (Π i, R i) (Π i, S i)) ↔
      ∀ i, Function.Injective (algebraMap (R i) (S i)) := by
  classical
  constructor
  · intro h i x y hxy
    have hxy' :
        algebraMap (Π j, R j) (Π j, S j) (Pi.single i x) =
          algebraMap (Π j, R j) (Π j, S j) (Pi.single i y) := by
      funext j
      by_cases hji : j = i
      · subst hji
        change algebraMap (R j) (S j) ((Pi.single j x) j) =
            algebraMap (R j) (S j) ((Pi.single j y) j)
        simpa using hxy
      · change algebraMap (R j) (S j) ((Pi.single i x) j) =
            algebraMap (R j) (S j) ((Pi.single i y) j)
        simp [Pi.single_eq_of_ne hji]
    simpa using congrFun (h hxy') i
  · intro h x y hxy
    ext i
    exact h i (by simpa using congrFun hxy i)

/-- Lemma 10.36.10 (2): the product map `∏ i, R i → ∏ i, S i` is integrally closed if and only
if each component map `R i → S i` is integrally closed. -/
-- Proof sketch: unfold `IsIntegrallyClosedIn` via `isIntegrallyClosedIn_iff`. Injectivity of the
-- product algebra map is equivalent to componentwise injectivity by testing on `Pi.single`, and
-- the existence condition is transported componentwise using `IsIntegral.pi_iff`.
theorem isIntegrallyClosedIn_pi_iff :
    IsIntegrallyClosedIn (Π i, R i) (Π i, S i) ↔ ∀ i, IsIntegrallyClosedIn (R i) (S i) := by
  classical
  rw [isIntegrallyClosedIn_iff, algebraMap_pi_injective_iff]
  constructor
  · intro h i
    rw [isIntegrallyClosedIn_iff]
    constructor
    · exact h.1 i
    · intro x hx
      have hs : IsIntegral (Π i, R i) (Pi.single i x) := by
        rw [IsIntegral.pi_iff]
        intro j
        by_cases hji : j = i
        · subst hji
          simpa using hx
        · simpa [Pi.single_eq_of_ne hji] using (isIntegral_zero : IsIntegral (R j) (0 : S j))
      obtain ⟨y, hy⟩ := h.2 hs
      exact ⟨y i, by simpa using congrFun hy i⟩
  · intro h
    constructor
    · intro i
      exact (isIntegrallyClosedIn_iff.mp (h i)).1
    · intro x hx
      choose y hy using fun i ↦ by
        letI : IsIntegrallyClosedIn (R i) (S i) := h i
        change ∃ y : R i, algebraMap (R i) (S i) y = x i
        exact IsIntegrallyClosedIn.algebraMap_eq_of_integral ((IsIntegral.pi_iff.mp hx) i)
      exact ⟨y, by funext i; exact hy i⟩

end
