import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_58_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

noncomputable section

universe u

section

variable {A : Type u} [AddCommGroup A]

/-- A function on the integers has degree `< m` if it is eventually zero, or eventually agrees
with a binomial-coefficient expansion indexed only up to some `r < m`. This packages the zero
function as having degree `-∞`, which is the convention used in Lemma 10.58.10. -/
def HasNumericalPolynomialDegreeLT (f : ℤ → A) (m : ℤ) : Prop :=
  (f =ᶠ[atTop] fun _ ↦ (0 : A)) ∨
    ∃ r : ℕ, (r : ℤ) < m ∧ ∃ a : Fin (r + 1) → A,
      f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i

/- Bridge/view: a degree bound in the source-facing sense still lands in the chapter's owner
notion `IsNumericalPolynomial`. -/
theorem HasNumericalPolynomialDegreeLT.isNumericalPolynomial
    {f : ℤ → A} {m : ℤ} (hf : HasNumericalPolynomialDegreeLT f m) :
    IsNumericalPolynomial f := by
  rcases hf with hzero | ⟨r, -, a, ha⟩
  · refine ⟨0, fun _ ↦ 0, ?_⟩
    exact hzero.trans <| Filter.EventuallyEq.of_eq <| by
      ext n
      simp
  · exact ⟨r, a, ha⟩

private theorem hasNumericalPolynomialDegreeLT_zero_iff {f : ℤ → A} :
    HasNumericalPolynomialDegreeLT f 0 ↔ f =ᶠ[atTop] fun _ ↦ (0 : A) := by
  constructor
  · intro hf
    rcases hf with hzero | ⟨r, hr, -, -⟩
    · exact hzero
    · have hnonneg : (0 : ℤ) ≤ r := by
        exact_mod_cast Nat.zero_le r
      exact (not_lt_of_ge hnonneg hr).elim
  · intro hzero
    exact Or.inl hzero

end

section

variable {k : Type u} [Field k] {d : ℕ}
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k))

local notation "S" => MvPolynomial (Fin d) k

/-- The image in `k[X₁, …, X_d] ⧸ I` of the homogeneous degree-`n` piece of the standard graded
polynomial ring. -/
private def homogeneousIdealQuotientDegreePiece (n : ℕ) :
    Submodule k (S ⧸ I.toIdeal) :=
  (MvPolynomial.homogeneousSubmodule (Fin d) k n).map (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap

/-- The Hilbert function of the homogeneous quotient module `k[X₁, …, X_d] ⧸ I`, computed from
the images of the homogeneous degree pieces in the quotient. The source's partial-function
convention is modeled here by declaring the value to be `0` in negative degrees. -/
def homogeneousIdealQuotientHilbertFunction : ℤ → ℤ :=
  fun n ↦
    if 0 ≤ n then
      Module.finrank k <| homogeneousIdealQuotientDegreePiece I n.toNat
    else 0

-- Proof sketch: for nonnegative `n` this is just the dimension of the image of the degree-`n`
-- homogeneous piece in the quotient module; for negative `n` the function is defined to be `0`.
/-- In nonnegative degree, the Hilbert function is the dimension of the corresponding degree piece
of the quotient module. -/
private theorem homogeneousIdealQuotientHilbertFunction_of_nonneg
    (n : ℤ) (hn : 0 ≤ n) :
    homogeneousIdealQuotientHilbertFunction I n =
      (Module.finrank k <| homogeneousIdealQuotientDegreePiece I n.toNat : ℤ) := by
  rw [homogeneousIdealQuotientHilbertFunction, if_pos hn]

/-- In negative degree, the Hilbert function is `0`. -/
@[simp] private theorem homogeneousIdealQuotientHilbertFunction_of_neg
    {n : ℤ} (hn : n < 0) :
    homogeneousIdealQuotientHilbertFunction I n = 0 := by
  have hnn : ¬ 0 ≤ n := by linarith
  simp [homogeneousIdealQuotientHilbertFunction, hnn]

-- Proof sketch: choose a nonzero homogeneous element of `I`, compare the degree-`n` piece of the
-- quotient with the corresponding degree-`n` piece of the ambient polynomial ring modulo the image
-- of multiplication by that element, and use the binomial-coefficient formula for the Hilbert
-- function of the standard graded polynomial ring to obtain a drop in degree.
/-- Lemma 10.58.10: for a nonzero homogeneous ideal in `k[X₁, …, X_d]`, the Hilbert function of
the quotient graded module `k[X₁, …, X_d] ⧸ I` is a numerical polynomial of degree `< d - 1`,
with the source's exceptional `d = 1` case absorbed by the convention that an eventually zero
function has degree `-∞`. -/
theorem nonzero_homogeneousIdeal_quotientHilbertFunction_degree_bound
    (hI : I ≠ ⊥) :
    HasNumericalPolynomialDegreeLT
      (homogeneousIdealQuotientHilbertFunction I) (d - 1 : ℤ) := sorry

/-- For any homogeneous ideal `I`, the quotient Hilbert function is a numerical polynomial in the
sense of Definition 10.58.3. This companion forgets the sharper source-facing degree bound from
Lemma 10.58.10 and retains only the chapter's core owner notion `IsNumericalPolynomial`. The
nonzero hypothesis is needed for the degree bound itself, not for eventual polynomiality. -/
theorem homogeneousIdeal_quotientHilbertFunction_isNumericalPolynomial :
    IsNumericalPolynomial (homogeneousIdealQuotientHilbertFunction I) := by
  by_cases hI : I = ⊥
  · sorry
  · exact (nonzero_homogeneousIdeal_quotientHilbertFunction_degree_bound I hI).isNumericalPolynomial

/-- In the exceptional case `d = 1`, Lemma 10.58.10 says that the quotient Hilbert function is
eventually zero. -/
theorem nonzero_homogeneousIdeal_quotientHilbertFunction_eventuallyEq_zero_of_eq_one
    (hI : I ≠ ⊥) (hd : d = 1) :
    homogeneousIdealQuotientHilbertFunction I =ᶠ[atTop] fun _ ↦ (0 : ℤ) := by
  simpa [hd, hasNumericalPolynomialDegreeLT_zero_iff] using
    (nonzero_homogeneousIdeal_quotientHilbertFunction_degree_bound I hI)

end
