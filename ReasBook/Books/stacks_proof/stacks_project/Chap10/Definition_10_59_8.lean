import stacks_proof.stacks_project.Chap10.Definition_10_59_1
import stacks_proof.stacks_project.Chap10.Definition_10_59_6
import stacks_proof.stacks_project.Chap10.Lemma_10_59_7
import stacks_proof.stacks_project.Chap10.Proposition_10_59_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Filter IsLocalRing
open scoped Ideal

section

variable (R : Type u) (M : Type v)
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

open Ideal

/-- For an ideal of definition `I`, the Hilbert-Samuel `χ`-function of `M` is eventually given by
some polynomial with rational coefficients. -/
theorem exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition {I : Ideal R}
    (hI : I.IsIdealOfDefinition) :
    ∃ P : Polynomial ℚ,
      ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ) := by
  exact IsNumericalPolynomial.exists_eventuallyEq_ratPolynomial <|
    hilbertSamuelChiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition I hI

omit [IsNoetherianRing R] [Module.Finite R M] in
private theorem eventuallyEq_polynomial_unique {f : ℕ → ℚ} {P P' : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = f n)
    (hP' : ∀ᶠ n : ℕ in atTop, P'.eval (n : ℚ) = f n) :
    P = P' := by
  rcases eventually_atTop.mp (hP.and hP') with ⟨N, hN⟩
  let s : Set ℚ := Set.range fun n : ℕ ↦ ((n + N : ℕ) : ℚ)
  have hs : s.Infinite := Set.infinite_range_of_injective fun m n hmn ↦ by
    have hmn' : (m + N : ℚ) = (n + N : ℚ) := by
      simpa using hmn
    have hmn'' : m + N = n + N := by
      exact_mod_cast hmn'
    exact Nat.add_right_cancel hmn''
  refine Polynomial.eq_of_infinite_eval_eq P P' <| Set.Infinite.mono ?_ hs
  intro x hx
  rcases hx with ⟨n, rfl⟩
  rcases hN (n + N) (Nat.le_add_left N n) with ⟨hPn, hP'n⟩
  simpa [add_comm] using hPn.trans hP'n.symm

private theorem existsUnique_hilbertSamuelChiPolynomial :
    ∃! P : Polynomial ℚ,
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(maximalIdeal R) M n).toNat : ℚ) := by
  rcases exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition R M
      Ideal.maximalIdeal_isIdealOfDefinition with ⟨P, hP⟩
  refine ⟨P, hP, ?_⟩
  intro P' hP'
  exact eventuallyEq_polynomial_unique hP' hP

/-- The canonical eventual Hilbert-Samuel `χ`-polynomial of `M` over `R`, taken with respect to
the maximal ideal. -/
noncomputable def hilbertSamuelChiPolynomial : Polynomial ℚ :=
  Classical.choose <| ExistsUnique.exists <| existsUnique_hilbertSamuelChiPolynomial R M

private theorem hilbertSamuelChiPolynomial_spec :
    ∀ᶠ n : ℕ in atTop,
      (hilbertSamuelChiPolynomial R M).eval (n : ℚ) =
        ((χ_(maximalIdeal R) M n).toNat : ℚ) :=
  Classical.choose_spec <| ExistsUnique.exists <| existsUnique_hilbertSamuelChiPolynomial R M

/-- The canonical Hilbert-Samuel `χ`-polynomial eventually agrees with the Hilbert-Samuel
`χ`-function of `M` over `R`. -/
theorem hilbertSamuelChiPolynomial_eventuallyEq :
    ∀ᶠ n : ℕ in atTop,
      (hilbertSamuelChiPolynomial R M).eval (n : ℚ) =
        ((χ_(maximalIdeal R) M n).toNat : ℚ) :=
  hilbertSamuelChiPolynomial_spec R M

/-- Any eventual polynomial representative of the Hilbert-Samuel `χ`-function with respect to the
maximal ideal is the canonical Hilbert-Samuel `χ`-polynomial. -/
theorem eq_hilbertSamuelChiPolynomial {P : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(maximalIdeal R) M n).toNat : ℚ)) :
    P = hilbertSamuelChiPolynomial R M :=
  ExistsUnique.unique (existsUnique_hilbertSamuelChiPolynomial R M) hP
    (hilbertSamuelChiPolynomial_spec R M)

/-- Definition 10.59.8: for a finite module over a local Noetherian ring, `d(M)` is the degree of
any eventual polynomial representative of the Hilbert-Samuel `χ`-function attached to the maximal
ideal; Lemma 10.59.7 shows that this degree is independent of the chosen representative. -/
@[stacks 00KA]
noncomputable def hilbertSamuelPolynomialDegree : WithBot ℕ :=
  (hilbertSamuelChiPolynomial R M).degree

/-- If `P` is an eventual polynomial representative of `χ_{I,M}` for an ideal of definition `I`,
then Definition 10.59.8 computes `d(M)` as `P.degree`. -/
theorem hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition {I : Ideal R}
    (hI : I.IsIdealOfDefinition) {P : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ)) :
    hilbertSamuelPolynomialDegree R M = P.degree := by
  have hmax : (maximalIdeal R).IsIdealOfDefinition := Ideal.maximalIdeal_isIdealOfDefinition
  simpa [hilbertSamuelPolynomialDegree] using
    Ideal.hilbertSamuelChi_degree_eq_of_isIdealOfDefinition hmax hI
      (hilbertSamuelChiPolynomial_eventuallyEq R M) hP

/-- Any eventual polynomial representative of the Hilbert-Samuel `χ`-function with respect to the
maximal ideal has degree `d(M)`. -/
theorem hilbertSamuelPolynomialDegree_eq_degree {P : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(maximalIdeal R) M n).toNat : ℚ)) :
    hilbertSamuelPolynomialDegree R M = P.degree := by
  simpa using
    hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition R M
      Ideal.maximalIdeal_isIdealOfDefinition hP

/-- The Hilbert-Samuel degree invariant is preserved by `R`-linear equivalences of finite
modules. -/
theorem hilbertSamuelPolynomialDegree_eq_of_linearEquiv
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) :
    hilbertSamuelPolynomialDegree R M = hilbertSamuelPolynomialDegree R N := by
  let P := hilbertSamuelChiPolynomial R N
  have hP :
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(maximalIdeal R) N n).toNat : ℚ) :=
    hilbertSamuelChiPolynomial_eventuallyEq R N
  have hPM :
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(maximalIdeal R) M n).toNat : ℚ) := by
    filter_upwards [hP] with n hn
    have hchi :
        χ_(maximalIdeal R) M n =
          χ_(maximalIdeal R) N n := by
      simp only [hilbertSamuelChi]
      let P' : Submodule R M := maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M)
      let Q : Submodule R N := maximalIdeal R ^ (n + 1) • (⊤ : Submodule R N)
      have hPQ : P'.map (e : M →ₗ[R] N) = Q := by
        simp [P', Q, Submodule.map_smul'']
      exact LinearEquiv.length_eq (Submodule.Quotient.equiv P' Q e hPQ)
    have hchiNat :
        ((χ_(maximalIdeal R) M n).toNat : ℚ) =
          ((χ_(maximalIdeal R) N n).toNat : ℚ) := by
      simpa using congrArg (fun x : ℕ∞ ↦ (x.toNat : ℚ)) hchi
    exact hn.trans hchiNat.symm
  rw [hilbertSamuelPolynomialDegree_eq_degree R M hPM, hilbertSamuelPolynomialDegree]

/-- The zero-module clause in Definition 10.59.8, with `M = 0` expressed in Lean by
`Subsingleton M`. -/
@[simp] theorem hilbertSamuelPolynomialDegree_eq_bot [Subsingleton M] :
    hilbertSamuelPolynomialDegree R M = (⊥ : WithBot ℕ) := by
  have hdeg : hilbertSamuelPolynomialDegree R M = (0 : Polynomial ℚ).degree :=
    hilbertSamuelPolynomialDegree_eq_degree R M <|
      Eventually.of_forall fun n ↦ by
        haveI :
            Subsingleton (M ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M))) := by
          infer_instance
        simp [hilbertSamuelChi, Module.length_eq_zero]
  rw [hdeg]
  simp

end
