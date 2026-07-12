import StacksProject_2024.Chap10.Proposition_10_59_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open IsLocalRing
open scoped BigOperators
open scoped Ideal

section

variable (R : Type u) (M : Type v)
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

open Ideal

private noncomputable def numericalPolynomialCandidate {r : ℕ} (a : Fin (r + 1) → ℚ) :
    Polynomial ℚ :=
  ∑ i : Fin (r + 1), a i • Polynomial.preHilbertPoly ℚ i i

private theorem numericalPolynomialCandidate_spec {r : ℕ} (a : Fin (r + 1) → ℚ) :
    ∀ᶠ n : ℕ in atTop,
      (numericalPolynomialCandidate a).eval (n : ℚ) =
        ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
  filter_upwards [eventually_ge_atTop r] with n hn
  simp only [numericalPolynomialCandidate, Polynomial.eval_finset_sum, Polynomial.eval_smul,
    zsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add]
  · rw [Nat.sub_add_cancel (le_trans (Nat.lt_succ_iff.mp i.2) hn)]
    simp [Ring.choose_natCast, mul_comm]
  · exact le_trans (Nat.lt_succ_iff.mp i.2) hn

/-- A numerical polynomial on `ℤ` with values `f n.toNat` yields an eventual polynomial
representative on `ℕ`. This is the canonical bridge from Definition 10.58.3 to the ordinary
polynomial used in Definition 10.59.6. -/
theorem IsNumericalPolynomial.exists_eventuallyEq_ratPolynomial {f : ℕ → ℚ}
    (hf : IsNumericalPolynomial (fun n : ℤ ↦ f n.toNat)) :
    ∃ P : Polynomial ℚ, ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = f n := by
  rcases hf with ⟨r, a, h⟩
  refine ⟨numericalPolynomialCandidate a, ?_⟩
  have hNat :
      (fun n : ℕ ↦ f n) =ᶠ[atTop]
        fun n ↦ ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
    simpa using h.comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop atTop)
  filter_upwards [hNat, numericalPolynomialCandidate_spec a] with n hf' hP
  exact hP.trans hf'.symm

/-- A Hilbert polynomial for `M` over `R` exists. -/
private theorem exists_hilbertPolynomial :
    ∃ P : Polynomial ℚ,
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((φ_ (maximalIdeal R) M n).toNat : ℚ) := by
  let 𝔪 : Ideal R := maximalIdeal R
  let phiFun : ℕ → ℚ := fun n ↦ ((φ_ 𝔪 M n).toNat : ℚ)
  have h𝔪 : 𝔪.IsIdealOfDefinition := by
    change (maximalIdeal R).IsIdealOfDefinition
    exact Ideal.maximalIdeal_isIdealOfDefinition
  have hnum' :
      IsNumericalPolynomial fun n : ℤ ↦ ((φ_ 𝔪 M n.toNat).toNat : ℚ) :=
    hilbertSamuelPhiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition 𝔪 h𝔪
  have hnum : IsNumericalPolynomial (fun n : ℤ ↦ phiFun n.toNat) := by
    simpa [phiFun] using
      hnum'
  rcases IsNumericalPolynomial.exists_eventuallyEq_ratPolynomial hnum with ⟨P, hP⟩
  exact ⟨P, by simpa [𝔪] using hP⟩

omit [IsNoetherianRing R] [Module.Finite R M] in
private theorem hilbertPolynomial_unique {P P' : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop,
      P'.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ)) :
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
  · intro x hx
    rcases hx with ⟨n, rfl⟩
    rcases hN (n + N) (Nat.le_add_left N n) with ⟨hPn, hP'n⟩
    simpa [add_comm] using hPn.trans hP'n.symm

/-- There is a unique Hilbert polynomial for `M` over `R`. -/
private theorem existsUnique_hilbertPolynomial :
    ∃! P : Polynomial ℚ,
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ) := by
  rcases exists_hilbertPolynomial R M with ⟨P, hP⟩
  refine ⟨P, hP, ?_⟩
  intro P' hP'
  exact hilbertPolynomial_unique R M hP' hP

/-- Definition 10.59.6: the Hilbert polynomial of `M` over `R` is the unique polynomial in `ℚ[t]`
whose values agree with the Hilbert-Samuel function `φ_M` for all sufficiently large `n`. -/
noncomputable def hilbertPolynomial : Polynomial ℚ :=
  Classical.choose <| ExistsUnique.exists <| existsUnique_hilbertPolynomial R M

private theorem hilbertPolynomial_spec :
    ∀ᶠ n : ℕ in atTop,
      (hilbertPolynomial R M).eval (n : ℚ) =
        ((φ_(maximalIdeal R) M n).toNat : ℚ) :=
  Classical.choose_spec <| ExistsUnique.exists <| existsUnique_hilbertPolynomial R M

/-- The Hilbert polynomial eventually agrees with the Hilbert-Samuel function `φ_M`. -/
theorem hilbertPolynomial_eventuallyEq :
    ∀ᶠ n : ℕ in atTop,
      (hilbertPolynomial R M).eval (n : ℚ) =
        ((φ_(maximalIdeal R) M n).toNat : ℚ) :=
  hilbertPolynomial_spec R M

/-- Any Hilbert polynomial for `M` over `R` is the Hilbert polynomial; equivalently, any
eventual polynomial representative of `φ_M` is the Hilbert polynomial. -/
theorem eq_hilbertPolynomial {P : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ)) :
    P = hilbertPolynomial R M :=
  ExistsUnique.unique (existsUnique_hilbertPolynomial R M) hP (hilbertPolynomial_spec R M)

/-- A rational polynomial agrees eventually with `φ_M` if and only if it is the Hilbert
polynomial. -/
@[simp] theorem eventuallyEq_hilbertSamuelPhi_iff_eq_hilbertPolynomial
    (P : Polynomial ℚ) :
    (∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ)) ↔
        P = hilbertPolynomial R M := by
  constructor
  · exact eq_hilbertPolynomial R M
  · rintro rfl
    exact hilbertPolynomial_spec R M

end
