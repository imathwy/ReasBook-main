import stacks_project.Chap10.Lemma_10_115_1

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

universe u

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

private noncomputable def noetherNormalizationInverseShear (e : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.aeval
    (Fin.snoc (fun i : Fin n ↦ X i.castSucc - X (Fin.last n) ^ e i) (X (Fin.last n)))

/-- The triangular automorphism `x_i ↦ x_i + x_n^(e i)` for `i < n`, with the last variable
`x_n` fixed. Here `MvPolynomial (Fin (n + 1)) R` is viewed as `R[x₁, …, xₙ, x_n]`, and
`Fin.last n` plays the role of `x_n`. -/
noncomputable def noetherNormalizationShear (e : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval
      (Fin.snoc (fun i : Fin n ↦ X i.castSucc + X (Fin.last n) ^ e i) (X (Fin.last n))))
    (noetherNormalizationInverseShear e)
    (by
      ext i
      cases i using Fin.lastCases <;> simp [noetherNormalizationInverseShear])
    (by
      ext i
      cases i using Fin.lastCases <;> simp [noetherNormalizationInverseShear])

/-- The canonical view of `MvPolynomial (Fin (n + 1)) R` as polynomials in the last variable
with coefficients in the first `n` variables. -/
noncomputable def noetherNormalizationLastVariableEquiv :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (MvPolynomial.renameEquiv R finSuccEquivLast).trans (MvPolynomial.optionEquivLeft R (Fin n))

@[simp] theorem noetherNormalizationLastVariableEquiv_X_castSucc (i : Fin n) :
    (noetherNormalizationLastVariableEquiv :
      MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)) (X (Fin.castSucc i)) =
      Polynomial.C (X i) := by
  simp [noetherNormalizationLastVariableEquiv]

@[simp] theorem noetherNormalizationLastVariableEquiv_X_last :
    (noetherNormalizationLastVariableEquiv :
      MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)) (X (Fin.last n)) =
      Polynomial.X := by
  simp [noetherNormalizationLastVariableEquiv]

/-- The sheared polynomial, viewed as a polynomial in the last variable over the first `n`
variables. -/
noncomputable def noetherNormalizationLastVariablePolynomial (e : Fin n → ℕ)
    (g : MvPolynomial (Fin (n + 1)) R) : Polynomial (MvPolynomial (Fin n) R) :=
  noetherNormalizationLastVariableEquiv (noetherNormalizationShear e g)

/-- The weight inequalities expressing `e₁ ≫ e₂ ≫ ⋯ ≫ eₙ₋₁ ≫ 1` relative to the support of
`g`. -/
def noetherNormalizationDominatingWeights (g : MvPolynomial (Fin (n + 1)) R)
    (e : Fin n → ℕ) : Prop :=
  let w : Fin (n + 1) → ℕ := Fin.snoc e 1
  let spread : Fin (n + 1) → ℕ := fun i ↦
    (g.support.product g.support).sup fun m ↦ m.1 i - m.2 i
  g.support.Nonempty ∧
    ∀ i : Fin (n + 1),
      w i >
        Finset.sum (Finset.univ.filter fun j : Fin (n + 1) ↦ i < j)
          (fun j ↦ spread j * w j)

/-- A dominating system of weights can occur only when the support of the polynomial is nonempty. -/
-- Proof sketch: unfold `noetherNormalizationDominatingWeights`; its first component is the
-- nonemptiness of `g.support`.
theorem noetherNormalizationDominatingWeights_support_nonempty
    {g : MvPolynomial (Fin (n + 1)) R} {e : Fin n → ℕ}
    (he : noetherNormalizationDominatingWeights g e) :
    g.support.Nonempty := by
  simpa [noetherNormalizationDominatingWeights] using he.1

/-- Lemma 10.115.2: after the triangular substitution `x_i ↦ x_i + x_n^(e i)` with dominating
weights, a nonconstant polynomial acquires positive degree in `x_n`, and its leading coefficient
is a constant coefficient already occurring in the original polynomial. -/
-- Proof sketch: expand `g` as a finite sum of monomials and compare the resulting `x_n`-degrees
-- after the substitution. The dominating-weight hypothesis, via Lemma `10.115.1`, gives a unique
-- monomial of maximal weighted degree, so the highest `x_n`-term comes from a single support
-- monomial and has coefficient equal to the corresponding coefficient of `g`.
theorem exists_positive_natDegree_and_constant_leadingCoeff_of_noetherNormalizationLastVariablePolynomial
    (g : MvPolynomial (Fin (n + 1)) R) (hg : ¬ ∃ a : R, g = C a)
    (e : Fin n → ℕ) (he : noetherNormalizationDominatingWeights g e) :
    let p := noetherNormalizationLastVariablePolynomial e g
    0 < p.natDegree ∧ ∃ a : R, p.leadingCoeff = C a ∧ ∃ m ∈ g.support, g.coeff m = a := sorry

end
