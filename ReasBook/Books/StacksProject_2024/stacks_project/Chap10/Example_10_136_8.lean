import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

/-- The polynomial-ring map `ℤ[a₁, \ldots, aₙ] → ℤ[α₁, \ldots, αₙ]` sending `aᵢ` to the
`i`th elementary symmetric polynomial in the variables `α₁, \ldots, αₙ`. It is the source-facing
map obtained by composing the canonical owner `MvPolynomial.esymmAlgHom` with the inclusion of the
symmetric subalgebra into the full polynomial ring. -/
noncomputable def elementary_symmetric_ring_hom (n : ℕ) :
    MvPolynomial (Fin n) ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ :=
  (symmetricSubalgebra (Fin n) ℤ).val.comp (esymmAlgHom (Fin n) ℤ n)

/-- The elementary-symmetric map sends the source variable `aᵢ` to the corresponding elementary
symmetric polynomial in the root variables. -/
@[simp] theorem elementary_symmetric_ring_hom_apply_X (n : ℕ) (i : Fin n) :
    elementary_symmetric_ring_hom n (X i) = esymm (Fin n) ℤ (i + 1) := by
  simp [elementary_symmetric_ring_hom, esymmAlgHom]

-- Proof sketch: identify `elementary_symmetric_ring_hom n` with the canonical fundamental-theorem
-- owner for symmetric polynomials and use the standard monomial basis to obtain finite generation
-- and freeness over `ℤ[a₁, \ldots, aₙ]`.
/-- Example 10.136.8: the elementary-symmetric map
`ℤ[a₁, \ldots, aₙ] → ℤ[α₁, \ldots, αₙ]` is finite free. -/
theorem elementary_symmetric_ring_hom_finite_free (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (elementary_symmetric_ring_hom n).toAlgebra
    Module.Finite (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) ∧
      Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) := sorry

-- Proof sketch: the finite-free statement gives finite generation of the target polynomial ring as
-- a module over the source polynomial ring for the algebra structure induced by
-- `elementary_symmetric_ring_hom n`; this is exactly the ring-hom notion of finiteness.
/-- The elementary-symmetric map is finite. -/
theorem elementary_symmetric_ring_hom_finite (n : ℕ) :
    (elementary_symmetric_ring_hom n).Finite := sorry

-- Proof sketch: every finite ring map is quasi-finite in mathlib, so this follows formally from
-- `elementary_symmetric_ring_hom_finite n`.
/-- The elementary-symmetric map is quasi-finite, equivalently its fibers are finite. -/
theorem elementary_symmetric_ring_hom_quasi_finite (n : ℕ) :
    (elementary_symmetric_ring_hom n).QuasiFinite := sorry

-- Proof sketch: a finite free module is flat, and because its rank is positive the induced map on
-- spectra is surjective; equivalently, the ring map is faithfully flat.
/-- The elementary-symmetric map is faithfully flat. -/
theorem elementary_symmetric_ring_hom_faithfully_flat (n : ℕ) :
    (elementary_symmetric_ring_hom n).FaithfullyFlat := sorry
