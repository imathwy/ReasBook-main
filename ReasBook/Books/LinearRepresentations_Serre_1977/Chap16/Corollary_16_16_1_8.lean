import Mathlib
import Mathlib.Analysis.Matrix.PosDef
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8_CartanGramSupport
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u x

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

variable [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [NeZero (Nat.card G : IsLocalRing.ResidueField A)]

variable
  (π : ι → FDRep (IsLocalRing.ResidueField A) G)
  (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
  (hπ_pairwise : PairwiseNonisomorphic π)
  (hπ_complete : IsCompleteIrreducibleFamily π)
  (hP_envelope :
    ∀ i, ∃ f :
      (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
        f.IsProjectiveEnvelope)

/- Domain-style sampling for Corollary 16-16.1-8:
* primary domain: the Cartan homomorphism `cartanHom k G : P₀[k](G) → R₀[k](G)` and its canonical
  matrix view with respect to the Chapter `14` distinguished bases;
* relevant owner declarations inspected in this domain:
  `cartanHom`,
  `cartanMatrix`,
  `simple_finiteRep_classes_basis_of_complete_family`,
  `projectiveEnvelope_classes_basis_of_complete_family`;
* best owner abstraction: the canonical owner matrix `cartanMatrix k G`, with the simple-class and
  projective-envelope bases treated as derived input data from the Chapter `14` owner theorems;
* source/core/bridge triage:
  source-facing: symmetry, positive definiteness, and determinant shape of LinearRepresentations_Serre_1977's distinguished
    Cartan matrix under the large-field hypothesis;
  core/canonical: `cartanMatrix k G` as the matrix of `cartanHom k G`;
  bridge/view: the Chapter `14` basis constructions that realize the source's distinguished bases.

Primitive data vs derived API:
* primitive data for this file: the complete simple family `π`, the projective envelopes `P i`,
  and the corresponding envelope witnesses;
* derived API: the distinguished Chapter `14` bases and the resulting canonical Cartan matrix
  `cartanMatrix k G`. The finiteness bookkeeping needed to form that matrix is recovered locally
  from `hπ_complete` and `hπ_pairwise` via `finite_index`, rather than exported on the theorem
  surface.
-/

local notation "bP" =>
  projectiveEnvelope_classes_basis_of_complete_family
    π hπ_pairwise hπ_complete P hP_envelope

local notation "bR" =>
  simple_finiteRep_classes_basis_of_complete_family
    π hπ_pairwise hπ_complete

/-- Helper for Corollary 16-16.1-8: the large-field proof should show that the distinguished
Cartan matrix is positive definite. -/
private theorem cartanMatrix_source_faithful_gram_data
    [Finite ι] [Fintype ι] [DecidableEq ι]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G bP bR = E.transpose * E ∧ Function.Injective E.mulVec := by
  exact
    cartanMatrix_source_faithful_gram_data_support
      (A := A) (K := K) (G := G) π P hπ_pairwise hπ_complete hP_envelope

/-- Helper for Corollary 16-16.1-8: the large-field proof should show that the distinguished
Cartan matrix is positive definite. -/
private theorem cartanMatrix_posDef_of_sufficiently_large_aux
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      exact (cartanMatrix k G bP bR).PosDef
  := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  obtain ⟨κ, _, _, E, hGram, hEinj⟩ :=
    cartanMatrix_source_faithful_gram_data
      (A := A) (K := K) (G := G) (π := π) (P := P)
      (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (hP_envelope := hP_envelope)
  -- Once the Chapter `15` pairing step is read as `C = Eᵀ * E`, positivity is a pure matrix
  -- consequence of the injectivity of scalar extension from Theorem `16-16.1-2`.
  simpa [hGram] using Matrix.PosDef.conjTranspose_mul_self E hEinj

-- Proof sketch: when `K` is sufficiently large, Theorem `16-16.1-2` makes the scalar-extension
-- matrix `E` split injective and the `cde` triangle identifies the Cartan matrix with `Eᵀ * E`;
-- this expression is visibly symmetric.
/-- Corollary 16-16.1-8 (1): if `K` is sufficiently large, then the Cartan matrix of `G` over the
residue field `k = A/𝔪_A`, written in the distinguished bases coming from a complete simple family
and their projective envelopes, is symmetric. -/
theorem cartanMatrix_isSymm_of_sufficiently_large
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      exact (cartanMatrix k G bP bR).IsSymm
  := by
    -- Symmetry is the Hermitian shadow of the positive-definite Cartan form.
    simpa [Matrix.IsSymm, Matrix.IsHermitian] using
      (cartanMatrix_posDef_of_sufficiently_large_aux
        (A := A) (K := K) (G := G) (π := π) (P := P)
        (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
        (hP_envelope := hP_envelope)).isHermitian

-- Proof sketch: write the Cartan form as the pullback of the standard character pairing over `K`
-- along the injective scalar-extension matrix from Theorem `16-16.1-2`; the transported matrix is
-- therefore positive definite.
/-- Corollary 16-16.1-8 (2): if `K` is sufficiently large, then the Cartan matrix of `G` over the
residue field `k = A/𝔪_A`, written in the distinguished bases coming from a complete simple family
and their projective envelopes, is positive definite. -/
theorem cartanMatrix_posDef_of_sufficiently_large
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      exact (cartanMatrix k G bP bR).PosDef
  := by
    -- Reuse the dedicated owner proof so the public corollary stays source-facing.
    exact cartanMatrix_posDef_of_sufficiently_large_aux
      (A := A) (K := K) (G := G) (π := π) (P := P)
      (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (hP_envelope := hP_envelope)

/-- Helper for Corollary 16-16.1-8: the absolute value of the distinguished Cartan determinant is
the cardinality of the Cartan cokernel. -/
private theorem cartanMatrix_det_natAbs_eq_card_cokernel :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      exact
        Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) =
          Nat.card (cartanCokernel k G)
  := by
    letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    have hcartan : Function.Injective (cartanHom k G) := Representation.cartanHom_injective
    let eRange :
        finiteProjectiveGroupAlgebraGrothendieckGroup k G ≃+ (cartanHom k G).range :=
      AddMonoidHom.ofInjective hcartan
    let bRange : Module.Basis ι ℤ (cartanHom k G).range :=
      Module.Basis.map bP eRange.toIntLinearEquiv
    have hindex :
        (cartanHom k G).range.index =
          Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) := by
      -- Compute the range index from the determinant of the transported projective basis.
      rw [AddSubgroup.index_eq_natAbs_det bR (cartanHom k G).range bRange]
      congr 1
      have hbRange :
          (fun i ↦ ((bRange i : (cartanHom k G).range) : R₀[k](G))) =
            (cartanHom k G) ∘ bP := by
        ext i
        change ↑(eRange (bP i)) = cartanHom k G (bP i)
        simpa [cartanHom_projectiveClass_eq] using
          (AddMonoidHom.ofInjective_apply (f := cartanHom k G) hcartan (x := bP i))
      rw [hbRange, Module.Basis.det_apply]
      congr
      ext i j
      simp [cartanMatrix, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    -- The Cartan cokernel is the quotient by the Cartan range, so its cardinality is the range
    -- index.
    calc
      Int.natAbs (Matrix.det (cartanMatrix k G bP bR))
          = (cartanHom k G).range.index := hindex.symm
      _ = Nat.card (cartanCokernel k G) := by
        simpa [cartanCokernel] using
          (AddSubgroup.index_eq_card (H := (cartanHom k G).range) (G := R₀[k](G)))

/-- Helper for Corollary 16-16.1-8: the absolute value of the distinguished Cartan determinant is
a power of `p` because the Cartan cokernel is a finite `p`-group. -/
private theorem cartanMatrix_det_natAbs_eq_prime_pow_of_sufficiently_large
    {p : ℕ} [CharP k p] [Fact p.Prime] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      exact ∃ n : ℕ, Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) = p ^ n
  := by
    letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    have hfiniteCokernel : Finite (cartanCokernel k G) := by
      exact cartanCokernel_finite
    letI : Finite (cartanCokernel k G) := hfiniteCokernel
    have hCokernelPGroup :
        IsPGroup p (Multiplicative (cartanCokernel k G)) :=
      cartanCokernel_isPGroup
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hCokernelPGroup
    refine ⟨n, ?_⟩
    -- Replace the determinant absolute value by the Cartan-cokernel cardinality, then use the
    -- `p`-group cardinality formula.
    rw [cartanMatrix_det_natAbs_eq_card_cokernel]
    simpa using hn

/-- Helper for Corollary 16-16.1-8: once the Cartan determinant is known to be nonnegative, its
`Int.natAbs` formula upgrades to an equality in `ℤ`. -/
private theorem int_eq_natAbs_of_nonneg {z : ℤ} {n : ℕ}
    (hnatAbs : Int.natAbs z = n) (hz : 0 ≤ z) :
    z = n := by
  -- Replace `Int.natAbs z` by `z` using nonnegativity and then rewrite with the known formula.
  calc
    z = (Int.natAbs z : ℤ) := (Int.natAbs_of_nonneg hz).symm
    _ = n := by rw [hnatAbs]

/-- Helper for Corollary 16-16.1-8: any integral Gram matrix `Eᵀ * E` has nonnegative
determinant. This isolates the determinant sign step from the representation-theoretic proof of
the Cartan Gram identity. -/
private theorem Matrix.int_gram_det_nonneg_local
    {κ η : Type*} [Fintype κ] [Fintype η] [DecidableEq η]
    (E : Matrix κ η ℤ) :
    0 ≤ Matrix.det (E.transpose * E) := by
  let Eℝ : Matrix κ η ℝ := E.map (Int.castRingHom ℝ)
  have hpsd : Matrix.PosSemidef (Eℝ.transpose * Eℝ) := by
    -- After casting to `ℝ`, the Gram matrix is visibly positive semidefinite.
    simpa [Eℝ] using (Matrix.posSemidef_conjTranspose_mul_self Eℝ)
  have hmap :
      (E.transpose * E).map (Int.castRingHom ℝ) = Eℝ.transpose * Eℝ := by
    -- Entrywise, casting commutes with transpose and matrix multiplication.
    ext i j
    simp [Eℝ, Matrix.mul_apply]
  have hdet_nonneg : 0 ≤ Matrix.det (Eℝ.transpose * Eℝ) :=
    Matrix.PosSemidef.det_nonneg hpsd
  have hcast :
      ((Matrix.det (E.transpose * E) : ℤ) : ℝ) = Matrix.det (Eℝ.transpose * Eℝ) := by
    -- Rewrite the determinant after casting the integral matrix entries to `ℝ`.
    rw [Int.cast_det]
    simpa [hmap] using congrArg Matrix.det hmap
  have hreal : 0 ≤ (((Matrix.det (E.transpose * E) : ℤ) : ℝ)) := by
    rw [hcast]
    exact hdet_nonneg
  exact_mod_cast hreal

/-- Helper for Corollary 16-16.1-8: once the source-faithful proof provides a Gram factorization
`C = Eᵀ * E`, the determinant sign follows from the previous pure matrix lemma. -/
private theorem Matrix.int_det_nonneg_of_eq_transpose_mul_self_local
    {κ η : Type*} [Fintype κ] [Fintype η] [DecidableEq η]
    (C : Matrix η η ℤ) (E : Matrix κ η ℤ)
    (hC : C = E.transpose * E) :
    0 ≤ Matrix.det C := by
  -- Replace `C` by the Gram matrix exhibited by the source-faithful positive-definite route.
  simpa [hC] using Matrix.int_gram_det_nonneg_local E

/-- Helper for Corollary 16-16.1-8: after LinearRepresentations_Serre_1977's quadratic-form route has produced positive
definiteness of the distinguished Cartan matrix, only the sign bridge from `PosDef` to
`0 ≤ det C` remains before the `natAbs` formula can be turned into an equality in `ℤ`. -/
private theorem cartanMatrix_det_nonneg_of_sufficiently_large_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      exact 0 ≤ Matrix.det (cartanMatrix k G bP bR)
  := by
    classical
    letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    obtain ⟨κ, _, _, E, hGram, _⟩ :=
      cartanMatrix_source_faithful_gram_data
        (A := A) (K := K) (G := G) (π := π) (P := P)
        (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
        (hP_envelope := hP_envelope)
    exact
      Matrix.int_det_nonneg_of_eq_transpose_mul_self_local
        (C := cartanMatrix k G bP bR) E hGram

-- Proof sketch: part `(2)` gives positivity of the determinant. Corollary `16-16.1-6`
-- identifies the cokernel of the Cartan homomorphism as a finite `p`-group, so the determinant of
-- the Cartan matrix, which computes the index of the image in the distinguished bases, must be a
-- power of `p`.
/-- Corollary 16-16.1-8 (3): if `K` is sufficiently large, then the determinant of the Cartan
matrix of `G` over the residue field `k = A/𝔪_A`, written in the distinguished bases coming from a
complete simple family and their projective envelopes, is a power of `p`. -/
theorem cartanMatrix_det_eq_prime_pow_of_sufficiently_large
    {p : ℕ} [CharP k p] [Fact p.Prime]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      exact ∃ n : ℕ, Matrix.det (cartanMatrix k G bP bR) = (p : ℤ) ^ n
  := by
  -- Route correction: this sign upgrade is now completely formal once
  -- `cartanMatrix_posDef_of_sufficiently_large_aux` is finished. The remaining implementation work
  -- is to stabilize the elaboration of `Matrix.PosDef.det_pos` on the local abbreviation
  -- `C := cartanMatrix k G bP bR`, then combine it with
  -- `cartanMatrix_det_natAbs_eq_prime_pow_of_sufficiently_large` via
  -- `int_eq_natAbs_of_nonneg`.
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  obtain ⟨n, hn⟩ :=
    cartanMatrix_det_natAbs_eq_prime_pow_of_sufficiently_large
      (A := A) (G := G) (π := π) (P := P)
      (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (hP_envelope := hP_envelope) (p := p)
  refine ⟨n, ?_⟩
  have hz :
      0 ≤ Matrix.det (cartanMatrix k G bP bR) :=
    cartanMatrix_det_nonneg_of_sufficiently_large_local
      (A := A) (K := K) (G := G) (π := π) (P := P)
      (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (hP_envelope := hP_envelope)
  simpa using
    (int_eq_natAbs_of_nonneg
      (z := Matrix.det (cartanMatrix k G bP bR)) (n := p ^ n) hn hz)

end

end Representation
