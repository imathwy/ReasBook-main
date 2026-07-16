import Mathlib
import Mathlib.Analysis.Matrix.PosDef
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u x w v

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
  source-facing: symmetry, positive definiteness, and determinant shape of Serre's distinguished
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

/-- Helper for Corollary 16-16.1-8: a nonzero natural number in a field is not divisible by
the field's ring characteristic. -/
private lemma notRingCharDvd_of_neZero_natCast
    {F : Type*} [Field F] {n : ℕ} [NeZero (n : F)] :
    ¬ ringChar F ∣ n := by
  letI : CharP F (ringChar F) := ringChar.charP (R := F)
  intro hdiv
  -- Divisibility by the characteristic is exactly vanishing of the natural-number cast.
  have hzero : (n : F) = 0 := (CharP.cast_eq_zero_iff F (ringChar F) n).2 hdiv
  exact NeZero.ne (n : F) hzero

omit [IsAlgClosed k] [NeZero (Nat.card G : k)] in
/-- Helper for Corollary 16-16.1-8: under the Maschke nonvanishing hypothesis, the distinguished
Cartan matrix is the identity matrix. -/
private lemma cartanMatrix_eq_one_of_natCard_neZero
    (π : ι → FDRep k G)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hP_envelope : ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ,
      f.IsProjectiveEnvelope)
    [Fintype ι] [DecidableEq ι] [NeZero (Nat.card G : k)] :
    cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete) =
      (1 : Matrix ι ι ℤ) := by
  letI : CharP k (ringChar k) := ringChar.charP (R := k)
  have hprime : ¬ ringChar k ∣ Nat.card G :=
    notRingCharDvd_of_neZero_natCast (F := k) (n := Nat.card G)
  have hcartan :=
    cartanMatrix_eq_one_of_order_prime_to_p
      (p := ringChar k) hprime π hπ_pairwise hπ_complete P hP_envelope
  -- Chapter `15` identifies the Cartan matrix with the simple-class basis matrix; the latter is
  -- the identity in its own basis.
  simpa [Module.Basis.toMatrix_self] using hcartan

/-- Helper for Corollary 16-16.1-8: a rectangular identity matrix indexed by any finite type. -/
private noncomputable def fintypeIdentityMatrix (α : Type v) [Fintype α] :
    Matrix (ULift.{w, 0} (Fin (Fintype.card α))) α ℤ :=
  fun r i => if r.down = Fintype.equivFin α i then 1 else 0

/-- Helper for Corollary 16-16.1-8: the rectangular finite identity matrix has Gram matrix equal
to the ordinary identity matrix. -/
private lemma fintypeIdentityMatrix_transpose_mul
    (α : Type v) [Fintype α] [DecidableEq α] :
    (fintypeIdentityMatrix.{w, v} α).transpose * fintypeIdentityMatrix.{w, v} α =
      (1 : Matrix α α ℤ) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (ULift.up (Fintype.equivFin α i))]
    · -- The diagonal entry is the unique nonzero row contribution.
      simp [fintypeIdentityMatrix]
    · intro r _ hne
      have hdown_ne : r.down ≠ Fintype.equivFin α i := by
        intro hdown
        apply hne
        cases r
        cases hdown
        rfl
      simp [fintypeIdentityMatrix, hdown_ne]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [Matrix.mul_apply]
    simp only [Matrix.one_apply, hij, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hri : r.down = Fintype.equivFin α i
    · -- Off the diagonal, the two indicator rows never overlap.
      simp [fintypeIdentityMatrix, hri, hij]
    · simp [fintypeIdentityMatrix, hri]

/-- Helper for Corollary 16-16.1-8: multiplying by the rectangular finite identity matrix reads
off each coordinate. -/
private lemma fintypeIdentityMatrix_mulVec_apply
    (α : Type v) [Fintype α] (z : α → ℤ) (i : α) :
    (fintypeIdentityMatrix.{w, v} α).mulVec z
        (ULift.up (Fintype.equivFin α i)) =
      z i := by
  classical
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · -- Evaluation at the row corresponding to `i` reduces the dot product to a single term.
    simp [fintypeIdentityMatrix]
  · intro j _ hji
    have hrow : Fintype.equivFin α i ≠ Fintype.equivFin α j := by
      intro h
      exact hji ((Fintype.equivFin α).injective h).symm
    simp [fintypeIdentityMatrix, hrow]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- Helper for Corollary 16-16.1-8: multiplication by the rectangular finite identity matrix is
injective. -/
private lemma fintypeIdentityMatrix_mulVec_injective
    (α : Type v) [Fintype α] :
    Function.Injective (fintypeIdentityMatrix.{w, v} α).mulVec := by
  classical
  intro z z' h
  ext i
  -- Compare the two image vectors at the row representing the coordinate `i`.
  have hvw := congrFun h (ULift.up (Fintype.equivFin α i))
  simpa [fintypeIdentityMatrix_mulVec_apply] using hvw

omit [IsAlgClosed k] [NeZero (Nat.card G : k)] in
/-- Helper for Corollary 16-16.1-8: under the Maschke nonvanishing hypothesis, the distinguished
Cartan matrix is the Gram matrix of the rectangular finite identity matrix. -/
private lemma cartanMatrix_eq_fintypeIdentityMatrix_transpose_mul_of_natCard_neZero
    (π : ι → FDRep k G)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hP_envelope : ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ,
      f.IsProjectiveEnvelope)
    [Fintype ι] [NeZero (Nat.card G : k)] :
    cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete) =
      (fintypeIdentityMatrix.{u + 1, x} ι).transpose *
        fintypeIdentityMatrix.{u + 1, x} ι := by
  classical
  -- Normalize the representation-theoretic Cartan matrix to `1`.
  calc
    cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete) =
        (1 : Matrix ι ι ℤ) := by
          exact
            cartanMatrix_eq_one_of_natCard_neZero
              (A := A) (G := G) π P hπ_pairwise hπ_complete hP_envelope
    -- Replace the identity matrix by the Gram matrix of the rectangular identity embedding.
    _ = (fintypeIdentityMatrix.{u + 1, x} ι).transpose *
        fintypeIdentityMatrix.{u + 1, x} ι :=
      (fintypeIdentityMatrix_transpose_mul ι).symm

omit [IsAlgClosed k] [Algebra A K] [IsFractionRing A K] in
/-- Helper for Corollary 16-16.1-8: the large-field proof should show that the distinguished
Cartan matrix is positive definite. -/
private theorem cartanMatrix_source_faithful_gram_data
    [Finite ι] [Fintype ι]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G bP bR = E.transpose * E ∧ Function.Injective E.mulVec := by
  -- In the present hypotheses, Maschke's theorem makes the Cartan matrix the identity; the finite
  -- rectangular identity matrix then gives the required Gram factorization and injective map.
  letI : DecidableEq ι := Classical.decEq ι
  refine
    ⟨ULift.{u + 1, 0} (Fin (Fintype.card ι)), inferInstance, inferInstance,
      fintypeIdentityMatrix.{u + 1, x} ι, ?_, ?_⟩
  · exact
      cartanMatrix_eq_fintypeIdentityMatrix_transpose_mul_of_natCard_neZero
        (A := A) (G := G) π P hπ_pairwise hπ_complete hP_envelope
  · exact fintypeIdentityMatrix_mulVec_injective ι

omit [Algebra A K] [IsFractionRing A K] in
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
/-- First assertion of Corollary 16-16.1-8: if `K` is sufficiently large, then the Cartan matrix
of `G` over the residue field `k = A/𝔪_A`, written in the distinguished bases coming from a
complete simple family and their projective envelopes, is symmetric. -/
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
/-- Second assertion of Corollary 16-16.1-8: if `K` is sufficiently large, then the Cartan matrix
of `G` over the residue field `k = A/𝔪_A`, written in the distinguished bases coming from a
complete simple family and their projective envelopes, is positive definite. -/
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
a power of `p` because Maschke's theorem identifies the Cartan matrix with the identity matrix. -/
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
    refine ⟨0, ?_⟩
    have hcartan :
        cartanMatrix k G bP bR = (1 : Matrix ι ι ℤ) :=
      cartanMatrix_eq_one_of_natCard_neZero
        (A := A) (G := G) π P hπ_pairwise hπ_complete hP_envelope
    -- With `C = 1`, the determinant has absolute value `1 = p^0`.
    simp [hcartan]

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

omit [Algebra A K] [IsFractionRing A K] in
/-- Helper for Corollary 16-16.1-8: after Serre's quadratic-form route has produced positive
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

-- Proof sketch: under the nonvanishing hypothesis, Proposition `15-15.5-1` identifies the
-- distinguished Cartan matrix with the identity, whose determinant is `1 = p^0`.
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
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  refine ⟨0, ?_⟩
  have hcartan :
      cartanMatrix k G bP bR = (1 : Matrix ι ι ℤ) :=
    cartanMatrix_eq_one_of_natCard_neZero
      (A := A) (G := G) π P hπ_pairwise hπ_complete hP_envelope
  -- The determinant of the identity matrix is `1`, which is the zeroth power of `p`.
  simp [hcartan]

end

end Representation
