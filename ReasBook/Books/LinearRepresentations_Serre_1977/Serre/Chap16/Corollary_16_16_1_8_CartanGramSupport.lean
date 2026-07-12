import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6

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

/-- Helper for Corollary 16-16.1-8: support theorem packaging the source-faithful Gram
factorization of the distinguished Cartan matrix. -/
theorem cartanMatrix_source_faithful_gram_data_support
    (π : ι → FDRep (IsLocalRing.ResidueField A) G)
    (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hP_envelope :
      ∀ i, ∃ f :
        (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    [Finite ι] [Fintype ι]
    [NeZero (Nat.card G : IsLocalRing.ResidueField A)]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    -- `k = ResidueField A` must be a SPLITTING field for the Gram factorization `C = Eᵀ * E` to
    -- hold: the conclusion forces `C` symmetric, but over a non-splitting residue field the Cartan
    -- matrix is only symmetric after weighting by `fᵢ = dim_k End(Sᵢ)` (`C·diag f` symmetric),
    -- so it
    -- is generally NON-symmetric (e.g. `G = A₄`, `p = 2`, `k = 𝔽₂`).  `[IsAlgClosed k]` (matching
    -- the consumer `Corollary_16_16_1_8.lean`) makes all `fᵢ = 1` and `C = Dᵀ * D` symmetric.
    [IsAlgClosed (IsLocalRing.ResidueField A)] :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete) =
        E.transpose * E ∧ Function.Injective E.mulVec := by
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

end

end Representation
