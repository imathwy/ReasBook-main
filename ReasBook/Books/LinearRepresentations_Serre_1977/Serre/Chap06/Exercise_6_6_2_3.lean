import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra InnerProductSpace Representation
open CategoryTheory
open MonoidAlgebra

noncomputable section

namespace MonoidAlgebra

section

variable {R G : Type} [Semiring R] [StarAddMonoid R] [Group G]

/-- The canonical conjugate-inverse element of a group algebra. Its coefficient at `s` is the star
of the coefficient of the original element at `s⁻¹`. -/
noncomputable def conjInv (a : R[G]) : R[G] :=
  mapDomain Inv.inv (a.mapRange star (star_zero _))

@[simp] theorem conjInv_apply (a : R[G]) (s : G) : conjInv a s = star (a s⁻¹) := by
  simpa [conjInv] using
    (Finsupp.mapDomain_apply inv_injective (a.mapRange star (star_zero _)) s⁻¹)

end

end MonoidAlgebra

namespace Representation

attribute [local instance] Fintype.ofFinite

section

variable {ι G : Type} [Group G] [Finite G]
variable (π : ι → FDRep ℂ G)
variable [IsCompleteIrreducibleFamily π]

/-- Helper for Exercise 6-6.2-3: the coefficient of `1` in `MonoidAlgebra.conjInv a * a` is the
sum of the squared norms of the coefficients of `a`. -/
lemma conjInv_mul_apply_one_eq_sum_normSq (a : ℂ[G]) :
    (MonoidAlgebra.conjInv a * a) 1 = ((∑ s : G, Complex.normSq (a s) : ℝ) : ℂ) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- Rewrite the coefficient of the product as the coefficientwise support sum in the right factor.
  rw [MonoidAlgebra.mul_apply_right, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp only [MonoidAlgebra.conjInv_apply, one_mul, inv_inv]
  -- Each term is `conj (a s) * a s`, which is exactly `normSq (a s)` over `ℂ`.
  suffices
      ∑ s : G, star (a s) * a s = ∑ s : G, (Complex.normSq (a s) : ℂ) by
    simpa using this
  refine Finset.sum_congr rfl fun s _ => ?_
  simpa [Complex.normSq_eq_norm_sq] using (RCLike.conj_mul (a s))

-- Proof sketch: apply Proposition
-- `groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace` to `MonoidAlgebra.conjInv a * a` at
-- `s = 1` gives the formula, since the coefficient of `1` in `MonoidAlgebra.conjInv a * a` is
-- `∑ s, |a_s|^2`. The basis-dependent
-- matrix identity is a companion bridge theorem below.
/-- Exercise 6-6.2-3 at the canonical Wedderburn owner layer: for `a = ∑ a_s s ∈ ℂ[G]`, the sum of
the squared moduli of its coefficients is the normalized sum of the traces of the canonical
Wedderburn components of the canonical conjugate-inverse product
`MonoidAlgebra.conjInv a * a` on the irreducible factors. -/
theorem groupAlgebra_plancherel_formula
    (hpairwise : PairwiseNonisomorphic π)
    (a : ℂ[G]) :
    let _ : Finite ι :=
      IsCompleteIrreducibleFamily.finite_index π inferInstance hpairwise
    let _ : Fintype ι := Fintype.ofFinite ι
    let φ := ρ̃[fun i ↦ Rep.of (π i).ρ]
    ((∑ s : G, Complex.normSq (a s) : ℝ) : ℂ) =
      (Nat.card G : ℂ)⁻¹ *
        ∑ i : ι,
          (Module.finrank ℂ (π i) : ℂ) *
            LinearMap.trace ℂ (π i) (φ (MonoidAlgebra.conjInv a * a) i) := by
  classical
  let _ : Finite ι :=
    IsCompleteIrreducibleFamily.finite_index π inferInstance hpairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : DecidableEq ι := Classical.decEq ι
  let φ := ρ̃[fun i ↦ Rep.of (π i).ρ]
  letI : Invertible (Nat.card G : ℂ) := by
    refine invertibleOfNonzero ?_
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hpairwise_rep : PairwiseNonisomorphic (fun i ↦ Rep.of (π i).ρ) := by
    intro i j hij hij_iso
    apply hpairwise hij
    rcases hij_iso with ⟨e⟩
    exact ⟨(forget₂ (FDRep ℂ G) (Rep ℂ G)).preimageIso e⟩
  have hcomplete_rep :
      IsCompleteIrreducibleFamily (fun i ↦ FDRep.of ((fun i ↦ Rep.of (π i).ρ) i).ρ) := by
    simpa using (inferInstance : IsCompleteIrreducibleFamily π)
  -- Evaluate Proposition `6-6.2-2` at the positive element `MonoidAlgebra.conjInv a * a`
  -- and the identity element of `G`.
  have hcoeff :=
    Representation.groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace
      (π := fun i ↦ Rep.of (π i).ρ)
      hpairwise_rep hcomplete_rep
      (u := MonoidAlgebra.conjInv a * a) (s := (1 : G))
  -- The left-hand side is the coefficient computation above, and the right-hand side simplifies
  -- because `ρ(1) = 1`.
  simpa [φ, conjInv_mul_apply_one_eq_sum_normSq, Representation.finsum_eq_sum_univ] using hcoeff

end

section

variable {ι G : Type} [Group G] [Finite G]
variable {V : ι → Type}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
variable [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i))
variable [IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (ρ i))]

omit [Finite G] [IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (ρ i))] in
/-- Helper for Exercise 6-6.2-3: a unitary representation sends `s⁻¹` to the adjoint of `s`. -/
lemma rep_adjoint_eq_inv
    (hunitary : ∀ i (s : G) (x y : V i), ⟪ρ i s x, ρ i s y⟫_ℂ = ⟪x, y⟫_ℂ)
    (i : ι) (s : G) :
    LinearMap.adjoint (ρ i s) = ρ i s⁻¹ := by
  -- Characterize the adjoint by the inner-product identity supplied by unitarity.
  symm
  refine (LinearMap.eq_adjoint_iff (A := ρ i s⁻¹) (B := ρ i s)).2 ?_
  intro x y
  have hs := hunitary i s (ρ i s⁻¹ x) y
  simpa [Representation.self_inv_apply, Module.End.mul_apply] using hs.symm

/-- Helper for Exercise 6-6.2-3: `conjInv` on the group algebra is sent to adjoint on each
representation factor. -/
lemma asAlgebraHom_conjInv_eq_adjoint
    (hunitary : ∀ i (s : G) (x y : V i), ⟪ρ i s x, ρ i s y⟫_ℂ = ⟪x, y⟫_ℂ)
    (i : ι) (a : ℂ[G]) :
    (ρ i).asAlgebraHom (MonoidAlgebra.conjInv a) = LinearMap.adjoint ((ρ i).asAlgebraHom a) := by
  -- Route correction: prove the star-compatibility first, then rewrite `star = adjoint`.
  have hstar :
      (ρ i).asAlgebraHom (MonoidAlgebra.conjInv a) = star ((ρ i).asAlgebraHom a) := by
    refine MonoidAlgebra.induction_on
      (p := fun a : ℂ[G] =>
        (ρ i).asAlgebraHom (MonoidAlgebra.conjInv a) = star ((ρ i).asAlgebraHom a))
      a ?_ ?_ ?_
    · intro g
      -- On basis group elements, `conjInv` sends `g` to `g⁻¹`, and unitarity identifies
      -- `ρ(g⁻¹)` with the adjoint of `ρ(g)`.
      have hconjInv_single_one :
          MonoidAlgebra.conjInv (MonoidAlgebra.single g (1 : ℂ)) =
            MonoidAlgebra.single g⁻¹ (1 : ℂ) := by
        ext s
        by_cases hs : s = g⁻¹
        · subst hs
          simp [MonoidAlgebra.conjInv_apply]
        · have hs' : s⁻¹ ≠ g := by
            intro hsg
            apply hs
            simpa using congrArg Inv.inv hsg
          simp [MonoidAlgebra.conjInv_apply, hs, hs']
      simpa
        [hconjInv_single_one, Representation.asAlgebraHom_single_one, LinearMap.star_eq_adjoint]
        using
        (rep_adjoint_eq_inv (ρ := ρ) hunitary i g).symm
    · intro a b ha hb
      -- Both `conjInv` and adjoint are additive.
      have hconjInv_add :
          MonoidAlgebra.conjInv (a + b) = MonoidAlgebra.conjInv a + MonoidAlgebra.conjInv b := by
        ext s
        simp [MonoidAlgebra.conjInv_apply]
      simp [hconjInv_add, map_add, ha, hb]
    · intro c a ha
      -- `conjInv` is conjugate-linear in the coefficients, matching the star-linearity of adjoint.
      have hconjInv_smul : MonoidAlgebra.conjInv (c • a) = star c • MonoidAlgebra.conjInv a := by
        ext s
        simp [MonoidAlgebra.conjInv_apply, smul_eq_mul]
      simpa [hconjInv_smul, map_smul] using congrArg (fun T => star c • T) ha
  simpa [LinearMap.star_eq_adjoint] using hstar

/-- Helper for Exercise 6-6.2-3: the factor trace of `MonoidAlgebra.conjInv a * a` is the trace
of the conjugate-transpose product of the corresponding matrix. -/
lemma trace_factor_conjInv_mul_eq_matrix_trace
    (b : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (V i))) ℂ (V i))
    (hunitary : ∀ i (s : G) (x y : V i), ⟪ρ i s x, ρ i s y⟫_ℂ = ⟪x, y⟫_ℂ)
    (a : ℂ[G]) (i : ι) :
    let φ := ρ̃[fun i ↦ Rep.of (ρ i)]
    let A := fun i ↦ (φ a i).toMatrix (b i).toBasis (b i).toBasis
    LinearMap.trace ℂ (V i) (φ (MonoidAlgebra.conjInv a * a) i) =
      ((A i).conjTranspose * A i).trace := by
  let φ := ρ̃[fun i ↦ Rep.of (ρ i)]
  let A := fun i ↦ (φ a i).toMatrix (b i).toBasis (b i).toBasis
  have hfactor' :
      (ρ i).asAlgebraHom (MonoidAlgebra.conjInv a * a) =
        LinearMap.adjoint ((ρ i).asAlgebraHom a) * (ρ i).asAlgebraHom a := by
    -- Push the product through the algebra hom and replace `conjInv` by adjoint.
    rw [map_mul, asAlgebraHom_conjInv_eq_adjoint (ρ := ρ) hunitary i a]
  have hfactor :
      φ (MonoidAlgebra.conjInv a * a) i = LinearMap.adjoint (φ a i) * φ a i := by
    simpa [φ] using hfactor'
  -- Convert the intrinsic trace to matrix trace in the chosen orthonormal basis.
  calc
    LinearMap.trace ℂ (V i) (φ (MonoidAlgebra.conjInv a * a) i)
        = LinearMap.trace ℂ (V i) (LinearMap.adjoint (φ a i) * φ a i) := by
            rw [hfactor]
    _ = (((LinearMap.adjoint (φ a i) * φ a i).toMatrix (b i).toBasis (b i).toBasis)).trace := by
          rw [LinearMap.trace_eq_matrix_trace ℂ (b i).toBasis]
    _ = ((((LinearMap.adjoint (φ a i)).toMatrix (b i).toBasis (b i).toBasis) *
            ((φ a i).toMatrix (b i).toBasis (b i).toBasis))).trace := by
          rw [LinearMap.toMatrix_mul]
    _ = ((A i).conjTranspose * A i).trace := by
          simp [A, LinearMap.toMatrix_adjoint]

-- Proof sketch: apply the owner-level formula above to `a`. Unitarity identifies
-- `(ρ i).asAlgebraHom (MonoidAlgebra.conjInv a * a)` with
-- `star ((ρ i).asAlgebraHom a) * (ρ i).asAlgebraHom a`, and
-- `LinearMap.trace_eq_matrix_trace` together with `LinearMap.toMatrix_adjoint` turns that
-- intrinsic trace into the usual
-- matrix expression `(A i).conjTranspose * A i` in the chosen orthonormal basis.
/-- Exercise 6-6.2-3 in orthonormal bases: the intrinsic Plancherel trace formula becomes the
usual matrix identity `∑ |a_s|² = |G|⁻¹ ∑ dim(V_i) Tr({}^t\!\overline{A_i} · A_i)`, where `A_i`
is the matrix of the `i`-th canonical Wedderburn component of `a`. -/
theorem groupAlgebra_plancherel_formula_matrix
    (hpairwise : PairwiseNonisomorphic (fun i ↦ Rep.of (ρ i)))
    (b : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (V i))) ℂ (V i))
    (hunitary : ∀ i (s : G) (x y : V i), ⟪ρ i s x, ρ i s y⟫_ℂ = ⟪x, y⟫_ℂ)
    (a : ℂ[G]) :
    let _ : Finite ι :=
      IsCompleteIrreducibleFamily.finite_index_of_rep (fun i ↦ Rep.of (ρ i)) inferInstance
        hpairwise
    let _ : Fintype ι := Fintype.ofFinite ι
    let φ := ρ̃[fun i ↦ Rep.of (ρ i)]
    let A := fun i ↦ (φ a i).toMatrix (b i).toBasis (b i).toBasis
    ((∑ s : G, Complex.normSq (a s) : ℝ) : ℂ) =
      (Nat.card G : ℂ)⁻¹ *
        ∑ i : ι,
          (Module.finrank ℂ (V i) : ℂ) * ((A i).conjTranspose * A i).trace := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let _ : Finite ι :=
    IsCompleteIrreducibleFamily.finite_index_of_rep (fun i ↦ Rep.of (ρ i)) inferInstance
      hpairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  let φ := ρ̃[fun i ↦ Rep.of (ρ i)]
  let A := fun i ↦ (φ a i).toMatrix (b i).toBasis (b i).toBasis
  have hpairwise_fdrep :
      PairwiseNonisomorphic (fun i ↦ FDRep.of (ρ i)) := by
    simpa using
      (Representation.pairwiseNonisomorphic_fdrep_of_rep (π := fun i ↦ Rep.of (ρ i)) hpairwise)
  -- First apply the intrinsic Plancherel formula to the finite-dimensional owner family.
  have hmain :=
    Representation.groupAlgebra_plancherel_formula
      (π := fun i ↦ FDRep.of (ρ i))
      hpairwise_fdrep a
  -- Then rewrite each factor trace as the matrix trace of `A iᴴ * A i`.
  calc
    ((∑ s : G, Complex.normSq (a s) : ℝ) : ℂ)
        = (Nat.card G : ℂ)⁻¹ *
            ∑ i : ι,
              (Module.finrank ℂ (V i) : ℂ) *
                LinearMap.trace ℂ (V i) (φ (MonoidAlgebra.conjInv a * a) i) := by
            simpa [φ, Nat.card_eq_fintype_card] using hmain
    _ = (Nat.card G : ℂ)⁻¹ *
          ∑ i : ι,
            (Module.finrank ℂ (V i) : ℂ) * ((A i).conjTranspose * A i).trace := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          simpa [φ, A] using
            trace_factor_conjInv_mul_eq_matrix_trace (ρ := ρ) b hunitary a i

end

end Representation
