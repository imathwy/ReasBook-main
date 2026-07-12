import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_2_2

/-!
# General-field Fourier inversion / Schur orthogonality for `Proposition 16-16.4-1`

The characteristic-zero branch of `Proposition 16-16.4-1` needs Schur's matrix-coefficient
orthogonality and the resulting Fourier inversion over the algebraic closure `AlgebraicClosure K`
of the (characteristic-zero) fraction field, i.e. over a *general* algebraically closed field, not
just `ℂ`.  `Serre/Chap02/Corollary_2_2_2_2.lean` already provides the Schur averaging machinery
(`averageMap_linHom_self_eq_trace_smul_id`, `averageMap_linHom_basis_entry_eq`,
`averageMap_linHom_eq_zero_of_not_isomorphic`) over a general algebraically closed field; only the
final orthogonality corollaries (`Corollary_2_2_2_3/4`) were specialised to `ℂ`.  This file ports
the matrix-coefficient orthogonality to a general field, which is the foundation for the
supported-family coefficient formula used by the packet argument.
-/

open scoped BigOperators MonoidAlgebra
noncomputable section
universe u v w

namespace Representation

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeG_fourierInvGeneral : Fintype G := Fintype.ofFinite G

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {ι : Type w} [Fintype ι]
variable [Invertible (Fintype.card G : k)] [Invertible (Module.finrank k V : k)]

open scoped Classical in
/-- General-field form of Corollary 2-2.2-4: for an irreducible finite-dimensional representation
over an algebraically closed field in which `|G|` and `dim V` are invertible, the averaged product
of matrix coefficients `ρ(t⁻¹)_{i2 j2}` and `ρ(t)_{j1 i1}` is `(dim V)⁻¹` when `i1 = i2, j1 = j2`,
and `0` otherwise.  (The `ℂ`-only `Representation.matrix_coefficient_orthogonality_of_irreducible`
ports verbatim because all its inputs are already general-field.) -/
theorem matrixCoeff_orthogonality_irreducible_general
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (b : Module.Basis ι k V)
    (i1 j1 i2 j2 : ι) :
    (Nat.card G : k)⁻¹ *
        ∑ t : G, (ρ t⁻¹).toMatrix b b i2 j2 * (ρ t).toMatrix b b j1 i1 =
      if i2 = i1 then
        if j2 = j1 then (Module.finrank k V : k)⁻¹ else 0
      else 0 := by
  classical
  let e : Module.End k V := b.end (j2, j1)
  have htrace : LinearMap.trace k V e = if j2 = j1 then 1 else 0 := by
    dsimp [e]
    rw [Module.Basis.end_apply, Matrix.trace_toLin_eq, Matrix.stdBasis_eq_single]
    by_cases h : j2 = j1
    · subst h
      simp [Matrix.trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne j2 j1 (1 : k) h, h]
  calc
    (Nat.card G : k)⁻¹ *
        ∑ t : G, (ρ t⁻¹).toMatrix b b i2 j2 * (ρ t).toMatrix b b j1 i1
      = (((ρ.linHom ρ).averageMap e).toMatrix b b i2 i1) := by
          simpa [e, Nat.card_eq_fintype_card] using
            (averageMap_linHom_basis_entry_eq ρ ρ b b i1 j1 i2 j2).symm
    _ = ((((Module.finrank k V : k)⁻¹ * LinearMap.trace k V e) •
          (LinearMap.id : V →ₗ[k] V)).toMatrix b b i2 i1) := by
          simpa [e] using congrArg (fun f ↦ f.toMatrix b b i2 i1)
            (averageMap_linHom_self_eq_trace_smul_id ρ e)
    _ = if i2 = i1 then
          if j2 = j1 then (Module.finrank k V : k)⁻¹ else 0
        else 0 := by
          rw [htrace]
          by_cases hj : j2 = j1 <;> simp [hj, Matrix.one_apply]

/-- Operator-level Fourier inversion: for an irreducible finite-dimensional representation over an
algebraically closed field with `|G|` and `dim V` invertible, every endomorphism `f` is recovered
from its matrix-coefficient Fourier coefficients `Tr (ρ s⁻¹ ∘ f)`:
`(dim V / |G|) • ∑ s, Tr (ρ s⁻¹ ∘ f) • ρ s = f`. This is the `i = j` (single-rep) building block of
the Wedderburn Fourier-coefficient formula. -/
theorem fourier_inversion_irreducible_general
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (f : Module.End k V) :
    ((Module.finrank k V : k) / Nat.card G) •
        (∑ s : G, LinearMap.trace k V (ρ s⁻¹ * f) • ρ s) = f := by
  classical
  -- Use Classical decidability for the basis index so the `toMatrix` instance matches the
  -- `open scoped Classical`-stated `matrixCoeff_orthogonality_irreducible_general`.
  letI : DecidableEq (Fin (Module.finrank k V)) := Classical.decEq _
  let b : Module.Basis (Fin (Module.finrank k V)) k V := Module.finBasis k V
  have hcardne : (Nat.card G : k) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact isUnit_iff_ne_zero.mp (isUnit_of_invertible (Fintype.card G : k))
  have hdimne : (Module.finrank k V : k) ≠ 0 :=
    isUnit_iff_ne_zero.mp (isUnit_of_invertible (Module.finrank k V : k))
  -- Each Fourier coefficient `Tr (ρ s⁻¹ ∘ f)` as a double matrix sum.
  have htr : ∀ s : G,
      LinearMap.trace k V (ρ s⁻¹ * f) =
        ∑ a : Fin (Module.finrank k V), ∑ e : Fin (Module.finrank k V),
          (LinearMap.toMatrix b b (ρ s⁻¹)) a e * (LinearMap.toMatrix b b f) e a := by
    intro s
    rw [LinearMap.trace_eq_matrix_trace k b, show (ρ s⁻¹ * f) = ρ s⁻¹ ∘ₗ f from rfl,
      LinearMap.toMatrix_comp b b b]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  -- Reduce to a matrix-entry identity in the chosen basis `b`.
  apply (LinearMap.toMatrix b b).injective
  rw [map_smul, map_sum]
  ext c d
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  -- Entry-level orthogonality (rewritten from `matrixCoeff_orthogonality_irreducible_general`).
  have horth : ∀ a e : Fin (Module.finrank k V),
      (∑ s : G, (LinearMap.toMatrix b b (ρ s⁻¹)) a e * (LinearMap.toMatrix b b (ρ s)) c d) =
        (Nat.card G : k) *
          (if a = d then if e = c then (Module.finrank k V : k)⁻¹ else 0 else 0) := by
    intro a e
    have h := matrixCoeff_orthogonality_irreducible_general ρ b d c a e
    have hS : (∑ s : G, (LinearMap.toMatrix b b (ρ s⁻¹)) a e * (LinearMap.toMatrix b b (ρ s)) c d)
        = (Nat.card G : k) * ((Nat.card G : k)⁻¹ *
            ∑ s : G, (LinearMap.toMatrix b b (ρ s⁻¹)) a e * (LinearMap.toMatrix b b (ρ s)) c d) := by
      rw [← mul_assoc, mul_inv_cancel₀ hcardne, one_mul]
    rw [hS, h]
  -- Each summand `(Tr • ρ s) c d = Tr * (M ρ s) c d`.
  have hentry : ∀ s : G,
      (LinearMap.toMatrix b b (LinearMap.trace k V (ρ s⁻¹ * f) • ρ s)) c d =
        LinearMap.trace k V (ρ s⁻¹ * f) * (LinearMap.toMatrix b b (ρ s)) c d := by
    intro s; rw [map_smul, Matrix.smul_apply, smul_eq_mul]
  -- Rearrange: distribute the trace expansion and exchange the `s`-sum inward.
  have hrearrange :
      (∑ s : G, (LinearMap.toMatrix b b (LinearMap.trace k V (ρ s⁻¹ * f) • ρ s)) c d) =
        ∑ a : Fin (Module.finrank k V), ∑ e : Fin (Module.finrank k V),
          (LinearMap.toMatrix b b f) e a *
            ∑ s : G, (LinearMap.toMatrix b b (ρ s⁻¹)) a e * (LinearMap.toMatrix b b (ρ s)) c d := by
    simp_rw [hentry, htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  rw [hrearrange]
  simp_rw [horth]
  -- Collapse the double `if` sum to the single surviving `(c, d)` entry.
  have hcollapse :
      (∑ a : Fin (Module.finrank k V), ∑ e : Fin (Module.finrank k V),
          (LinearMap.toMatrix b b f) e a *
            ((Nat.card G : k) *
              (if a = d then if e = c then (Module.finrank k V : k)⁻¹ else 0 else 0))) =
        (LinearMap.toMatrix b b f) c d * ((Nat.card G : k) * (Module.finrank k V : k)⁻¹) := by
    rw [Finset.sum_eq_single d]
    · rw [Finset.sum_eq_single c]
      · simp
      · intro e _ hec; simp [hec]
      · intro h; exact absurd (Finset.mem_univ c) h
    · intro a _ had
      refine Finset.sum_eq_zero (fun e _ => ?_)
      simp [had]
    · intro h; exact absurd (Finset.mem_univ d) h
  rw [hcollapse,
    show (Module.finrank k V : k) / Nat.card G *
        ((LinearMap.toMatrix b b f) c d * ((Nat.card G : k) * (Module.finrank k V : k)⁻¹)) =
      (LinearMap.toMatrix b b f) c d *
        ((Module.finrank k V : k) * (Module.finrank k V : k)⁻¹) *
          ((Nat.card G : k) / Nat.card G) from by ring]
  rw [mul_inv_cancel₀ hdimne, div_self hcardne, mul_one, mul_one]

end


end Representation
