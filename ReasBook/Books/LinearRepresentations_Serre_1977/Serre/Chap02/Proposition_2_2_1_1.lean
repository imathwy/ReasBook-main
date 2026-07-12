import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section FiniteOrderCharpolyRoots

variable {G : Type u} [Group G]
variable {k : Type w} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

namespace Representation

open Module.End

variable (ρ : Representation k G V)

/-- Helper for finite-order character arguments: a root of the characteristic polynomial of `ρ s`
has `orderOf s`-th power equal to `1`. -/
lemma charpoly_root_pow_orderOf_eq_one (s : G) {μ : k}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    μ ^ orderOf s = 1 := by
  have hρs_pow_eq_one : (ρ s) ^ orderOf s = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hμeig : HasEigenvalue (ρ s) μ :=
    (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).2 <|
      (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).1 hμ
  have hμpow : HasEigenvalue (1 : Module.End k V) (μ ^ orderOf s) := by
    simpa [hρs_pow_eq_one] using hμeig.pow (orderOf s)
  obtain ⟨v, hv⟩ := hμpow.exists_hasEigenvector
  have hsmul : (μ ^ orderOf s - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← hv.apply_eq_smul]
    simp
  exact sub_eq_zero.mp <| (smul_eq_zero_iff_left hv.2).mp hsmul

end Representation

end FiniteOrderCharpolyRoots

section

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- Proposition 2-2.1-1 (1): the character at the identity element equals the degree
`Module.finrank ℂ V` of the representation. This is the existing theorem
`Representation.char_one`. -/
recall Representation.char_one

namespace Representation

open Module.End

variable (ρ : Representation ℂ G V)

/- Bridge/view for Proposition 2-2.1-1 (2): if `s` has finite order, then the character at `s⁻¹`
is the complex conjugate of the character at `s`. The source finite-group statement is recovered
from `isOfFinOrder_of_finite`. -/
-- Proof sketch: if `s : G` has finite order, then `ρ s` has finite order as a
-- linear automorphism. Its eigenvalues are roots of unity, hence their inverses are their complex
-- conjugates; taking traces gives the stated identity.
/-- Helper for Proposition 2-2.1-1: over `ℂ`, a finite-order root of the characteristic
polynomial has conjugate equal to its inverse. -/
lemma star_eq_inv_of_charpoly_root (s : G) (hs : IsOfFinOrder s) {μ : ℂ}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    star μ = μ⁻¹ := by
  -- The previous lemma puts `μ` on the unit circle.
  have hμpow : μ ^ orderOf s = 1 :=
    ρ.charpoly_root_pow_orderOf_eq_one s hμ
  have hnorm : ‖μ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hμpow hs.orderOf_pos.ne'
  simpa using (Complex.inv_eq_conj hnorm).symm

/-- Helper for Proposition 2-2.1-1: the trace of `ρ s⁻¹` is the sum of the inverse roots of the
characteristic polynomial of `ρ s`. -/
lemma trace_inv_eq_sum_inv_charpoly_roots (s : G) :
    LinearMap.trace ℂ V (ρ s⁻¹) = ((ρ s).charpoly.roots.map fun μ ↦ μ⁻¹).sum := by
  let b := Module.Free.chooseBasis ℂ V
  let ι := Module.Free.ChooseBasisIndex ℂ V
  let A : Matrix ι ι ℂ :=
    LinearMap.toMatrix b b (ρ s)
  by_cases hι : IsEmpty ι
  · letI := hι
    -- In the zero-dimensional case both traces and root sums vanish.
    rw [LinearMap.trace_eq_matrix_trace ℂ b, ← LinearMap.charpoly_toMatrix (ρ s) b]
    simp [b, ι]
  · letI := Classical.decEq ι
    letI : Nonempty ι := not_isEmpty_iff.mp hι
    have hA_mul : A * LinearMap.toMatrix b b (ρ s⁻¹) = 1 := by
      -- The matrix of `ρ s⁻¹` is a right inverse for the matrix of `ρ s`.
      change LinearMap.toMatrix b b (ρ s) * LinearMap.toMatrix b b (ρ s⁻¹) = 1
      rw [← LinearMap.toMatrix_mul b (ρ s) (ρ s⁻¹), ← ρ.map_mul, mul_inv_cancel,
        ρ.map_one, LinearMap.toMatrix_one]
    have hAinv : A⁻¹ = LinearMap.toMatrix b b (ρ s⁻¹) :=
      Matrix.inv_eq_right_inv hA_mul
    have hAeval0_ne : A.charpoly.eval 0 ≠ 0 := by
      -- Invertibility of `A` forces the constant coefficient of its characteristic polynomial
      -- to be nonzero.
      intro h0
      have hdet0 : A.det = 0 := by
        rw [Matrix.det_eq_sign_charpoly_coeff, Polynomial.coeff_zero_eq_eval_zero, h0]
        simp
      exact (Matrix.isUnit_det_of_right_inverse hA_mul).ne_zero hdet0
    have hscalar :
        (-1 : ℂ) ^ Fintype.card ι * A.det⁻¹ = (A.charpoly.eval 0)⁻¹ := by
      rw [Matrix.det_eq_sign_charpoly_coeff, Polynomial.coeff_zero_eq_eval_zero]
      field_simp [hAeval0_ne]
    have hcoeff_rev :
        A.charpolyRev.coeff (Fintype.card ι - 1) = A.charpoly.coeff 1 := by
      -- The coefficient just below the top degree in the reverse polynomial is the linear
      -- coefficient of the original characteristic polynomial.
      rw [← A.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim]
      have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos
      have hsub : Fintype.card ι - (Fintype.card ι - 1) = 1 := by omega
      simp [hsub]
    have htrace_inv :
        A⁻¹.trace = - (A.charpoly.derivative.eval 0 / A.charpoly.eval 0) := by
      -- `charpoly_inv` expresses the characteristic polynomial of `A⁻¹`; extracting the
      -- coefficient of degree `dim V - 1` gives a trace formula for the inverse.
      have hA_unit : IsUnit A := IsUnit.of_mul_eq_one _ hA_mul
      have hcoeff_outer :
          (Polynomial.C ((-1 : ℂ) ^ Fintype.card ι) *
              (Polynomial.C (Ring.inverse A.det) * A.charpolyRev)).coeff
              (Fintype.card ι - 1) =
            (-1 : ℂ) ^ Fintype.card ι *
              (Polynomial.C (Ring.inverse A.det) * A.charpolyRev).coeff (Fintype.card ι - 1) := by
        simpa [mul_assoc] using
          (Polynomial.coeff_C_mul (p := Polynomial.C (Ring.inverse A.det) * A.charpolyRev)
            (a := (-1 : ℂ) ^ Fintype.card ι) (n := Fintype.card ι - 1))
      have hcoeff_inner :
          (Polynomial.C (Ring.inverse A.det) * A.charpolyRev).coeff (Fintype.card ι - 1) =
            A.det⁻¹ * A.charpolyRev.coeff (Fintype.card ι - 1) := by
        simp [Polynomial.coeff_C_mul, Ring.inverse_eq_inv]
      have hcoeff_total :
          (Polynomial.C ((-1 : ℂ) ^ Fintype.card ι) *
              (Polynomial.C (Ring.inverse A.det) * A.charpolyRev)).coeff
              (Fintype.card ι - 1) =
            (((-1 : ℂ) ^ Fintype.card ι) * A.det⁻¹) *
              A.charpolyRev.coeff (Fintype.card ι - 1) := by
        calc
          (Polynomial.C ((-1 : ℂ) ^ Fintype.card ι) *
              (Polynomial.C (Ring.inverse A.det) * A.charpolyRev)).coeff
              (Fintype.card ι - 1) =
              (-1 : ℂ) ^ Fintype.card ι *
                (Polynomial.C (Ring.inverse A.det) * A.charpolyRev).coeff
                  (Fintype.card ι - 1) := by
                  simpa [mul_assoc] using hcoeff_outer
          _ = (((-1 : ℂ) ^ Fintype.card ι) * A.det⁻¹) *
                A.charpolyRev.coeff (Fintype.card ι - 1) := by
                rw [hcoeff_inner]
                ac_rfl
      calc
        A⁻¹.trace = - (A⁻¹).charpoly.coeff (Fintype.card ι - 1) := by
          simpa using Matrix.trace_eq_neg_charpoly_coeff (A⁻¹)
        _ = - ((((-1 : ℂ) ^ Fintype.card ι) * A.det⁻¹) *
            A.charpolyRev.coeff (Fintype.card ι - 1)) := by
              rw [Matrix.charpoly_inv A hA_unit]
              simpa [mul_assoc] using congrArg Neg.neg hcoeff_total
        _ = - ((A.charpoly.eval 0)⁻¹ * A.charpoly.coeff 1) := by
              rw [hscalar, hcoeff_rev]
        _ = - (A.charpoly.coeff 1 * (A.charpoly.eval 0)⁻¹) := by
              rw [mul_comm]
        _ = - (A.charpoly.derivative.eval 0 * (A.charpoly.eval 0)⁻¹) := by
              congr 2
              rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
              norm_num
        _ = - (A.charpoly.derivative.eval 0 / A.charpoly.eval 0) := by
              rw [div_eq_mul_inv]
    have hratio :
        A.charpoly.derivative.eval 0 / A.charpoly.eval 0 =
          - (A.charpoly.roots.map fun μ ↦ μ⁻¹).sum := by
      -- The logarithmic derivative of a split polynomial is the sum of reciprocal linear factors.
      simpa [div_eq_mul_inv] using
        (IsAlgClosed.splits A.charpoly).eval_derivative_div_eval_of_ne_zero (x := 0) hAeval0_ne
    calc
      LinearMap.trace ℂ V (ρ s⁻¹) = (LinearMap.toMatrix b b (ρ s⁻¹)).trace := by
        rw [LinearMap.trace_eq_matrix_trace ℂ b]
      _ = A⁻¹.trace := by rw [← hAinv]
      _ = - (A.charpoly.derivative.eval 0 / A.charpoly.eval 0) := htrace_inv
      _ = ((A.charpoly.roots.map fun μ ↦ μ⁻¹).sum) := by rw [hratio, neg_neg]
      _ = ((ρ s).charpoly.roots.map fun μ ↦ μ⁻¹).sum := by
        simp [A, LinearMap.charpoly_toMatrix]

/-- Proposition 2-2.1-1 (2): if `s` has finite order, then
`χ(s⁻¹) = star (χ s)` for the character `χ = ρ.character`. -/
theorem char_inv_eq_star_of_isOfFinOrder (s : G) (hs : IsOfFinOrder s) :
    ρ.character s⁻¹ = star (ρ.character s) := by
  -- Rewrite the left-hand side as the trace of the inverse and the right-hand side as the
  -- conjugate of the trace.
  change LinearMap.trace ℂ V (ρ s⁻¹) = star (ρ.character s)
  rw [ρ.trace_inv_eq_sum_inv_charpoly_roots s]
  change ((ρ s).charpoly.roots.map fun μ ↦ μ⁻¹).sum = star (LinearMap.trace ℂ V (ρ s))
  rw [trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  rw [show star (Multiset.sum (ρ s).charpoly.roots) =
      (Multiset.map star (ρ s).charpoly.roots).sum by
        simpa using map_multiset_sum (starRingEnd ℂ) ((ρ s).charpoly.roots)]
  -- Each root is inverted by complex conjugation because it is a root of unity.
  refine congrArg Multiset.sum ?_
  refine Multiset.map_congr rfl fun μ hμ ↦ ?_
  simpa using (ρ.star_eq_inv_of_charpoly_root s hs hμ).symm

/- Proposition 2-2.1-1 (2), canonical dual-character recall: the identity
`χ_{ρᵛ}(s) = χ_ρ(s⁻¹)` is the existing theorem
`Representation.char_dual`. -/
recall Representation.char_dual

/-- Proposition 2-2.1-1 (2), dual form: for a finite-dimensional complex representation of a
finite group, the character of the dual representation is the complex conjugate of the original
character. -/
theorem char_dual_eq_star [Finite G] (s : G) :
    ρ.dual.character s = star (ρ.character s) := by
  simpa using ρ.char_inv_eq_star_of_isOfFinOrder s (isOfFinOrder_of_finite s)

/- Proposition 2-2.1-1 (3): the character is constant on conjugacy classes. This is the existing
theorem `Representation.char_conj`. -/
recall Representation.char_conj

section ClassFunctionInfrastructure

variable {R : Type v}

/-- Helper for Proposition 2-2.1-1: a class function on a group factors through conjugacy classes.
-/
@[mk_iff]
class IsClassFunction (f : G → R) : Prop where
  factorsThrough : f.FactorsThrough ConjClasses.mk

/-- Helper for Proposition 2-2.1-1: the complex-valued class functions on `G` form a subspace. -/
abbrev classFunctionSubspace (G : Type u) [Group G] : Submodule ℂ (G → ℂ) where
  carrier := { f | IsClassFunction f }
  zero_mem' := by
    exact ⟨fun _ _ _ ↦ rfl⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨?_⟩
    intro x y hxy
    change f x + g x = f y + g y
    simpa using congrArg₂ (· + ·) (hf.factorsThrough hxy) (hg.factorsThrough hxy)
  smul_mem' := by
    intro c f hf
    refine ⟨?_⟩
    intro x y hxy
    change c • f x = c • f y
    simpa using congrArg (c • ·) (hf.factorsThrough hxy)

/-- Helper for Proposition 2-2.1-1: membership in `classFunctionSubspace G` is exactly the class
function property. -/
@[simp] theorem mem_classFunctionSubspace_iff (f : G → ℂ) :
    f ∈ classFunctionSubspace G ↔ IsClassFunction f := by
  rfl

end ClassFunctionInfrastructure

omit [FiniteDimensional ℂ V] in
/-- Bridge/view from the canonical conjugacy formula `Representation.char_conj` to the chapter-level
predicate `IsClassFunction`. -/
theorem char_eq_of_isConj {x y : G} (hxy : IsConj x y) :
    ρ.character x = ρ.character y := by
  rcases isConj_iff.1 hxy with ⟨a, rfl⟩
  exact (ρ.char_conj x a).symm

/-- The character of a finite-dimensional complex representation is a class function. -/
instance : IsClassFunction ρ.character :=
  ⟨fun _ _ h ↦ ρ.char_eq_of_isConj <| ConjClasses.mk_eq_mk_iff_isConj.mp h⟩

omit [FiniteDimensional ℂ V] in
/-- Helper for Proposition 2-2.1-1: the character of a representation lies in the
class-function subspace. -/
theorem character_mem_classFunctionSubspace :
    ρ.character ∈ classFunctionSubspace G := by
  -- Membership in the subspace is exactly the conjugacy-invariance property already proved above.
  exact (mem_classFunctionSubspace_iff _).2 inferInstance

/-- The character of a finite-dimensional complex representation, viewed as an element of the
class-function subspace. -/
abbrev classFunction : classFunctionSubspace G :=
  ⟨ρ.character, ρ.character_mem_classFunctionSubspace⟩

omit [FiniteDimensional ℂ V] in
@[simp] theorem classFunction_apply (g : G) :
    (ρ.classFunction : G → ℂ) g = ρ.character g :=
  rfl

end Representation

end
