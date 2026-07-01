import Serre.Chap02.Corollary_2_2_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra
noncomputable section
universe u v w

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable {ι : Type w} [Fintype ι]

local instance : Fintype G := Fintype.ofFinite G

/- Source-facing bridge: the core/canonical owner is the averaged intertwiner
`(linHom ρ ρ).averageMap`, and the relevant primitive data is the canonical matrix-unit basis
vector `b.end (j2, j1)` of `Module.End ℂ V`. This corollary extracts one matrix entry of that
canonical averaged endomorphism. -/
-- Proof sketch: apply `averageMap_linHom_self_eq_trace_smul_id` to the canonical basis vector
-- `b.end (j2, j1)` of `Module.End ℂ V`. Evaluating the resulting identity on the `(i2, j1)`
-- matrix entry gives the Kronecker-delta formula, with scalar `(Module.finrank ℂ V : ℂ)⁻¹`.
open scoped Classical in
/-- Corollary 2-2.2-4: for an irreducible complex representation with basis `b`, the averaged
product of the matrix coefficients `r i2 j2 (t⁻¹)` and `r j1 i1 (t)` is `(1 / dim V)` when
`i1 = i2` and `j1 = j2`, and `0` otherwise. -/
theorem matrix_coefficient_orthogonality_of_irreducible
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (b : Module.Basis ι ℂ V)
    (i1 j1 i2 j2 : ι) :
    (Nat.card G : ℂ)⁻¹ *
        ∑ t : G, (ρ t⁻¹).toMatrix b b i2 j2 * (ρ t).toMatrix b b j1 i1 =
      if i2 = i1 then
        if j2 = j1 then (Module.finrank ℂ V : ℂ)⁻¹ else 0
      else 0 := by
  letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  letI : NeZero (Module.finrank ℂ V) := NeZero.of_pos Module.finrank_pos
  let e : Module.End ℂ V := b.end (j2, j1)
  have htrace : LinearMap.trace ℂ V e = if j2 = j1 then 1 else 0 := by
    dsimp [e]
    rw [Module.Basis.end_apply, Matrix.trace_toLin_eq, Matrix.stdBasis_eq_single]
    by_cases h : j2 = j1
    · subst h
      simp [Matrix.trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne j2 j1 (1 : ℂ) h, h]
  calc
    (Nat.card G : ℂ)⁻¹ *
        ∑ t : G, (ρ t⁻¹).toMatrix b b i2 j2 * (ρ t).toMatrix b b j1 i1
      = (((ρ.linHom ρ).averageMap e).toMatrix b b i2 i1) := by
          simpa [e, Nat.card_eq_fintype_card] using
            (averageMap_linHom_basis_entry_eq ρ ρ b b i1 j1 i2 j2).symm
    _ = ((((Module.finrank ℂ V : ℂ)⁻¹ * LinearMap.trace ℂ V e) •
          (LinearMap.id : V →ₗ[ℂ] V)).toMatrix b b i2 i1) := by
          simpa [e] using congrArg (fun f ↦ f.toMatrix b b i2 i1)
            (averageMap_linHom_self_eq_trace_smul_id ρ e)
    _ = if i2 = i1 then
          if j2 = j1 then (Module.finrank ℂ V : ℂ)⁻¹ else 0
        else 0 := by
          rw [htrace]
          by_cases hj : j2 = j1 <;> simp [hj, Matrix.one_apply]

end

end Representation
