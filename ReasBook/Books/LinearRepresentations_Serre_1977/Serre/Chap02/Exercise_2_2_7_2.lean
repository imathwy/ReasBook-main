import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_7_1
import LinearRepresentations_Serre_1977.FiniteToFintype

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Representation.ExplicitDecomposition

noncomputable section

universe u w x y

namespace Representation

namespace ExplicitDecomposition

open IntertwiningMap

section

variable {G : Type u} [Group G]
variable [Finite G]
variable {V : Type w} [AddCommGroup V] [Module ℂ V]
variable {W : Type x} [AddCommGroup W] [Module ℂ W]
variable {ι : Type y} [Fintype ι]

open scoped Classical in
/-- Helper for Exercise 2-2.7-2: the source matrix units act on the chosen basis as the usual
standard matrix units. -/
private theorem self_matrixUnit_apply_basis
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α β : ι) :
    p⟮σ,σ,basis⟯ β α (basis α) = basis β := by
  letI : FiniteDimensional ℂ W := basis.finiteDimensional_of_finite
  letI : Module (MonoidAlgebra ℂ G) W := σ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule (MonoidAlgebra ℂ G) W :=
    (irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
  letI : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) W
  have hcard :
      (Fintype.card ι : ℂ) = (Module.finrank ℂ W : ℂ) := by
    exact_mod_cast (Module.finrank_eq_card_basis basis).symm
  have hfinrank_ne_zero : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  -- Compare basis coordinates and collapse the averaging sum with matrix-coefficient orthogonality.
  apply basis.repr.injective
  ext γ
  have horth0 :=
    Representation.matrixCoefficient_pairing_of_irreducible
      σ basis α γ α β
  have horth :
      (Nat.card G : ℂ)⁻¹ *
          ∑ s : G, (basis.repr (σ s⁻¹ (basis β))) α * (basis.repr (σ s (basis α))) γ =
        if β = γ then (Module.finrank ℂ W : ℂ)⁻¹ else 0 := by
    by_cases hβγ : β = γ
    · simpa [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card,
        LinearMap.toMatrix_apply, hβγ] using horth0
    · simpa [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card,
        LinearMap.toMatrix_apply, hβγ] using horth0
  calc
    basis.repr (p⟮σ,σ,basis⟯ β α (basis α)) γ
        = ((Fintype.card ι : ℂ) / Nat.card G) *
            ∑ s : G, (basis.repr (σ s⁻¹ (basis β))) α * (basis.repr (σ s (basis α))) γ := by
            simp [matrixUnit, Finsupp.smul_apply, smul_eq_mul]
    _ = (Module.finrank ℂ W : ℂ) *
          ((Nat.card G : ℂ)⁻¹ *
            ∑ s : G, (basis.repr (σ s⁻¹ (basis β))) α * (basis.repr (σ s (basis α))) γ) := by
          rw [div_eq_mul_inv, hcard]
          ring
    _ = (Module.finrank ℂ W : ℂ) * (if β = γ then (Module.finrank ℂ W : ℂ)⁻¹ else 0) := by
          rw [horth]
    _ = basis.repr (basis β) γ := by
          by_cases hβγ : β = γ
          · subst hβγ
            simp [hfinrank_ne_zero]
          · simp [hβγ]

open scoped Classical in
/-- Helper for Exercise 2-2.7-2: applying the matrix unit `p_{βα}` to the single vector
`h(e_α)` recovers the value `h(e_β)` of the intertwiner. -/
private theorem matrixUnit_apply_intertwining_basis
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α β : ι) (h : σ.IntertwiningMap ρ) :
    p⟮ρ,σ,basis⟯ β α (h (basis α)) = h (basis β) := by
  -- Push the intertwiner through the averaging operator and then use the source basis identity.
  calc
    p⟮ρ,σ,basis⟯ β α (h (basis α))
        = h (p⟮σ,σ,basis⟯ β α (basis α)) := by
            simp [matrixUnit, h.isIntertwining, map_sum, map_smul]
    _ = h (basis β) := by
          rw [self_matrixUnit_apply_basis σ basis α β]

open scoped Classical in
/-- Helper for Exercise 2-2.7-2: the canonical reconstruction map sends the basis vector `e_β`
to `p_{βα}(x)`. -/
private theorem coordinateFamilyHom_apply_basis
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α β : ι) (x : V⟮ρ,σ,basis⟯ α) :
    coordinateFamilyHom ρ σ basis α x (basis β) = p⟮ρ,σ,basis⟯ β α x := by
  -- Evaluate the reconstructed family on the chosen basis vector `e_β`.
  simp [coordinateFamilyHom, coordinateFamilyMap, coordinateVector]

-- Proof sketch: if `h : W_i → V` intertwines the actions, then the explicit formulas for the
-- matrix units `p_{αβ}` from Proposition 2-2.7-1 force the vector `h(e_α)` to lie in the image
-- of `p_{αα}`, namely in `V_{i,α}`.
/-- Every intertwining map sends the basis vector `e_α` of `W_i` into the coordinate subspace
`V_{i,α}`. -/
private theorem intertwiningMap_apply_basis_mem_coordinateSubspace
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α : ι) (h : σ.IntertwiningMap ρ) :
    h (basis α) ∈ V⟮ρ,σ,basis⟯ α := by
  -- The vector `h(e_α)` is fixed by `p_{αα}`, so it belongs to the image of that projector.
  refine LinearMap.mem_range.mpr ?_
  refine ⟨h (basis α), ?_⟩
  simpa using matrixUnit_apply_intertwining_basis ρ σ basis α α h

/-- The evaluation map `h ↦ h(e_α)` from `H_i = Hom_G(W_i, V)` to the coordinate subspace
`V_{i,α}`. -/
def intertwiningMapEvaluation
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α : ι) :
    σ.IntertwiningMap ρ →ₗ[ℂ] V⟮ρ,σ,basis⟯ α :=
  ((LinearMap.applyₗ (basis α)).comp (toLinearMapl σ ρ)).codRestrict _
    (intertwiningMap_apply_basis_mem_coordinateSubspace ρ σ basis α)

-- Proof sketch: the inverse is the canonical reconstruction map `coordinateFamilyHom` from
-- Proposition `2-2.7-1`, which sends a vector of `V_{i,α}` to the unique intertwiner obtained by
-- transporting it through the matrix units `p_{βα}`.
/-- Exercise 2-2.7-2: evaluating an intertwining map `h : W_i → V` at the basis vector `e_α`
identifies the intertwining space `H_i = Hom_G(W_i, V)` with the coordinate subspace
`V_{i,α}`. -/
def intertwiningMapEvaluationEquiv
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α : ι) :
    σ.IntertwiningMap ρ ≃ₗ[ℂ] V⟮ρ,σ,basis⟯ α :=
  LinearEquiv.mk
    (intertwiningMapEvaluation ρ σ basis α)
    (coordinateFamilyHom ρ σ basis α)
    (by
      intro h
      -- Compare the reconstructed intertwiner with `h` on the chosen basis of `W_i`.
      apply IntertwiningMap.ext
      exact basis.ext fun β ↦ by
        -- On `e_β`, the inverse candidate evaluates to `p_{βα}(h(e_α))`, hence to `h(e_β)`.
        have hβ :
            coordinateFamilyHom ρ σ basis α (intertwiningMapEvaluation ρ σ basis α h) (basis β) =
              h (basis β) := by
          rw [coordinateFamilyHom_apply_basis]
          simpa [intertwiningMapEvaluation] using
            matrixUnit_apply_intertwining_basis ρ σ basis α β h
        simpa using hβ)
    (by
      intro x
      -- Evaluate the reconstructed intertwiner at `e_α` and use idempotence on the image of
      -- `p_{αα}`.
      apply Subtype.ext
      have hx :
          coordinateFamilyHom ρ σ basis α x (basis α) = x := by
        rw [coordinateFamilyHom_apply_basis]
        rcases LinearMap.mem_range.mp x.property with ⟨u, hu⟩
        rw [← hu]
        simpa [LinearMap.comp_apply] using
          congrArg (fun f : Module.End ℂ V ↦ f u) (matrixUnit_comp ρ σ basis α α α α rfl)
      simpa [intertwiningMapEvaluation] using hx)

/-- The evaluation map `h ↦ h(e_α)` is bijective from `H_i` onto `V_{i,α}`. -/
theorem intertwiningMapEvaluation_bijective
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α : ι) :
    Function.Bijective (intertwiningMapEvaluation ρ σ basis α) := by
  simpa [intertwiningMapEvaluationEquiv] using
    (intertwiningMapEvaluationEquiv ρ σ basis α).bijective

end

end ExplicitDecomposition

end Representation
