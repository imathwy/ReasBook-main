import Mathlib
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_2_2_7_1 (from Chap02) -/
open scoped BigOperators

noncomputable section

universe u v w x y z

namespace Representation

namespace ExplicitDecomposition

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W]
variable {ι : Type x} [Fintype ι]

local instance : Fintype G := Fintype.ofFinite G

/-- The source-facing matrix unit `p_{αβ}` attached to the irreducible model `σ`, the ambient
representation `ρ`, and the chosen basis of `W_i`. -/
def matrixUnit
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (α β : ι) : Module.End ℂ V :=
  ((Fintype.card ι : ℂ) / Nat.card G) •
    ∑ s : G, (basis.repr (σ s⁻¹ (basis α))) β • ρ s

scoped[Representation.ExplicitDecomposition] notation3 "p⟮" ρ "," σ "," basis "⟯" =>
  Representation.ExplicitDecomposition.matrixUnit ρ σ basis

open scoped Representation.ExplicitDecomposition

open scoped Classical in
/-- Helper for Proposition 2-2.7-1: left composition by `ρ s` expands the source matrix unit
along the first index using the matrix of `σ s` in the chosen basis. -/
private theorem matrixUnit_left_action_expansion
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (s : G) (α γ : ι) :
    (ρ s).comp (p⟮ρ,σ,basis⟯ α γ) =
      ∑ β : ι,
        (basis.repr (σ s (basis α))) β • p⟮ρ,σ,basis⟯ β γ := by
  ext v
  let c : ℂ := (Fintype.card ι : ℂ) / Nat.card G
  calc
    ((ρ s).comp (p⟮ρ,σ,basis⟯ α γ)) v
        = ∑ t : G, c • (basis.repr (σ t⁻¹ (basis α))) γ • ρ (s * t) v := by
            -- Expand the definition of the matrix unit and compose termwise with `ρ s`.
            simp [Representation.ExplicitDecomposition.matrixUnit, c, LinearMap.comp_apply,
              Finset.smul_sum, Module.End.mul_apply, smul_smul]
    _ = ∑ u : G, c • (basis.repr (σ (u⁻¹ * s) (basis α))) γ • ρ u v := by
          -- Reindex the averaging sum by left multiplication with `s`.
          refine Fintype.sum_bijective (s * ·) (Group.mulLeft_bijective s) _ _ ?_
          intro t
          simp [c, mul_assoc]
    _ = ∑ u : G, c • (basis.repr ((σ u⁻¹) ((σ s) (basis α)))) γ • ρ u v := by
          -- Rewrite the coefficient using the representation law for `σ`.
          apply Finset.sum_congr rfl
          intro u hu
          simp [map_mul, Module.End.mul_apply]
    _ = ∑ u : G, c • (basis.repr ((σ u⁻¹) (∑ β : ι, (basis.repr (σ s (basis α))) β • basis β))) γ •
          ρ u v := by
          -- Expand `σ s (basis α)` in the chosen basis.
          simp_rw [basis.sum_repr]
    _ = ∑ u : G, c • (basis.repr
          (∑ β : ι, (basis.repr (σ s (basis α))) β • (σ u⁻¹) (basis β))) γ • ρ u v := by
          -- Push `σ u⁻¹` through the basis expansion.
          apply Finset.sum_congr rfl
          intro u hu
          congr 1
          congr 1
          rw [map_sum]
          simp_rw [map_smul]
    _ = ∑ u : G, c •
          (∑ β : ι, (basis.repr (σ s (basis α))) β * (basis.repr ((σ u⁻¹) (basis β))) γ) • ρ u v := by
          -- Read off the `γ`-coordinate after applying `basis.repr`.
          apply Finset.sum_congr rfl
          intro u hu
          congr 1
          have hreplin :
              basis.repr (∑ β : ι, (basis.repr (σ s (basis α))) β • (σ u⁻¹) (basis β)) =
                ∑ β : ι, (basis.repr (σ s (basis α))) β • basis.repr ((σ u⁻¹) (basis β)) := by
            rw [map_sum]
            simp_rw [map_smul]
          simpa [Finsupp.smul_apply, smul_eq_mul] using
            congrArg (fun f : ι →₀ ℂ ↦ f γ) hreplin
    _ = ∑ u : G, ∑ β : ι,
          (basis.repr (σ s (basis α))) β • (c • (basis.repr ((σ u⁻¹) (basis β))) γ • ρ u v) := by
          -- Distribute the scalar coefficient and rearrange the finite sum.
          apply Finset.sum_congr rfl
          intro u hu
          calc
            c • (∑ β : ι,
                (basis.repr (σ s (basis α))) β * (basis.repr ((σ u⁻¹) (basis β))) γ) • ρ u v
              = c • ∑ β : ι,
                  ((basis.repr (σ s (basis α))) β * (basis.repr ((σ u⁻¹) (basis β))) γ) • ρ u v := by
                    rw [Finset.sum_smul]
            _ = ∑ β : ι,
                  c • (((basis.repr (σ s (basis α))) β * (basis.repr ((σ u⁻¹) (basis β))) γ) • ρ u v) := by
                    exact Finset.smul_sum
            _ = ∑ β : ι,
                  (basis.repr (σ s (basis α))) β •
                    (c • (basis.repr ((σ u⁻¹) (basis β))) γ • ρ u v) := by
                    apply Finset.sum_congr rfl
                    intro β hβ
                    simp [smul_smul, mul_left_comm]
    _ = ∑ β : ι, (basis.repr (σ s (basis α))) β • ∑ u : G,
          c • (basis.repr ((σ u⁻¹) (basis β))) γ • ρ u v := by
          -- Commute the two finite sums.
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro β hβ
          exact Finset.smul_sum.symm
    _ = ∑ β : ι, (basis.repr (σ s (basis α))) β • p⟮ρ,σ,basis⟯ β γ v := by
          -- Recognize the remaining sum as the matrix unit `p_{βγ}`.
          apply Finset.sum_congr rfl
          intro β hβ
          congr 1
          simpa [Representation.ExplicitDecomposition.matrixUnit, c, smul_smul] using
            (Finset.smul_sum :
              c •
                  ∑ x : G,
                    (basis.repr ((σ x⁻¹) (basis β))) γ • ρ x v
                =
                  ∑ x : G,
                    c • ((basis.repr ((σ x⁻¹) (basis β))) γ • ρ x v)).symm
    _ = (∑ β : ι, (basis.repr (σ s (basis α))) β • p⟮ρ,σ,basis⟯ β γ) v := by
          -- Repackage the pointwise equality as an equality of linear maps.
          simp [Finset.sum_apply]

open scoped Classical in
omit [Finite G] in
/-- Helper for Proposition 2-2.7-1: the basis coefficients appearing in the source formula are
the matrix entries of the representing matrix of `σ s` in the chosen basis. -/
private theorem matrixUnit_coefficient_eq_toMatrix_entry
    (σ : Representation ℂ G W) (basis : Module.Basis ι ℂ W) (s : G) (α β : ι) :
    (basis.repr (σ s (basis α))) β = (σ s).toMatrix basis basis β α := by
  -- This is the interface bridge from basis coordinates to the orthogonality theorem's matrix API.
  simpa using (LinearMap.toMatrix_apply basis basis (σ s) β α).symm

omit [Finite G] in
/-- Helper for Proposition 2-2.7-1: in the chosen basis, the character is the sum of the diagonal
matrix coefficients. -/
private theorem character_eq_sum_diagonal_matrix_coefficients_local
    (σ : Representation ℂ G W) (basis : Module.Basis ι ℂ W) [DecidableEq ι] :
    σ.character = fun g ↦ ∑ α, (σ g).toMatrix basis basis α α := by
  letI : FiniteDimensional ℂ W := basis.finiteDimensional_of_finite
  -- Rewrite the trace defining the character as the trace of the representing matrix.
  ext g
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ basis, Matrix.trace]
  simp [Matrix.diag]

/-- Helper for Proposition 2-2.7-1: the orthogonality theorem collapses the coefficient
convolution in the source matrix-unit product to the Kronecker delta. -/
private theorem matrixUnit_coefficient_convolution_of_irreducible
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) [DecidableEq ι] (α β γ η : ι) :
    ((Fintype.card ι : ℂ) / Nat.card G) *
        ∑ s : G,
          (basis.repr (σ s⁻¹ (basis α))) β * (basis.repr (σ s (basis γ))) η =
      if β = γ then
        if α = η then 1 else 0
      else 0 := by
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
  have horth0 :=
    Representation.matrixCoefficient_pairing_of_irreducible σ basis γ η β α
  have horth :
      (Nat.card G : ℂ)⁻¹ *
          ∑ s : G,
            (basis.repr (σ s⁻¹ (basis α))) β * (basis.repr (σ s (basis γ))) η =
        if β = γ then
          if α = η then (Module.finrank ℂ W : ℂ)⁻¹ else 0
        else 0 := by
    classical
    -- Rewrite the source coefficients as matrix entries and unfold the normalized pairing.
    by_cases hβγ : β = γ <;> by_cases hαη : α = η <;>
      simpa [Representation.groupFunctionPairingOverField, matrixUnit_coefficient_eq_toMatrix_entry,
        Nat.card_eq_fintype_card, hβγ, hαη] using horth0
  calc
    ((Fintype.card ι : ℂ) / Nat.card G) *
        ∑ s : G,
          (basis.repr (σ s⁻¹ (basis α))) β * (basis.repr (σ s (basis γ))) η
      = (Module.finrank ℂ W : ℂ) *
          ((Nat.card G : ℂ)⁻¹ *
            ∑ s : G,
              (basis.repr (σ s⁻¹ (basis α))) β * (basis.repr (σ s (basis γ))) η) := by
          -- Isolate the normalized averaging scalar so the orthogonality theorem applies verbatim.
          simp [div_eq_mul_inv, hcard, mul_assoc, mul_left_comm, mul_comm]
    _ = (Module.finrank ℂ W : ℂ) *
          (if β = γ then
            if α = η then (Module.finrank ℂ W : ℂ)⁻¹ else 0
          else 0) := by
          rw [horth]
    _ = if β = γ then
          if α = η then 1 else 0
        else 0 := by
          by_cases hβγ : β = γ <;> by_cases hαη : α = η <;>
            simp [hβγ, hαη, hfinrank_ne_zero]

open scoped Classical in
/-- Helper for Proposition 2-2.7-1: composing two source matrix units first expands to a single
`η`-indexed sum whose coefficients are the convolution kernel appearing in the orthogonality
relation. -/
private theorem matrixUnit_comp_expansion
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (α β γ δ : ι) :
    (p⟮ρ,σ,basis⟯ α β).comp (p⟮ρ,σ,basis⟯ γ δ) =
      ∑ η : ι,
        ((((Fintype.card ι : ℂ) / Nat.card G) *
            ∑ s : G,
              (basis.repr (σ s⁻¹ (basis α))) β *
                (basis.repr (σ s (basis γ))) η)) •
          p⟮ρ,σ,basis⟯ η δ := by
  ext v
  let c : ℂ := (Fintype.card ι : ℂ) / Nat.card G
  calc
    ((p⟮ρ,σ,basis⟯ α β).comp (p⟮ρ,σ,basis⟯ γ δ)) v
        = ((((Fintype.card ι : ℂ) / Nat.card G) •
              ∑ s : G, (basis.repr (σ s⁻¹ (basis α))) β • ρ s).comp
            (p⟮ρ,σ,basis⟯ γ δ)) v := by
            rfl
    _ = c •
          ∑ s : G, (basis.repr (σ s⁻¹ (basis α))) β •
            ((ρ s).comp (p⟮ρ,σ,basis⟯ γ δ)) v := by
            -- Expand the outer matrix unit and compose termwise with the inner map.
            simp [c, LinearMap.comp_apply, Finset.sum_apply, Finset.smul_sum, smul_smul]
    _ = ∑ s : G, c • (basis.repr (σ s⁻¹ (basis α))) β •
          ((ρ s).comp (p⟮ρ,σ,basis⟯ γ δ)) v := by
          -- Move the outer scalar inside the finite sum so each summand has the convolution form.
          simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using
            (Finset.smul_sum :
              c •
                  ∑ s : G,
                    (basis.repr (σ s⁻¹ (basis α))) β •
                      ((ρ s).comp (p⟮ρ,σ,basis⟯ γ δ)) v
                =
                  ∑ s : G,
                    c •
                      ((basis.repr (σ s⁻¹ (basis α))) β •
                        ((ρ s).comp (p⟮ρ,σ,basis⟯ γ δ)) v))
    _ = ∑ s : G, c • (basis.repr (σ s⁻¹ (basis α))) β •
          (∑ η : ι, (basis.repr (σ s (basis γ))) η • p⟮ρ,σ,basis⟯ η δ) v := by
          -- Route correction: the missing step is the linear-map normalization, so rewrite the
          -- inner composition by the already-proved left-action expansion before simplifying.
          apply Finset.sum_congr rfl
          intro s hs
          rw [matrixUnit_left_action_expansion ρ σ basis s γ δ]
    _ = ∑ s : G, ∑ η : ι,
          (c * ((basis.repr (σ s⁻¹ (basis α))) β * (basis.repr (σ s (basis γ))) η)) •
            p⟮ρ,σ,basis⟯ η δ v := by
          -- Reassociate the scalar factors so each `η`-term carries one coefficient.
          apply Finset.sum_congr rfl
          intro s hs
          calc
            c • (basis.repr (σ s⁻¹ (basis α))) β •
                (∑ η : ι, (basis.repr (σ s (basis γ))) η • p⟮ρ,σ,basis⟯ η δ) v
                = c • (basis.repr (σ s⁻¹ (basis α))) β •
                    ∑ η : ι, (basis.repr (σ s (basis γ))) η • p⟮ρ,σ,basis⟯ η δ v := by
                      simp [Finset.sum_apply]
            _ =
                (c * (basis.repr (σ s⁻¹ (basis α))) β) •
                  ∑ η : ι, (basis.repr (σ s (basis γ))) η • p⟮ρ,σ,basis⟯ η δ v := by
                      simp [smul_smul, mul_assoc]
            _ = ∑ η : ι,
                  (c * (basis.repr (σ s⁻¹ (basis α))) β) •
                    ((basis.repr (σ s (basis γ))) η • p⟮ρ,σ,basis⟯ η δ v) := by
                      exact Finset.smul_sum
            _ = ∑ η : ι,
                  (c * ((basis.repr (σ s⁻¹ (basis α))) β *
                      (basis.repr (σ s (basis γ))) η)) •
                    p⟮ρ,σ,basis⟯ η δ v := by
                      apply Finset.sum_congr rfl
                      intro η hη
                      simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ η : ι, ∑ s : G,
          (c * ((basis.repr (σ s⁻¹ (basis α))) β * (basis.repr (σ s (basis γ))) η)) •
            p⟮ρ,σ,basis⟯ η δ v := by
          -- Commute the finite `s`- and `η`-sums once and for all.
          rw [Finset.sum_comm]
    _ = ∑ η : ι,
          (c *
              ∑ s : G,
                (basis.repr (σ s⁻¹ (basis α))) β *
                  (basis.repr (σ s (basis γ))) η) •
            p⟮ρ,σ,basis⟯ η δ v := by
          -- Collect the scalar kernel multiplying the fixed vector `p_{ηδ}(v)`.
          apply Finset.sum_congr rfl
          intro η hη
          rw [← Finset.sum_smul]
          congr 1
          rw [Finset.mul_sum]
    _ = (∑ η : ι,
          ((((Fintype.card ι : ℂ) / Nat.card G) *
              ∑ s : G,
                (basis.repr (σ s⁻¹ (basis α))) β *
                  (basis.repr (σ s (basis γ))) η)) •
            p⟮ρ,σ,basis⟯ η δ) v := by
          -- Repackage the pointwise identity back into an equality of linear maps.
          simp [c, Finset.sum_apply]

-- Proof sketch: expand both matrix units as finite sums, compose termwise, and apply the
-- irreducible matrix-coefficient orthogonality relations to the convolution kernel.
/-- The source matrix units satisfy the usual matrix-unit composition law
`p_{αβ} ∘ p_{γδ} = p_{αδ}` when the middle indices agree; the complementary vanishing case is
`matrixUnit_comp_eq_zero_of_ne`. -/
theorem matrixUnit_comp
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α β γ δ : ι) (hβγ : β = γ) :
    (p⟮ρ,σ,basis⟯ α β).comp (p⟮ρ,σ,basis⟯ γ δ) = p⟮ρ,σ,basis⟯ α δ := by
  classical
  -- Route correction: package the double-sum rearrangement once, then the orthogonality
  -- coefficient collapse is a single `simp` step.
  rw [matrixUnit_comp_expansion ρ σ basis α β γ δ]
  have hcoeff :
      ∀ η : ι,
        ((Fintype.card ι : ℂ) / Nat.card G) *
            ∑ s : G,
              (basis.repr (σ s⁻¹ (basis α))) β * (basis.repr (σ s (basis γ))) η =
          if α = η then 1 else 0 := by
    intro η
    simpa [hβγ] using
      (matrixUnit_coefficient_convolution_of_irreducible σ basis α β γ η)
  simp_rw [hcoeff]
  simp

/-- The source matrix units satisfy the vanishing branch of the usual matrix-unit composition law:
`p_{αβ} ∘ p_{γδ} = 0` when the middle indices are distinct. -/
theorem matrixUnit_comp_eq_zero_of_ne
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α β γ δ : ι) (hβγ : β ≠ γ) :
    (p⟮ρ,σ,basis⟯ α β).comp (p⟮ρ,σ,basis⟯ γ δ) = 0 := by
  classical
  -- After the composition expansion, the `β ≠ γ` branch of orthogonality kills every term.
  rw [matrixUnit_comp_expansion ρ σ basis α β γ δ]
  have hcoeff :
      ∀ η : ι,
        ((Fintype.card ι : ℂ) / Nat.card G) *
            ∑ s : G,
              (basis.repr (σ s⁻¹ (basis α))) β * (basis.repr (σ s (basis γ))) η = 0 := by
    intro η
    simpa [hβγ] using
      (matrixUnit_coefficient_convolution_of_irreducible σ basis α β γ η)
  simp_rw [hcoeff]
  simp

-- Proof sketch: reindex the defining sum of `p_{αγ}` after composing on the left with `ρ_s`,
-- then use the matrix identity expressing the action of `σ_s` on the chosen basis.
/-- Left composition by `ρ_s` transforms the first index of the matrix units according to the
matrix of `σ_s` in the chosen basis. -/
theorem action_matrixUnit
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (s : G) (α γ : ι) :
    (ρ s).comp (p⟮ρ,σ,basis⟯ α γ) =
      ∑ β : ι,
        (basis.repr (σ s (basis α))) β • p⟮ρ,σ,basis⟯ β γ := by
  -- This is exactly the source-faithful left-action expansion proved above.
  simpa using matrixUnit_left_action_expansion ρ σ basis s α γ

/-- The coordinate subspace `V_{i,α}`, defined as the image of the diagonal matrix unit
`p_{αα}`. -/
def coordinateSubspace
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (α : ι) : Submodule ℂ V :=
  LinearMap.range (p⟮ρ,σ,basis⟯ α α)

scoped[Representation.ExplicitDecomposition] notation3 "V⟮" ρ "," σ "," basis "⟯" =>
  Representation.ExplicitDecomposition.coordinateSubspace ρ σ basis

/-- The vector `x_α = p_{α,oneIndex}(x₁)` associated with a vector
`x₁ ∈ V_{i,oneIndex}`. -/
def coordinateVector
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) (α : ι) : V :=
  p⟮ρ,σ,basis⟯ α oneIndex x₁

/-- The canonical linear map from the model representation `W_i` to the vectors
`x_α = p_{α,oneIndex}(x₁)`. -/
def coordinateFamilyMap
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) : W →ₗ[ℂ] V :=
  basis.constr ℂ (coordinateVector ρ σ basis oneIndex x₁)

-- Proof sketch: evaluate `action_matrixUnit` at `x₁`.
/-- Proposition 2-2.7-1 (7): source part (c). The vectors `x_α = p_{α,oneIndex}(x₁)` transform
under `ρ_s` with the same matrix coefficients as the chosen model basis of `W_i`. -/
theorem coordinateVector_action
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) (s : G) (α : ι) :
    ρ s (coordinateVector ρ σ basis oneIndex x₁ α) =
      ∑ β : ι,
        (basis.repr (σ s (basis α))) β • coordinateVector ρ σ basis oneIndex x₁ β := by
  -- Evaluate the left-action formula for `p_{α,oneIndex}` at the chosen vector `x₁`.
  simpa [coordinateVector] using
    congrArg (fun f : Module.End ℂ V ↦ f x₁)
      (matrixUnit_left_action_expansion ρ σ basis s α oneIndex)

/-- The canonical map sending `e_α` to `x_α` intertwines `σ` with the ambient action `ρ`. -/
private theorem coordinateFamilyMap_isIntertwining
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) (s : G) (w : W) :
    coordinateFamilyMap ρ σ basis oneIndex x₁ (σ s w) =
      ρ s (coordinateFamilyMap ρ σ basis oneIndex x₁ w) := by
  -- Expand `w` in the chosen basis and compare the images of each basis vector `e_α`.
  rw [← basis.sum_repr w]
  simp_rw [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro α hα
  rw [coordinateFamilyMap, Module.Basis.constr_basis]
  simpa using (congrArg (fun z : V ↦ (basis.repr w) α • z)
    (coordinateVector_action ρ σ basis oneIndex x₁ s α)).symm

/-- The canonical intertwining map from the model representation `W_i` to the ambient
representation `ρ`, sending the chosen basis vector `e_α` to `x_α = p_{α,oneIndex}(x₁)`. -/
def coordinateFamilyHom
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) :
    IntertwiningMap σ ρ :=
  (coordinateFamilyMap ρ σ basis oneIndex x₁).intertwiningMap_of_isIntertwiningMap σ ρ
    (coordinateFamilyMap_isIntertwining ρ σ basis oneIndex x₁)

/-- The source-facing stable subrepresentation `W(x₁)`, defined as the canonical range
subrepresentation of `coordinateFamilyHom`. -/
abbrev generatedSubrepresentation
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) : Subrepresentation ρ :=
  (coordinateFamilyHom ρ σ basis oneIndex x₁).range

scoped[Representation.ExplicitDecomposition] notation3
    "W⟮" ρ "," σ "," basis "," oneIndex "⟯" =>
  Representation.ExplicitDecomposition.generatedSubrepresentation ρ σ basis oneIndex

-- Proof sketch: write a vector of `V_{i,β}` as `p_{ββ}(u)` and use the matrix-unit relation
-- `p_{αβ} ∘ p_{ββ} = p_{αβ}` together with `p_{αα} ∘ p_{αβ} = p_{αβ}`.
/-- Each matrix unit `p_{αβ}` maps the coordinate subspace `V_{i,β}` into `V_{i,α}`. -/
private theorem matrixUnit_maps_to_coordinateSubspace
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α β : ι) :
    ∀ v : V, v ∈ V⟮ρ,σ,basis⟯ β → p⟮ρ,σ,basis⟯ α β v ∈ V⟮ρ,σ,basis⟯ α := by
  intro v hv
  rcases LinearMap.mem_range.mp hv with ⟨u, rfl⟩
  -- Write `v` as `p_{ββ}(u)` and use the matrix-unit relation to land in `V_{i,α}`.
  refine LinearMap.mem_range.mpr ?_
  refine ⟨p⟮ρ,σ,basis⟯ α β u, ?_⟩
  calc
    p⟮ρ,σ,basis⟯ α α (p⟮ρ,σ,basis⟯ α β u)
        = p⟮ρ,σ,basis⟯ α β u := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun f : Module.End ℂ V ↦ f u) (matrixUnit_comp ρ σ basis α α α β rfl)
    _ = p⟮ρ,σ,basis⟯ α β (p⟮ρ,σ,basis⟯ β β u) := by
          symm
          simpa [LinearMap.comp_apply] using
            congrArg (fun f : Module.End ℂ V ↦ f u) (matrixUnit_comp ρ σ basis α β β β rfl)

/-- The coordinate map `p_{αβ}` viewed as a map from `V_{i,β}` to `V_{i,α}`. -/
def coordinateChange
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α β : ι) :
    V⟮ρ,σ,basis⟯ β →ₗ[ℂ] V⟮ρ,σ,basis⟯ α :=
  (p⟮ρ,σ,basis⟯ α β).restrict
    (matrixUnit_maps_to_coordinateSubspace ρ σ basis α β)

/-- Proposition 2-2.7-1 (6): source part (c). The canonical intertwining map from `W_i` into the
stable subrepresentation `W(x₁)`, viewed through the owner `IntertwiningMap.range`. -/
def generatedSubrepresentationHom
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) :
    IntertwiningMap σ (W⟮ρ,σ,basis,oneIndex⟯ x₁).toRepresentation :=
  let f := coordinateFamilyHom ρ σ basis oneIndex x₁
  let fRange := f.toLinearMap.rangeRestrict
  fRange.intertwiningMap_of_isIntertwiningMap σ f.range.toRepresentation
    (fun s w ↦ by
      ext
      exact coordinateFamilyMap_isIntertwining ρ σ basis oneIndex x₁ s w)

/-- Helper for Proposition 2-2.7-1: applying the reverse matrix unit `p_{oneIndex,η}` to
`x_α = p_{α,oneIndex}(x₁)` isolates the `η = α` coordinate and returns `x₁`. -/
private theorem reverse_matrixUnit_apply_coordinateVector
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) [DecidableEq ι] (oneIndex η α : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) :
    p⟮ρ,σ,basis⟯ oneIndex η (coordinateVector ρ σ basis oneIndex x₁ α) =
      if η = α then x₁ else 0 := by
  -- Apply the matrix-unit composition law to `p_{oneIndex,η} ∘ p_{α,oneIndex}` and then use
  -- that `x₁` already lies in the image of `p_{oneIndex,oneIndex}`.
  by_cases hηα : η = α
  · subst η
    have hx₁_fix : p⟮ρ,σ,basis⟯ oneIndex oneIndex (x₁ : V) = x₁ := by
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp x₁.2
      calc
        p⟮ρ,σ,basis⟯ oneIndex oneIndex (x₁ : V)
            = p⟮ρ,σ,basis⟯ oneIndex oneIndex (p⟮ρ,σ,basis⟯ oneIndex oneIndex u) := by
                rw [hu]
        _ = p⟮ρ,σ,basis⟯ oneIndex oneIndex u := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ V ↦ f u)
                  (matrixUnit_comp ρ σ basis oneIndex oneIndex oneIndex oneIndex rfl)
        _ = x₁ := hu
    -- The equal-middle-index branch reduces the composition to `p_{oneIndex,oneIndex}`.
    calc
      p⟮ρ,σ,basis⟯ oneIndex α (coordinateVector ρ σ basis oneIndex x₁ α)
          = p⟮ρ,σ,basis⟯ oneIndex oneIndex (x₁ : V) := by
              simpa [coordinateVector, LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ V ↦ f x₁)
                  (matrixUnit_comp ρ σ basis oneIndex α α oneIndex rfl)
      _ = x₁ := hx₁_fix
      _ = if α = α then x₁ else 0 := by simp
  · -- The unequal-middle-index branch annihilates the coordinate vector.
    simpa [coordinateVector, hηα, LinearMap.comp_apply] using
      congrArg (fun f : Module.End ℂ V ↦ f x₁)
        (matrixUnit_comp_eq_zero_of_ne ρ σ basis oneIndex η α oneIndex hηα)

-- Proof sketch: apply the reverse matrix units `p_{oneIndex,α}` to isolate each coefficient.
/-- Proposition 2-2.7-1 (8): source part (c). If `x₁ ≠ 0`, then the vectors
`x_α = p_{α,oneIndex}(x₁)` are linearly independent. -/
theorem coordinateVector_linearIndependent
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) (hx₁ : (x₁ : V) ≠ 0) :
    LinearIndependent ℂ (coordinateVector ρ σ basis oneIndex x₁) := by
  classical
  refine linearIndependent_iff'.mpr ?_
  intro s a hsum α hα
  have happly0 := congrArg (p⟮ρ,σ,basis⟯ oneIndex α) hsum
  have happly1 :
      p⟮ρ,σ,basis⟯ oneIndex α
          (∑ i ∈ s, a i • coordinateVector ρ σ basis oneIndex x₁ i) = 0 := by
    simpa using happly0
  have happly := happly1
  simp [map_sum, map_smul, reverse_matrixUnit_apply_coordinateVector] at happly
  -- Applying `p_{oneIndex,α}` isolates the `α`-th coefficient of the relation.
  have hsingle_term :
      a α • (if α = α then (x₁ : V) else 0) =
        ∑ i ∈ s, a i • (if α = i then (x₁ : V) else 0) := by
    rw [Finset.sum_eq_single_of_mem α hα]
    intro i hi hia
    simp [hia.symm]
  have hsingle :
      ∑ i ∈ s, a i • (if α = i then (x₁ : V) else 0) = a α • (x₁ : V) := by
    calc
      ∑ i ∈ s, a i • (if α = i then (x₁ : V) else 0)
          = a α • (if α = α then (x₁ : V) else 0) := by
              simpa using hsingle_term.symm
      _ = a α • (x₁ : V) := by simp
  have happly' :
      ∑ i ∈ s, a i • (if α = i then (x₁ : V) else 0) = 0 := by
    calc
      ∑ i ∈ s, a i • (if α = i then (x₁ : V) else 0)
          = ∑ i ∈ s, a i • ((if α = i then x₁ else 0 : V⟮ρ,σ,basis⟯ oneIndex) : V) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases h : α = i <;> simp [h]
      _ = 0 := happly
  have hscalar : a α • (x₁ : V) = 0 := by
    calc
      a α • (x₁ : V) = ∑ i ∈ s, a i • (if α = i then (x₁ : V) else 0) := by
        exact hsingle.symm
      _ = 0 := happly'
  exact (smul_eq_zero.mp hscalar).resolve_right hx₁

-- Proof sketch: use the matrix-unit identities to show that `p_{βα}` is the inverse of `p_{αβ}`
-- on the corresponding coordinate subspaces.
/-- The restricted map `p_{αβ} : V_{i,β} → V_{i,α}` is bijective. -/
private theorem coordinateChange_bijective
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α β : ι) :
    Function.Bijective (coordinateChange ρ σ basis α β) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    -- Compose with the inverse matrix unit `p_{βα}` to isolate the original coordinate.
    rcases hx with ⟨u, rfl⟩
    rcases hy with ⟨v, rfl⟩
    have hxyv :
        p⟮ρ,σ,basis⟯ α β (p⟮ρ,σ,basis⟯ β β u) =
          p⟮ρ,σ,basis⟯ α β (p⟮ρ,σ,basis⟯ β β v) := by
      change
        (((coordinateChange ρ σ basis α β)
            ⟨p⟮ρ,σ,basis⟯ β β u, LinearMap.mem_range_self _ u⟩ : V)) =
          (((coordinateChange ρ σ basis α β)
            ⟨p⟮ρ,σ,basis⟯ β β v, LinearMap.mem_range_self _ v⟩ : V))
      exact congrArg Subtype.val hxy
    have hxy' := congrArg (p⟮ρ,σ,basis⟯ β α) hxyv
    exact Subtype.ext <| by
      calc
        p⟮ρ,σ,basis⟯ β β u = p⟮ρ,σ,basis⟯ β β (p⟮ρ,σ,basis⟯ β β u) := by
          symm
          simpa [LinearMap.comp_apply] using
            congrArg (fun f : Module.End ℂ V ↦ f u) (matrixUnit_comp ρ σ basis β β β β rfl)
        _ = p⟮ρ,σ,basis⟯ β α (p⟮ρ,σ,basis⟯ α β (p⟮ρ,σ,basis⟯ β β u)) := by
              symm
              simpa [LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ V ↦ f (p⟮ρ,σ,basis⟯ β β u))
                  (matrixUnit_comp ρ σ basis β α α β rfl)
        _ = p⟮ρ,σ,basis⟯ β α (p⟮ρ,σ,basis⟯ α β (p⟮ρ,σ,basis⟯ β β v)) := hxy'
        _ = p⟮ρ,σ,basis⟯ β β (p⟮ρ,σ,basis⟯ β β v) := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ V ↦ f (p⟮ρ,σ,basis⟯ β β v))
                  (matrixUnit_comp ρ σ basis β α α β rfl)
        _ = p⟮ρ,σ,basis⟯ β β v := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ V ↦ f v) (matrixUnit_comp ρ σ basis β β β β rfl)
  · rintro ⟨y, hy⟩
    -- The reverse matrix unit `p_{βα}` gives an explicit preimage.
    rcases hy with ⟨u, rfl⟩
    refine ⟨coordinateChange ρ σ basis β α ⟨p⟮ρ,σ,basis⟯ α α u, LinearMap.mem_range_self _ u⟩, ?_⟩
    exact Subtype.ext <| by
      calc
        ((coordinateChange ρ σ basis α β)
            (coordinateChange ρ σ basis β α
              ⟨p⟮ρ,σ,basis⟯ α α u, LinearMap.mem_range_self _ u⟩) : V)
            = p⟮ρ,σ,basis⟯ α α (p⟮ρ,σ,basis⟯ α α u) := by
                simpa [coordinateChange, LinearMap.restrict_apply, LinearMap.comp_apply] using
                  congrArg (fun f : Module.End ℂ V ↦ f (p⟮ρ,σ,basis⟯ α α u))
                    (matrixUnit_comp ρ σ basis α β β α rfl)
        _ = p⟮ρ,σ,basis⟯ α α u := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ V ↦ f u) (matrixUnit_comp ρ σ basis α α α α rfl)

-- Proof sketch: linear independence of the vectors `x_α` shows injectivity, while the
-- codomain is the range `W(x₁)` of the canonical map, giving surjectivity.
/-- The canonical map from `W_i` onto `W(x₁)` is bijective when `x₁ ≠ 0`. -/
private theorem generatedSubrepresentationHom_bijective
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) (hx₁ : (x₁ : V) ≠ 0) :
    Function.Bijective
      (generatedSubrepresentationHom ρ σ basis oneIndex x₁) := by
  change Function.Bijective ((coordinateFamilyHom ρ σ basis oneIndex x₁).toLinearMap.rangeRestrict)
  let f : W →ₗ[ℂ] V := coordinateFamilyMap ρ σ basis oneIndex x₁
  have hf_inj : Function.Injective f := by
    -- The basis coordinates are linearly independent, so the basis-constrained map is injective.
    exact basis.injective_constr_of_linearIndependent
      (coordinateVector_linearIndependent ρ σ basis oneIndex x₁ hx₁)
  refine ⟨?_, ?_⟩
  · -- Range restriction preserves injectivity exactly.
    simpa [f] using (LinearMap.injective_rangeRestrict_iff f).2 hf_inj
  · -- Surjectivity is built into the range restriction.
    simpa [f] using (LinearMap.surjective_rangeRestrict f)

-- Proof sketch: `matrixUnit_comp` with equal middle indices shows that `p_{αα}` is idempotent,
-- and its image is `V_{i,α}` by definition.
/-- Proposition 2-2.7-1 (1): source part (a). Each diagonal operator `p_{αα}` is a projection onto
its image `V_{i,α}`. -/
theorem diagonal_matrixUnit_isProj
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α : ι) :
    LinearMap.IsProj (V⟮ρ,σ,basis⟯ α) (p⟮ρ,σ,basis⟯ α α) := by
  refine LinearMap.IsProj.mk ?_ ?_
  · intro v
    -- By definition, the image of `p_{αα}` is `V_{i,α}`.
    exact LinearMap.mem_range_self _ v
  · intro v hv
    -- On its image, `p_{αα}` acts as the identity because `p_{αα} ∘ p_{αα} = p_{αα}`.
    rcases LinearMap.mem_range.mp hv with ⟨u, rfl⟩
    simpa [coordinateSubspace, LinearMap.comp_apply] using
      congrArg (fun f : Module.End ℂ V ↦ f u) (matrixUnit_comp ρ σ basis α α α α rfl)

open scoped Classical in
/-- Helper for Proposition 2-2.7-1: the diagonal projector `p_{αα}` acts as the identity on
`V_{i,α}` and annihilates every distinct coordinate subspace `V_{i,β}`. -/
private theorem coordinate_subspace_projection_isolation
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) [DecidableEq ι] {α β : ι} {v : V}
    (hv : v ∈ V⟮ρ,σ,basis⟯ β) :
    p⟮ρ,σ,basis⟯ α α v = if α = β then v else 0 := by
  rcases LinearMap.mem_range.mp hv with ⟨u, rfl⟩
  -- Write `v` as `p_{ββ}(u)` and reduce to the matrix-unit composition law.
  by_cases hαβ : α = β
  · subst β
    calc
      p⟮ρ,σ,basis⟯ α α (p⟮ρ,σ,basis⟯ α α u)
          = p⟮ρ,σ,basis⟯ α α u := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ V ↦ f u)
                  (matrixUnit_comp ρ σ basis α α α α rfl)
      _ = if α = α then p⟮ρ,σ,basis⟯ α α u else 0 := by
            simp
  · calc
      p⟮ρ,σ,basis⟯ α α (p⟮ρ,σ,basis⟯ β β u) = 0 := by
          simpa [LinearMap.comp_apply] using
            congrArg (fun f : Module.End ℂ V ↦ f u)
              (matrixUnit_comp_eq_zero_of_ne ρ σ basis α α β β hαβ)
      _ = if α = β then p⟮ρ,σ,basis⟯ β β u else 0 := by
            simp [hαβ]

-- Proof sketch: use `matrixUnit_comp` to prove pairwise disjointness of the coordinate
-- subspaces inside their supremum. Since the ambient subspace is already the generated sum,
-- `iSupIndep` is the primitive content and `DirectSum.IsInternal` is recovered from it when needed.
/-- Proposition 2-2.7-1 (2): source part (a). The coordinate subspaces `V_{i,α}` are independent
inside the subspace that they generate; this is the primitive content of the internal direct-sum
statement. -/
theorem iSupIndep_coordinateSubspaces
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) :
    iSupIndep
      (fun α : ι ↦
        (V⟮ρ,σ,basis⟯ α).comap
          (iSup fun α : ι ↦ V⟮ρ,σ,basis⟯ α).subtype) := by
  classical
  let S : Submodule ℂ V := iSup fun α : ι ↦ V⟮ρ,σ,basis⟯ α
  -- Route correction: use the submodule finset-sum criterion and isolate each summand by
  -- applying the diagonal projector `p_{αα}`.
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
  intro s v hv hsum α hα
  apply Subtype.ext
  have happly :
      ∑ i ∈ s,
          p⟮ρ,σ,basis⟯ α α (((v i : S) : V)) = 0 := by
    have := congrArg
      (fun z : S ↦
        p⟮ρ,σ,basis⟯ α α (z : V)) hsum
    simpa [map_sum] using this
  calc
    ((v α : S) : V) = ∑ i ∈ s, if α = i then (((v i : S) : V)) else 0 := by
            symm
            rw [Finset.sum_eq_single_of_mem α hα]
            · simp
            · intro i hi hneq
              by_cases hαi : α = i
              · exact (hneq hαi.symm).elim
              · simp [hαi]
    _ = ∑ i ∈ s,
          p⟮ρ,σ,basis⟯ α α (((v i : S) : V)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hmem :
                (((v i : S) : V)) ∈ V⟮ρ,σ,basis⟯ i := by
              simpa using hv i hi
            symm
            simpa using coordinate_subspace_projection_isolation ρ σ basis hmem
    _ = 0 := happly

/-- Helper for Proposition 2-2.7-1: the diagonal coefficient sum in the source projector formula
is the conjugate of the irreducible character value. -/
private theorem diagonal_matrixUnit_character_bridge
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) [DecidableEq ι] (s : G) :
    ∑ α : ι, basis.repr (σ s⁻¹ (basis α)) α = star (σ.character s) := by
  letI : FiniteDimensional ℂ W := basis.finiteDimensional_of_finite
  -- Rewrite the diagonal source coefficients as matrix entries, then identify their sum with the
  -- character at `s⁻¹` and use the finite-order conjugation formula.
  calc
    ∑ α : ι, basis.repr (σ s⁻¹ (basis α)) α
        = ∑ α : ι, (σ s⁻¹).toMatrix basis basis α α := by
            apply Finset.sum_congr rfl
            intro α hα
            simpa using (LinearMap.toMatrix_apply basis basis (σ s⁻¹) α α).symm
    _ = σ.character s⁻¹ := by
          simpa using
            (congrArg (fun f : G → ℂ ↦ f s⁻¹)
              (character_eq_sum_diagonal_matrix_coefficients_local σ basis)).symm
    _ = star (σ.character s) := by
          simpa using σ.char_inv_eq_star_of_isOfFinOrder s (isOfFinOrder_of_finite s)

-- Proof sketch: sum the diagonal matrix units, rewrite the diagonal coefficient sum as the
-- character, and recognize the resulting averaged operator as the owner
-- `characterWeightedEndomorphism`.
/-- The diagonal sum of the source matrix units is the canonical character-weighted endomorphism
from Theorem `2-2.6-1`. This is the bridge from the source-facing `p_{αα}` construction to the
owner abstraction `characterWeightedEndomorphism`. -/
theorem sum_diagonal_matrixUnit_eq_characterWeightedEndomorphism
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) :
    (∑ α : ι, p⟮ρ,σ,basis⟯ α α) = characterWeightedEndomorphism ρ σ := by
  classical
  let c : ℂ := (Fintype.card ι : ℂ) / Nat.card G
  have hcard :
      (Fintype.card ι : ℂ) = (Module.finrank ℂ W : ℂ) := by
    exact_mod_cast (Module.finrank_eq_card_basis basis).symm
  ext v
  calc
    (∑ α : ι, p⟮ρ,σ,basis⟯ α α) v
        = ∑ α : ι, p⟮ρ,σ,basis⟯ α α v := by
            simp [Finset.sum_apply]
    _ = ∑ α : ι, ∑ s : G,
          c • (basis.repr (σ s⁻¹ (basis α))) α • ρ s v := by
            -- Expand each diagonal matrix unit at the vector `v`.
            apply Finset.sum_congr rfl
            intro α hα
            simp [Representation.ExplicitDecomposition.matrixUnit, c, Finset.smul_sum,
              smul_smul]
    _ = ∑ s : G, c • (∑ α : ι, basis.repr (σ s⁻¹ (basis α)) α) • ρ s v := by
          -- Commute the `α`- and `s`-sums and gather the scalar kernel in front of `ρ s v`.
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s hs
          calc
            ∑ α : ι, c • (basis.repr (σ s⁻¹ (basis α))) α • ρ s v
                = ∑ α : ι, (c * (basis.repr (σ s⁻¹ (basis α))) α) • ρ s v := by
                    apply Finset.sum_congr rfl
                    intro α hα
                    simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
            _ = (∑ α : ι, c * (basis.repr (σ s⁻¹ (basis α))) α) • ρ s v := by
                  symm
                  exact Finset.sum_smul
            _ = (c * ∑ α : ι, basis.repr (σ s⁻¹ (basis α)) α) • ρ s v := by
                  congr 1
                  rw [← Finset.mul_sum]
            _ = c • (∑ α : ι, basis.repr (σ s⁻¹ (basis α)) α) • ρ s v := by
                  simp [smul_smul, mul_assoc]
    _ = ∑ s : G, c • star (σ.character s) • ρ s v := by
          -- Replace the diagonal coefficient sum by the conjugated character value.
          apply Finset.sum_congr rfl
          intro s hs
          rw [diagonal_matrixUnit_character_bridge σ basis s]
    _ = characterWeightedEndomorphism ρ σ v := by
          -- The remaining expression is exactly the definition of the character-weighted operator.
          simp [characterWeightedEndomorphism, Representation.asAlgebraHom_def,
            MonoidAlgebra.lift_apply, c, hcard, Finset.smul_sum, smul_smul, mul_comm,
            mul_left_comm, mul_assoc]

-- Proof sketch: the diagonal sum of the source matrix units is the character-weighted projector
-- from Theorem `2-2.6-1`, so its image is exactly the canonical isotypic piece `V_i`.
/-- Proposition 2-2.7-1 (3): source part (a). The `i`-isotypic piece `V_i` is the sum of the
coordinate subspaces `V_{i,α}`. -/
theorem iSup_coordinateSubspaces_eq_isotypic
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) :
    iSup (fun α : ι ↦ V⟮ρ,σ,basis⟯ α) =
      (ρ.isotypicSubrepresentation σ).toSubmodule := by
  classical
  apply le_antisymm
  · refine iSup_le ?_
    intro α x hx
    -- Each coordinate vector is fixed by the diagonal sum, hence belongs to the isotypic piece.
    have hfix : characterWeightedEndomorphism ρ σ x = x := by
      rcases LinearMap.mem_range.mp hx with ⟨u, rfl⟩
      have hsumComp :
          (∑ η : ι, p⟮ρ,σ,basis⟯ η η).comp (p⟮ρ,σ,basis⟯ α α) = p⟮ρ,σ,basis⟯ α α := by
        ext v
        calc
          (∑ η : ι, p⟮ρ,σ,basis⟯ η η).comp (p⟮ρ,σ,basis⟯ α α) v
              = ∑ η : ι, p⟮ρ,σ,basis⟯ η η (p⟮ρ,σ,basis⟯ α α v) := by
                  simp [LinearMap.comp_apply, Finset.sum_apply]
          _ = ∑ η : ι, if η = α then p⟮ρ,σ,basis⟯ α α v else 0 := by
                apply Finset.sum_congr rfl
                intro η hη
                by_cases h : η = α
                · subst η
                  simpa [LinearMap.comp_apply] using
                    congrArg (fun f : Module.End ℂ V ↦ f v)
                      (matrixUnit_comp ρ σ basis α α α α rfl)
                · have hηα : η ≠ α := h
                  simpa [hηα, LinearMap.comp_apply] using
                    congrArg (fun f : Module.End ℂ V ↦ f v)
                      (matrixUnit_comp_eq_zero_of_ne ρ σ basis η η α α hηα)
          _ = p⟮ρ,σ,basis⟯ α α v := by
                simp
      calc
        characterWeightedEndomorphism ρ σ (p⟮ρ,σ,basis⟯ α α u)
            = (∑ η : ι, p⟮ρ,σ,basis⟯ η η) (p⟮ρ,σ,basis⟯ α α u) := by
                rw [← sum_diagonal_matrixUnit_eq_characterWeightedEndomorphism ρ σ basis]
        _ = p⟮ρ,σ,basis⟯ α α u := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ V ↦ f u) hsumComp
    exact (LinearMap.IsProj.mem_iff_map_id
      (characterWeightedEndomorphism_isProj_isotypicSubrepresentation ρ σ)).2 hfix
  · intro x hx
    -- A vector fixed by the isotypic projector is the sum of its diagonal coordinate pieces.
    have hfix : characterWeightedEndomorphism ρ σ x = x :=
      (LinearMap.IsProj.mem_iff_map_id
        (characterWeightedEndomorphism_isProj_isotypicSubrepresentation ρ σ)).1 hx
    rw [← sum_diagonal_matrixUnit_eq_characterWeightedEndomorphism ρ σ basis] at hfix
    rw [← hfix]
    simpa using
      (Submodule.sum_mem (iSup fun α : ι ↦ V⟮ρ,σ,basis⟯ α)
        (fun α hα ↦ Submodule.mem_iSup_of_mem α (LinearMap.mem_range_self _ x)))

/-- Proposition 2-2.7-1 (4): source part (a). The diagonal sum of the matrix units `p_{αα}` is
the projector onto the canonical `σ`-isotypic piece `V_i`. -/
theorem sum_diagonal_matrixUnit_isProj_isotypicSubrepresentation
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) :
    LinearMap.IsProj (ρ.isotypicSubrepresentation σ).toSubmodule
      (∑ α : ι, p⟮ρ,σ,basis⟯ α α) := by
  simpa [sum_diagonal_matrixUnit_eq_characterWeightedEndomorphism ρ σ basis] using
    characterWeightedEndomorphism_isProj_isotypicSubrepresentation ρ σ

/- Proposition 2-2.7-1 (5): the canonical vanishing-on-other-isotypics statement used in part (b)
is already Theorem `2-2.6-1`, namely
`characterWeightedEndomorphism_eq_zero_of_mem_other_isotypicSubrepresentation`. -/
recall characterWeightedEndomorphism_eq_zero_of_mem_other_isotypicSubrepresentation

-- Proof sketch: if `v ∈ V_{i,γ}` with `γ ≠ β`, write `v = p_{γγ}(u)` and use
-- `p_{αβ} ∘ p_{γγ} = 0`.
/-- Proposition 2-2.7-1 (4): source part (b). The matrix unit `p_{αβ}` vanishes on
`V_{i,γ}` whenever `γ ≠ β`. -/
theorem matrixUnit_apply_eq_zero_of_mem_other_coordinate
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W)
    {α β γ : ι} (hγ : γ ≠ β) {v : V} (hv : v ∈ V⟮ρ,σ,basis⟯ γ) :
    p⟮ρ,σ,basis⟯ α β v = 0 := by
  rcases LinearMap.mem_range.mp hv with ⟨u, rfl⟩
  -- Writing `v` as `p_{γγ}(u)` reduces the claim to the off-diagonal matrix-unit relation.
  have hβγ : β ≠ γ := fun h ↦ hγ h.symm
  simpa [coordinateSubspace, LinearMap.comp_apply] using
    congrArg (fun f : Module.End ℂ V ↦ f u)
      (matrixUnit_comp_eq_zero_of_ne ρ σ basis α β γ γ hβγ)

/-- Proposition 2-2.7-1 (5): source part (b). The matrix unit `p_{αβ}` restricts to a linear
isomorphism from `V_{i,β}` onto `V_{i,α}`. -/
def coordinateChangeEquiv
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (α β : ι) :
    V⟮ρ,σ,basis⟯ β ≃ₗ[ℂ] V⟮ρ,σ,basis⟯ α :=
  LinearEquiv.ofBijective (coordinateChange ρ σ basis α β)
    (coordinateChange_bijective ρ σ basis α β)

open scoped Classical in
/-- Helper for Proposition 2-2.7-1: applying `p_{oneIndex,η}` to a general vector in the copy
`W(x₁)` extracts the `η`-th basis coordinate and returns that scalar multiple of `x₁`. -/
private theorem reverse_matrixUnit_apply_coordinateFamilyMap
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) [DecidableEq ι] (oneIndex η : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) (w : W) :
    p⟮ρ,σ,basis⟯ oneIndex η (coordinateFamilyMap ρ σ basis oneIndex x₁ w) =
      (basis.repr w η) • (x₁ : V) := by
  have hw_expand :
      coordinateFamilyMap ρ σ basis oneIndex x₁ w =
        ∑ x : ι, (basis.repr w x) • coordinateVector ρ σ basis oneIndex x₁ x := by
    -- Expand the basis-constrained map by the standard `Basis.constr` formula.
    simpa [coordinateFamilyMap] using
      (basis.constr_apply_fintype ℂ (coordinateVector ρ σ basis oneIndex x₁) w)
  -- Expand `w` in the chosen basis and collapse each basis vector with the reverse matrix unit.
  rw [hw_expand]
  calc
    p⟮ρ,σ,basis⟯ oneIndex η
        (∑ x : ι, (basis.repr w x) • coordinateVector ρ σ basis oneIndex x₁ x)
        = ∑ x : ι, (basis.repr w x) •
            p⟮ρ,σ,basis⟯ oneIndex η (coordinateVector ρ σ basis oneIndex x₁ x) := by
              simp [map_sum, map_smul]
    _ = ∑ x, (basis.repr w x) • ↑(if η = x then x₁ else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [reverse_matrixUnit_apply_coordinateVector]
    _ = ∑ x, if η = x then (basis.repr w x) • (x₁ : V) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hηx : η = x <;> simp [hηx]
    _ = (basis.repr w η) • (x₁ : V) := by
          simp

-- Proof sketch: the canonical intertwining equivalence `W_i ≃ W(x₁)` identifies the generated
-- subrepresentation with the model representation `W_i`, whose chosen basis has cardinality
-- `Fintype.card ι`.
/-- Proposition 2-2.7-1 (9): source part (c). If `x₁ ≠ 0`, then the generated
subrepresentation `W(x₁)` has dimension `Fintype.card ι`. -/
theorem finrank_generatedSubrepresentation_eq
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) (hx₁ : (x₁ : V) ≠ 0) :
    Module.finrank ℂ (W⟮ρ,σ,basis,oneIndex⟯ x₁).toSubmodule = Fintype.card ι := by
  simpa [Module.finrank_eq_card_basis basis] using
    ((generatedSubrepresentationHom ρ σ basis oneIndex x₁).ofBijective
      (generatedSubrepresentationHom_bijective ρ σ basis oneIndex x₁ hx₁)).finrank_eq.symm

/-- Proposition 2-2.7-1 (10): source part (c). If `x₁ ≠ 0`, the canonical map sending the chosen
basis of `W_i` to the vectors `x_α = p_{α,oneIndex}(x₁)` gives an isomorphism of
representations `W_i ≃ W(x₁)`. -/
def generatedSubrepresentationEquiv
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (x₁ : V⟮ρ,σ,basis⟯ oneIndex) (hx₁ : (x₁ : V) ≠ 0) :
    σ.Equiv (W⟮ρ,σ,basis,oneIndex⟯ x₁).toRepresentation :=
  (generatedSubrepresentationHom ρ σ basis oneIndex x₁).ofBijective
    (generatedSubrepresentationHom_bijective ρ σ basis oneIndex x₁ hx₁)

-- Proof sketch: use part (c) for each basis vector of `V_{i,oneIndex}`; the corresponding
-- subspaces are pairwise disjoint because the basis vectors are, and they form an internal direct
-- sum inside their total span.
/-- Proposition 2-2.7-1 (11): source part (d). A basis of `V_{i,oneIndex}` yields an internal
direct sum of the subrepresentations `W(x₁^{(k)})` inside the subspace that they generate. -/
theorem isInternal_generatedSubrepresentations_of_basis
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    {κ : Type y} (b : Module.Basis κ ℂ (V⟮ρ,σ,basis⟯ oneIndex)) :
    iSupIndep
      (fun k : κ ↦ (W⟮ρ,σ,basis,oneIndex⟯ (b k)).toSubmodule) := by
  classical
  -- Route correction: use the finset-sum criterion and apply `p_{oneIndex,η}` to isolate the
  -- basis coordinates inside `V_{i,oneIndex}`.
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
  intro s v hv hsum k hk
  let w : κ → W := fun i ↦
    if hi : i ∈ s then Classical.choose (LinearMap.mem_range.mp (hv i hi)) else 0
  have hw :
      ∀ i ∈ s, coordinateFamilyMap ρ σ basis oneIndex (b i) (w i) = v i := by
    intro i hi
    simpa [w, hi] using Classical.choose_spec (LinearMap.mem_range.mp (hv i hi))
  have hsum_w :
      ∑ i ∈ s, coordinateFamilyMap ρ σ basis oneIndex (b i) (w i) = 0 := by
    calc
      ∑ i ∈ s, coordinateFamilyMap ρ σ basis oneIndex (b i) (w i)
          = ∑ i ∈ s, v i := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hw i hi
      _ = 0 := hsum
  have hcoeff :
      ∀ η : ι, basis.repr (w k) η = 0 := by
    intro η
    have happly := congrArg (p⟮ρ,σ,basis⟯ oneIndex η) hsum_w
    have happly_sub :
        (∑ i ∈ s, (basis.repr (w i) η) • b i : V⟮ρ,σ,basis⟯ oneIndex) = 0 := by
      apply Subtype.ext
      simpa [map_sum, map_smul, reverse_matrixUnit_apply_coordinateFamilyMap]
        using happly
    have hkcoeff := congrArg (fun z : V⟮ρ,σ,basis⟯ oneIndex ↦ b.repr z k) happly_sub
    simpa [Finsupp.single_apply, hk] using hkcoeff
  have hwk_repr : basis.repr (w k) = 0 := by
    ext η
    exact hcoeff η
  have hwk : w k = 0 := by
    apply basis.repr.injective
    simpa using hwk_repr
  calc
    v k = coordinateFamilyMap ρ σ basis oneIndex (b k) (w k) := by
            symm
            exact hw k hk
    _ = 0 := by
          simp [hwk]

-- Proof sketch: each basis vector of `V_{i,oneIndex}` produces one copy of the model
-- representation inside `V_i`, and the internal-direct-sum statement identifies their sum with
-- all of `V_i`.
/-- Proposition 2-2.7-1 (12): source part (d). The underlying submodules of the
subrepresentations attached to a basis of `V_{i,oneIndex}` sum to the full isotypic piece `V_i`. -/
theorem iSup_generatedSubrepresentations_eq_isotypic_of_basis
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    {κ : Type z} (b : Module.Basis κ ℂ (V⟮ρ,σ,basis⟯ oneIndex)) :
    iSup (fun k : κ ↦ (W⟮ρ,σ,basis,oneIndex⟯ (b k)).toSubmodule) =
      (ρ.isotypicSubrepresentation σ).toSubmodule := by
  classical
  apply le_antisymm
  · refine iSup_le ?_
    intro k x hx
    rcases LinearMap.mem_range.mp hx with ⟨w, rfl⟩
    have hw :
        coordinateFamilyMap ρ σ basis oneIndex (b k) w ∈
          iSup (fun α : ι ↦ V⟮ρ,σ,basis⟯ α) := by
      -- Every basis image `x_α = p_{α,oneIndex}(b k)` lies in the corresponding coordinate
      -- subspace `V_{i,α}`, so the whole generated copy lies in the coordinate sum.
      rw [← basis.sum_repr w]
      simp_rw [coordinateFamilyMap, map_sum, map_smul, Module.Basis.constr_basis]
      exact Submodule.sum_mem _
        (fun α hα ↦
          Submodule.smul_mem _ _ <|
            Submodule.mem_iSup_of_mem α <|
              matrixUnit_maps_to_coordinateSubspace ρ σ basis α oneIndex _ (b k).2)
    simpa [iSup_coordinateSubspaces_eq_isotypic ρ σ basis] using hw
  · rw [← iSup_coordinateSubspaces_eq_isotypic ρ σ basis]
    refine iSup_le ?_
    intro α x hx
    rcases (coordinateChange_bijective ρ σ basis α oneIndex).2 ⟨x, hx⟩ with ⟨y, hy⟩
    have hxy : p⟮ρ,σ,basis⟯ α oneIndex y = x := by
      simpa [coordinateChange, LinearMap.restrict_apply] using congrArg Subtype.val hy
    have hy_repr : (y : V) = (b.repr y).sum fun k a ↦ a • (b k : V) := by
      -- Coerce the basis expansion in the coordinate subspace back to the ambient space.
      have hy_repr_sub :
          ((b.repr y).sum fun k a ↦ a • b k : V⟮ρ,σ,basis⟯ oneIndex) = y := by
        simpa [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr y
      calc
        (y : V) = (((b.repr y).sum fun k a ↦ a • b k : V⟮ρ,σ,basis⟯ oneIndex) : V) := by
          exact congrArg (fun z : V⟮ρ,σ,basis⟯ oneIndex ↦ (z : V)) hy_repr_sub.symm
        _ = (b.repr y).sum fun k a ↦ a • (b k : V) := by
          simp [Finsupp.sum, Submodule.coe_sum]
    rw [← hxy, hy_repr]
    simpa [Finsupp.sum] using
      (Submodule.sum_mem
        (iSup (fun k : κ ↦ (W⟮ρ,σ,basis,oneIndex⟯ (b k)).toSubmodule))
        (fun k hk ↦
          Submodule.smul_mem _ _ <|
            Submodule.mem_iSup_of_mem k <| by
              refine LinearMap.mem_range.mpr ?_
              refine ⟨basis α, ?_⟩
              simp [generatedSubrepresentation, coordinateFamilyHom, coordinateFamilyMap,
                coordinateVector]))

end

end ExplicitDecomposition

end Representation
