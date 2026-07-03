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


/-! ### Corollary_2_2_2_3 (from Chap02) -/
open scoped BigOperators
universe u v w u₁ u₂

namespace Representation

noncomputable section

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {V1 : Type v} [AddCommGroup V1] [Module k V1]
variable {V2 : Type w} [AddCommGroup V2] [Module k V2]
variable {ι1 : Type u₁} [Fintype ι1]
variable {ι2 : Type u₂} [Fintype ι2]

local instance : Fintype G := Fintype.ofFinite G

variable [Invertible (Nat.card G : k)]

/- Source-facing bridge: the core/canonical owner is the averaged intertwiner
`(ρ1.linHom ρ2).averageMap`; the new owner-level bridge
`averageMap_linHom_basis_entry_eq` computes its matrix entry on the canonical basis vector
`b1.linearMap b2 (j2, j1)`. This corollary is the vanishing specialization of that bridge for
nonisomorphic irreducibles. -/
-- Proof sketch: apply `averageMap_linHom_eq_zero_of_not_isomorphic` to the canonical basis vector
-- `b1.linearMap b2 (j2, j1)`, then read off its `(i2, i1)` matrix entry through
-- `averageMap_linHom_basis_entry_eq`.
open scoped Classical in
/-- Corollary 2-2.2-3: for nonisomorphic irreducible representations of a finite group over a
field in which `|G|` is invertible, the normalized sum of the corresponding matrix-coefficient
products is zero for arbitrary basis indices. -/
theorem matrix_coefficient_orthogonality_of_not_isomorphic
    (ρ1 : Representation k G V1) (ρ2 : Representation k G V2)
    [ρ1.IsIrreducible] [ρ2.IsIrreducible]
    (hρ : ¬ Nonempty (ρ1.Equiv ρ2))
    (b1 : Module.Basis ι1 k V1) (b2 : Module.Basis ι2 k V2)
    (i1 j1 : ι1) (i2 j2 : ι2) :
    (Nat.card G : k)⁻¹ *
      ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 = 0 := by
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  let e := b1.linearMap b2 (j2, j1)
  have hbridge :
      (Nat.card G : k)⁻¹ *
          ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 =
        (((ρ1.linHom ρ2).averageMap e).toMatrix b1 b2 i2 i1) := by
    simpa [e, Nat.card_eq_fintype_card] using
      (averageMap_linHom_basis_entry_eq ρ1 ρ2 b1 b2 i1 j1 i2 j2).symm
  have hzero :
      (((ρ1.linHom ρ2).averageMap e).toMatrix b1 b2 i2 i1) = 0 := by
    simpa [e] using congrArg (fun f ↦ f.toMatrix b1 b2 i2 i1) <|
      averageMap_linHom_eq_zero_of_not_isomorphic ρ1 ρ2 e hρ
  exact hbridge.trans hzero

end

end

end Representation

/-! ### Corollary_2_2_2_4 (from Chap02) -/
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

/-! ### Proposition_2_2_2_1 (from Chap02) -/
universe u v w

namespace Representation

section

variable {k : Type*} [Field k]
variable {G : Type u} [Monoid G]
variable {V1 : Type v} [AddCommGroup V1] [Module k V1]
variable {V2 : Type w} [AddCommGroup V2] [Module k V2]
variable (ρ1 : Representation k G V1) (ρ2 : Representation k G V2)
variable [ρ1.IsIrreducible] [ρ2.IsIrreducible]

-- Source/core/bridge triage:
-- * source-facing: Schur's lemma as LinearRepresentations_Serre_1977 states it, namely zero/nonzero and scalar-identity
--   consequences for equivariant maps.
-- * core/canonical: the owner abstraction is `Representation.IntertwiningMap` together with the
--   `Representation.IsIrreducible` API in mathlib.
-- * bridge/view: this file keeps only the thin source-facing consequences of the canonical owner
--   facts, rather than re-packaging irreducibility data locally.

omit [ρ1.IsIrreducible] [ρ2.IsIrreducible] in
/-- Helper for Proposition 2-2.2-1: a bijective intertwining map between two representations
produces an isomorphism of representations. -/
theorem nonempty_equiv_of_bijective_intertwiningMap
    (f : ρ1.IntertwiningMap ρ2) (hf : Function.Bijective f) :
    Nonempty (ρ1.Equiv ρ2) := by
  -- Package the bijective equivariant linear map into the canonical representation equivalence.
  exact ⟨f.ofBijective hf⟩

-- Proof sketch: `Representation.IsIrreducible.bijective_or_eq_zero` says a nonzero intertwiner
-- between irreducibles is bijective, hence an equivalence of representations; the nonisomorphism
-- hypothesis rules out that case.
/-- Proposition 2-2.2-1 (1): an equivariant linear map between two nonisomorphic irreducible
representations over a field is zero. -/
theorem intertwiningMap_eq_zero_of_not_isomorphic
    (f : ρ1.IntertwiningMap ρ2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    f = 0 := by
  -- Exclude the bijective branch by converting it into a forbidden representation equivalence.
  simpa using
    (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_left
      (fun hf ↦ hρ <| nonempty_equiv_of_bijective_intertwiningMap (ρ1 := ρ1) (ρ2 := ρ2) f hf)

variable {V : Type v} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)
variable [ρ.IsIrreducible] [FiniteDimensional k V] [IsAlgClosed k]

omit [ρ.IsIrreducible] [FiniteDimensional k V] [IsAlgClosed k] in
/-- Helper for Proposition 2-2.2-1: the scalar coming from the endomorphism-ring `algebraMap`
acts as the same scalar multiple of the identity intertwining map. -/
lemma algebraMap_eq_smul_id (c : k) :
    algebraMap k (ρ.IntertwiningMap ρ) c = c • 1 := by
  -- Identify scalar endomorphisms pointwise with the corresponding homothety.
  simp

-- Proof sketch: use the owner theorem
-- `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`, then rewrite
-- the resulting scalar endomorphism using `Representation.algebraMap_apply`.
/-- Proposition 2-2.2-1 (2): every equivariant endomorphism of an irreducible finite-dimensional
representation over an algebraically closed field is a scalar multiple of the identity
intertwining map. -/
theorem intertwiningMap_eq_smul_id
    (f : ρ.IntertwiningMap ρ) :
    ∃ c : k, f = c • 1 := by
  -- Pull the endomorphism back through the scalar algebra map supplied by Schur's lemma.
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  refine ⟨c, ?_⟩
  -- Rewrite the abstract scalar endomorphism into LinearRepresentations_Serre_1977's source-facing homothety form.
  calc
    f = algebraMap k (ρ.IntertwiningMap ρ) c := hc.symm
    _ = c • 1 := algebraMap_eq_smul_id (ρ := ρ) c

end

end Representation

/-! ### Remark_2_2_2_5 (from Chap02) -/
open scoped BigOperators MonoidAlgebra

noncomputable section

universe u v w u₁ u₂

namespace Representation

section

variable {K : Type v} [Field K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGRemark2225 : Fintype G := Fintype.ofFinite G

/- Remark 2-2.2-5 uses LinearRepresentations_Serre_1977's complex pairing; the canonical owner in the project is the
field-valued pairing `groupFunctionPairingOverField`, and the bracket notation is the source-facing
surface form. -/
open scoped Representation

/- Layer triage for this remark:
* core/canonical: `groupFunctionPairingOverField`
* source-facing: the symmetric bilinear pairing statements written with `⟪-, -⟫`
* bridge/view: the chapter corollaries on matrix coefficients, restated here in the pairing
  notation. -/

/- Remark 2-2.2-5 first records basic owner-level API for LinearRepresentations_Serre_1977's normalized pairing. Those
canonical statements now live with `groupFunctionPairingOverField` itself:
`groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply`, `groupFunctionPairing_comm`,
`groupFunctionPairing_add_left`, `groupFunctionPairing_smul_left`,
`groupFunctionPairing_add_right`, and `groupFunctionPairing_smul_right`. -/

variable [Invertible (Nat.card G : K)]
variable {V1 : Type w} [AddCommGroup V1] [Module K V1]
variable {V2 : Type u₁} [AddCommGroup V2] [Module K V2]
variable {ι1 : Type u₁} [Fintype ι1]
variable {ι2 : Type u₂} [Fintype ι2]

-- Proof sketch: unfold the canonical pairing owner `groupFunctionPairingOverField`; the result is
-- exactly the vanishing specialization of the canonical averaged-intertwiner bridge
-- `averageMap_linHom_basis_entry_eq`.
open scoped Classical in
/-- The orthogonality relation for matrix coefficients of nonisomorphic irreducible
representations, expressed with the pairing notation. -/
theorem matrixCoefficient_pairing_eq_zero_of_not_isomorphic
    (ρ1 : Representation K G V1) (ρ2 : Representation K G V2)
    [ρ1.IsIrreducible] [ρ2.IsIrreducible]
    (hρ : ¬ Nonempty (ρ1.Equiv ρ2))
    (b1 : Module.Basis ι1 K V1) (b2 : Module.Basis ι2 K V2)
    (i1 j1 : ι1) (i2 j2 : ι2) :
    ⟪fun t ↦ (ρ2 t).toMatrix b2 b2 i2 j2, fun t ↦ (ρ1 t).toMatrix b1 b1 j1 i1⟫ = 0 := by
  letI : Invertible (Fintype.card G : K) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  calc
    ⟪fun t ↦ (ρ2 t).toMatrix b2 b2 i2 j2, fun t ↦ (ρ1 t).toMatrix b1 b1 j1 i1⟫
      = (((ρ1.linHom ρ2).averageMap (b1.linearMap b2 (j2, j1))).toMatrix b1 b2 i2 i1) := by
          simpa [groupFunctionPairingOverField, Nat.card_eq_fintype_card] using
            (averageMap_linHom_basis_entry_eq ρ1 ρ2 b1 b2 i1 j1 i2 j2).symm
    _ = 0 := by
          simpa using congrArg (fun f ↦ f.toMatrix b1 b2 i2 i1) <|
            averageMap_linHom_eq_zero_of_not_isomorphic ρ1 ρ2 (b1.linearMap b2 (j2, j1)) hρ

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
variable {ι : Type u₁} [Fintype ι]

-- Proof sketch: apply `averageMap_linHom_self_eq_trace_smul_id` to the canonical basis vector
-- `b.end (j2, j1)` of `Module.End ℂ V`, read off the `(i2, i1)` matrix entry using
-- `averageMap_linHom_basis_entry_eq`, and compute the trace of that matrix unit.
open scoped Classical in
/-- The orthogonality relation for matrix coefficients of one irreducible representation, expressed
with the pairing notation. -/
theorem matrixCoefficient_pairing_of_irreducible
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (b : Module.Basis ι ℂ V) (i1 j1 i2 j2 : ι) :
    ⟪fun t ↦ (ρ t).toMatrix b b i2 j2, fun t ↦ (ρ t).toMatrix b b j1 i1⟫ =
      if i2 = i1 then
        if j2 = j1 then (Module.finrank ℂ V : ℂ)⁻¹ else 0
      else 0 := by
  letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  letI : NeZero (Module.finrank ℂ V) := NeZero.of_pos Module.finrank_pos
  have htrace : LinearMap.trace ℂ V (b.end (j2, j1)) = if j2 = j1 then 1 else 0 := by
    rw [Module.Basis.end_apply, Matrix.trace_toLin_eq, Matrix.stdBasis_eq_single]
    by_cases h : j2 = j1
    · subst h
      simp [Matrix.trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne j2 j1 (1 : ℂ) h, h]
  calc
    ⟪fun t ↦ (ρ t).toMatrix b b i2 j2, fun t ↦ (ρ t).toMatrix b b j1 i1⟫
      = (((ρ.linHom ρ).averageMap (b.end (j2, j1))).toMatrix b b i2 i1) := by
          simpa [groupFunctionPairingOverField, Nat.card_eq_fintype_card] using
            (averageMap_linHom_basis_entry_eq ρ ρ b b i1 j1 i2 j2).symm
    _ = ((((Module.finrank ℂ V : ℂ)⁻¹ * LinearMap.trace ℂ V (b.end (j2, j1))) •
          (LinearMap.id : V →ₗ[ℂ] V)).toMatrix b b i2 i1) := by
          simpa using congrArg (fun f ↦ f.toMatrix b b i2 i1)
            (averageMap_linHom_self_eq_trace_smul_id ρ (b.end (j2, j1)))
    _ = if i2 = i1 then
          if j2 = j1 then (Module.finrank ℂ V : ℂ)⁻¹ else 0
        else 0 := by
          rw [htrace]
          by_cases hi : i2 = i1
          · subst hi
            by_cases hj : j2 = j1
            · simp [hj]
            · simp [hj]
          · by_cases hj : j2 = j1
            · simp [hj, hi]
            · simp [hj, hi]

end

end Representation

/-! ### Corollary_2_2_3_3 (from Chap02) -/
universe u v w u₁ u₂ u₃

namespace Representation

noncomputable section

section

open CategoryTheory
open scoped Representation
open scoped MonoidAlgebra

variable {G : Type u} [Group G] [Finite G]
variable {K : Type u₁} [Field K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

local instance (α : Type*) [Finite α] : DecidableEq α :=
  Classical.decEq α

-- Source/core/bridge triage:
-- * source-facing: the decomposition-independent multiplicity statement below.
-- * core/canonical: `Representation.IntertwiningMap` via the owner theorem
--   `card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`.
-- * bridge/view: the internal direct-sum decompositions `σ₁`, `σ₂`.
--
-- Proof sketch: when `τ` is irreducible, apply the canonical multiplicity owner theorem to each
-- decomposition and compare both counts with the same invariant
-- `Module.finrank K (ρ.IntertwiningMap τ)`. If `τ` is not irreducible, then no irreducible
-- summand can be equivalent to `τ`, so both counted subtypes are empty.
omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: irreducibility is preserved by an equivalence of
representations. -/
private theorem isIrreducible_of_equiv
    {V' : Type*} [AddCommGroup V'] [Module K V']
    {W' : Type*} [AddCommGroup W'] [Module K W']
    {ρ : Representation K G V'} {σ : Representation K G W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) :
    σ.IsIrreducible := by
  letI : Module K[G] V' := ρ.instModuleMonoidAlgebraAsModule
  letI : Module K[G] W' := σ.instModuleMonoidAlgebraAsModule
  -- Translate irreducibility to simplicity over the group ring.
  have hρsimple : IsSimpleModule K[G] V' := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  -- Transport simplicity through the `K[G]`-linear equivalence induced by `e`.
  let eAsModule : V' ≃ₗ[K[G]] W' :=
    LinearEquiv.ofBijective
      (show V' →ₗ[K[G]] W' from
        (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := σ))
          e.toIntertwiningMap)
      (show Function.Bijective
          (((Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := σ))
            e.toIntertwiningMap) : V' → W') from
        e.toLinearEquiv.bijective)
  have hσsimple : IsSimpleModule K[G] W' :=
    (LinearEquiv.isSimpleModule_iff eAsModule).mp hρsimple
  -- Translate back to irreducibility of the target representation.
  simpa using (Representation.irreducible_iff_isSimpleModule_asModule σ).mpr hσsimple

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: any representation equivalent to an irreducible one is
irreducible. -/
private theorem isIrreducible_of_nonempty_rep_equiv
    {V' : Type*} [AddCommGroup V'] [Module K V']
    {W' : Type*} [AddCommGroup W'] [Module K W']
    {ρ : Representation K G V'} {σ : Representation K G W'}
    [ρ.IsIrreducible] (h : Nonempty (ρ.Equiv σ)) :
    σ.IsIrreducible := by
  -- Unpack the equivalence witness and transport irreducibility along it.
  rcases h with ⟨e⟩
  exact isIrreducible_of_equiv e

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: an irreducible representation cannot be equivalent to a
reducible one. -/
private theorem not_nonempty_rep_equiv_of_isIrreducible_of_not_isIrreducible
    {V' : Type*} [AddCommGroup V'] [Module K V']
    {W' : Type*} [AddCommGroup W'] [Module K W']
    {ρ : Representation K G V'} {σ : Representation K G W'}
    (hρ : ρ.IsIrreducible) (hσ : ¬ σ.IsIrreducible) :
    ¬ Nonempty (ρ.Equiv σ) := by
  -- Any equivalence would transport irreducibility from `ρ` to `σ`.
  intro h
  letI : ρ.IsIrreducible := hρ
  exact hσ (isIrreducible_of_nonempty_rep_equiv h)

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: if the target representation is not irreducible, then the
summand indices carrying an equivalent representation form an empty type. -/
private theorem isEmpty_isomorphic_irreducible_summands_of_not_isIrreducible
    {ι : Type*} [Finite ι] {V' : Type*} [AddCommGroup V'] [Module K V']
    (ρ : Representation K G V')
    (σ : ι → Subrepresentation ρ)
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    {W' : Type*} [AddCommGroup W'] [Module K W']
    (τ : Representation K G W')
    (hτ : ¬ τ.IsIrreducible) :
    IsEmpty { i // Nonempty ((σ i).toRepresentation.Equiv τ) } := by
  -- Any witness would contradict the incompatibility between irreducibility and reducibility.
  refine ⟨fun i ↦ ?_⟩
  exact
    not_nonempty_rep_equiv_of_isIrreducible_of_not_isIrreducible
      (hσ i.1) hτ i.2

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: if the target representation is not irreducible, then no
irreducible summand in a decomposition can be equivalent to it, so the counted subtype has
cardinality zero. -/
private theorem nat_card_isomorphic_irreducible_summands_eq_zero_of_not_isIrreducible
    {ι : Type*} [Finite ι] {V' : Type*} [AddCommGroup V'] [Module K V']
    (ρ : Representation K G V')
    (σ : ι → Subrepresentation ρ)
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    {W' : Type*} [AddCommGroup W'] [Module K W']
    (τ : Representation K G W')
    (hτ : ¬ τ.IsIrreducible) :
    Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ) } = 0 := by
  -- First show the witness type is empty, then read off its cardinality.
  letI : IsEmpty { i // Nonempty ((σ i).toRepresentation.Equiv τ) } :=
    isEmpty_isomorphic_irreducible_summands_of_not_isIrreducible ρ σ hσ τ hτ
  exact Nat.card_of_isEmpty

omit [Finite G] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: when the target representation is irreducible, the number of
isomorphic irreducible summands in a fixed decomposition is the finrank of the intertwining
space. -/
private theorem nat_card_isomorphic_irreducible_summands_eq_finrank_of_isIrreducible
    {ι : Type*} [Finite ι] {V' : Type*} [AddCommGroup V'] [Module K V']
    [FiniteDimensional K V']
    (ρ : Representation K G V')
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    {W' : Type*} [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']
    (τ : Representation K G W')
    (hτ : τ.IsIrreducible) :
    Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ) } =
      Module.finrank K (ρ.IntertwiningMap τ) := by
  -- This is exactly the owner multiplicity theorem from Theorem 2-2.3-2.
  simpa using
    card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
      ρ σ hinternal hσ τ hτ

omit [Finite G] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: when `τ` is irreducible, two irreducible decompositions of `ρ`
have the same number of summands equivalent to `τ` because both counts equal the same
intertwining-space dimension. -/
private theorem card_isomorphic_irreducible_summands_eq_of_two_decompositions_of_isIrreducible
    {ι₁ : Type u₂} [Finite ι₁] {ι₂ : Type u₃} [Finite ι₂]
    (ρ : Representation K G V)
    (σ₁ : ι₁ → Subrepresentation ρ)
    (hinternal₁ : DirectSum.IsInternal (fun i ↦ (σ₁ i).toSubmodule))
    (hσ₁ : ∀ i, (σ₁ i).toRepresentation.IsIrreducible)
    (σ₂ : ι₂ → Subrepresentation ρ)
    (hinternal₂ : DirectSum.IsInternal (fun i ↦ (σ₂ i).toSubmodule))
    (hσ₂ : ∀ i, (σ₂ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W)
    (hτ : τ.IsIrreducible) :
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } =
      Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := by
  -- Compare both decomposition counts through the same canonical intertwining-space invariant.
  calc
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } =
        Module.finrank K (ρ.IntertwiningMap τ) := by
      exact
        nat_card_isomorphic_irreducible_summands_eq_finrank_of_isIrreducible
          ρ σ₁ hinternal₁ hσ₁ τ hτ
    _ = Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := by
      symm
      exact
        nat_card_isomorphic_irreducible_summands_eq_finrank_of_isIrreducible
          ρ σ₂ hinternal₂ hσ₂ τ hτ

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)]
  [FiniteDimensional K V] [FiniteDimensional K W] in
/-- Helper for Corollary 2-2.3-3: when `τ` is not irreducible, no irreducible summand from either
decomposition can be equivalent to `τ`, so both multiplicity counts vanish. -/
private theorem card_isomorphic_irreducible_summands_eq_of_two_decompositions_of_not_isIrreducible
    {ι₁ : Type u₂} [Finite ι₁] {ι₂ : Type u₃} [Finite ι₂]
    (ρ : Representation K G V)
    (σ₁ : ι₁ → Subrepresentation ρ)
    (hσ₁ : ∀ i, (σ₁ i).toRepresentation.IsIrreducible)
    (σ₂ : ι₂ → Subrepresentation ρ)
    (hσ₂ : ∀ i, (σ₂ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W)
    (hτ : ¬ τ.IsIrreducible) :
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } =
      Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := by
  have hzero₁ :
      Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } = 0 :=
    nat_card_isomorphic_irreducible_summands_eq_zero_of_not_isIrreducible ρ σ₁ hσ₁ τ hτ
  have hzero₂ :
      Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } = 0 :=
    nat_card_isomorphic_irreducible_summands_eq_zero_of_not_isIrreducible ρ σ₂ hσ₂ τ hτ
  -- Compare both sides through the common zero value forced by reducibility of `τ`.
  calc
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } = 0 := hzero₁
    _ = Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := hzero₂.symm

omit [Finite G] [Invertible (Nat.card G : K)] in
/-- Corollary 2-2.3-3: for a finite-dimensional representation `τ`, the number of irreducible
summands of a decomposition of `ρ` that are isomorphic to `τ` is independent of the chosen
decomposition. In particular, when `τ` is irreducible this common value is the multiplicity of
`τ` in `ρ`. -/
theorem card_isomorphic_irreducible_summands_eq_of_two_decompositions
    {ι₁ : Type u₂} [Finite ι₁] {ι₂ : Type u₃} [Finite ι₂]
    (ρ : Representation K G V)
    (σ₁ : ι₁ → Subrepresentation ρ)
    (hinternal₁ : DirectSum.IsInternal (fun i ↦ (σ₁ i).toSubmodule))
    (hσ₁ : ∀ i, (σ₁ i).toRepresentation.IsIrreducible)
    (σ₂ : ι₂ → Subrepresentation ρ)
    (hinternal₂ : DirectSum.IsInternal (fun i ↦ (σ₂ i).toSubmodule))
    (hσ₂ : ∀ i, (σ₂ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W) :
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } =
      Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := by
  classical
  by_cases hτ : τ.IsIrreducible
  · -- In the irreducible branch, reduce immediately to the common intertwining-space dimension.
    exact
      card_isomorphic_irreducible_summands_eq_of_two_decompositions_of_isIrreducible
        ρ σ₁ hinternal₁ hσ₁ σ₂ hinternal₂ hσ₂ τ hτ
  · -- In the reducible branch, reduce immediately to the common zero multiplicity.
    exact
      card_isomorphic_irreducible_summands_eq_of_two_decompositions_of_not_isIrreducible
        ρ σ₁ hσ₁ σ₂ hσ₂ τ hτ

end

end

end Representation

/-! ### Corollary_2_2_3_4 (from Chap02) -/
universe u v w u₁

namespace Representation

noncomputable section

section

open scoped Representation

variable {G : Type u} [Group G] [Finite G]
variable {K : Type u₁} [Field K] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

local instance instNeZeroNatCardField : NeZero (Nat.card G : K) :=
  ⟨Invertible.ne_zero (Nat.card G : K)⟩

/- Domain-style sampling for this item:
* primary domain: finite-dimensional character theory of semisimple representations of finite
  groups over an algebraically closed field;
* relevant owner declarations inspected before refining:
  `Representation.exists_isCompl_of_mem_invtSubmodule`,
  `Representation.exists_isInternal_irreducible_subrepresentations`,
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`,
  `Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap`;
* best owner abstraction: the public statement is about the canonical owners
  `Representation.character` and `Representation.Equiv`, while irreducible decompositions,
  complementary invariant subspaces, and multiplicity counts remain internal bridge data.

Primitive data vs derived API:
* primitive data are the representations `ρ`, `σ`, and the equality `ρ.character = σ.character`;
* the chosen irreducible summand, complementary invariant subspaces, and recursive splitting are
  derived proof data, so the file keeps them private and reuses the chapter multiplicity owner
  theorem instead of rebuilding a parallel projection-based positivity argument. -/

omit [Finite G] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
    [FiniteDimensional K V] in
/-- Helper for Corollary 2-2.3-4: a bundled subrepresentation defines an invariant submodule. -/
private theorem toSubmodule_mem_invtSubmodule
    (ρ : Representation K G V) (σ : Subrepresentation ρ) :
    σ.toSubmodule ∈ ρ.invtSubmodule := by
  simpa [Representation.mem_invtSubmodule,
    Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] using σ.apply_mem_toSubmodule

omit [Finite G] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
    [FiniteDimensional K V] in
/-- Helper for Corollary 2-2.3-4: an invariant submodule is stable under the representation. -/
private theorem subrepresentationOfInvtSubmodule_apply_mem
    (ρ : Representation K G V) (W : ρ.invtSubmodule) :
    ∀ g v, v ∈ (W : Submodule K V) → ρ g v ∈ (W : Submodule K V) := by
  intro g v hv
  have hW : (↑W : Submodule K V) ∈ Module.End.invtSubmodule (ρ g) :=
    (ρ.mem_invtSubmodule.mp W.property) g
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hW
  exact hW v hv

/-- Helper for Corollary 2-2.3-4: repackage an invariant submodule as a subrepresentation. -/
private def subrepresentationOfInvtSubmodule
    (ρ : Representation K G V) (W : ρ.invtSubmodule) :
    Subrepresentation ρ where
  toSubmodule := W
  apply_mem_toSubmodule := subrepresentationOfInvtSubmodule_apply_mem ρ W

omit [Finite G] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-4: products of equivariant isomorphisms remain equivariant. -/
private theorem prodCongr_isIntertwining
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W₁ : Type*} [AddCommGroup W₁] [Module K W₁]
    {W₂ : Type*} [AddCommGroup W₂] [Module K W₂]
    {ρ₁ : Representation K G V₁} {ρ₂ : Representation K G V₂}
    {σ₁ : Representation K G W₁} {σ₂ : Representation K G W₂}
    (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂) :
    ∀ g,
      (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) ∘ₗ (ρ₁.prod ρ₂) g =
        (σ₁.prod σ₂) g ∘ₗ (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) := by
  intro g
  ext x <;> simp [Representation.prod, e₁.isIntertwining, e₂.isIntertwining]

/-- Helper for Corollary 2-2.3-4: product decompositions transport equivariant isomorphisms. -/
private def prodCongr
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W₁ : Type*} [AddCommGroup W₁] [Module K W₁]
    {W₂ : Type*} [AddCommGroup W₂] [Module K W₂]
    {ρ₁ : Representation K G V₁} {ρ₂ : Representation K G V₂}
    {σ₁ : Representation K G W₁} {σ₂ : Representation K G W₂}
    (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂) :
    (ρ₁.prod ρ₂).Equiv (σ₁.prod σ₂) :=
  .mk (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) (prodCongr_isIntertwining e₁ e₂)

omit [Finite G] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
    [FiniteDimensional K V] in
/-- Helper for Corollary 2-2.3-4: the direct-sum equivalence from complementary
subrepresentations is equivariant. -/
private theorem prodEquivOfIsCompl_isIntertwining
    (ρ : Representation K G V) (σ τ : Subrepresentation ρ)
    (hστ : IsCompl σ.toSubmodule τ.toSubmodule) :
    ∀ g,
      (σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ) ∘ₗ
          (σ.toRepresentation.prod τ.toRepresentation) g =
        (ρ g) ∘ₗ (σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ) := by
  intro g
  ext z
  · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inl,
      LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype, Representation.prod]
      using (show ↑((σ.toRepresentation g) z) = (ρ g) ↑z from rfl)
  · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inr,
      LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype, Representation.prod]
      using (show ↑((τ.toRepresentation g) z) = (ρ g) ↑z from rfl)

/-- Helper for Corollary 2-2.3-4: complementary invariant summands split the representation as a
product. -/
private def prodEquivOfIsCompl
    (ρ : Representation K G V) (σ τ : Subrepresentation ρ)
    (hστ : IsCompl σ.toSubmodule τ.toSubmodule) :
    (σ.toRepresentation.prod τ.toRepresentation).Equiv ρ :=
  .mk (σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ)
    (prodEquivOfIsCompl_isIntertwining ρ σ τ hστ)

omit [Finite G] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
    [FiniteDimensional K V] in
/-- Helper for Corollary 2-2.3-4: irreducible representations are nontrivial. -/
private theorem nontrivial_of_isIrreducible
    (ρ : Representation K G V) [ρ.IsIrreducible] : Nontrivial V := by
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- If two finite-dimensional representations in the semisimple algebraically closed setting have
the same character, then they are equivariantly isomorphic. The companion iff theorem below is the
source-facing Corollary `2-2.3-4`. -/
theorem nonempty_equiv_of_character_eq
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (hchar : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  classical
  -- Split first by whether the source representation is nontrivial.
  by_cases hV : Nontrivial V
  · letI : Nontrivial V := hV
    -- Evaluate the common character at `1` to synchronize dimensions.
    have hdim' : (Module.finrank K V : K) = Module.finrank K W := by
      simpa [Representation.char_one] using congrFun hchar 1
    have hdim : Module.finrank K V = Module.finrank K W :=
      Nat.cast_injective hdim'
    have hW : Nontrivial W := by
      exact Module.nontrivial_of_finrank_pos (hdim ▸ Module.finrank_pos)
    letI : Nontrivial W := hW
    -- Choose an irreducible summand of `ρ`; equality of characters will force the same summand
    -- to appear inside `σ`.
    obtain ⟨ιρ, _, πρ, hπρ_indep, hπρ_top, hπρ_irr⟩ :
        ∃ (ι : Type v) (_ : Fintype ι) (π : ι → Subrepresentation ρ),
          iSupIndep (fun i ↦ (π i).toSubmodule) ∧
            (⨆ i, (π i).toSubmodule) = ⊤ ∧
            ∀ i, (π i).toRepresentation.IsIrreducible := by
      exact exists_isInternal_irreducible_subrepresentations ρ
    have hπρ_internal : DirectSum.IsInternal (fun i ↦ (πρ i).toSubmodule) :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hπρ_indep hπρ_top
    have hιρ : Nonempty ιρ := by
      by_cases hιρ : IsEmpty ιρ
      · letI := hιρ
        exact False.elim <|
          (show (⊥ : Submodule K V) ≠ ⊤ from bot_ne_top) <|
            by simp [iSup_of_empty] at hπρ_top
      · exact not_isEmpty_iff.mp hιρ
    let iρ := Classical.choice hιρ
    let σ₁ : Subrepresentation ρ := πρ iρ
    have hσ₁_irr : σ₁.toRepresentation.IsIrreducible := hπρ_irr iρ
    letI : σ₁.toRepresentation.IsIrreducible := hσ₁_irr
    have hσ₁_count :
        Nat.card { i // Nonempty ((πρ i).toRepresentation.Equiv σ₁.toRepresentation) } =
          Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) := by
      simpa [σ₁] using
        card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
          ρ πρ hπρ_internal hπρ_irr σ₁.toRepresentation hσ₁_irr
    have hσ₁_count_pos :
        0 < Nat.card { i // Nonempty ((πρ i).toRepresentation.Equiv σ₁.toRepresentation) } := by
      letI :
          Fintype { i // Nonempty ((πρ i).toRepresentation.Equiv σ₁.toRepresentation) } :=
        Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨⟨iρ, ⟨Representation.Equiv.refl _⟩⟩⟩
    have hρ_intertwining_pos :
        0 < Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) := by
      rw [← hσ₁_count]
      exact hσ₁_count_pos
    haveI : Nontrivial σ₁.toSubmodule := nontrivial_of_isIrreducible σ₁.toRepresentation
    have hσ₁_pos : 0 < Module.finrank K σ₁.toSubmodule := Module.finrank_pos
    -- Split off a complementary invariant summand from `ρ`.
    obtain ⟨V₀, hV₀⟩ :=
      exists_isCompl_of_mem_invtSubmodule ρ σ₁.toSubmodule
        (toSubmodule_mem_invtSubmodule ρ σ₁)
    let ρ₀ : Subrepresentation ρ := subrepresentationOfInvtSubmodule ρ V₀
    have hρ₀ : IsCompl σ₁.toSubmodule ρ₀.toSubmodule := by
      simpa [ρ₀, subrepresentationOfInvtSubmodule] using hV₀
    let eρ : (σ₁.toRepresentation.prod ρ₀.toRepresentation).Equiv ρ :=
      prodEquivOfIsCompl ρ σ₁ ρ₀ hρ₀
    have hσ_intertwining' :
        (Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) : K) =
          Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) := by
      calc
        (Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) : K) =
            ⟪σ.character, σ₁.toRepresentation.character⟫ := by
              symm
              simpa using
                (groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                  K σ σ₁.toRepresentation)
        _ = ⟪ρ.character, σ₁.toRepresentation.character⟫ := by
              simp [hchar]
        _ = Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) := by
              simpa using
                (groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                  K ρ σ₁.toRepresentation)
    have hσ_intertwining :
        Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) =
          Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) :=
      Nat.cast_injective hσ_intertwining'
    have hσ_intertwining_pos :
        0 < Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) := by
      rw [hσ_intertwining]
      exact hρ_intertwining_pos
    -- The same irreducible summand appears in `σ` with positive multiplicity.
    obtain ⟨ι, _, τ, hτ_indep, hτ_top, hτ_irr⟩ :
        ∃ (ι : Type w) (_ : Fintype ι) (τ : ι → Subrepresentation σ),
          iSupIndep (fun i ↦ (τ i).toSubmodule) ∧
            (⨆ i, (τ i).toSubmodule) = ⊤ ∧
            ∀ i, (τ i).toRepresentation.IsIrreducible := by
      exact exists_isInternal_irreducible_subrepresentations σ
    let hτ_internal : DirectSum.IsInternal (fun i ↦ (τ i).toSubmodule) :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hτ_indep hτ_top
    have hcount :
        Nat.card { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } =
          Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) := by
      simpa using
        card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
          σ τ hτ_internal hτ_irr σ₁.toRepresentation hσ₁_irr
    have hcount_pos :
        0 < Nat.card { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } := by
      rw [hcount]
      exact hσ_intertwining_pos
    letI : Fintype { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } :=
      Fintype.ofFinite _
    have hnonempty :
        Nonempty { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } := by
      rw [Nat.card_eq_fintype_card] at hcount_pos
      exact Fintype.card_pos_iff.mp hcount_pos
    let i₀ : { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } :=
      Classical.choice hnonempty
    let σ₂ : Subrepresentation σ := τ i₀.1
    have hσ₂ : Nonempty (σ₂.toRepresentation.Equiv σ₁.toRepresentation) := i₀.2
    letI : σ₂.toRepresentation.IsIrreducible := hτ_irr i₀.1
    obtain ⟨W₀, hW₀⟩ :=
      exists_isCompl_of_mem_invtSubmodule σ σ₂.toSubmodule
        (toSubmodule_mem_invtSubmodule σ σ₂)
    let σ₀ : Subrepresentation σ := subrepresentationOfInvtSubmodule σ W₀
    have hσ₀ : IsCompl σ₂.toSubmodule σ₀.toSubmodule := by
      simpa [σ₀, subrepresentationOfInvtSubmodule] using hW₀
    let eσ : (σ₂.toRepresentation.prod σ₀.toRepresentation).Equiv σ :=
      prodEquivOfIsCompl σ σ₂ σ₀ hσ₀
    rcases hσ₂ with ⟨e₁₂⟩
    -- After cancelling the common irreducible character, recurse on the complements.
    have hcomp_char : ρ₀.toRepresentation.character = σ₀.toRepresentation.character := by
      have hsum :
          σ₁.toRepresentation.character + ρ₀.toRepresentation.character =
            σ₂.toRepresentation.character + σ₀.toRepresentation.character := by
        calc
          σ₁.toRepresentation.character + ρ₀.toRepresentation.character =
              (σ₁.toRepresentation.prod ρ₀.toRepresentation).character := by
                symm
                exact Representation.char_prod σ₁.toRepresentation ρ₀.toRepresentation
          _ = ρ.character := Representation.char_iso eρ
          _ = σ.character := hchar
          _ = (σ₂.toRepresentation.prod σ₀.toRepresentation).character := by
                exact (Representation.char_iso eσ).symm
          _ = σ₂.toRepresentation.character + σ₀.toRepresentation.character := by
                exact Representation.char_prod σ₂.toRepresentation σ₀.toRepresentation
      ext g
      have hg := congrFun hsum g
      have hfirst : σ₂.toRepresentation.character g = σ₁.toRepresentation.character g :=
        congrFun (Representation.char_iso e₁₂) g
      have hg' :
          σ₁.toRepresentation.character g + ρ₀.toRepresentation.character g =
            σ₁.toRepresentation.character g + σ₀.toRepresentation.character g := by
        simpa [hfirst] using hg
      exact add_left_cancel hg'
    have hρ₀_lt : Module.finrank K ρ₀.toSubmodule < Module.finrank K V := by
      have hsplit :
          Module.finrank K V =
            Module.finrank K σ₁.toSubmodule + Module.finrank K ρ₀.toSubmodule := by
        calc
          Module.finrank K V =
              Module.finrank K (σ₁.toSubmodule × ρ₀.toSubmodule) := by
                symm
                exact eρ.toLinearEquiv.finrank_eq
          _ = Module.finrank K σ₁.toSubmodule + Module.finrank K ρ₀.toSubmodule := by
                simp
      rw [hsplit]
      exact Nat.lt_add_of_pos_left hσ₁_pos
    have hrest : Nonempty (ρ₀.toRepresentation.Equiv σ₀.toRepresentation) :=
      nonempty_equiv_of_character_eq ρ₀.toRepresentation σ₀.toRepresentation hcomp_char
    rcases hrest with ⟨e₀⟩
    exact ⟨eρ.symm.trans ((prodCongr e₁₂.symm e₀).trans eσ)⟩
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    -- In the zero-dimensional branch, both representations are forced to be trivial.
    have hV0 : Module.finrank K V = 0 := Module.finrank_zero_iff.mpr inferInstance
    have hW0' : (Module.finrank K W : K) = (0 : K) := by
      simpa [hV0, Representation.char_one] using (congrFun hchar 1).symm
    have hW0 : Module.finrank K W = 0 := by
      exact_mod_cast hW0'
    haveI : Subsingleton W := Module.finrank_zero_iff.mp hW0
    refine ⟨Representation.Equiv.mk (LinearEquiv.ofSubsingleton V W) ?_⟩
    intro g
    ext x
    exact Subsingleton.elim _ _
termination_by Module.finrank K V
decreasing_by
  simpa using hρ₀_lt

/-- Corollary 2-2.3-4: two finite-dimensional representations of a finite group over an
algebraically closed field of characteristic zero in which `|G|` is invertible have the same
character if and only if they are isomorphic. The source-text complex statement is the
specialization `K = ℂ`. -/
theorem character_eq_iff_nonempty_equiv
    (ρ : Representation K G V) (σ : Representation K G W) :
    ρ.character = σ.character ↔ Nonempty (ρ.Equiv σ) := by
  constructor
  · exact nonempty_equiv_of_character_eq ρ σ
  · rintro ⟨e⟩
    exact Representation.char_iso e

end

end

end Representation

/-! ### Exercise_2_2_3_6 (from Chap02) -/
noncomputable section

open scoped BigOperators Representation

universe u v u₁

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {ι : Type u₁} [Finite ι]

local instance : Fintype G := Fintype.ofFinite G
local instance : DecidableEq ι := Classical.decEq ι

-- Proof sketch: specialize `card_isomorphic_irreducible_summands_eq_character_pairing` to the
-- trivial representation `trivial ℂ G ℂ`. Its character is the constant function `1`, so the
-- character pairing reduces to the average `(Nat.card G : ℂ)⁻¹ * ∑ s : G, ρ.character s`.
/-- Exercise 2-2.3-6: if a finite-dimensional complex representation `ρ` is a direct sum of
irreducible subrepresentations `σ i`, then the number of summands isomorphic to the unit
representation is the normalized average of the character `ρ.character`, equivalently the pairing
`(χ|1)`. -/
theorem card_trivial_irreducible_summands_eq_character_average
    (ρ : Representation ℂ G V) (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible) :
    (Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv (trivial ℂ G ℂ)) } : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ s : G, ρ.character s := by
  -- The trivial representation is irreducible because its carrier has complex dimension one.
  haveI : (trivial ℂ G ℂ).IsIrreducible := by
    simpa using
      isIrreducible_of_finrank_eq_one (trivial ℂ G ℂ)
        (by simp : Module.finrank ℂ ℂ = 1)
  -- The averaging formulas use the standard inverse of `|G|` in characteristic zero.
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  calc
    -- First identify the multiplicity of the trivial summand with the character pairing `(χ|1)`.
    (Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv (trivial ℂ G ℂ)) } : ℂ) =
        ⟪ρ.character, (trivial ℂ G ℂ).character⟫ := by
          simpa using
            card_isomorphic_irreducible_summands_cast_eq_character_pairing
              ρ σ hinternal hσ (trivial ℂ G ℂ)
    -- Then expand the pairing against the trivial character, which is constantly equal to `1`.
    _ = (Nat.card G : ℂ)⁻¹ * ∑ s : G, ρ.character s := by
          rw [groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
          simp [Representation.character, Representation.trivial]

end

end Representation
