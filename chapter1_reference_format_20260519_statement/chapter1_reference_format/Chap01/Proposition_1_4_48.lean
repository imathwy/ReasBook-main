import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open List
open scoped Algebra IntermediateField

universe u v

section Subalgebra

variable {F : Type u} {K : Type v} [Field F] [Ring K] [Algebra F K]

-- Domain sample: field-theoretic algebraicity and simple adjunction.
-- Core/canonical owner: `IsAlgebraic F α`.
-- Source-facing layer here: the simple `F`-subalgebra `F[α]`.
-- Derived API sampled upstream: `IntermediateField.adjoin.finiteDimensional`,
-- `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`, and
-- `IsAlgebraic.of_finite`.
--
-- Primitive data: the element `α`.
-- Derived API: algebraicity of `α` and finite-dimensionality of the generated subalgebra.
--
-- Proof sketch: in the field specialization below, algebraicity of `α` makes the generated simple
-- extension finite-dimensional, hence also its underlying subalgebra `F[α]`. Conversely, a
-- finite-dimensional `F`-subalgebra is algebraic over `F`, so its generator `α` is algebraic by
-- `IsAlgebraic.of_finite`.
/-- The element `α` is algebraic over `F` exactly when the simple `F`-subalgebra `F[α]` is
finite-dimensional as an `F`-vector space. -/
theorem isAlgebraic_iff_finiteDimensional_adjoin (α : K) :
    IsAlgebraic F α ↔ FiniteDimensional F ↥(F[α]) := by
  constructor
  · intro hα
    -- Algebraicity makes the simple adjunction finite as an `F`-module.
    letI : Module.Finite F ↥(F[α]) :=
      Algebra.finite_adjoin_simple_of_isIntegral hα.isIntegral
    -- Over a field, finite generation upgrades to finite dimensionality.
    infer_instance
  · intro hfd
    let x : F[α] := ⟨α, Algebra.subset_adjoin (Set.mem_singleton α)⟩
    letI : FiniteDimensional F ↥(F[α]) := hfd
    -- The generator is algebraic inside the finite-dimensional simple subalgebra.
    have hx : IsAlgebraic F x := IsAlgebraic.of_finite F x
    -- Algebraicity of the subtype element is equivalent to algebraicity of its value in `K`.
    exact (Subalgebra.isAlgebraic_iff_isAlgebraic_val).mp hx

end Subalgebra

section IntermediateField

variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]

/-- Helper for Proposition 1.4.48: if `α⁻¹` already lies in the simple subalgebra `F[α]`, then
`α` satisfies a nontrivial polynomial relation over `F`. -/
lemma isAlgebraic_of_inv_mem_adjoin {α : K} (hα : α ≠ 0) (h_inv : α⁻¹ ∈ F[α]) :
    IsAlgebraic F α := by
  let y : F[α] := ⟨α⁻¹, h_inv⟩
  obtain ⟨p, hp_sub⟩ := Algebra.adjoin_eq_exists_aeval (R := F) (x := α) y
  have hp : Polynomial.aeval α p = α⁻¹ := by
    -- Every element of `F[α]` is a polynomial in `α`; here we apply this to `α⁻¹`.
    simpa [y] using hp_sub
  have hq_eval : Polynomial.aeval α ((1 : Polynomial F) - Polynomial.X * p) = 0 := by
    -- Multiplying the relation `p(α) = α⁻¹` by `α` gives a polynomial vanishing at `α`.
    rw [map_sub, map_one, Polynomial.aeval_mul, Polynomial.aeval_X, hp]
    simp [hα]
  have hq_ne : ((1 : Polynomial F) - Polynomial.X * p) ≠ 0 := by
    -- The constant coefficient is `1`, so this witness polynomial is nonzero.
    intro hq
    have hcoeff := congrArg (fun q : Polynomial F => q.coeff 0) hq
    simp at hcoeff
  -- A nonzero polynomial in the kernel of `aeval α` shows that `α` is algebraic.
  refine isAlgebraic_iff_not_injective.mpr ?_
  intro h_inj
  have hq_zero : (1 : Polynomial F) - Polynomial.X * p = 0 := by
    apply h_inj
    simpa using hq_eval
  exact hq_ne hq_zero

-- Proof sketch: the forward implication is
-- `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`. For the converse, if the
-- underlying subalgebra of `F⟮α⟯` already equals `F[α]`, then `F[α]` is closed under inverses, so
-- `α⁻¹ ∈ F[α]`; rewriting this membership via `IntermediateField.mem_adjoin_simple_iff` yields a
-- nontrivial polynomial relation over `F`.
/-- The element `α` is algebraic over `F` exactly when adjoining `α` as a field or as a
subalgebra produces the same `F`-subalgebra of `K`. -/
theorem isAlgebraic_iff_intermediateField_adjoin_toSubalgebra_eq_adjoin (α : K) :
    IsAlgebraic F α ↔ F⟮α⟯.toSubalgebra = F[α] := by
  constructor
  · intro hα
    -- Algebraic simple field adjunctions are already closed inside the simple subalgebra.
    exact IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hα
  · intro hEq
    by_cases hα : α = 0
    · -- The zero element is obviously algebraic.
      simpa [hα] using (isAlgebraic_algebraMap (R := F) (A := K) 0)
    · have h_inv_if : α⁻¹ ∈ F⟮α⟯.toSubalgebra := by
        -- The simple intermediate field is closed under inversion.
        change α⁻¹ ∈ F⟮α⟯
        exact (F⟮α⟯).inv_mem (IntermediateField.mem_adjoin_simple_self (F := F) α)
      have h_inv : α⁻¹ ∈ F[α] := by
        -- The assumed equality transports inverse-closure to the simple subalgebra.
        simpa [hEq] using h_inv_if
      exact isAlgebraic_of_inv_mem_adjoin hα h_inv

-- Proof sketch: combine the two preceding equivalences. The implication
-- `(1) → (2)` uses `IntermediateField.adjoin.finiteDimensional`, `(2) → (1)` uses
-- `IsAlgebraic.of_finite`, `(1) → (3)` uses
-- `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`, and `(3) → (1)` follows from
-- the fact that if `F[α]` is already a field, then `α⁻¹ ∈ F[α]` gives a polynomial relation for
-- `α`.
/-- Proposition 1.4.48: for `α` in a field extension `K / F`, the following are equivalent:
`α` is algebraic over `F`, the `F`-subalgebra `F[α]` is finite-dimensional as an `F`-vector space,
and the field generated by `α` has underlying subalgebra `F[α]`. -/
theorem tfae_isAlgebraic_finiteDimensional_adjoin_eq_intermediateField_adjoin_toSubalgebra
    (α : K) :
    List.TFAE
      [ IsAlgebraic F α,
        FiniteDimensional F ↥(F[α]),
        F⟮α⟯.toSubalgebra = F[α] ] := by
  -- The three-way equivalence is the combination of the two canonical simple-adjunction bridges.
  tfae_have 1 ↔ 2 := isAlgebraic_iff_finiteDimensional_adjoin (F := F) α
  tfae_have 1 ↔ 3 :=
    isAlgebraic_iff_intermediateField_adjoin_toSubalgebra_eq_adjoin (F := F) α
  tfae_finish

end IntermediateField
