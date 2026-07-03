import Mathlib
import StacksProject_2024.Chap10.Lemma_10_52_11
import StacksProject_2024.Chap15.Lemma_15_121_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IsLocalRing Module.End

universe u v w

section

/-
Domain triage:
- primary domain: finite-length determinants of scalar-multiplication endomorphisms after
  restricting scalars along a local homomorphism;
- sampled owner API:
  `Module.End.finiteLengthDeterminant`,
  `Module.End.finiteLengthDeterminant_eq_mul_of_shortExact`,
  `isFiniteLength_iff_exists_compositionSeries`,
  `CompositionSeries.factor_isSimpleModule`,
  `Module.length_compositionSeries`;
- core/canonical owner: `Module.End.finiteLengthDeterminant` on the restricted-scalar endomorphism
  `Algebra.lsmul R R' R M' u`;
- source-facing layer: Lemma `15.121.2`, expressing that determinant by the residue-field norm
  formula;
- bridge/view layer: an `R'`-composition series is an internal proof device for the
  restricted-scalar finite-length hypothesis and the factorwise reduction, but it is not part of
  the public determinant statement;
- primitive data: the local map `R → R'`, the scalar `u : R'`, and the finite-length owner
  hypothesis `IsFiniteLength R' M'`;
- derived API: restricted-scalar finite length, an internally chosen composition series, and the
  simple-factor norm computation.
-/

variable {R : Type u} {R' : Type v} {M' : Type w}
variable [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
variable [Algebra R R'] [IsLocalHom (algebraMap R R')]
variable [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']

local notation "κ" => IsLocalRing.ResidueField R
local notation "κ'" => IsLocalRing.ResidueField R'

/-- A simple `R'`-module has finite length after restricting scalars along a local homomorphism
with finite residue-field extension. -/
private theorem isFiniteLength_restrictScalars_of_simple [Module.Finite κ κ']
    (N : Type*) [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N]
    [IsSimpleModule R' N] :
    IsFiniteLength R N := by
  sorry

/-- An `R'`-composition series from `⊥` to `⊤` yields finite length for the underlying
`R`-module. -/
private theorem isFiniteLength_restrictScalars_of_compositionSeries
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤) :
    IsFiniteLength R M' := by
  sorry

/-- A finite-length `R'`-module has finite length after restricting scalars along a local
homomorphism with finite residue-field extension. -/
private theorem isFiniteLength_restrictScalars [Module.Finite κ κ']
    (hM' : IsFiniteLength R' M') :
    IsFiniteLength R M' := by
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM'
  exact isFiniteLength_restrictScalars_of_compositionSeries s h₀ h₁

/-- Each simple `R'`-factor in a composition series has finite length over the restricted scalar
ring `R`. -/
private theorem factor_isFiniteLength_restrictScalars [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) :
    IsFiniteLength R (s.factor i) := by
  have hsimple : IsSimpleModule R' (s.factor i) := s.factor_isSimpleModule i
  exact @isFiniteLength_restrictScalars_of_simple R R' _ _ _ _ _ _ _ (s.factor i) _ _ _ _ hsimple

/-- On a simple `R'`-composition factor, the canonical finite-length determinant of multiplication
by `u` over `R` is the norm of `u mod maximalIdeal R'`. -/
private theorem factor_finiteLengthDeterminant_eq_norm_residue
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) (u : R') :
    (Algebra.lsmul R R (s.factor i) u).finiteLengthDeterminant
        (factor_isFiniteLength_restrictScalars s i) =
      Algebra.norm κ (IsLocalRing.residue R' u) := by
  sorry

-- Proof sketch: derive an internal composition series of the finite-length `R'`-module `M'` from
-- `isFiniteLength_iff_exists_compositionSeries`, use it to build the restricted-scalar
-- finite-length hypothesis on `M'`, and then apply multiplicativity of
-- `Module.End.finiteLengthDeterminant` along the successive short exact sequences. Each simple
-- factor contributes the same norm term by `factor_finiteLengthDeterminant_eq_norm_residue`, and
-- `Module.length_compositionSeries` identifies the number of factors with `length_{R'}(M')`.
/-- Lemma 15.121.2: for a local homomorphism `(R, 𝔪, κ) → (R', 𝔪', κ')` with finite residue-field
extension and a finite-length `R'`-module `M'`, the canonical finite-length determinant over `κ`
of multiplication by `u` on the restricted-scalar `R`-module underlying `M'` is
`Norm_{κ'/κ}(u mod 𝔪') ^ length_{R'}(M')`. -/
theorem finiteLengthDeterminant_algebraLsmul_eq_norm_pow_length
    [Module.Finite κ κ']
    (u : R') (hM' : IsFiniteLength R' M') :
    (Algebra.lsmul R R M' u).finiteLengthDeterminant
        (isFiniteLength_restrictScalars hM') =
      Algebra.norm κ (IsLocalRing.residue R' u) ^ (Module.length R' M').toNat := by
  sorry

end
