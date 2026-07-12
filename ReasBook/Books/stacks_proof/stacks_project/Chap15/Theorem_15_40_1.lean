import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_158_4
import StacksProject_2024.Chap10.Lemma_10_156_5
import StacksProject_2024.Chap10.Definition_10_166_2
import StacksProject_2024.Chap15.Lemma_15_37_8
import StacksProject_2024.Chap15.Lemma_15_38_2
import StacksProject_2024.Chap15.Proposition_15_35_1

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open IsLocalRing
open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]

/-- Helper for Theorem 15.40.1: in characteristic `p > 0`, the geometric-regularity clause, the
finite purely inseparable tensor-base-change clause, and the two cotangent-theoretic injectivity
clauses form a `TFAE`. -/
lemma char_p_regularity_criteria_tfae
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) k A] :
    List.TFAE [
      IsGeometricallyRegular k A,
      ∀ (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
        [IsPurelyInseparable k K],
          IsRegularRing (K ⊗[k] A),
      IsRegularLocalRing A ∧
        Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)),
      IsRegularLocalRing A ∧
        Function.Injective
          (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
    ] := by
  have hsource :
      List.TFAE [
        IsGeometricallyRegular k A,
        ∀ (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K],
          K ≤ onePthRootExtension k p →
            IsRegularRing (K ⊗[k] A),
        IsRegularLocalRing A ∧
          Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)),
        IsRegularLocalRing A ∧
          Function.Injective
            (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
      ] :=
    geometricallyRegularLocalRing_tfae_of_charP (k := k) (A := A) (p := p)
  -- Route correction: instead of transporting the proposition's finite-intermediate-field clause
  -- directly, tie both second clauses back to geometric regularity and reuse the owner TFAE.
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hgeom
      -- Proof comment: this is the canonical bridge view of geometric regularity.
      exact
        (Algebra.isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing
          (k := k) (A := A)).mp hgeom
    · intro hbase
      -- Proof comment: the reverse implication is the converse direction of the same bridge.
      exact
        (Algebra.isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing
          (k := k) (A := A)).mpr hbase
  tfae_have 1 → 3 := by
    intro hgeom
    -- Proof comment: after fixing the second clause through geometric regularity, clause `(3)` is
    -- exactly the imported proposition's third clause.
    exact (hsource.out 0 2).mp hgeom
  tfae_have 3 → 4 := by
    intro hh1
    -- Proof comment: the cotangent-space injectivity implication is already packaged upstream.
    exact (hsource.out 2 3).mp hh1
  tfae_have 4 → 1 := by
    intro hdiff
    -- Proof comment: close the cycle by returning to geometric regularity through the owner TFAE.
    exact (hsource.out 3 0).mp hdiff
  tfae_finish

/-- Helper for Theorem 15.40.1: the source-proof `(2) → (3)` route starts by base-changing
maximal-ideal-adic formal smoothness from `k → A` to the structural map `K → K ⊗[k] A`. -/
lemma tensorBaseChange_formally_smooth_for_maximalIdeal_adic
    (hfs : (algebraMap k A).formally_smooth_for_adic (maximalIdeal A))
    (K : Type (max u v)) [Field K] [Algebra k K] :
    RingHom.formally_smooth_for_adic
      (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[k] A)
      (Ideal.map Algebra.TensorProduct.includeRight.toRingHom (maximalIdeal A)) := by
  -- Proof comment: this is exactly Lemma `15.37.8` specialized to the extension field `K/k`.
  simpa using
    RingHom.formally_smooth_for_adic_baseChange
      (R := k) (S := A) (R' := K) (𝔫 := maximalIdeal A) hfs

/-- Helper for Theorem 15.40.1: for a finite purely inseparable extension `K / k`, the tensor
product `A ⊗[k] K` is local. This isolates the locality input from Lemma `10.156.5` in the exact
orientation used by the source proof before commuting factors. -/
lemma tensorBaseChange_isLocalRing
    (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
    [IsPurelyInseparable k K] :
    IsLocalRing (A ⊗[k] K) := by
  -- Proof comment: apply the purely inseparable tensor-product locality criterion with base ring
  -- `k`, left factor `A`, and right factor `K`.
  let _ : IsLocalRing (A ⊗[k] K) :=
    tensorProduct_isLocalRing_of_local_of_integral_of_residueField_purelyInseparable
      (A := k) (B := A) (C := K) (Or.inl inferInstance)
  infer_instance

/-- Helper for Theorem 15.40.1: the commuted tensor product `K ⊗[k] A` is also local. This is the
preferred orientation for the base-changed formal-smoothness statement from Lemma `15.37.8`. -/
lemma tensorBaseChange_comm_isLocalRing
    (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
    [IsPurelyInseparable k K] :
    IsLocalRing (K ⊗[k] A) := by
  letI : IsLocalRing (A ⊗[k] K) := tensorBaseChange_isLocalRing (k := k) (A := A) K
  -- Proof comment: commute the tensor factors and transport the local-ring structure along the
  -- tensor-product symmetry equivalence.
  exact (Algebra.TensorProduct.comm k A K).toRingEquiv.isLocalRing

/-- Helper for Theorem 15.40.1: maximal-ideal-adic formal smoothness survives finite purely
inseparable field extension and forces the tensor base change to be a regular ring. -/
lemma isRegularRing_tensorBaseChange_of_formally_smooth_for_maximalIdeal_adic
    (hfs : (algebraMap k A).formally_smooth_for_adic (maximalIdeal A))
    (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
    [IsPurelyInseparable k K] :
    IsRegularRing (K ⊗[k] A) := by
  have hbase :
      RingHom.formally_smooth_for_adic
        (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[k] A)
        (Ideal.map Algebra.TensorProduct.includeRight.toRingHom (maximalIdeal A)) :=
    tensorBaseChange_formally_smooth_for_maximalIdeal_adic (k := k) (A := A) hfs K
  letI : IsLocalRing (K ⊗[k] A) := tensorBaseChange_comm_isLocalRing (k := k) (A := A) K
  -- Proof comment: the intended route is the source-proof base-change argument:
  -- transport formal smoothness to `K ⊗[k] A`, use the tensor-product local-ring criterion,
  -- enlarge the adic ideal to the maximal ideal, and then apply Lemma `15.38.2` over `K`.
  -- The base-changed formal-smoothness statement and the target local-ring structure have now
  -- both been isolated; the remaining gap is the maximal-ideal comparison needed to feed
  -- Lemma `15.38.2` in the commuted tensor orientation.
  -- TODO: finish the Noetherianity/locality transport on `K ⊗[k] A` and conclude via
  -- `isRegularLocalRing_of_formallySmooth_for_maximalIdeal_adic`.
  sorry

/-- Helper for Theorem 15.40.1: in characteristic `p > 0`, injectivity of the residue-field
comparison on Kähler differentials upgrades regularity to maximal-ideal-adic formal smoothness. -/
lemma formally_smooth_for_maximalIdeal_adic_of_residueFieldComparison_injective
    (p : ℕ) [Fact p.Prime] [CharP k p]
    [CharP A p] [Algebra (ZMod p) k] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) k A]
    (hdiff :
      IsRegularLocalRing A ∧
        Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A)) :
    (algebraMap k A).formally_smooth_for_adic (maximalIdeal A) := by
  letI : IsRegularLocalRing A := hdiff.1
  -- Route correction: the remaining source-faithful gap is exactly the derivation-correction
  -- lifting argument from the textbook proof of `(5) → (2)`.
  -- Proof comment: Lemma `15.38.5` gives the preliminary `ZMod p`-lift; the missing work is to
  -- compare the two maps `k → B` in a small extension, express their difference as a derivation,
  -- and extend that derivation across the injective residue-field comparison map.
  -- TODO: apply
  -- `RingHom.formally_smooth_for_maximalIdeal_adic_iff_local_smallExtension_residueFieldIso_lifting`,
  -- reduce to kernels annihilated by `maximalIdeal A`, extend the resulting `k`-derivation
  -- through `KaehlerDifferential.residueFieldComparison (ZMod p) k A`, and correct the lift.
  sorry

/-- Helper for Theorem 15.40.1: over a characteristic-zero field, a regular local `k`-algebra is
maximal-ideal-adically formally smooth. -/
lemma formally_smooth_for_maximalIdeal_adic_of_isRegularLocalRing_in_charZero
    [CharZero k] [IsRegularLocalRing A] :
    (algebraMap k A).formally_smooth_for_adic (maximalIdeal A) := by
  letI : PerfectField k := PerfectField.ofCharZero
  letI : Algebra.IsSeparableOver k (ResidueField A) := Algebra.IsSeparableOver.of_perfectField
  -- Proof comment: this is exactly the characteristic-zero specialization of the source lemma
  -- proved in Lemma `15.38.5`.
  -- TODO: use
  -- `formallySmooth_for_maximalIdeal_adic_of_isRegularLocalRing_of_isSeparableOver (k := k)
  --   (A := A)`
  -- once the compiled owner artifact `stacks_project/Chap15/Lemma_15_38_5.olean` is available in
  -- this workspace; currently the single-file check fails before elaboration when that module is
  -- imported.
  sorry

/- Domain-style sampling for Theorem 15.40.1:
- primary domain: local commutative algebra of Noetherian local `k`-algebras, relating adic
  formal smoothness, geometric regularity, and the cotangent-theoretic residue-field criteria;
- sampled owner declarations:
  `RingHom.formally_smooth_for_adic`,
  `IsGeometricallyRegular`,
  `H1Cotangent.map`,
  `KaehlerDifferential.residueFieldComparison`;
- best owner abstraction: this theorem remains `source-facing`, but its clauses should reuse the
  chapter owners above rather than introducing a parallel local regularity owner;
- primitive data: the field `k`, the Noetherian local `k`-algebra `A`, and the characteristic
  branch;
- derived API: the finite purely inseparable tensor-base-change clause is stated directly as the
  canonical bridge view of `IsGeometricallyRegular k A`, not through a second owner notion.

Source/core/bridge triage:
- `source-facing`: the characteristic-split theorem asserting the textbook equivalences;
- `core/canonical`: `RingHom.formally_smooth_for_adic`, `IsGeometricallyRegular`,
  `H1Cotangent.map`, and `KaehlerDifferential.residueFieldComparison`;
- `bridge/view`: the finite purely inseparable base-change criterion supplied by
  `isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing`.
-/

-- Proof sketch: in characteristic zero, combine Lemma `15.38.2` with Lemma `15.38.5`; the latter
-- applies because Proposition `10.158.9` makes every residue-field extension of a characteristic-zero
-- field separable in the Stacks Project sense. In characteristic `p > 0`, use Proposition
-- `15.35.1` for the equivalence among geometric regularity, the finite purely inseparable
-- base-change criterion, and the two cotangent-theoretic injectivity criteria; then combine
-- Lemmas `15.38.2`, `15.38.5`, and `15.37.8` to identify formal smoothness in the
-- `maximalIdeal A`-adic topology with the same list.
/-- Theorem 15.40.1: for a Noetherian local `k`-algebra `A`, if `k` has characteristic zero then
`A` is a regular local ring exactly when `k → A` is formally smooth for the `maximalIdeal A`-adic
topology. If `k` has characteristic `p > 0`, then the following project-facing clauses are
equivalent: `A` is geometrically regular over `k`; `k → A` is formally smooth for the
`maximalIdeal A`-adic topology; every finite purely inseparable field extension `k' / k` yields a
regular ring `k' ⊗[k] A`; `A` is regular local with injective canonical map
`H_1(L_{κ(A)/k}) → 𝔪_A / 𝔪_A^2`; and `A` is regular local with injective canonical map
`KaehlerDifferential.residueFieldComparison (ZMod p) k A`. -/
@[stacks 07EL]
theorem regularLocalRing_formallySmooth_for_maximalIdeal_adic_tfae_by_characteristic :
    (∀ [CharZero k],
      IsRegularLocalRing A ↔
        (algebraMap k A).formally_smooth_for_adic (maximalIdeal A)) ∧
      ∀ (p : ℕ) [Fact p.Prime] [CharP k p],
        by
          letI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
          letI : Algebra (ZMod p) k := ZMod.algebra k p
          letI : Algebra (ZMod p) A := ZMod.algebra A p
          letI : IsScalarTower (ZMod p) k A := by infer_instance
          exact
            List.TFAE [
              IsGeometricallyRegular k A,
              (algebraMap k A).formally_smooth_for_adic (maximalIdeal A),
              ∀ (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
                [IsPurelyInseparable k K],
                  IsRegularRing (K ⊗[k] A),
              IsRegularLocalRing A ∧
                Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)),
              IsRegularLocalRing A ∧
                Function.Injective
                  (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
            ] := by
  constructor
  · intro _
    constructor
    · intro hregular
      letI : IsRegularLocalRing A := hregular
      -- Proof comment: in characteristic zero, perfectness makes the residue-field extension
      -- separable, so Lemma `15.38.5` applies directly.
      exact formally_smooth_for_maximalIdeal_adic_of_isRegularLocalRing_in_charZero
    · intro hfs
      -- Proof comment: the reverse implication is exactly Lemma `15.38.2`.
      exact isRegularLocalRing_of_formallySmooth_for_maximalIdeal_adic hfs
  · intro p
    intro _ _
    letI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    letI : Algebra (ZMod p) A := ZMod.algebra A p
    letI : IsScalarTower (ZMod p) k A := by infer_instance
    have hcriteria :
        List.TFAE [
          IsGeometricallyRegular k A,
          ∀ (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
            [IsPurelyInseparable k K],
              IsRegularRing (K ⊗[k] A),
          IsRegularLocalRing A ∧
            Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)),
          IsRegularLocalRing A ∧
            Function.Injective
              (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
        ] :=
      char_p_regularity_criteria_tfae (k := k) (A := A) p
    -- Proof comment: follow the source-proof cycle
    -- `(1) → (5) → (2) → (3) → (4) → (1)`.
    tfae_have 1 → 5 := by
      intro hgeom
      exact (hcriteria.out 0 3).mp hgeom
    tfae_have 5 → 2 := by
      intro hdiff
      exact
        formally_smooth_for_maximalIdeal_adic_of_residueFieldComparison_injective
          (k := k) (A := A) (p := p) hdiff
    tfae_have 2 → 3 := by
      intro hfs K _ _ _ _
      exact
        isRegularRing_tensorBaseChange_of_formally_smooth_for_maximalIdeal_adic
          (k := k) (A := A) hfs K
    tfae_have 3 → 4 := by
      intro hbase
      exact (hcriteria.out 1 2).mp hbase
    tfae_have 4 → 1 := by
      intro hh1
      exact (hcriteria.out 2 0).mp hh1
    tfae_finish

end
