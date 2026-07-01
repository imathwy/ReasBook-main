import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Definition_10_166_2
import stacks_project.Chap15.Lemma_15_38_2
import stacks_project.Chap15.Lemma_15_38_5
import stacks_project.Chap15.Proposition_15_35_1

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]

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
            ] := sorry

end
