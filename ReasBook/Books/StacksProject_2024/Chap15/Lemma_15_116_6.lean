import Mathlib
import StacksProject_2024.Chap15.Lemma_15_111_2

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal
open IsLocalRing
open scoped Pointwise TensorProduct

universe u v w

noncomputable section

section B1Action

variable {B : Type v} {K : Type u} {L : Type v} {K1 : Type w}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Field K] [Algebra B K] [IsFractionRing B K]
variable [Field L] [Algebra B L] [Algebra K L] [IsScalarTower B K L]
variable [Field K1] [Algebra K K1]

local notation "G" => Gal(K1 / K)
local notation "L10" => TensorProduct K L K1
local notation "L1" => L10 ⧸ nilradical L10
local notation "B1" => integralClosure B L1

local instance l1CommRing : CommRing L1 :=
  Ideal.Quotient.commRing _

local instance b1CommRing : CommRing B1 :=
  inferInstance

local instance b1Algebra : Algebra B B1 :=
  inferInstance

/- Domain-style sampling for Lemma 15.116.6:
- primary domain: Galois actions on the reduced tensor-product base change and the induced action
  on the corresponding integral closure over a discrete valuation ring
- sampled owner declarations:
  `MulSemiringAction.compHom`,
  `quotientMulSemiringAction`,
  `AlgEquiv.mapIntegralClosure`,
  `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `exists_gal_smul_eq_of_isMaximal`
- best owner abstraction: the source-facing owner layer is the canonical `Gal(K1 / K)`-action on
  `L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)` together with the induced action on
  `B1 = integralClosure B L1` and its invariant-extension transitivity specialization
  `exists_gal_smul_eq_of_under_eq_of_reducedTensorBaseChange`; the maximal-ideal conjugacy
  statement should then be a thin specialization of that public owner layer
- primitive data: the reduced tensor product `L1 = (L ⊗[K] K1)_red`, the integral closure
  `B1 = integralClosure B L1`, and maximal ideals `m, m' : Ideal B1`
- derived API: the descended quotient action on `L1`, the induced action on `B1`, the invariant
  owner `Algebra.IsInvariant B B1 Gal(K1 / K)`, the under-equality transitivity theorem, and the
  maximal-ideal transitivity statement

Source/core/bridge triage:
- `source-facing`: transitivity of the `Gal(K1 / K)`-action on maximal ideals of `B1`
- `core/canonical`: `MulSemiringAction Gal(K1 / K) L1`,
  `MulSemiringAction Gal(K1 / K) B1`, and
  `Algebra.IsInvariant.exists_smul_of_under_eq`
- `bridge/view`: the tensor-product automorphisms of `L ⊗[K] K1`, their quotient descendant on
  `L1`, the induced integral-closure action on `B1`, and the source-facing under-equality
  specialization
-/

/-- The `K`-algebra automorphism of `L ⊗[K] K1` induced by a `K`-automorphism of `K1`. -/
private noncomputable def reducedBaseChangeAutAux (σ : Gal(K1/K)) :
    L10 ≃ₐ[K] L10 :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) σ

/-- The `B`-algebra automorphism of `L ⊗[K] K1` induced by a `K`-automorphism of `K1`. -/
private noncomputable def reducedBaseChangeAlgEquiv (σ : G) :
    L10 ≃ₐ[B] L10 where
  toRingEquiv := (reducedBaseChangeAutAux σ).toRingEquiv
  commutes' b := by
    change
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) σ)
          (algebraMap B L b ⊗ₜ[K] (1 : K1)) =
        algebraMap B L b ⊗ₜ[K] (1 : K1)
    simp

/-- The canonical `Gal(K1 / K)`-action on `L ⊗[K] K1`, acting through the `K1`-factor. -/
private noncomputable abbrev reducedBaseChangeMulSemiringAction :
    MulSemiringAction G L10 :=
  { smul := fun σ x ↦ reducedBaseChangeAutAux σ x
    one_smul := by
      sorry
    mul_smul := by
      sorry
    smul_zero := by
      sorry
    smul_add := by
      sorry
    smul_one := by
      sorry
    smul_mul := by
      sorry }

-- Proof sketch: ring automorphisms preserve nilpotent elements, so the nilradical is stable under
-- the induced action.
/-- The induced `Gal(K1 / K)`-action on `L ⊗[K] K1` preserves the nilradical. -/
private theorem reducedBaseChangeAutAux_map_nilradical (σ : G) :
    Ideal.map (reducedBaseChangeAutAux σ).toRingHom
        (nilradical L10) =
      nilradical L10 := sorry

/-- The canonical `Gal(K1 / K)`-action on
`L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)`. -/
noncomputable abbrev reducedTensorBaseChangeMulSemiringAction :
    MulSemiringAction G L1 :=
  let _ : MulSemiringAction G L10 := reducedBaseChangeMulSemiringAction
  quotientMulSemiringAction (nilradical L10) fun σ ↦ by
    simpa [Ideal.pointwise_smul_def, reducedBaseChangeMulSemiringAction, reducedBaseChangeAutAux]
      using reducedBaseChangeAutAux_map_nilradical σ

/-- The induced `B`-algebra automorphism of
`L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)`. -/
private noncomputable def reducedBaseChangeAut (σ : G) :
    L1 ≃ₐ[B] L1 :=
  let h :
      nilradical L10 =
        Ideal.map
          (reducedBaseChangeAutAux σ).toRingHom
          (nilradical L10) :=
    (reducedBaseChangeAutAux_map_nilradical σ).symm
  Ideal.quotientEquivAlg (nilradical L10) (nilradical L10) (reducedBaseChangeAlgEquiv σ) h

/-- The canonical `Gal(K1 / K)`-action on `B1 = integralClosure B L1`. -/
noncomputable abbrev reducedTensorBaseChangeIntegralClosureMulSemiringAction :
    MulSemiringAction G B1 :=
  { smul := fun σ x ↦
      (reducedBaseChangeAut σ).mapIntegralClosure x
    one_smul := by
      sorry
    mul_smul := by
      sorry
    smul_zero := by
      sorry
    smul_add := by
      sorry
    smul_one := by
      sorry
    smul_mul := by
      sorry }

local instance : SMul G B1 :=
  reducedTensorBaseChangeIntegralClosureMulSemiringAction.toSMul

local instance : MulSemiringAction G B1 :=
  reducedTensorBaseChangeIntegralClosureMulSemiringAction

/-- The canonical `Gal(K1 / K)`-action on the reduced tensor-base-change integral closure `B1`
commutes with the scalar action of `B`. -/
theorem reducedTensorBaseChangeIntegralClosure_smulCommClass :
    SMulCommClass G B B1 := by
  sorry

/-- The reduced tensor-base-change integral closure `B1 = integralClosure B L1` is invariant under
the canonical `Gal(K1 / K)`-action. -/
theorem reducedTensorBaseChangeIntegralClosure_isInvariant :
    Algebra.IsInvariant B B1 G := by
  sorry

attribute [local instance] reducedTensorBaseChangeIntegralClosure_smulCommClass
attribute [local instance] reducedTensorBaseChangeIntegralClosure_isInvariant

variable [FiniteDimensional K K1] [Normal K K1]

/-- Any maximal ideal of `B1 = integralClosure B L1` lies over `maximalIdeal B`. -/
private instance liesOver_maximalIdeal_of_isMaximal
    (m : Ideal B1) [m.IsMaximal] : m.LiesOver (maximalIdeal B) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

/-- If two prime ideals of `B1 = integralClosure B L1` contract to the same ideal of `B`, then
they are Galois-conjugate under the canonical `Gal(K1 / K)`-action. -/
theorem exists_gal_smul_eq_of_under_eq_of_reducedTensorBaseChange
    (m m' : Ideal B1) [m.IsPrime] [m'.IsPrime]
    (hunder : m.under B = m'.under B) :
    ∃ σ : G, σ • m = m' := by
  sorry

-- Proof sketch: maximal ideals of `B1` all lie over `maximalIdeal B`, so the under-equality
-- transitivity theorem above applies directly to the invariant extension `B → B1`.
/-- Lemma 15.116.6: with
`L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)` and `B1 = integralClosure B L1`, the canonical
`Gal(K1 / K)`-action on `B1` is transitive on the maximal ideals of `B1`. -/
theorem exists_gal_smul_eq_of_isMaximal_of_reducedTensorBaseChange
    (m m' : Ideal B1) (hm : m.IsMaximal) (hm' : m'.IsMaximal) :
    ∃ σ : G, σ • m = m' := by
  letI : m.IsMaximal := hm
  letI : m'.IsMaximal := hm'
  exact exists_gal_smul_eq_of_under_eq_of_reducedTensorBaseChange m m'
    ((m.over_def (maximalIdeal B)).symm.trans (m'.over_def (maximalIdeal B)))

end B1Action
