import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators nonZeroDivisors
open IsLocalRing

noncomputable section

universe u v

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section InjectiveAlgebraMapFact

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

local instance injectiveAlgebraMapFact_of_finiteFractionRingExtension :
    Fact (Function.Injective (algebraMap A B)) :=
  ⟨algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)⟩

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

/-- Under a finite-type extension of domains with finite fraction-field extension from a
Noetherian local domain of Krull dimension at most `1`, the target ring has finite maximal
spectrum. -/
theorem finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    Finite (MaximalSpectrum B) := by
  sorry

end

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [IsLocalRing A]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

/-- Every maximal ideal of `B` lies over the maximal ideal of the local base ring `A`. -/
theorem comap_maximalIdeal_of_finiteType_of_finiteFractionRingExtension
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (m : MaximalSpectrum B) :
    Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A := by
  sorry

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

instance residueFieldAlgebra_of_finiteType_of_finiteFractionRingExtension
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (m : MaximalSpectrum B) :
    Algebra κA (Ideal.ResidueField m.asIdeal) :=
  (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B)
    (comap_maximalIdeal_of_finiteType_of_finiteFractionRingExtension A m).symm).toAlgebra

/-- The residue-field extension at any maximal ideal of `B` is module-finite over the residue field
of the maximal ideal of `A`. -/
theorem moduleFinite_residueField_of_finiteType_of_finiteFractionRingExtension
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (m : MaximalSpectrum B) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) := by
  sorry

instance residueFieldModuleFinite_of_finiteType_of_finiteFractionRingExtension
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (m : MaximalSpectrum B) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) :=
  moduleFinite_residueField_of_finiteType_of_finiteFractionRingExtension A m

end

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

private theorem isScalarTower_fractionRing_localization_fractionRing [Module.Finite A B] :
    let K := FractionRing A
    let L := FractionRing B
    let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
    let S := Localization M
    let _ : FaithfulSMul A B :=
      (faithfulSMul_iff_algebraMap_injective A B).mpr
        (algebraMap_injective_of_field_isFractionRing A B K L)
    let hS : M ≤ B⁰ :=
      algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B
        (show nonZeroDivisors A ≤ A⁰ by rfl)
    let hS' : M ≤ Submonoid.comap (RingHom.id B) B⁰ := by
      simpa using hS
    let f : S →+* L := IsLocalization.map L (RingHom.id B) hS'
    let _ : Algebra S L := f.toAlgebra
    IsScalarTower K S L := by
  simp only
  let K := FractionRing A
  let L := FractionRing B
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr
      (algebraMap_injective_of_field_isFractionRing A B K L)
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  let S := Localization M
  have hS : M ≤ B⁰ :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B (show nonZeroDivisors A ≤ A⁰ by rfl)
  have hS' : M ≤ Submonoid.comap (RingHom.id B) B⁰ := by
    simpa using hS
  let f : S →+* L := IsLocalization.map L (RingHom.id B) hS'
  let _ : Algebra S L := f.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  apply IsLocalization.ringHom_ext (nonZeroDivisors A)
  ext a
  have h1 : (algebraMap K L) ((algebraMap A K) a) = algebraMap A L a :=
    (IsScalarTower.algebraMap_apply A K L a).symm
  have h2 : (((algebraMap S L).comp (algebraMap K S)).comp (algebraMap A K)) a =
      algebraMap A L a := by
    rw [RingHom.comp_apply, RingHom.comp_apply, (IsScalarTower.algebraMap_apply A K S a).symm]
    have hABS : algebraMap A S a = algebraMap B S (algebraMap A B a) :=
      IsScalarTower.algebraMap_apply A B S a
    rw [hABS]
    have hmap : f (algebraMap B S (algebraMap A B a)) = algebraMap B L (algebraMap A B a) := by
      simpa [f] using (IsLocalization.map_eq hS' (algebraMap A B a) : _)
    simpa [IsScalarTower.algebraMap_apply A B L] using hmap
  exact h1.trans h2.symm

private theorem finiteDimensional_fractionRing_of_moduleFinite [Module.Finite A B] :
    FiniteDimensional (FractionRing A) (FractionRing B) := by
  let K := FractionRing A
  let L := FractionRing B
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr
      (algebraMap_injective_of_field_isFractionRing A B K L)
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  let S := Localization M
  have hS : M ≤ B⁰ :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B (show nonZeroDivisors A ≤ A⁰ by rfl)
  have hS' : M ≤ Submonoid.comap (RingHom.id B) B⁰ := by
    simpa using hS
  let f : S →+* L := IsLocalization.map L (RingHom.id B) hS'
  let _ : Algebra S L := f.toAlgebra
  let _ : IsScalarTower B S L := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp hS', RingHomCompTriple.comp_eq])
  let _ : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hS
  let _ : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S L
  let _ : FiniteDimensional K S := inferInstance
  let _ : Field S := fieldOfFiniteDimensional K S
  let _ : IsScalarTower K S L := isScalarTower_fractionRing_localization_fractionRing A
  let _ : FiniteDimensional S L := by
    let _ : IsFractionRing S S := IsFractionRing.idem S S
    exact LinearEquiv.finiteDimensional
      (((FractionRing.algEquiv S S).symm.trans (FractionRing.algEquiv S L)).toLinearEquiv)
  exact FiniteDimensional.trans K S L

/-
Domain triage:
* primary domain: orders of vanishing for module-finite extensions of one-dimensional Noetherian
  local domains, expressed through the canonical valuation owner `Ring.ordFrac`;
* sampled owner API: `Ring.ordFrac`,
  `Ring.KrullDimLE.of_isLocalization`,
  `length_eq_sum_residueFieldDegree_mul_length_localizedModule`,
  `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`,
  `comap_maximalIdeal_of_finiteType_of_finiteFractionRingExtension`, and
  `moduleFinite_residueField_of_finiteType_of_finiteFractionRingExtension`;
* source-facing layer: the weighted sum formula over maximal localizations;
* core/canonical owners: `Ring.ordFrac` for the valuation and `Module.finrank` for the
  residue-field degree;
* bridge/view: the semilocal bridge theorems above supply finite maximal spectrum, contraction to
  `maximalIdeal A`, and residue-field finiteness, while the only additional local bridge below is
  localization permanence for the `Ring.ordFrac` owner.

Primitive data are the finite algebra `A → B`, the element `y : Frac(B)ˣ`, and the canonical
dimension-at-most-one owner hypothesis `[Ring.KrullDimLE 1 A]`. Derived API consists of
semilocality of `B`, contraction to `maximalIdeal A`, the induced residue-field extensions,
injectivity of `A → B` from the fraction-ring tower, and localization permanence needed to
evaluate `Ring.ordFrac` after localizing at maximal ideals.
-/

-- Proof sketch: first pass the dimension-at-most-one hypothesis from `A` to the finite extension
-- `B`, then localize at `m`. Localization cannot increase Krull dimension, so `Bₘ` still
-- satisfies the `Ring.KrullDimLE 1` hypothesis needed for `Ring.ordFrac`.
/-- The localization of a module-finite extension of a one-dimensional Noetherian local domain at a
maximal ideal still has Krull dimension at most `1`. -/
theorem krullDimLE_one_localizationAtPrime_of_moduleFinite
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B]
    (m : MaximalSpectrum B) :
    Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) := by
  sorry

end

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

section

variable [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B]

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

local instance :
    FiniteDimensional (FractionRing A) (FractionRing B) :=
  finiteDimensional_fractionRing_of_moduleFinite A

local instance residueFieldAlgebra_of_moduleFinite (m : MaximalSpectrum B) :
    Algebra κA (Ideal.ResidueField m.asIdeal) :=
  residueFieldAlgebra_of_finiteType_of_finiteFractionRingExtension A m

local instance residueFieldModuleFinite_of_moduleFinite (m : MaximalSpectrum B) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) :=
  moduleFinite_residueField_of_finiteType_of_finiteFractionRingExtension A m

-- Proof sketch: write the order on the left as the length of `B / yB` via the determinant formula
-- for lattices from Lemma `10.121.7`, decompose that length into the sum of the local lengths over
-- the finitely many maximal ideals of `B` using Lemma `10.52.12`, and identify each local length
-- with the local order of vanishing. The determinant giving the lattice distance is exactly the
-- field norm `Norm_{Frac(B)/Frac(A)}(y)`.
/-- Lemma 10.121.8: if `A → B` is a module-finite extension of domains with `A` a one-dimensional
Noetherian local domain, then the order of vanishing on `A` of the norm of `y ∈ Frac(B)ˣ` equals
the sum over the maximal ideals `m` of `B` of the residue-field degree
`[κ(m) : κ(maximalIdeal A)]` times the order of vanishing of `y` in `Bₘ`. -/
theorem ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac (y : (FractionRing B)ˣ) :
    WithZero.log (Ring.ordFrac A (Algebra.norm (FractionRing A) (y : FractionRing B))) =
      let _ : Finite (MaximalSpectrum B) :=
        finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
      let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
      let _ : IsNoetherianRing B := IsNoetherianRing.of_finite A B
      let _ : ∀ m : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
        fun m ↦
          IsLocalization.isNoetherianRing m.asIdeal.primeCompl
            (Localization.AtPrime m.asIdeal) inferInstance
      let _ : ∀ m : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
        fun m ↦ krullDimLE_one_localizationAtPrime_of_moduleFinite A m
      ∑ m : MaximalSpectrum B,
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
          WithZero.log (Ring.ordFrac (Localization.AtPrime m.asIdeal) (y : FractionRing B)) := by
  sorry

end

end

end InjectiveAlgebraMapFact
