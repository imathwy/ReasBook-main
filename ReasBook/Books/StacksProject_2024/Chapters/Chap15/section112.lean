import Mathlib
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_112_1 (from Chap15) -/
universe u v w

open Ideal IsLocalRing

/- Domain-style sampling for Definition 15.112.1:
- primary domain: extensions of discrete valuation rings and the induced ramification/inertia data
  on maximal ideals and residue fields;
- sampled owner declarations:
  `IsLocalHom`,
  `Ideal.ramificationIdx`,
  `Ideal.inertiaDeg`,
  `Ideal.inertiaDeg_algebraMap`;
- best owner abstraction: the source-facing owner is
  `IsExtensionOfDiscreteValuationRings`, while the ramification index and residue degree are
  the chapter owners on extensions of discrete valuation rings, with the maximal-ideal
  ideal-theoretic owners used only as bridge API;
- primitive-vs-derived split: the primitive data are the injective local algebra map `A → B`,
  while the faithful scalar action on `B`, `ramificationIndex`, `residueDegree`,
  `WeaklyUnramified`, and the finite-dimensional `finrank` description of the residue degree are
  derived API.

Source/core/bridge triage:
- `source-facing`: `IsExtensionOfDiscreteValuationRings`, `ramificationIndex`, `residueDegree`,
  `WeaklyUnramified`;
- `core/canonical`: `IsLocalHom`, `Ideal.ramificationIdx`, `Ideal.inertiaDeg`,
  `FractionRing.liftAlgebra`;
- `bridge/view`: `ramificationIndex_eq_iff`, `residueDegree_eq_inertiaDeg`, and
  `weaklyUnramified_iff_map_maximalIdeal`.
-/

/-- Definition 15.112.1: an extension of discrete valuation rings is an injective local algebra map
`A → B` between discrete valuation rings. -/
class IsExtensionOfDiscreteValuationRings (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B] : Prop
    extends IsLocalHom (algebraMap A B) where
  algebraMap_injective : Function.Injective (algebraMap A B)

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- The identity map of a discrete valuation ring is an extension of discrete valuation rings. -/
instance : IsExtensionOfDiscreteValuationRings A A where
  toIsLocalHom := by simpa using isLocalHom_id A
  algebraMap_injective := fun _ _ h ↦ h

end

namespace IsExtensionOfDiscreteValuationRings

/-- A tower of extensions of discrete valuation rings induces an extension on the composite map
`A → C`. -/
theorem of_tower
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [hAB : IsExtensionOfDiscreteValuationRings A B]
    [hBC : IsExtensionOfDiscreteValuationRings B C] :
    IsExtensionOfDiscreteValuationRings A C := by
  refine
    { toIsLocalHom := ?_
      algebraMap_injective := ?_ }
  · simpa [IsScalarTower.algebraMap_eq A B C] using
      (RingHom.isLocalHom_comp (algebraMap B C) (algebraMap A B))
  · simpa [IsScalarTower.algebraMap_eq A B C] using
      hBC.algebraMap_injective.comp hAB.algebraMap_injective

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]
variable [IsExtensionOfDiscreteValuationRings A B]

/-- Definition 15.112.1: the ramification index of an extension of discrete valuation rings is the
unique integer `e ≥ 1` such that the image of the maximal ideal of `A` is the `e`-th power of the
maximal ideal of `B`. -/
noncomputable def ramificationIndex : ℕ :=
  (maximalIdeal A).ramificationIdx (maximalIdeal B)

/-- The extension `B` is weakly unramified over `A` when its maximal-ideal ramification index is
`1`. -/
class WeaklyUnramified : Prop where
  ramificationIndex_eq_one : ramificationIndex A B = 1

omit [IsExtensionOfDiscreteValuationRings A B] in
@[simp] theorem weaklyUnramified_iff_ramificationIndex_eq_one :
    WeaklyUnramified A B ↔ ramificationIndex A B = 1 :=
  by
    constructor
    · intro h
      exact h.ramificationIndex_eq_one
    · intro h
      exact ⟨h⟩

end

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]
variable [IsExtensionOfDiscreteValuationRings A B]

/-- The residue degree of the induced residue-field extension `κ_A ⊆ κ_B`. When this extension is
finite, it is the degree `[κ_B : κ_A]`. -/
noncomputable def residueDegree [FiniteDimensional (ResidueField A) (ResidueField B)] : ℕ :=
  Module.finrank (ResidueField A) (ResidueField B)

/-- The residue degree agrees with the canonical maximal-ideal inertia degree. -/
theorem residueDegree_eq_inertiaDeg
    [FiniteDimensional (ResidueField A) (ResidueField B)] :
    residueDegree A B = (maximalIdeal A).inertiaDeg (maximalIdeal B) :=
  (Ideal.inertiaDeg_algebraMap (maximalIdeal A) (maximalIdeal B)).symm

/-- For an extension of discrete valuation rings, the residue degree is the finite-dimensional
degree of the induced residue-field extension. -/
theorem residueDegree_eq_finrank [FiniteDimensional (ResidueField A) (ResidueField B)] :
    residueDegree A B = Module.finrank (ResidueField A) (ResidueField B) := by
  rfl

end

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]

/-- The `A`-action on `B` is faithful for an extension of discrete valuation rings because
`A → B` is injective. -/
instance [h : IsExtensionOfDiscreteValuationRings A B] : FaithfulSMul A B :=
  (faithfulSMul_iff_algebraMap_injective A B).mpr h.algebraMap_injective

-- Proof sketch: for extensions of discrete valuation rings, the maximal ideal of the target is
-- the unique prime above the maximal ideal of the source, so the Dedekind-domain ramification
-- index specializes to the textbook equality `m_A B = m_B^e` with `e > 0`.
/-- Companion characterization: `e` is the ramification index of `A ⊆ B` exactly when the image
of the maximal ideal of `A` is the `e`-th power of the maximal ideal of `B`. -/
theorem ramificationIndex_eq_iff [IsExtensionOfDiscreteValuationRings A B] (e : ℕ) :
    ramificationIndex A B = e ↔
      0 < e ∧ (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ e := sorry

/-- The ramification index of an extension of discrete valuation rings is positive. -/
theorem ramificationIndex_pos [IsExtensionOfDiscreteValuationRings A B] :
    0 < ramificationIndex A B :=
  (ramificationIndex_eq_iff A B (ramificationIndex A B)).mp rfl |>.1

-- Proof sketch: specialize `ramificationIndex_eq_iff` to `e = 1`.
/-- Weakly unramified extensions are exactly those whose maximal ideal maps onto the maximal ideal.
-/
theorem weaklyUnramified_iff_map_maximalIdeal [IsExtensionOfDiscreteValuationRings A B] :
    WeaklyUnramified A B ↔
      (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
  rw [weaklyUnramified_iff_ramificationIndex_eq_one]
  simpa using (ramificationIndex_eq_iff A B 1)

end

section IntegralClosure

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [FaithfulSMul A L]

omit [IsDomain A] [IsDiscreteValuationRing A] in
private theorem integralClosure_algebraMap_injective :
    Function.Injective (algebraMap A (integralClosure A L)) := by
  intro x y hxy
  apply FaithfulSMul.algebraMap_injective A L
  change algebraMap (integralClosure A L) L (algebraMap A (integralClosure A L) x) =
      algebraMap (integralClosure A L) L (algebraMap A (integralClosure A L) y)
  exact congrArg (algebraMap (integralClosure A L) L) hxy

/-- The normalization map `A → integralClosure A L` is an extension of discrete valuation rings as
soon as the normalization is itself a discrete valuation ring and the original `A`-action on `L`
is faithful. -/
instance
    [IsDiscreteValuationRing (integralClosure A L)] :
    IsExtensionOfDiscreteValuationRings A (integralClosure A L) where
  toIsLocalHom :=
    (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom
      integralClosure_algebraMap_injective
  algebraMap_injective := integralClosure_algebraMap_injective

end IntegralClosure

end IsExtensionOfDiscreteValuationRings

/-! ### Lemma_15_112_2 (from Chap15) -/
universe u v

open Ideal IsLocalRing

/- Domain-style sampling for Lemma 15.112.2:
- primary domain: ramification and inertia for extensions of discrete valuation rings with finite
  fraction-field extension;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings.residueDegree`,
  `IsExtensionOfDiscreteValuationRings.residueDegree_eq_finrank`,
  `finiteDimensional_residueField_of_finiteDimensional_fractionField_extension`,
  `ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension`;
- best owner abstraction: the source-facing DVR extension owner is
  `IsExtensionOfDiscreteValuationRings`, while the core numerical statements are the valuation-ring
  extension theorems from `Lemma_15_124_2`;
- primitive-vs-derived split: the primitive data for the source-facing lemma are the DVR extension
  together with the finite-dimensional fraction-field hypothesis, while the owner-level comparison
  `valuationRing_ramificationIndex_eq` is derived directly from the two ramification-index owners
  and does not use finiteness; the chapter names `ramificationIndex` and `residueDegree` are the
  source-facing DVR owners reused directly in the bridge statements below.

Source/core/bridge triage:
- `source-facing`: the textbook statements in terms of `ramificationIndex A B` and
  `residueDegree A B`;
- `core/canonical`: the valuation-ring extension theorems
  `finiteDimensional_residueField_of_finiteDimensional_fractionField_extension` and
  `ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension`;
- `bridge/view`: the specialization of those valuation-ring theorems to the chapter-local DVR
  owner.
-/

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/- Lemma 15.112.2 (1): for an extension of discrete valuation rings `A ⊂ B`, if the induced
fraction-field extension `FractionRing B / FractionRing A` is finite, then the induced residue
field extension is finite. This is the exact valuation-ring owner theorem recalled in the
discrete-valuation-ring setting via the canonical instance
`discreteValuationRingExtension_toIsExtensionOfValuationRings`. -/
recall finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

attribute [local instance]
  finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

namespace IsExtensionOfDiscreteValuationRings

/-- The valuation-ring ramification index agrees with the source-facing DVR ramification index. -/
theorem valuationRing_ramificationIndex_eq
    : IsExtensionOfValuationRings.ramificationIndex A B = ramificationIndex A B := by
  sorry

-- Proof sketch: first rewrite the valuation-ring ramification index through
-- `valuationRing_ramificationIndex_eq`; the valuation-ring residue degree is definitionally the
-- same as the chapter-local DVR residue degree. Then specialize the canonical valuation-ring
-- inequality from `Lemma_15_124_2` to the DVR extension `A ⊂ B` and convert the resulting `ℕ∞`
-- inequality back to `ℕ`.
/-- Lemma 15.112.2 (2): for an extension of discrete valuation rings `A ⊂ B`, if the induced
fraction-field extension `FractionRing B / FractionRing A` is finite, then the ramification index
times the residue degree is bounded by `[FractionRing B : FractionRing A]`. This is the
source-facing DVR restatement of the canonical valuation-ring inequality from `Lemma_15_124_2`. -/
theorem ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    ramificationIndex A B * residueDegree A B ≤
      Module.finrank (FractionRing A) (FractionRing B) := by
  sorry

end IsExtensionOfDiscreteValuationRings

end

/-! ### Lemma_15_112_3 (from Chap15) -/
universe u v w

open Ideal IsLocalRing IsExtensionOfDiscreteValuationRings

/-!
- primary domain: ramification and residue degrees in towers of discrete valuation rings
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings.of_tower`,
  `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `IsExtensionOfDiscreteValuationRings.residueDegree`,
  `IsExtensionOfDiscreteValuationRings.residueDegree_eq_inertiaDeg`,
  `Ideal.ramificationIdx_algebra_tower'`,
  `Ideal.inertiaDeg_algebra_tower`
- owner abstraction: the source-facing owners are
  `IsExtensionOfDiscreteValuationRings.ramificationIndex` and
  `IsExtensionOfDiscreteValuationRings.residueDegree`; the ideal-theoretic tower lemmas are the
  canonical core API used only to derive these source-facing formulas
- layer triage: this file is a `bridge/view` item from the ideal-theoretic tower lemmas to the
  chapter owners on extensions of discrete valuation rings
- primitive data: the algebra tower together with the two extension owners
  `IsExtensionOfDiscreteValuationRings A B` and `IsExtensionOfDiscreteValuationRings B C`
- derived API: the equalities comparing the chapter owners with
  `Ideal.ramificationIdx` and `Ideal.inertiaDeg`, where the ramification-index comparison is by
  direct unfolding of `ramificationIndex`
-/

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]

namespace IsExtensionOfDiscreteValuationRings

-- Proof sketch: derive the torsion-free instances from the injective extension owners, then
-- specialize `Ideal.ramificationIdx_algebra_tower'` to the maximal ideals in the DVR tower and
-- rewrite by unfolding the chapter owner `ramificationIndex`.
/-- Lemma 15.112.3: for extensions `A ⊂ B ⊂ C` of discrete valuation rings, the ramification
index from `A` to `C` is the product of the ramification indices from `A` to `B` and from `B` to
`C`. -/
theorem ramificationIndex_algebra_tower :
    ramificationIndex A C = ramificationIndex A B * ramificationIndex B C := by
  let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
  simpa [ramificationIndex] using
    ramificationIdx_algebra_tower' (maximalIdeal A) (maximalIdeal B) (maximalIdeal C)

-- Proof sketch: specialize `Ideal.inertiaDeg_algebra_tower` to the maximal ideals in the tower
-- `maximalIdeal A ⊂ maximalIdeal B ⊂ maximalIdeal C`; for discrete valuation rings these inertia
-- degrees are the residual degrees, so this gives multiplicativity for the chapter owner
-- `residueDegree` in the finite-residue-field case via `residueDegree_eq_inertiaDeg`.
/-- Lemma 15.112.3: for extensions `A ⊂ B ⊂ C` of discrete valuation rings, the residue degree
from `A` to `C` is the product of the residue degrees from `A` to `B` and from `B` to `C`. -/
theorem residueDegree_algebra_tower
    [FiniteDimensional (ResidueField A) (ResidueField B)]
    [FiniteDimensional (ResidueField B) (ResidueField C)] :
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    let _ : FiniteDimensional (ResidueField A) (ResidueField C) :=
      FiniteDimensional.trans (ResidueField A) (ResidueField B) (ResidueField C)
    residueDegree A C = residueDegree A B * residueDegree B C := by
  let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
  let _ : FiniteDimensional (ResidueField A) (ResidueField C) :=
    FiniteDimensional.trans (ResidueField A) (ResidueField B) (ResidueField C)
  simpa [residueDegree_eq_inertiaDeg] using
    inertiaDeg_algebra_tower (maximalIdeal A) (maximalIdeal B) (maximalIdeal C)

end IsExtensionOfDiscreteValuationRings

end

/-! ### Lemma_15_112_4 (from Chap15) -/
open IsExtensionOfDiscreteValuationRings

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/- Domain-style sampling:
- primary domain: ramification theory for extensions of discrete valuation rings with purely
  inseparable fraction-field extension;
- sampled owner declarations:
  `FractionRing.liftAlgebra`,
  `FractionRing.isScalarTower_liftAlgebra`,
  `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `isPurelyInseparable_iff_pow_mem`;
- best owner abstraction: the source-facing owner remains `ramificationIndex A B`, while the
  induced fraction-field algebra `FractionRing A → FractionRing B` and its scalar-tower
  compatibility with `A → B` are canonical derived infrastructure exported by the DVR-extension
  owner rather than installed locally in this file;
- primitive vs. derived: the primitive public data are the DVR extension owner together with the
  characteristic-`p` and purely inseparable hypotheses on the induced fraction-field extension;
  the fraction-field algebra/scalar-tower instances and the `p`-power conclusion are derived API.

Source/core/bridge triage:
- `source-facing`: the conclusion that the ramification index of `A ⊆ B` is a power of `p`;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `FractionRing.liftAlgebra`, and
  `isPurelyInseparable_iff_pow_mem`;
- `bridge/view`: direct unfolding of `ramificationIndex`, used only to compare the chapter owner
  with the underlying ideal-theoretic invariant.
-/

-- Proof sketch: write a uniformizer of `A` as a unit times a power of a uniformizer of `B`, then
-- use pure inseparability to find a `p`-power of the target uniformizer lying in `FractionRing A`.
-- Comparing valuations gives an equality `k * e = p ^ n` for some `k` and `n`, forcing the
-- ramification index `e` to be a power of `p`.
/-- Lemma 15.112.4: if `A ⊆ B` is an extension of discrete valuation rings, the induced extension
of fraction fields `FractionRing A ⊆ FractionRing B` has characteristic `p > 0`, and
`FractionRing B` is purely inseparable over `FractionRing A`, then the ramification index of
`A ⊆ B` is a power of `p`. -/
theorem ramificationIndex_eq_pow_of_isPurelyInseparable
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing A) p]
    [IsPurelyInseparable (FractionRing A) (FractionRing B)] :
    ∃ n : ℕ,
      ramificationIndex A B = p ^ n := sorry

end

/-! ### Lemma_15_112_5 (from Chap15) -/
open IsExtensionOfDiscreteValuationRings
open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

/- Domain-style sampling for Lemma 15.112.5:
- primary domain: extensions of discrete valuation rings, formal smoothness for the maximal-ideal
  adic topology, and weak ramification on maximal ideals and residue fields;
- sampled owner declarations:
  `RingHom.formally_smooth_for_adic`,
  `IsExtensionOfDiscreteValuationRings.WeaklyUnramified`,
  `IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal`,
  `flat_geometricallyRegularSpecialFiber_formallySmooth_tfae`;
- best owner abstraction: the formal smoothness side is owned by
  `RingHom.formally_smooth_for_adic`, while weak ramification is owned by `WeaklyUnramified`; the
  maximal-ideal equality is only a bridge view of the latter, not primitive public data;
- primitive-vs-derived split: the primitive data are the DVR extension structure
  `[IsExtensionOfDiscreteValuationRings A B]`, while the maximal-ideal equality and the formal
  smoothness criterion are derived API.

Source/core/bridge triage:
- `source-facing`: the equivalence in Lemma 15.112.5;
- `core/canonical`: `(algebraMap A B).formally_smooth_for_adic (maximalIdeal B)` and
  `WeaklyUnramified A B`;
- `bridge/view`: `weaklyUnramified_iff_map_maximalIdeal`.
-/

-- Proof sketch: apply Proposition `15.40.5` to the local map `A → B`. For extensions of
-- discrete valuation rings, flatness is automatic from torsion-freeness, while the special fiber
-- over `ResidueField A` is a field. Then use Proposition `10.158.9` and the field-extension
-- criterion for geometric regularity versus formal smoothness to identify geometric regularity of
-- the special fiber with separability of `ResidueField B / ResidueField A`; in this DVR setting,
-- weakly unramified is the canonical owner `WeaklyUnramified A B`, with
-- `weaklyUnramified_iff_map_maximalIdeal` as the maximal-ideal bridge.
/-- Lemma 15.112.5: for an extension `A ⊆ B` of discrete valuation rings, the map `A → B` is
formally smooth for the `maximalIdeal B`-adic topology if and only if `A ⊆ B` is weakly
unramified and the residue field extension `ResidueField B / ResidueField A` is separable. -/
theorem formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField :
    (algebraMap A B).formally_smooth_for_adic (maximalIdeal B) ↔
      WeaklyUnramified A B ∧
        Algebra.IsSeparable (ResidueField A) (ResidueField B) := sorry

end

/-! ### Remark_15_112_6 (from Chap15) -/
universe u v

open Ideal IsLocalRing
open scoped BigOperators

/-
Domain-style sampling for Remark 15.112.6:
- primary domain: ramification and inertia for finite separable extensions of fraction fields of
  discrete valuation rings, together with the henselian local integral-closure specialization;
- sampled owner declarations:
  `integralClosure.isFractionRing_of_finite_extension`,
  `IsIntegralClosure.finite`,
  `integralClosure_isDedekindDomain_of_ringKrullDim_eq_one`,
  `Ideal.sum_ramification_inertia`,
  `integralClosure_henselianLocalRing`,
  `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`;
- best owner abstraction: the core owner is the integral closure `integralClosure A L`;
- primitive data: the owner ring `B = integralClosure A L`; the fraction-field extension
  `L / FractionRing A` together with its separability is only primitive for the ramification
  identity, while the henselian uniqueness statement needs only the integral-closure-in-a-field
  owner and the henselian local source ring;
- derived API: the fraction-field structure on `B`, finiteness over `A` from
  `IsIntegralClosure.finite`, the ramification/inertia identity, and the henselian-locality of `B`
  used to identify the unique prime above `maximalIdeal A`.

Source/core/bridge triage:
 - `core/canonical`: `integralClosure A L` together with the sampled mathlib/project owner
  theorems above;
 - `source-facing`: the specialized degree formula and the henselian uniqueness result;
 - `bridge/view`: the specialization from the general ramification theorem to the DVR setting, and
  the use of the canonical henselian-local owner instance on `integralClosure A L`.
-/

section Ramification

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

local notation "K" => FractionRing A
local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A

private theorem not_isField : ¬ IsField A := by
  intro hA
  exact IsDiscreteValuationRing.not_a_field A
    ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hA)

local instance : Module.Finite A B :=
  IsIntegralClosure.finite A K L B

local instance : IsFractionRing B L :=
  integralClosure.isFractionRing_of_finite_extension K L

local instance : IsDedekindDomain B :=
  integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
    (IsPrincipalIdealRing.ringKrullDim_eq_one A not_isField)

-- Proof sketch: apply the fundamental identity `Ideal.sum_ramification_inertia` to the maximal
-- ideal of `A` and the integral closure `B` in `L`; the separable finite extension hypothesis
-- yields the finite integral-closure owner by `IsIntegralClosure.finite`.
/-- Remark 15.112.6: if `A` is a discrete valuation ring with fraction field `FractionRing A`,
`L / FractionRing A` is a finite separable extension, then for the integral closure
`B = integralClosure A L` the degree `[L : FractionRing A]` is the sum over the primes of `B`
above the maximal ideal of `A` of the products of ramification indices and residue degrees. -/
theorem integralClosure_finrank_eq_sum_ramificationIdx_mul_inertiaDeg :
    Module.finrank K L =
      ∑ Q ∈ primesOverFinset p B,
        Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q := by
  simpa using
    (Ideal.sum_ramification_inertia B K L (IsDiscreteValuationRing.not_a_field A)).symm

end Ramification

section Henselian

variable {A : Type u} {L : Type v}
variable [CommRing A] [Field L] [Algebra A L] [HenselianLocalRing A]

local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A

local instance : Algebra.IsIntegral A B :=
  IsIntegralClosure.isIntegral_algebra A L

local instance : HenselianLocalRing B :=
  integralClosure_henselianLocalRing

private instance liesOver_maximalIdeal_of_isMaximal (P : Ideal B) [P.IsMaximal] :
    P.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩

-- Proof sketch: the canonical owner instance puts the integral closure `B` of a henselian local
-- ring in a field back in the henselian-local world. Any prime of `B` above `maximalIdeal A` is
-- maximal by integrality, hence equals the unique maximal ideal of the local ring `B`.
/-- If `A` is henselian local, then exactly one prime of the integral closure lies above the
maximal ideal of `A`. -/
theorem integralClosure_primesOver_maximalIdeal_eq_singleton_of_henselianLocalRing
    : primesOver p B = {maximalIdeal B} := by
  ext P
  constructor
  · intro hP
    let _ : P.IsPrime := hP.1
    let _ : P.LiesOver p := hP.2
    exact Set.mem_singleton_iff.mpr <| IsLocalRing.eq_maximalIdeal <|
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P <| by
        simpa [P.over_def p] using (maximalIdeal.isMaximal A : IsMaximal p)
  · rintro rfl
    exact ⟨inferInstance, inferInstance⟩

end Henselian

/-! ### Definition_15_112_7 (from Chap15) -/
universe u v

open Ideal IsLocalRing

section

/-- A natural number is prime to the residue characteristic of a local ring `A` if it is coprime
to every prime realizing the characteristic of the residue field of `A`. -/
def PrimeToResidueCharacteristic
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p], Nat.Coprime n p

end

section

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]

local instance (P : Ideal (integralClosure A L)) [P.IsMaximal] : P.IsPrime :=
  Ideal.IsMaximal.isPrime inferInstance

/-
Domain-style sampling for Definition 15.112.7:
- primary domain: ramification theory for finite separable extensions of the fraction field of a
  discrete valuation ring, measured on maximal ideals of the integral closure;
- sampled owner declarations:
  `Algebra.IsUnramifiedAt`,
  `Ideal.ramificationIdx`,
  `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`,
  `Algebra.isUnramifiedAt_iff_map_eq`;
- best owner abstraction: the integral-closure branches above `maximalIdeal A`, with the canonical
  branchwise owner `Algebra.IsUnramifiedAt A P` supplying the primitive local unramified data once
  the branch algebra is known to be essentially of finite type over `A`, and the ideal-theoretic
  ramification owner `Ideal.ramificationIdx` supplying the derived equality `ramificationIdx = 1`;
- primitive-vs-derived split: tame ramification carries the residue-separability and prime-to-
  residue-characteristic branch conditions, while unramified stores only the stronger canonical
  branchwise owner and derives those tame consequences from it; the ambient
  `A → FractionRing A → L` tower is primitive because the source definition is about extensions
  `L / FractionRing A`, while the finite separable fraction-field hypotheses belong to the
  downstream bridge that makes `integralClosure A L` essentially of finite type over `A`.

Source/core/bridge triage:
- `source-facing`: `IsUnramifiedWithRespectTo`, `IsTamelyRamifiedWithRespectTo`,
  `IsTotallyRamifiedWithRespectTo`;
- `core/canonical`: `integralClosure A L`, `Algebra.IsUnramifiedAt`, `Ideal.ramificationIdx`, and
  the induced residue-field map;
- `bridge/view`: the finite-extension bridge furnishing `Module.Finite` and `EssFiniteType` on
  `integralClosure A L`.
-/

/-- Definition 15.112.7 (2): the finite separable extension `L / FractionRing A` is tamely
ramified with respect to the discrete valuation ring `A` if the residue-field extensions above
`maximalIdeal A` are separable and every ramification index is prime to the residue characteristic
of `A`; when `κA = Ideal.ResidueField (maximalIdeal A)` has characteristic `0`, the coprimality
condition is vacuous. -/
class IsTamelyRamifiedWithRespectTo (A : Type u) (L : Type v) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] : Prop where
  residueField_separable (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      let _ : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
      let _ : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
        ResidueField.instAlgebra
      Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) P.ResidueField
  ramificationIdx_coprime (q : ℕ) [_hq : Fact q.Prime]
      [CharP (Ideal.ResidueField (maximalIdeal A)) q]
      (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
      Nat.Coprime (ramificationIdx (maximalIdeal A) P) q

/-- Definition 15.112.7 (1): the finite separable extension `L / FractionRing A` is unramified
with respect to the discrete valuation ring `A` if for every maximal ideal of
`B = integralClosure A L` above `maximalIdeal A`, the ramification index is `1` and the induced
residue-field extension is separable. The bridge to the canonical owner
`Algebra.IsUnramifiedAt A P` is derived only under the finite-type hypotheses needed by that
owner. -/
class IsUnramifiedWithRespectTo (A : Type u) (L : Type v) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] : Prop where
  residueField_separable (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      let _ : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
      let _ : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
        ResidueField.instAlgebra
      Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) P.ResidueField
  ramificationIdx_eq_one (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      ramificationIdx (maximalIdeal A) P = 1

namespace IsUnramifiedWithRespectTo

variable [Algebra.EssFiniteType A (integralClosure A L)]

/-- The source-facing unramified branch data recover the canonical owner
`Algebra.IsUnramifiedAt A P` under the finite-type hypotheses required by that owner. -/
theorem isUnramifiedAt (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] [h : _root_.IsUnramifiedWithRespectTo A L] :
    Algebra.IsUnramifiedAt A P := sorry

/-- Under the finite-type bridge, the source-facing unramified predicate is equivalent to the
branchwise canonical owner `Algebra.IsUnramifiedAt`. -/
theorem iff_isUnramifiedAt :
    _root_.IsUnramifiedWithRespectTo A L ↔
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        Algebra.IsUnramifiedAt A P := sorry

end IsUnramifiedWithRespectTo

section FractionFieldExtension

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

omit [Algebra.IsSeparable (FractionRing A) L] in
instance integralClosure_moduleFinite : Module.Finite A (integralClosure A L) :=
  IsIntegralClosure.finite A (FractionRing A) L (integralClosure A L)

omit [Algebra.IsSeparable (FractionRing A) L] in
instance integralClosure_essFiniteType : Algebra.EssFiniteType A (integralClosure A L) := by
  infer_instance

instance [h : IsUnramifiedWithRespectTo A L] : IsTamelyRamifiedWithRespectTo A L := by
  refine
    { residueField_separable := ?_
      ramificationIdx_coprime := ?_ }
  · intro P _ _
    letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
    letI : Algebra (Ideal.ResidueField (maximalIdeal A)) P.ResidueField :=
      ResidueField.instAlgebra
    simpa using h.residueField_separable P
  · intro p _ _ P _ _
    have hramification : ramificationIdx (maximalIdeal A) P = 1 := h.ramificationIdx_eq_one P
    simpa [hramification]

end FractionFieldExtension

/-- Definition 15.112.7 (3): the finite separable extension `L / FractionRing A` is totally
ramified with respect to the discrete valuation ring `A` if there is a unique maximal ideal of
`B = integralClosure A L` above `maximalIdeal A` and the induced residue-field extension over
`κA = Ideal.ResidueField (maximalIdeal A)` is trivial; existence of a maximal ideal above
`maximalIdeal A` is ambiently supplied by lying-over for `integralClosure A L`. -/
class IsTotallyRamifiedWithRespectTo (A : Type u) (L : Type v) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] : Prop where
  unique_maximalIdeal (P Q : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] [Q.IsMaximal] [Q.LiesOver (maximalIdeal A)] :
      P = Q
  residueField_bijective (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A (integralClosure A L))
          (P.over_def (maximalIdeal A)))

/-- The trivial extension of the fraction field of a discrete valuation ring is unramified with
respect to the base ring. -/
instance fractionRing_isUnramifiedWithRespectTo :
    IsUnramifiedWithRespectTo A (FractionRing A) := by
  sorry

/-- The trivial extension of the fraction field of a discrete valuation ring is totally ramified
with respect to the base ring. -/
instance fractionRing_isTotallyRamifiedWithRespectTo :
    IsTotallyRamifiedWithRespectTo A (FractionRing A) := sorry

end

/-! ### Lemma_15_112_8 (from Chap15) -/
universe u v w

section

open IntermediateField

/- Domain-style sampling:
- source-facing owner: `IsUnramifiedWithRespectTo A L` from `Definition_15_112_7`;
- sampled canonical declarations in this domain:
  `IsUnramifiedWithRespectTo`,
  `isUnramifiedAt_of_integralClosure_tower`,
  `normalClosure K L (AlgebraicClosure L)`,
  `isGalois_normalClosure_of_separable`,
  `IntermediateField.finiteDimensional_sup`,
  `IntermediateField.isSeparable_sup`;
- best owner abstraction: the chapter owner `IsUnramifiedWithRespectTo`, with
  the source-facing existential overfield statement as the main theorem for clause `(2)`,
  the canonical Galois-closure field `normalClosure K L (AlgebraicClosure L)` as its preferred
  bridge witness, and `isUnramifiedAt_of_integralClosure_tower` as the canonical bridge from
  branchwise `Algebra.IsUnramifiedAt` data along integral-closure towers;
- primitive-vs-derived split: the finite/separable hypotheses on the bottom extension
  `L / FractionRing A` are primitive because they supply the integral-closure finite-type owner
  needed by `IsUnramifiedWithRespectTo A L`, while the tower hypotheses
  `[FiniteDimensional K L]`, `[FiniteDimensional L M]`, `[Algebra.IsSeparable K L]`, and
  `[Algebra.IsSeparable L M]` canonically derive the corresponding finite/separable structure on
  `M / K`, hence also the `Algebra.EssFiniteType A (integralClosure A M)` owner needed to state
  `IsUnramifiedWithRespectTo A M`; in the theorem surface below, those top-extension instances are
  derived locally from the tower rather than exposed as public binders.

This file is therefore a `bridge/view` layer: its numbered statements remain source-facing
existence theorems, while the canonical tower, normal-closure, and compositum owners serve only as
bridge infrastructure rather than parallel local wrappers.
-/

end

section

open IntermediateField

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

section Tower

variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L]
variable {M : Type w} [Field M] [Algebra A M] [Algebra (FractionRing A) M] [Algebra L M]
variable [IsScalarTower A (FractionRing A) M] [IsScalarTower (FractionRing A) L M]
variable [FiniteDimensional (FractionRing A) L] [FiniteDimensional L M]
variable [Algebra.IsSeparable (FractionRing A) L] [Algebra.IsSeparable L M]

local notation "K" => FractionRing A

-- Proof sketch: let `B = integralClosure A L` and `C = integralClosure A M`. For a maximal ideal
-- `p : Ideal B` over `maximalIdeal A`, choose a maximal ideal `P : Ideal C` above `p` by lying
-- over. Since `M` is unramified with respect to `A`, the branch `P` is unramified over `A`, so
-- its ramification index over `maximalIdeal A` is `1` and the residue-field extension is
-- separable. Comparing ramification indices in the tower `A ⊆ B ⊆ C` and descending separability
-- along `κ(P) / κ(p) / κA` gives that `p` is unramified over `A`.
/-- Lemma 15.112.8 (1): in a tower `M/L/K` of finite separable extensions over the fraction field
of a discrete valuation ring `A`, unramifiedness with respect to `A` descends from `M` to `L`. -/
theorem isUnramifiedWithRespectTo_of_tower
    (hM : IsUnramifiedWithRespectTo A M) :
    IsUnramifiedWithRespectTo A L := sorry

end Tower

section NormalClosure

variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]

local notation "K" => FractionRing A
local notation "N" => normalClosure K L (AlgebraicClosure L)

-- Proof sketch: take the canonical normal closure `normalClosure K L (AlgebraicClosure L)`;
-- Lemma `9.21.5` gives its Galois structure over `K`, and the remaining input is the companion
-- bridge that this normal closure is still unramified with respect to `A`.
/-- Companion bridge for Lemma 15.112.8 (2): the canonical normal closure witness inside
`AlgebraicClosure L` is itself unramified with respect to `A`. -/
theorem isUnramifiedWithRespectTo_normalClosure
    (hL : IsUnramifiedWithRespectTo A L) :
    IsUnramifiedWithRespectTo A N := sorry

/-- Lemma 15.112.8 (2): if `L / K` is finite separable and unramified with respect to `A`, then
there exists a finite Galois extension of `K` containing `L` that is still unramified with
respect to `A`. The canonical witness is the normal closure of `L / K` inside
`AlgebraicClosure L`. -/
theorem exists_isGalois_unramifiedWithRespectTo
    (hL : IsUnramifiedWithRespectTo A L) :
    ∃ (M : Type v) (_ : Field M) (_ : Algebra A M) (_ : Algebra K M) (_ : Algebra L M)
      (_ : IsScalarTower A K M),
      IsScalarTower K L M ∧ FiniteDimensional K M ∧ IsGalois K M ∧
        IsUnramifiedWithRespectTo A M := by
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact
    ⟨inferInstance, ⟨inferInstance,
      ⟨isGalois_normalClosure_of_separable, isUnramifiedWithRespectTo_normalClosure hL⟩⟩⟩

end NormalClosure

section CommonExtension

variable {L₁ : Type v} [Field L₁] [Algebra A L₁] [Algebra (FractionRing A) L₁]
  [IsScalarTower A (FractionRing A) L₁]
variable {L₂ : Type w} [Field L₂] [Algebra A L₂] [Algebra (FractionRing A) L₂]
  [IsScalarTower A (FractionRing A) L₂]
variable [FiniteDimensional (FractionRing A) L₁] [FiniteDimensional (FractionRing A) L₂]
variable [Algebra.IsSeparable (FractionRing A) L₁] [Algebra.IsSeparable (FractionRing A) L₂]

local notation "K" => FractionRing A

-- Proof sketch: embed both fields into a common normal closure and then pass to the compositum of
-- their images; `IntermediateField.finiteDimensional_sup` and
-- `IntermediateField.isSeparable_sup` provide the canonical finite/separable overfield owner.
/-- Lemma 15.112.8 (3): two finite separable extensions of `K` that are unramified with respect to
`A` embed in a common finite separable extension that is unramified with respect to `A`. -/
theorem exists_common_unramifiedWithRespectTo_extension
    (hL₁ : IsUnramifiedWithRespectTo A L₁) (hL₂ : IsUnramifiedWithRespectTo A L₂) :
    ∃ (L : Type (max v w)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : Algebra L₁ L) (_ : Algebra L₂ L) (_ : IsScalarTower A K L),
      IsScalarTower K L₁ L ∧ IsScalarTower K L₂ L ∧
        FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
        IsUnramifiedWithRespectTo A L := sorry

end CommonExtension

end

/-! ### Lemma_15_112_9 (from Chap15) -/
open Ideal IsLocalRing Algebra

universe u v w

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L]
variable {M : Type w} [Field M] [Algebra A M] [Algebra L M] [IsScalarTower A L M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M

/- Domain-style sampling for unramifiedness in an integral-closure tower:
- primary domain: commutative algebra of unramified local extensions detected on integral closures
  over a discrete valuation ring;
- core/canonical owner: `Algebra.IsUnramifiedAt`;
- bridge APIs used here: `AlgHom.mapIntegralClosure`, `Ideal.under`, `Ideal.LiesOver.trans`, and
  `Algebra.IsUnramifiedAt.comp`;
- source/core/bridge triage: this item is a `bridge/view` lemma specialized to the tower
  `A ⊆ B ⊆ C`, while the actual owner predicate remains `Algebra.IsUnramifiedAt`.

Primitive data are only the pointwise unramified hypotheses on `B/A` and `C/B`. The induced
`B`-algebra structure on `C` is derived canonically from the tower map `L → M` via
`AlgHom.mapIntegralClosure`; no separate public tower-map wrapper is needed. -/

noncomputable local instance : Algebra B C :=
  ((IsScalarTower.toAlgHom A L M).mapIntegralClosure : B →ₐ[A] C).toAlgebra

local instance :
    IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

-- Proof sketch: for `P : Ideal C`, let `p := P.under B`. Then `p` lies over `maximalIdeal A`,
-- and `P` lies over `p`. Apply the two hypotheses to get `Algebra.IsUnramifiedAt A p` and
-- `Algebra.IsUnramifiedAt B P`, then compose them with `Algebra.IsUnramifiedAt.comp`.
/-- Lemma 15.112.9: let `B = integralClosure A L` and `C = integralClosure A M`. If every maximal
ideal of `B` over `maximalIdeal A` is unramified over `A`, and every maximal ideal of `C` over
`maximalIdeal A` is unramified over the intermediate integral closure `B`, then every maximal
ideal of `C` over `maximalIdeal A` is unramified over `A`. -/
theorem isUnramifiedAt_of_integralClosure_tower
    (hL : ∀ (p : Ideal B) [p.IsMaximal] [p.LiesOver (maximalIdeal A)],
      Algebra.IsUnramifiedAt A p)
    (hM : ∀ (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        Algebra.IsUnramifiedAt B P)
    (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Algebra.IsUnramifiedAt A P := sorry

end
