import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

-- Declarations for this item will be appended below by the statement pipeline.

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
