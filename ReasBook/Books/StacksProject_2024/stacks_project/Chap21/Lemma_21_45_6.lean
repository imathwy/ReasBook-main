import Mathlib.CategoryTheory.ObjectProperty.Retract
import StacksProject_2024.Chap21.Definition_21_45_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open RingedSite.Hom
open ObjectProperty.IsStableUnderRetracts

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

open _root_.RingedSite.DerivedCategory
open _root_.RingedSite.Hom.ModuleDerived

section

/- Domain-style sampling for Lemma 21.45.6:
- primary domain: pseudo-coherence as an object property on `ModuleDerived X` over a ringed site,
  together with the generic retract/direct-summand API in additive categories;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the `core/canonical` layer is the object property
  `fun K : DMod ↦ K.IsMPseudoCoherent m` and its pseudo-coherent analogue on the bundled owner
  `X : RingedSite`; the four textbook biproduct statements are `bridge/view` consequences of
  retract stability and should therefore reuse the generic owner API rather than duplicating a
  presentation-specific pseudo-coherence surface via `RingedSite.ofCommRingSheaf`;
- primitive vs. derived:
  primitive data are the owner predicates `K.IsMPseudoCoherent m` and `K.IsPseudoCoherent`;
  derived API is the retract-stability instances and the left/right biproduct consequences.

Source/core/bridge triage:
- `source-facing`: the four direct-summand statements of Lemma `21.45.6`;
- `core/canonical`: `ObjectProperty.IsStableUnderRetracts` for the Chapter 21 pseudo-coherence
  owners on `ModuleDerived X`;
- `bridge/view`: `of_biprod_left` and `of_biprod_right`.
-/

variable {X : RingedSite.{u, v}}

local notation "Mod" => ModuleCat X
local notation "DMod" => ModuleDerived X

variable [HasBinaryProducts X.carrier]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]

local notation "PseudoCoherentObj" =>
  (IsPseudoCoherent : ObjectProperty DMod)

section

variable (m : ℤ)

local notation "MPseudoCoherentObj" =>
  (fun K : DMod ↦ IsMPseudoCoherent K m : ObjectProperty DMod)

/-- `m`-pseudo-coherent objects of `ModuleDerived X` are stable under retracts/direct summands. -/
instance isMPseudoCoherent_isStableUnderRetracts
    [Abelian (ModuleCat X)] :
    ObjectProperty.IsStableUnderRetracts MPseudoCoherentObj where
  of_retract h hK := by
    sorry

omit [∀ U : X, (localizedRestriction X U).Additive]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)] in
/-- If `K ⊞ L` is `m`-pseudo-coherent in `ModuleDerived X`, then both summands are
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_summands_of_biprod
    [Abelian (ModuleCat X)] (K L : DMod) [HasBinaryBiproduct K L]
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m ∧ L.IsMPseudoCoherent m :=
  ⟨of_biprod_left MPseudoCoherentObj hKL, of_biprod_right MPseudoCoherentObj hKL⟩

omit [∀ U : X, (localizedRestriction X U).Additive]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)] in
/-- Lemma 21.45.6 (1): if `K ⊞ L` is `m`-pseudo-coherent in `ModuleDerived X`, then `K` is
`m`-pseudo-coherent. -/
@[stacks 08FW]
theorem isMPseudoCoherent_left_of_biprod
    [Abelian (ModuleCat X)] (K L : DMod) [HasBinaryBiproduct K L]
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m :=
  (isMPseudoCoherent_summands_of_biprod m K L hKL).1

omit [∀ U : X, (localizedRestriction X U).Additive]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)] in
/-- Lemma 21.45.6 (2): if `K ⊞ L` is `m`-pseudo-coherent in `ModuleDerived X`, then `L` is
`m`-pseudo-coherent. -/
@[stacks 08FW]
theorem isMPseudoCoherent_right_of_biprod
    [Abelian (ModuleCat X)] (K L : DMod) [HasBinaryBiproduct K L]
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m :=
  (isMPseudoCoherent_summands_of_biprod m K L hKL).2

end

/-- Pseudo-coherent objects of `ModuleDerived X` are stable under retracts/direct summands. -/
instance isPseudoCoherent_isStableUnderRetracts
    [Abelian (ModuleCat X)] :
    ObjectProperty.IsStableUnderRetracts PseudoCoherentObj where
  of_retract h hK := by
    exact
      (RingedSite.DerivedCategory.isPseudoCoherent_iff _).2 fun m ↦
      prop_of_retract
        (fun K : DMod ↦ IsMPseudoCoherent K m : ObjectProperty DMod)
        h ((RingedSite.DerivedCategory.isPseudoCoherent_iff _).1 hK m)

omit [∀ U : X, (localizedRestriction X U).Additive]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)] in
/-- If `K ⊞ L` is pseudo-coherent in `ModuleDerived X`, then both summands are
pseudo-coherent. -/
theorem isPseudoCoherent_summands_of_biprod
    [Abelian (ModuleCat X)] (K L : DMod) [HasBinaryBiproduct K L]
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    K.IsPseudoCoherent ∧ L.IsPseudoCoherent :=
  ⟨of_biprod_left PseudoCoherentObj hKL, of_biprod_right PseudoCoherentObj hKL⟩

omit [∀ U : X, (localizedRestriction X U).Additive]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)] in
/-- Lemma 21.45.6 (3): if `K ⊞ L` is pseudo-coherent in `ModuleDerived X`, then `K` is
pseudo-coherent. -/
@[stacks 08FW]
theorem isPseudoCoherent_left_of_biprod
    [Abelian (ModuleCat X)] (K L : DMod) [HasBinaryBiproduct K L]
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    K.IsPseudoCoherent :=
  (isPseudoCoherent_summands_of_biprod K L hKL).1

omit [∀ U : X, (localizedRestriction X U).Additive]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)] in
/-- Lemma 21.45.6 (4): if `K ⊞ L` is pseudo-coherent in `ModuleDerived X`, then `L` is
pseudo-coherent. -/
@[stacks 08FW]
theorem isPseudoCoherent_right_of_biprod
    [Abelian (ModuleCat X)] (K L : DMod) [HasBinaryBiproduct K L]
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    L.IsPseudoCoherent :=
  (isPseudoCoherent_summands_of_biprod K L hKL).2

end

end SheafOfModules.RingedSite
