import StacksProject_2024.Chap13.Definition_13_6_1
import StacksProject_2024.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ObjectProperty.IsStableUnderRetracts
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [CategoryWithHomology (Modules X)]
variable [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)]

open _root_.AlgebraicGeometry.RingedSpace.ModuleDerived

local notation "DModX" => ModuleDerived X
local notation "PseudoCoherentObj" => (IsPseudoCoherent : ObjectProperty DModX)

/- Domain-style sampling for Lemma 20.47.6:
- primary domain: pseudo-coherence as an object property on `D(𝒪_X)`, together with the
  generic retract/direct-summand API in additive categories;
- sampled owner declarations:
  `ModuleDerived.IsMPseudoCoherent`,
  `ModuleDerived.IsPseudoCoherent`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the `core/canonical` layer is the object property
  `(fun K : DModX ↦ IsMPseudoCoherent K m : ObjectProperty DModX)` and its pseudo-coherent
  analogue `ModuleDerived.IsPseudoCoherent`; the source-facing
  biproduct statements below are `bridge/view` consequences of retract-stability, so the file
  should expose the owner-level retract-stability instances first and derive the textbook
  biproduct lemmas from them instead of keeping parallel local copies;
- primitive vs. derived:
  primitive data are the owner predicates `IsMPseudoCoherent K m` and `K.IsPseudoCoherent`;
  derived API is retract stability and the left/right biproduct consequences.

Source/core/bridge triage:
- `source-facing`: the four direct-summand statements of Lemma `20.47.6`;
- `core/canonical`: `ObjectProperty.IsStableUnderRetracts` for the Chapter 20 pseudo-coherence
  predicates;
-/

section

variable (m : ℤ)

local notation "MPseudoCoherentObj" =>
  (fun K : DModX ↦ ModuleDerived.IsMPseudoCoherent K m : ObjectProperty DModX)

/-- `m`-pseudo-coherent objects of `D(𝒪_X)` are stable under retracts/direct summands. -/
-- Proof sketch: if `K` is a retract of `L`, then `L` is isomorphic to `K ⊞ K'` for a
-- complementary summand `K'`. Apply the split-triangle argument from the Stacks proof, using
-- Lemma `20.47.4`, to descend `m`-pseudo-coherence from the biproduct to the retract.
instance isMPseudoCoherent_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts MPseudoCoherentObj where
  of_retract h hK := by
    sorry

omit [CategoryWithHomology (Modules X)]
  [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)] in
/-- If `K ⊞ L` is `m`-pseudo-coherent in `D(𝒪_X)`, then both summands are
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_summands_of_biprod (K L : DModX)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m ∧ L.IsMPseudoCoherent m :=
  ⟨of_biprod_left MPseudoCoherentObj hKL, of_biprod_right MPseudoCoherentObj hKL⟩

omit [CategoryWithHomology (Modules X)]
  [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)] in
/-- Lemma 20.47.6 (1): if `K ⊞ L` is `m`-pseudo-coherent in `D(𝒪_X)`, then `K` is
`m`-pseudo-coherent. -/
@[stacks 08CE]
theorem isMPseudoCoherent_left_of_biprod (K L : DModX)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m :=
  (isMPseudoCoherent_summands_of_biprod m K L hKL).1

omit [CategoryWithHomology (Modules X)]
  [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)] in
/-- Lemma 20.47.6 (2): if `K ⊞ L` is `m`-pseudo-coherent in `D(𝒪_X)`, then `L` is
`m`-pseudo-coherent. -/
@[stacks 08CE]
theorem isMPseudoCoherent_right_of_biprod (K L : DModX)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m :=
  (isMPseudoCoherent_summands_of_biprod m K L hKL).2

end

/-- Pseudo-coherent objects of `D(𝒪_X)` are stable under retracts/direct summands. -/
instance isPseudoCoherent_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts PseudoCoherentObj where
  of_retract h hK := by
    exact
      (ModuleDerived.isPseudoCoherent_iff_forall_isMPseudoCoherent _).2 <| fun m ↦
        prop_of_retract
          (fun K : DModX ↦ ModuleDerived.IsMPseudoCoherent K m : ObjectProperty DModX) h
          ((ModuleDerived.isPseudoCoherent_iff_forall_isMPseudoCoherent _).1 hK m)

omit [CategoryWithHomology (Modules X)]
  [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)] in
/-- If `K ⊞ L` is pseudo-coherent in `D(𝒪_X)`, then both summands are
pseudo-coherent. -/
theorem isPseudoCoherent_summands_of_biprod (K L : DModX)
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    K.IsPseudoCoherent ∧ L.IsPseudoCoherent :=
  ⟨of_biprod_left PseudoCoherentObj hKL, of_biprod_right PseudoCoherentObj hKL⟩

omit [CategoryWithHomology (Modules X)]
  [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)] in
/-- Lemma 20.47.6 (3): if `K ⊞ L` is pseudo-coherent in `D(𝒪_X)`, then `K` is
pseudo-coherent. -/
@[stacks 08CE]
theorem isPseudoCoherent_left_of_biprod (K L : DModX)
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    K.IsPseudoCoherent :=
  (isPseudoCoherent_summands_of_biprod K L hKL).1

omit [CategoryWithHomology (Modules X)]
  [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)] in
/-- Lemma 20.47.6 (4): if `K ⊞ L` is pseudo-coherent in `D(𝒪_X)`, then `L` is
pseudo-coherent. -/
@[stacks 08CE]
theorem isPseudoCoherent_right_of_biprod (K L : DModX)
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    L.IsPseudoCoherent :=
  (isPseudoCoherent_summands_of_biprod K L hKL).2

end AlgebraicGeometry.RingedSpace
