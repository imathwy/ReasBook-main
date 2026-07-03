import StacksProject_2024.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)

/- Domain-style sampling for Lemma 15.75.5:
- primary domain: perfect objects in the derived category `D(R)` as an object property, together
  with the generic retract/direct-summand API for additive categories;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the `core/canonical` owner is the object property `PerfectObj`; the
  textbook biproduct statement is a `bridge/view` specialization of the generic direct-summand API;
- primitive vs. derived:
  primitive data are the perfectness owner `DerivedCategory.IsPerfect` and its representative-based
  definition from Definition `15.75.1`;
  derived API is retract stability and the direct-summand consequence below.
-/

-- Proof sketch: choose a bounded finite-projective complex representing `K ⊞ L`; the projection
-- maps onto `K` and `L` split in the derived category, so degreewise splitting by projectivity
-- yields bounded finite-projective representatives of both summands.
/-- Perfect objects of `D(R)` are stable under retracts/direct summands. -/
instance perfectObjectProperty_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts PerfectObj where
  of_retract {X Y} h hY := by
    sorry

/-- Lemma 15.75.5: if the biproduct `K^• ⊕ L^•` is perfect, then both summands `K^•` and
`L^•` are perfect. -/
theorem isPerfect_summands_of_biprod
    (K L : DMod) (hKL : (K ⊞ L).IsPerfect) :
    K.IsPerfect ∧ L.IsPerfect :=
  ⟨of_biprod_left PerfectObj hKL, of_biprod_right PerfectObj hKL⟩

end

end CategoryTheory
