import StacksProject_2024.Chap19.Lemma_19_12_2
import StacksProject_2024.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open ComplexShape
open HomotopyCategory

universe v u

namespace CategoryTheory
namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Abelian C]

local notation "Cpx" => CochainComplex C ℤ
/- Domain-style sampling for Lemma 19.12.3:
- primary domain: K-injective cochain complexes in an abelian category, detected by vanishing of
  morphisms from acyclic complexes in the homotopy category and refined here using the small
  bounded-above acyclic generators supplied abstractly by the first conclusion of
  Lemma `19.12.2`;
- sampled owner declarations:
  `CochainComplex.IsKInjective`,
  `CochainComplex.isKInjective_iff_rightOrthogonal`,
  `CochainComplex.isKInjective_iff_homotopyCategory_from_acyclic_eq_zero`,
  `CategoryTheory.IsBoundedAbove`;
- best owner abstraction: the canonical owner is the target complex `I : Cpx` with property
  `I.IsKInjective`; bounded-above acyclicity is expressed through the existing project owner
  `IsBoundedAbove`, and the termwise subobject-cardinality bound remains an auxiliary source-side
  hypothesis rather than a new packaged owner;
- primitive data: the cardinal `κ`, the bounded-above acyclic small-subcomplex conclusion of
  Lemma `19.12.2` for that `κ`, the complex `I`, and the termwise injectivity hypothesis
  `∀ j, Injective (I.X j)`;
- derived API: the vanishing statement in the homotopy category for bounded-above acyclic
  `κ`-small complexes, which is a source-facing bridge to the canonical owner `I.IsKInjective`.

Source/core/bridge triage:
- `source-facing`: the Stacks-style reduction criterion saying it suffices to test vanishing on the
  bounded-above acyclic `κ`-small complexes produced by the first conclusion of
  Lemma `19.12.2`;
- `core/canonical`: `CochainComplex.IsKInjective`;
- `bridge/view`: the homotopy-category vanishing condition
  `∀ f : (quotient C (up ℤ)).obj M ⟶ (quotient C (up ℤ)).obj I, f = 0` for the chosen source
  complexes.
-/

-- Proof sketch: use the nonzero bounded-above acyclic `κ`-small subcomplexes from the first
-- conclusion of Lemma `19.12.2` inside any nonzero acyclic complex. The termwise injectivity of
-- `I` lets one descend along these subcomplexes and force vanishing in the homotopy category,
-- contradicting the existence of a nonzero morphism from an acyclic source. The canonical owner
-- theorem `CochainComplex.isKInjective_iff_homotopyCategory_from_acyclic_eq_zero` then upgrades
-- this vanishing criterion to K-injectivity.
/-- Lemma 19.12.3: if `κ` satisfies the bounded-above acyclic small-subcomplex conclusion of
Lemma `19.12.2`, a cochain complex `I`
with injective terms is K-injective provided that every morphism in the homotopy category from a
bounded-above acyclic complex whose terms have at most `κ` subobjects to `I` is zero. -/
theorem isKInjective_of_termwise_injective_of_small_boundedAbove_acyclic_vanishing
    (κ : Cardinal)
    (hκ_sub :
      ∀ (M : Cpx) (_ : M.Acyclic) (_ : ¬ IsZero M),
        ∃ N : Subobject M,
          ¬ IsZero (N : Cpx) ∧
            IsBoundedAbove (N : Cpx) ∧
            (N : Cpx).Acyclic ∧
            ∀ n : ℤ, Cardinal.mk (Subobject ((N : Cpx).X n)) ≤ κ)
    (I : Cpx) (hI : ∀ j : ℤ, Injective (I.X j))
    (hvanish :
      ∀ (M : Cpx)
        (hM_bounded : IsBoundedAbove M)
        (hM_acyclic : M.Acyclic)
        (hM_size : ∀ n : ℤ, Cardinal.mk (Subobject (M.X n)) ≤ κ)
        (f : (quotient C (up ℤ)).obj M ⟶ (quotient C (up ℤ)).obj I), f = 0) :
    I.IsKInjective := sorry

end

end CochainComplex
end CategoryTheory
