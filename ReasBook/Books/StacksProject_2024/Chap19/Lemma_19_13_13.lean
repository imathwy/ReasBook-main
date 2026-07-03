import Mathlib
import StacksProject_2024.Chap19.Lemma_19_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/-
Domain-style sampling for Lemma 19.13.13:
- primary domain: bifiltered complexes in a Grothendieck abelian category, with each filtration
  realizing an inverse system in the derived category;
- sampled owner declarations:
  `FilteredComplex`,
  `FilteredComplex.RealizesInverseSystem`,
  `FilteredComplex.underlying`,
  `Cocone.mk`,
  `FilteredObject`;
- best owner abstraction: the two filtered-complex owners carried by a bifiltered complex, namely
  the first filtration `K.base` and the second filtration `K.second`;
- primitive data: two filtered complexes with a common underlying cochain complex;
- derived API: the realization predicates for the two inverse-system cocones, together with the
  common-underlying comparison `K.underlying_eq`;
- source/core/bridge triage:
  `source-facing`: the existence theorem below for one bifiltered complex realizing two inverse
    systems with common target;
  `core/canonical`: `FilteredComplex A` together with
    `FilteredComplex.RealizesInverseSystem`;
  `bridge/view`: the common-underlying equality between the two filtered-complex owners.

The previous downstream API duplicated the owner-level `FilteredComplex` abstraction by storing
the second filtration degreewise and then rebuilding a filtered complex from that stagewise data.
This file keeps the source-facing bifiltered owner, but its primitive fields now live directly at
the canonical `FilteredComplex` layer reused from Lemma 19.13.12. -/

attribute [local instance] HasDerivedCategory.standard

/-- A bifiltered cochain complex is a filtered cochain complex together with a second decreasing
filtration on the same underlying complex that is preserved by the differentials. -/
structure BifilteredCochainComplex (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The first filtration on the complex. -/
  base : FilteredComplex A
  /-- The second filtration on the same underlying cochain complex. -/
  second : FilteredComplex A
  /-- The two filtered-complex owners have the same underlying cochain complex. -/
  underlying_eq : second.underlying = base.underlying

namespace BifilteredCochainComplex

variable (K : BifilteredCochainComplex A)

omit [IsGrothendieckAbelian.{w} A] in
@[simp] theorem second_underlying :
    K.second.underlying = K.base.underlying := K.underlying_eq

end BifilteredCochainComplex

-- Proof sketch: first choose a filtered realization of the system `E^i ⟶ E` as in Lemma
-- `19.13.12`, then choose a second filtered realization of `(E')^i ⟶ E`. Replace the first one by
-- a filtered K-injective complex using Lemma `19.13.7`, map the second realization into that
-- K-injective representative, and add an acyclic K-injective correction so that both maps into a
-- common target become termwise injective quasi-isomorphisms. Transport the two filtrations by
-- images to the common target to obtain the required bifiltered complex.
/-- Lemma 19.13.13: given two compatible inverse systems `E^i ⟶ E` and `(E')^i ⟶ E` in the
derived category of a Grothendieck abelian category, there exists a bifiltered cochain complex
whose underlying complex represents `E`, whose first filtration stages `F^i K^•` represent
`E^i`, and whose second filtration stages `(F')^i K^•` represent `(E')^i`, compatibly with the
given maps. -/
theorem exists_bifilteredCochainComplexRealization_of_inverseSystems
    (system system' : ℤᵒᵖ ⥤ DerivedCategory A) (E : DerivedCategory A)
    (π : system ⟶ (Functor.const ℤᵒᵖ).obj E)
    (π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E) :
    ∃ K : BifilteredCochainComplex A,
      K.base.RealizesInverseSystem (Cocone.mk E π) ∧
        K.second.RealizesInverseSystem (Cocone.mk E π') := sorry

end

end CategoryTheory
