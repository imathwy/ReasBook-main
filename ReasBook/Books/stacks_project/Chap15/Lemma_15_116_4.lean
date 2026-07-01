import Mathlib
import stacks_project.Chap15.Definition_15_116_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped TensorProduct

universe u v w x y z

/- Domain-style sampling for Lemma 15.116.4:
- primary domain: finite base change of extensions of discrete valuation rings, organized around
  the chapter solution predicates and reduced tensor-product field-factor decompositions;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsSolutionFor`,
  `exists_fractionRingTensorProduct_decomposition_with_unramifiedFactors`,
  `isExtensionOfDiscreteValuationRings_localizationBranch`;
- best owner abstraction: the source-facing solution predicates are already owned by
  `Definition_15_116_1`, so this file should reuse `IsWeakSolutionFor` / `IsSolutionFor` directly;
  the reduced tensor-product decomposition hypothesis is only bridge/view data and should be
  stated with the canonical `L`-algebra product decomposition shape used nearby in
  `Lemma_15_115_9`;
- primitive-vs-derived split: the primitive data are the DVR tower `A ⊂ B ⊂ C`, fraction fields
  `K ⊂ L ⊂ M`, the finite extension `K₁ / K`, and a decomposition of `((L ⊗[K] K₁)_red)` into
  field factors; the weak/solution conditions on those factors are derived API via the chapter
  owners.

Source/core/bridge triage:
- `source-facing`: the four ascent/descent theorems of Lemma `15.116.4`;
- `core/canonical`: `IsWeakSolutionFor` and `IsSolutionFor` from `Definition_15_116_1`;
- `bridge/view`: the explicit `L`-algebra product decomposition hypotheses for
  `((L ⊗[K] K₁)_red)`, which relate its field factors to the chapter solution predicates for
  `B ⊂ C`.
-/

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type z} {K1 : Type (max x y z)}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra B M] [Algebra C M] [Algebra K M] [Algebra L M]
variable [IsFractionRing C M]
variable [IsScalarTower A C M] [IsScalarTower A K M]
variable [IsScalarTower B C M] [IsScalarTower B L M]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)

-- Proof sketch: localize the integral closure `A1 = integralClosure A K1` at a maximal ideal and
-- compare the corresponding branches of `A1 ⊗[A] B` and `A1 ⊗[A] C`. If the branch over `C` is
-- weakly unramified, then every intermediate local extension of discrete valuation rings remains
-- weakly unramified by multiplicativity of ramification indices in towers.
/-- Lemma 15.116.4 (1): if `K1 / K` is a weak solution for `A → C`, then it is a weak solution for
`A → B`. -/
theorem weakSolutionFor_of_weakSolutionFor_comp
    (hK1 : IsWeakSolutionFor A C K M K1) :
    IsWeakSolutionFor A B K L K1 := sorry

-- Proof sketch: use the weak-solution descent from the previous clause together with
-- Lemma `15.112.5`: separability of the residue-field extension for the branch over `C` implies
-- separability for the intermediate branch over `B`, so every solution branch over `C` yields a
-- solution branch over `B`.
/-- Lemma 15.116.4 (2): if `K1 / K` is a solution for `A → C`, then it is a solution for `A → B`.
-/
theorem solutionFor_of_solutionFor_comp
    (hK1 : IsSolutionFor A C K M K1) :
    IsSolutionFor A B K L K1 := sorry

-- Proof sketch: write `L1 = ((L ⊗[K] K1)_red)` as a finite product of fields by hypothesis. For
-- each factor field, choose the corresponding weak solution branch for `B → C`, and combine it
-- with the given weak solution branches for `A → B`. The local tower criterion for ramification
-- indices then shows that the induced branches for `A → C` are weakly unramified.
/-- Lemma 15.116.4 (3): if `K1 / K` is a weak solution for `A → B` and
`((L ⊗[K] K1)_red)` is a product of fields that are weak solutions for `B → C`, then `K1 / K` is
a weak solution for `A → C`. -/
theorem weakSolutionFor_comp_of_weakSolutionFor_of_reducedTensorProductFactors
    (hAB : IsWeakSolutionFor A B K L K1)
    (hBC :
      ∃ (ι : Type u) (_ : Fintype ι) (F : ι → Type (max u v w x y))
        (_ : ∀ i, Field (F i))
        (_ : ∀ i, Algebra B (F i))
        (_ : ∀ i, Algebra L (F i))
        (_ : ∀ i, IsScalarTower B L (F i))
        (_ : ∀ i, FiniteDimensional L (F i)),
        Nonempty (L1 ≃ₐ[L] ∀ i, F i) ∧ ∀ i, IsWeakSolutionFor B C L M (F i)) :
    IsWeakSolutionFor A C K M K1 := sorry

-- Proof sketch: refine the preceding ascent argument with Lemma `15.112.5`: the factor branches
-- for `B → C` have separable residue-field extensions, and separability is preserved when passing
-- to the composite local branch over `A`. Together with weakly unramifiedness, this yields a
-- solution branch for `A → C`.
/-- Lemma 15.116.4 (4): if `K1 / K` is a solution for `A → B` and `((L ⊗[K] K1)_red)` is a
product of fields that are solutions for `B → C`, then `K1 / K` is a solution for `A → C`. -/
theorem solutionFor_comp_of_solutionFor_of_reducedTensorProductFactors
    (hAB : IsSolutionFor A B K L K1)
    (hBC :
      ∃ (ι : Type u) (_ : Fintype ι) (F : ι → Type (max u v w x y))
        (_ : ∀ i, Field (F i))
        (_ : ∀ i, Algebra B (F i))
        (_ : ∀ i, Algebra L (F i))
        (_ : ∀ i, IsScalarTower B L (F i))
        (_ : ∀ i, FiniteDimensional L (F i)),
        Nonempty (L1 ≃ₐ[L] ∀ i, F i) ∧ ∀ i, IsSolutionFor B C L M (F i)) :
    IsSolutionFor A C K M K1 := sorry

end
