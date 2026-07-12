import Mathlib
import StacksProject_2024.Chap13.Definition_13_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open scoped CategoryTheory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-
Domain-style sampling:
- primary domain: bounded-below injective resolutions viewed in the bounded-below homotopy
  category;
- sampled owner declarations:
  `CochainComplex.ResolutionFunctorOne`,
  `CategoryTheory.HomotopyResolutionFunctor`,
  `CategoryTheory.ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)`,
  `CochainComplex.InjectivePlus.toHomotopy`,
  `HomotopyCategory.Plus.quotient`;
- best owner abstraction: `CategoryTheory.HomotopyResolutionFunctor` is the canonical owner for
  the homotopy-category realization, while `ResolutionFunctorOne` is only the source-facing
  objectwise choice of injective resolutions;
- primitive data: `R : ResolutionFunctorOne 𝒜`;
- derived API: the induced object of `K^+(\mathcal I)`, the comparison morphism in
  `K^+(\mathcal A)`, and the bridge predicate comparing `R` with a homotopy resolution
  functor through explicit objectwise isomorphisms in `K^+(\mathcal I)`.

Source/core/bridge triage:
- `source-facing`: `ResolutionFunctorOne 𝒜`;
- `core/canonical`: `CategoryTheory.HomotopyResolutionFunctor 𝒜`;
- `bridge/view`: `ResolutionFunctorOne.homotopyObj`, `ResolutionFunctorOne.homotopyι`, and
  `ResolutionFunctorOne.RealizedBy`.
-/
namespace ResolutionFunctorOne

local notation "Qplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "KinjIncl" =>
  ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)

/-- The chosen injective resolution `j(K)` viewed as an object of `K^+(\mathcal I)`. -/
abbrev homotopyObj (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    K⁺ᵢ(𝒜) :=
  ⟨(Qplus).obj (R K : Plus 𝒜), fun n ↦ by
    simpa using (R K).injective n⟩

/-- The comparison map `K ⟶ j(K)` viewed in `K^+(\mathcal A)`. -/
abbrev homotopyι (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    (Qplus).obj K ⟶ (KinjIncl).obj (R.homotopyObj K) :=
  (Qplus).map ⟨(R K).ι⟩

/-- A homotopy resolution functor realizes `R` when, on each bounded-below complex `K`, its
value is canonically isomorphic to the chosen object `j(K)`, and after transporting along that
isomorphism its comparison morphism agrees in `K^+(\mathcal A)` with the chosen
quasi-isomorphism `K ⟶ j(K)`. -/
def RealizedBy (R : ResolutionFunctorOne 𝒜)
    (j : HomotopyResolutionFunctor 𝒜) : Prop :=
  ∀ K : Plus 𝒜, ∃! eK : j.toFunctor.obj ((Qplus).obj K) ≅ R.homotopyObj K,
    j.ι.app ((Qplus).obj K) ≫ (KinjIncl).map eK.hom = homotopyι R K

end ResolutionFunctorOne

-- Route correction: `HomotopyResolutionFunctor` and `K⁺ᵢ(𝒜)` now come from the earlier owner
-- file `Definition_13_23_2`, so this realization theorem no longer validates through the later
-- exactness file `Lemma_13_23_5`.
-- Proof sketch: for each morphism of bounded-below complexes, Lemmas 13.18.6 and 13.18.7 give a
-- unique induced morphism between the chosen injective resolutions in the homotopy category.
-- Those unique lifts force preservation of identities and composition, so the objectwise
-- resolution data extends uniquely to the canonical homotopy-category owner
-- `CategoryTheory.HomotopyResolutionFunctor`.
/-- Lemma 13.23.3: a resolution functor 1 on bounded-below cochain complexes admits a unique
homotopy-category realization. Equivalently, there is a unique
`HomotopyResolutionFunctor 𝒜` equipped with the canonical objectwise isomorphisms whose
comparison morphisms agree in `K^+(\mathcal A)` with the chosen quasi-isomorphisms of `R`. -/
theorem existsUnique_homotopyResolutionFunctor_of_resolutionFunctorOne
    (R : ResolutionFunctorOne 𝒜) :
    ∃! j : HomotopyResolutionFunctor 𝒜, R.RealizedBy j := sorry

end CochainComplex
