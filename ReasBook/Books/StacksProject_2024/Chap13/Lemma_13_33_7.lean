import Mathlib
import stacks_project.Chap13.Definition_13_33_1
import stacks_project.Chap13.Lemma_13_33_5
import stacks_project.Chap13.Lemma_13_33_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open CategoryTheory.Pretriangulated
open DerivedCategory

universe w v u

noncomputable section

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable [HasColimitsOfShape ℕ 𝒜] [HasExactColimitsOfShape ℕ 𝒜]

/- Domain-style sampling for Lemma 13.33.7:
- primary domain: homotopy colimits in derived categories, obtained from the telescope triangle of
  a sequential diagram of cochain complexes;
- inspected owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.derivedCategory_Q_preserves_countableCoproduct`,
  `CategoryTheory.sequentialTelescope_shortExact`;
- best owner abstraction:
  the source-facing datum is the sequential diagram `S : ℕ ⥤ CochainComplex 𝒜 ℤ`, and the
  canonical owner for the conclusion is `IsHomotopyColimitOf (S ⋙ DerivedCategory.Q)`;
- primitive-vs-derived split:
  the primitive data are only the diagram `S`;
  the countable coproduct in `DerivedCategory 𝒜` and the distinguished telescope triangle are
  derived API coming from the Chapter 13 coproduct-preservation bridge and the exact telescope
  short exact sequence.

Source/core/bridge triage:
- `source-facing`: the termwise colimit complex represents a homotopy colimit of the image
  sequence in the derived category;
- `core/canonical`: `IsHomotopyColimitOf (S ⋙ DerivedCategory.Q)`;
- `bridge/view`: the local countable-coproduct bridge on `𝒜`, together with
  `derivedCategory_hasCountableCoproducts_of_exactCountableCoproducts`, supplies the owner
  predicate with the needed coproduct of `Q.obj (S.obj n)`. -/

local instance : HasCountableCoproducts 𝒜 := hasCountableCoproducts_of_sequentialColimits

local instance : CountableAB4 𝒜 := by
  let _ : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts
  exact CountableAB4.of_countableAB5 𝒜

-- Proof sketch: exact sequential colimits give the short exact telescope sequence
-- `0 ⟶ ⨿ L_n^• ⟶ ⨿ L_n^• ⟶ colim L_n^• ⟶ 0`. Applying the localization functor
-- `CochainComplex 𝒜 ℤ ⥤ DerivedCategory 𝒜` and the canonical distinguished-triangle construction
-- for short exact sequences yields the standard telescope triangle, so the termwise colimit is
-- best recorded via the canonical owner `IsHomotopyColimitOf`.
/-- Lemma 13.33.7: if an abelian category admits exact sequential colimits, then the termwise
colimit of a sequential system of cochain complexes is a homotopy colimit of the induced
sequential diagram in the derived category. -/
theorem termwise_colimit_is_homotopy_colimit (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    IsHomotopyColimitOf (S ⋙ Q) (Q.obj (colimit S)) := by
  sorry

/-- The canonical map from the telescope coproduct `∐ Q(Sₙ)` to the derived image of the termwise
colimit complex. This is the source-facing map used when the homotopy-colimit presentation from
`termwise_colimit_is_homotopy_colimit` is expressed by the actual short exact telescope sequence of
`S`. -/
def termwise_colimit_presentation_map (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    ∐ (fun n ↦ Q.obj (S.obj n)) ⟶ Q.obj (colimit S) :=
  (PreservesCoproduct.iso Q S.obj).inv ≫ Q.map (Limits.Sigma.desc (colimit.ι S))

/-- The connecting morphism in the canonical telescope triangle presenting `Q.obj (colimit S)` as
a homotopy colimit of `S ⋙ Q`. -/
def termwise_colimit_presentation_connecting (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    Q.obj (colimit S) ⟶ (∐ fun n ↦ Q.obj (S.obj n))⟦(1 : ℤ)⟧ :=
  triangleOfSESδ (sequentialTelescope_shortExact S) ≫
    ((PreservesCoproduct.iso Q S.obj).hom⟦(1 : ℤ)⟧')

-- Proof sketch: start from the distinguished triangle `triangleOfSES` attached to the canonical
-- telescope short exact sequence of `S`, then transport its first two objects from
-- `Q.obj (∐ Sₙ)` to the actual coproduct `∐ Q(Sₙ)` using `PreservesCoproduct.iso Q S.obj`.
/-- The canonical telescope triangle for the termwise colimit complex is distinguished. This is
the explicit source-facing presentation underlying `termwise_colimit_is_homotopy_colimit`. -/
theorem termwise_colimit_presentation_distinguished (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    Triangle.mk
        (sequentialTelescopeMap (S ⋙ Q))
        (termwise_colimit_presentation_map S)
        (termwise_colimit_presentation_connecting S) ∈
      distTriang (DerivedCategory 𝒜) := by
  sorry

end

end CategoryTheory
