import StacksProject_2024.Chap20.Lemma_20_23_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Remark 20.23.5:
- primary domain: ordered and alternating Čech cochain complexes for a family of opens indexed by
  a type endowed with a chosen total order.
- sampled owner declarations:
  `orderedCechComplexOfOrder`,
  `alternatingCechComplex`,
  `orderedCechComparison`,
  `orderedCechComparisonOfOrderIso`.
- best owner abstraction: `orderedCechComplexOfOrder o 𝒰 F` from `Definition_20_23_2`, together
  with the canonical `IsIso (orderedCechComparison 𝒰 F)` instance from `Lemma_20_23_3`, viewed
  through the explicit-order bridge `orderedCechComparisonOfOrderIso`; this remark should remain
  at the `bridge/view` layer by comparing two order choices through the common alternating owner.

Source/core/bridge triage:
- `source-facing`: Remark 20.23.5, asserting that changing the total order on the index set does
  not change the ordered Čech complex up to canonical isomorphism.
- `core/canonical`: `orderedCechComplexOfOrder o 𝒰 F` and `alternatingCechComplex 𝒰 F`.
- `bridge/view`: the order-change isomorphism obtained by composing the canonical isomorphisms from
  each ordered complex to the alternating complex.

Primitive data versus derived API:
- primitive data: the two linear orders `o₁`, `o₂`, the cover `𝒰`, and the presheaf `F`.
- derived API: the comparison isomorphism between the two ordered Čech complexes. -/

/-- The ordered Čech complex for an explicit order `o` is canonically isomorphic to the
alternating Čech complex. -/
def orderedCechComparisonOfOrderIso (o : LinearOrder ι)
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    orderedCechComplexOfOrder o 𝒰 F ≅ alternatingCechComplex 𝒰 F :=
  let _ : LinearOrder ι := o
  asIso (orderedCechComparison 𝒰 F)

/-- Remark 20.23.5: two total orderings on the index set define canonically isomorphic ordered
Čech complexes, so the ordered Čech complex is independent of the chosen total ordering up to a
canonical isomorphism of complexes. -/
@[stacks 01FL]
def orderedCechComplexChangeOrderIso (o₁ o₂ : LinearOrder ι)
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    orderedCechComplexOfOrder o₁ 𝒰 F ≅ orderedCechComplexOfOrder o₂ 𝒰 F :=
  -- Compare both ordered complexes with the common alternating complex and invert the second
  -- comparison, matching the source formula `τ = π₂ ∘ c₁`.
  orderedCechComparisonOfOrderIso o₁ 𝒰 F ≪≫
    (orderedCechComparisonOfOrderIso o₂ 𝒰 F).symm

/-- The forward morphism of the order-change isomorphism is obtained by comparing the first
ordered Čech complex with the alternating complex and then applying the inverse comparison for the
second order. -/
@[simp] theorem orderedCechComplexChangeOrderIso_hom (o₁ o₂ : LinearOrder ι)
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (orderedCechComplexChangeOrderIso o₁ o₂ 𝒰 F).hom =
      (orderedCechComparisonOfOrderIso o₁ 𝒰 F).hom ≫
        (orderedCechComparisonOfOrderIso o₂ 𝒰 F).inv := rfl

/-- The inverse morphism of the order-change isomorphism is obtained by comparing the second
ordered Čech complex with the alternating complex and then projecting back to the first order. -/
@[simp] theorem orderedCechComplexChangeOrderIso_inv (o₁ o₂ : LinearOrder ι)
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (orderedCechComplexChangeOrderIso o₁ o₂ 𝒰 F).inv =
      (orderedCechComparisonOfOrderIso o₂ 𝒰 F).hom ≫
        (orderedCechComparisonOfOrderIso o₁ 𝒰 F).inv := rfl
