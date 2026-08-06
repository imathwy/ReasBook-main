import Mathlib.RingTheory.TensorProduct.Maps
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Proposition_24_1_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Theorem_24_2_1

open scoped ComplexKTheory TensorProduct

noncomputable section

universe u

/- Semantic recall via `lean_leansearch` did not surface a verified Bott-periodicity owner in the
current environment. This file therefore keeps the source-facing Bott external-product map at the
specification level: a Bott map is required to agree with the canonical pullbacks on honest bundle
classes and with the textbook pure-tensor formula, while the concrete quotient-lifted map data is
left abstract until its well-definedness is proved without quotient-level `sorryAx`. -/

/-- The first projection `X × S² ⟶ X` in `TopCat`. -/
abbrev bottLeftProjection (X : Type u) [TopologicalSpace X] :
    TopCat.of (X × SphereTwo) ⟶ TopCat.of X :=
  TopCat.ofHom ContinuousMap.fst

/-- The second projection `X × S² ⟶ S²` in `TopCat`. -/
abbrev bottRightProjection (X : Type u) [TopologicalSpace X] :
    TopCat.of (X × SphereTwo) ⟶ SphereTwo :=
  TopCat.ofHom ContinuousMap.snd

/-- A map `K(X) ⊗[ℤ] K(S²) → K(X × S²)` is a Bott external-product map when it is computed from
the two projection pullbacks on `K`-theory and satisfies the textbook pure-tensor formula.
This is bridge/view API: the source-facing pullback behavior is explicit, but the actual
quotient-lifted map data is not fixed until its well-definedness is proved without `sorryAx`. -/
def IsBottTensorProductMap
    (X : Type u) [TopologicalSpace X]
    (bottTensorProductMap : K(X) ⊗[ℤ] K(SphereTwo) →+ K(X × SphereTwo)) : Prop :=
  ∃ bottLeftPullback : K(X) →+ K(X × SphereTwo),
    ∃ bottRightPullback : K(SphereTwo) →+ K(X × SphereTwo),
      IsComplexKTheoryPresentationPullback (bottLeftProjection X) bottLeftPullback ∧
      IsComplexKTheoryPresentationPullback (bottRightProjection X) bottRightPullback ∧
      ∀ x : K(X), ∀ y : K(SphereTwo),
        bottTensorProductMap (x ⊗ₜ[ℤ] y) =
          bottLeftPullback x * bottRightPullback y

/-- A Bott external-product map comes with projection pullbacks on `K(X)` and `K(S²)` whose
bundle-level behavior is the canonical pullback along the two projections. -/
theorem IsBottTensorProductMap.spec
    {X : Type u} [TopologicalSpace X]
    {bottTensorProductMap : K(X) ⊗[ℤ] K(SphereTwo) →+ K(X × SphereTwo)}
    (hBott : IsBottTensorProductMap X bottTensorProductMap) :
    ∃ bottLeftPullback : K(X) →+ K(X × SphereTwo),
      ∃ bottRightPullback : K(SphereTwo) →+ K(X × SphereTwo),
        IsComplexKTheoryPresentationPullback (bottLeftProjection X) bottLeftPullback ∧
        IsComplexKTheoryPresentationPullback (bottRightProjection X) bottRightPullback ∧
        ∀ x : K(X), ∀ y : K(SphereTwo),
          bottTensorProductMap (x ⊗ₜ[ℤ] y) =
            bottLeftPullback x * bottRightPullback y :=
  hBott

/-- On pure tensors, a Bott external-product map multiplies the two projection pullbacks. -/
theorem IsBottTensorProductMap.tmul
    {X : Type u} [TopologicalSpace X]
    {bottTensorProductMap : K(X) ⊗[ℤ] K(SphereTwo) →+ K(X × SphereTwo)}
    (hBott : IsBottTensorProductMap X bottTensorProductMap)
    (x : K(X)) (y : K(SphereTwo)) :
    ∃ bottLeftPullback : K(X) →+ K(X × SphereTwo),
      ∃ bottRightPullback : K(SphereTwo) →+ K(X × SphereTwo),
        bottTensorProductMap (x ⊗ₜ[ℤ] y) =
          bottLeftPullback x * bottRightPullback y := by
  rcases hBott with ⟨bottLeftPullback, bottRightPullback, -, -, htmul⟩
  exact ⟨bottLeftPullback, bottRightPullback, htmul x y⟩

/-- Bott periodicity supplies a Bott external-product map for every compact space `X`. -/
theorem bottTensorProductMap_exists
    {X : Type u} [TopologicalSpace X] [CompactSpace X] :
    ∃ bottTensorProductMap : K(X) ⊗[ℤ] K(SphereTwo) →+ K(X × SphereTwo),
      IsBottTensorProductMap X bottTensorProductMap := by
  sorry

/-- Theorem 24.2.2: Bott periodicity for the two-sphere says that for every compact space `X`,
every Bott external-product map `K(X) ⊗[ℤ] K(S²) → K(X × S²)` is bijective. -/
theorem bottPeriodicity_tensorProductMap_bijective
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (bottTensorProductMap : K(X) ⊗[ℤ] K(SphereTwo) →+ K(X × SphereTwo))
    (hBott : IsBottTensorProductMap X bottTensorProductMap) :
    Function.Bijective bottTensorProductMap := by
  sorry

/-- Bott periodicity makes every Bott external-product map injective. -/
theorem bottTensorProductMap_injective
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (bottTensorProductMap : K(X) ⊗[ℤ] K(SphereTwo) →+ K(X × SphereTwo))
    (hBott : IsBottTensorProductMap X bottTensorProductMap) :
    Function.Injective bottTensorProductMap :=
  (bottPeriodicity_tensorProductMap_bijective bottTensorProductMap hBott).1

/-- Bott periodicity makes every Bott external-product map surjective. -/
theorem bottTensorProductMap_surjective
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (bottTensorProductMap : K(X) ⊗[ℤ] K(SphereTwo) →+ K(X × SphereTwo))
    (hBott : IsBottTensorProductMap X bottTensorProductMap) :
    Function.Surjective bottTensorProductMap :=
  (bottPeriodicity_tensorProductMap_bijective bottTensorProductMap hBott).2
