import Mathlib
import stacks_project.Chap13.Definition_13_15_3
import stacks_project.Chap13.Lemma_13_15_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped CategoryTheory ZeroObject

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- 
Domain-style sampling for Lemma 13.15.6:
- primary domain: bounded-below right-derived acyclicity obtained from bounded-below resolutions
  by a chosen object property `P`;
- sampled owner declarations:
  `ObjectProperty.HasMonoEmbedding`,
  `ObjectProperty.IsClosedUnderQuotients`,
  `Functor.ComputesRightDerivedAt`,
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `Functor.computesRightDerivedAt_of_mem_subset`;
- best owner abstraction: the source-facing data here is the object property `P` together with the
  exactness hypothesis; the canonical owner for the embedding hypothesis is
  `ObjectProperty.HasMonoEmbedding`, the canonical owner for closure under quotients is
  `ObjectProperty.IsClosedUnderQuotients`, and the target acyclicity notion is the chapter owner
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`;
- primitive data: `P`, the mono-embedding owner for `P`, the quotient-closure owner for `P`,
  and the hypothesis that `F` preserves short exactness on those short complexes;
- derived API: the acyclicity statement for the degree-zero object `A[0]` in `K⁺(𝒜)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, specialized to objects `A ∈ P`;
- `core/canonical`: `ObjectProperty.HasMonoEmbedding`,
  `ObjectProperty.IsClosedUnderQuotients`, `Functor.ComputesRightDerivedAt`, and
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`;
- `bridge/view`: this theorem, which turns the source-facing object-property hypotheses into the
  canonical bounded-below acyclicity owner. -/

-- Proof sketch: apply Lemma 13.15.5 to produce, from any bounded-below complex, a
-- quasi-isomorphic bounded-below complex whose terms lie in `P`. The short-exact-sequence
-- hypotheses first imply that `P` contains a zero object, so Lemma 13.15.5 applies to produce,
-- from any bounded-below complex, a quasi-isomorphic bounded-below complex whose terms lie in
-- `P`. The short-exact-sequence hypotheses imply that applying `F` to such a resolution remains
-- exact, so quasi-isomorphisms between these resolutions become isomorphisms after applying `F`.
-- Lemma 13.14.15 then shows that every degree-zero object `A[0]` with `A ∈ P` computes the
-- pointwise right derived functor.
/-- Lemma 13.15.6: if every object admits a monomorphism into an object of `P`, and if `P` is
stable under the quotients occurring in short exact sequences on which applying `F` stays short
exact, then every object `A` of `P` is acyclic for the bounded-below right derived functor of
`F`, i.e. the degree-zero complex `A[0]` computes that pointwise right derived functor. -/
private instance containsZero_of_hasMonoEmbedding_and_isClosedUnderQuotients
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients] :
    P.ContainsZero where
  exists_zero := by
    obtain ⟨Y, hY, _, _⟩ := (inferInstance : P.HasMonoEmbedding).exists_mono (0 : 𝒜)
    let S : ShortComplex 𝒜 := ShortComplex.mk (𝟙 Y) (0 : Y ⟶ 0) (by simp)
    have hS : S.ShortExact := by
      refine ShortComplex.Splitting.shortExact ?_
      exact
        { r := 𝟙 Y
          s := 0
          f_r := by simp [S]
          s_g := by simp [S]
          id := by simp [S] }
    exact ⟨0, isZero_zero 𝒜, by simpa [S] using P.prop_X₃_of_shortExact hS hY⟩

/-- Lemma 13.15.6: if every object admits a monomorphism into an object of `P`, and if `P` is
stable under the quotients occurring in short exact sequences on which applying `F` stays short
exact, then every object `A` of `P` is acyclic for the bounded-below right derived functor of
`F`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_of_mem
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A := sorry

end

end CategoryTheory
