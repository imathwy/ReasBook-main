import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Corollary_20_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_4_3.Tangential
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_4_4.Normal
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_1_1

open AlgebraicTopology
open scoped Manifold

noncomputable section

-- Chapter 23 already fixes the canonical owners for mod-`2` cohomology algebras, canonical
-- singular Kronecker pairings, transported mod-`2` pairings, and the source-facing normal-bundle
-- compatibility predicate `IsNormalBundleOfEuclideanEmbedding`. This file keeps Theorem 25.1.4 at
-- the source-facing layer by comparing the partition-indexed Stiefel-Whitney numbers of two
-- closed smooth manifolds directly, while retaining the chosen smooth closed Euclidean embeddings
-- from the Chapter 23 setup and reusing those canonical owners instead of restating the low-level
-- chosen-data infrastructure.

section

variable {n : ℕ} (M N : ClosedSmoothManifold n)

/-- A compatible mod-`2` Stiefel-Whitney theory together with its chosen normalization data. -/
structure StiefelWhitneyTheory where
  H2 : ModTwoCohomologyTheory
  w : StiefelWhitneyClassFamily.{0} H2
  normalizationData : StiefelWhitneyNormalization H2
  isStiefelWhitneyTheory : IsStiefelWhitneyTheory H2 normalizationData w

/-- The Chapter 23 evaluation data on a closed smooth manifold needed to turn the chosen
Stiefel-Whitney classes into explicit mod-`2` characteristic-number evaluations. -/
structure StiefelWhitneyEvaluationSetup
    {n : ℕ} (X : ClosedSmoothManifold n) (theory : StiefelWhitneyTheory) where
  algebra : CanonicalModTwoCohomologyAlgebra theory.H2 (TopCat.of X.M)
  fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of X.M)
  isFundamentalClass : IsRFundamentalClass (ZMod 2) n X.M fundamentalClass
  canonicalKroneckerPairing :
    rSingularCohomology (ZMod 2) (TopCat.of X.M) n →ₗ[ZMod 2]
      rSingularHomology (ZMod 2) n (TopCat.of X.M) →ₗ[ZMod 2] ZMod 2
  isCanonicalKroneckerPairing :
    IsCanonicalRSingularKroneckerPairing
      (ZMod 2) (TopCat.of X.M) n canonicalKroneckerPairing
  kroneckerPairing :
    modTwoCohomologyGroup theory.H2 n (TopCat.of X.M) →+
      rSingularHomology (ZMod 2) n (TopCat.of X.M) →+ ZMod 2
  isTransport :
    IsModTwoSingularKroneckerTransport
      theory.H2 canonicalKroneckerPairing kroneckerPairing

/-- A fixed normal-bundle setup on `X` compatible with the Chapter 23 Stiefel-Whitney-number
construction. -/
structure NormalStiefelWhitneySetup
    {n : ℕ} (X : ClosedSmoothManifold n) (theory : StiefelWhitneyTheory)
    extends StiefelWhitneyEvaluationSetup X theory where
  r : ℕ
  embedding : X.M → EuclideanSpace ℝ (Fin (n + r))
  normalBundle : TopCat.of X.M → Type
  [normalTotalSpaceTopology :
    TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
  [normalFiberNormedAddCommGroup : ∀ b, NormedAddCommGroup (normalBundle b)]
  [normalFiberNormedSpace : ∀ b, NormedSpace ℝ (normalBundle b)]
  [normalFiberBundle : FiberBundle (Fin r → ℝ) normalBundle]
  [normalVectorBundle : VectorBundle ℝ (Fin r → ℝ) normalBundle]
  smoothEmbedding :
    ContMDiff (𝓡 n)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + r)))) ⊤ embedding
  isClosedEmbedding : Topology.IsClosedEmbedding embedding
  isNormalBundle : IsNormalBundleOfEuclideanEmbedding embedding normalBundle

attribute [instance] NormalStiefelWhitneySetup.normalTotalSpaceTopology
attribute [instance] NormalStiefelWhitneySetup.normalFiberNormedAddCommGroup
attribute [instance] NormalStiefelWhitneySetup.normalFiberNormedSpace
attribute [instance] NormalStiefelWhitneySetup.normalFiberBundle
attribute [instance] NormalStiefelWhitneySetup.normalVectorBundle

/-- A fixed tangential setup on `X` compatible with the Chapter 23 tangential
Stiefel-Whitney-number construction. -/
structure TangentialStiefelWhitneySetup
    {n : ℕ} (X : ClosedSmoothManifold n) (theory : StiefelWhitneyTheory)
    extends StiefelWhitneyEvaluationSetup X theory where
  [tangentTotalSpaceTopology :
    TopologicalSpace
      (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of X.M → Type _))]
  [tangentFiberBundle :
    FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of X.M → Type _)]
  [tangentVectorBundle :
    VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of X.M → Type _)]

attribute [instance] TangentialStiefelWhitneySetup.tangentTotalSpaceTopology
attribute [instance] TangentialStiefelWhitneySetup.tangentFiberBundle
attribute [instance] TangentialStiefelWhitneySetup.tangentVectorBundle

namespace NormalStiefelWhitneySetup

/-- The normal Stiefel-Whitney number determined by a fixed compatible setup. -/
def number {n : ℕ} {X : ClosedSmoothManifold n} {theory : StiefelWhitneyTheory}
    (setup : NormalStiefelWhitneySetup X theory) (σ : Nat.Partition n) : ZMod 2 :=
  setup.algebra.normalStiefelWhitneyNumber theory.w
    setup.r setup.normalBundle setup.fundamentalClass setup.kroneckerPairing σ

@[simp] theorem number_def
    {n : ℕ} {X : ClosedSmoothManifold n} {theory : StiefelWhitneyTheory}
    (setup : NormalStiefelWhitneySetup X theory) (σ : Nat.Partition n) :
    setup.number σ =
      setup.algebra.normalStiefelWhitneyNumber theory.w
        setup.r setup.normalBundle setup.fundamentalClass setup.kroneckerPairing σ :=
  rfl

end NormalStiefelWhitneySetup

namespace TangentialStiefelWhitneySetup

/-- The tangential Stiefel-Whitney number determined by a fixed compatible setup. -/
def number {n : ℕ} {X : ClosedSmoothManifold n} {theory : StiefelWhitneyTheory}
    (setup : TangentialStiefelWhitneySetup X theory) (σ : Nat.Partition n) : ZMod 2 :=
  -- Local instance justification (defeq pin): keep the stored tangent total-space topology for `X`.
  letI :
      TopologicalSpace
        (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of X.M → Type _)) :=
    setup.tangentTotalSpaceTopology
  -- Local instance justification (defeq pin): keep the stored tangent-bundle `FiberBundle` for `X`.
  letI :
      FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of X.M → Type _) :=
    setup.tangentFiberBundle
  -- Local instance justification (defeq pin): keep the stored tangent `VectorBundle` for `X`.
  letI :
      VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of X.M → Type _) :=
    setup.tangentVectorBundle
  setup.algebra.tangentialStiefelWhitneyNumber theory.w
    setup.fundamentalClass setup.kroneckerPairing σ

end TangentialStiefelWhitneySetup

/-- The equality of the normal Stiefel-Whitney numbers of two closed smooth `n`-manifolds,
recorded intrinsically by quantifying over a chosen Stiefel-Whitney theory and compatible
Chapter 23 normal-bundle setups on the two manifolds. -/
def normalStiefelWhitneyNumbersAgree (M N : ClosedSmoothManifold n) : Prop :=
  ∀ (theory : StiefelWhitneyTheory)
    (setupM : NormalStiefelWhitneySetup M theory)
    (setupN : NormalStiefelWhitneySetup N theory)
    (σ : Nat.Partition n),
      setupM.number σ = setupN.number σ

namespace normalStiefelWhitneyNumbersAgree

/-- A proof of `normalStiefelWhitneyNumbersAgree M N` specializes to any fixed Chapter 23 setup
on `M` and `N` and any partition `σ`, given by smooth closed Euclidean embeddings, compatible
normal bundles, fundamental classes, and transported mod-`2` Kronecker pairings. -/
theorem in_setup
    (h_agree : normalStiefelWhitneyNumbersAgree M N)
    (theory : StiefelWhitneyTheory)
    (setupM : NormalStiefelWhitneySetup M theory)
    (setupN : NormalStiefelWhitneySetup N theory)
    (σ : Nat.Partition n) :
    setupM.number σ = setupN.number σ :=
  h_agree theory setupM setupN σ

/-- Agreement of normal Stiefel-Whitney numbers is symmetric in the two closed smooth
`n`-manifolds. -/
theorem symm
    (h_agree : normalStiefelWhitneyNumbersAgree M N) :
    normalStiefelWhitneyNumbersAgree N M := by
  intro theory setupN setupM σ
  exact Eq.symm <| h_agree theory setupM setupN σ

end normalStiefelWhitneyNumbersAgree

/-- The equality of the tangential Stiefel-Whitney numbers of two closed smooth `n`-manifolds,
recorded intrinsically by quantifying over a chosen Stiefel-Whitney theory and compatible
Chapter 23 tangential setups on the two manifolds. -/
def tangentialStiefelWhitneyNumbersAgree (M N : ClosedSmoothManifold n) : Prop :=
  ∀ (theory : StiefelWhitneyTheory)
    (setupM : TangentialStiefelWhitneySetup M theory)
    (setupN : TangentialStiefelWhitneySetup N theory)
    (σ : Nat.Partition n),
      setupM.number σ = setupN.number σ

namespace tangentialStiefelWhitneyNumbersAgree

/-- A proof of `tangentialStiefelWhitneyNumbersAgree M N` specializes to any fixed Chapter 23
setup on `M` and `N` and any partition `σ`, determined by compatible fundamental classes and
transported mod-`2` Kronecker pairings. -/
theorem in_setup
    (h_agree : tangentialStiefelWhitneyNumbersAgree M N)
    (theory : StiefelWhitneyTheory)
    (setupM : TangentialStiefelWhitneySetup M theory)
    (setupN : TangentialStiefelWhitneySetup N theory)
    (σ : Nat.Partition n) :
    setupM.number σ = setupN.number σ :=
  h_agree theory setupM setupN σ

/-- Agreement of tangential Stiefel-Whitney numbers is symmetric in the two closed smooth
`n`-manifolds. -/
theorem symm
    (h_agree : tangentialStiefelWhitneyNumbersAgree M N) :
    tangentialStiefelWhitneyNumbersAgree N M := by
  intro theory setupN setupM σ
  exact Eq.symm <| h_agree theory setupM setupN σ

end tangentialStiefelWhitneyNumbersAgree

/-- Theorem 25.1.4 (1). Two smooth closed `n`-manifolds are cobordant if and only if their
normal Stiefel-Whitney numbers agree, in the intrinsic Chapter 25 sense recorded by
`normalStiefelWhitneyNumbersAgree M N`. -/
theorem cobordant_iff_normalStiefelWhitneyNumbersAgree :
    cobordant n M N ↔ normalStiefelWhitneyNumbersAgree M N := sorry

namespace normalStiefelWhitneyNumbersAgree

/-- Theorem 25.1.4 (2). For two smooth closed `n`-manifolds, equality of the normal
Stiefel-Whitney numbers is equivalent to equality of the tangential Stiefel-Whitney numbers. -/
theorem iff_tangential :
    normalStiefelWhitneyNumbersAgree M N ↔ tangentialStiefelWhitneyNumbersAgree M N := sorry

/-- A cobordism between `M` and `N` forces agreement of their normal Stiefel-Whitney numbers. -/
theorem of_cobordant
    (h_cobordant : cobordant n M N) :
    normalStiefelWhitneyNumbersAgree M N :=
  Iff.mp (_root_.cobordant_iff_normalStiefelWhitneyNumbersAgree M N) h_cobordant

/-- Agreement of the normal Stiefel-Whitney numbers of `M` and `N` detects cobordism. -/
theorem cobordant
    (h_agree : normalStiefelWhitneyNumbersAgree M N) :
    cobordant n M N :=
  Iff.mpr (_root_.cobordant_iff_normalStiefelWhitneyNumbersAgree M N) h_agree

/-- Agreement of normal Stiefel-Whitney numbers implies agreement of tangential
Stiefel-Whitney numbers. -/
theorem tangential
    (h_agree : normalStiefelWhitneyNumbersAgree M N) :
    tangentialStiefelWhitneyNumbersAgree M N :=
  Iff.mp (iff_tangential M N) h_agree

/-- Agreement of tangential Stiefel-Whitney numbers implies agreement of normal
Stiefel-Whitney numbers. -/
theorem of_tangential
    (h_agree : tangentialStiefelWhitneyNumbersAgree M N) :
    normalStiefelWhitneyNumbersAgree M N :=
  Iff.mpr (iff_tangential M N) h_agree

end normalStiefelWhitneyNumbersAgree

end
