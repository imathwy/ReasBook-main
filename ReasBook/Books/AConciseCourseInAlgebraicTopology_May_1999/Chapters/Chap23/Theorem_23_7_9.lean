import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Construction_20_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.ManifoldEulerCharacteristic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_5_4

open CategoryTheory
open scoped Manifold TensorProduct

noncomputable section

section

variable {K : Type} [Field K]
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [T2Space M] [CompactSpace M]
variable [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)]
variable [IsManifold (𝓡 n) ⊤ M]
variable
  [TopologicalSpace
    (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _))]
variable [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]
variable
  [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]

-- `TangentSpace (𝓡 n) b` is definitionally the Euclidean model space.  Mathlib deliberately does
-- not register its transported norm globally (it can conflict with a chosen Riemannian norm), so
-- select the canonical model norm locally for the one-point compactification used by the Thom
-- construction.
local instance tangentSpaceNormedAddCommGroup (b : M) :
    NormedAddCommGroup (TangentSpace (𝓡 n) b) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))

local instance tangentSpaceNormedSpace (b : M) :
    NormedSpace ℝ (TangentSpace (𝓡 n) b) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))

local notation "tangentThomReducedCohomology" =>
  thomReducedCohomology n (TangentSpace (𝓡 n) : TopCat.of M → Type _)

/-- The square `μ ∪ μ` of an integral Thom class of the tangent bundle, formed with the
relative cup product of the chosen multiplicative integral pair-cohomology theory. -/
noncomputable def tangentThomClassSquare
    (H : MultiplicativePairCohomologyTheory ℤ)
    (fiberRestriction :
      ∀ b : M,
        tangentThomReducedCohomology H (n : ℤ) →ₗ[ℤ]
          reducedCohomology H (n : ℤ)
            (compactifiedFiberSphere ((TangentSpace (𝓡 n) : TopCat.of M → Type _) b)))
    (mu : ThomClass H fiberRestriction) :
    tangentThomReducedCohomology H ((n : ℤ) + (n : ℤ)) :=
  let E := (TangentSpace (𝓡 n) : TopCat.of M → Type _)
  let A : Set (TopCat.of (ThomSpace n E)) := thomInfinitySubset n E
  cast
      (congrArg
        (fun S : Set (TopCat.of (ThomSpace n E)) ↦ H ((n : ℤ) + (n : ℤ)) _ S)
        (Set.union_self A)) <|
    H.relativeCup (X := TopCat.of (ThomSpace n E)) A A (n : ℤ) (n : ℤ)
      (mu.toReducedCohomology ⊗ₜ[ℤ] mu.toReducedCohomology)

/-- A fiberwise Kronecker pairing makes a tangent Thom class compatible with the chosen
orientation of `M` when its restriction evaluates to `1` on every local orientation generator.
This is the formal sign compatibility needed between the Euler class and the fundamental class. -/
def ThomClass.IsCompatibleWithManifoldOrientation
    (H : MultiplicativePairCohomologyTheory ℤ)
    (o : ROrientedManifold ℤ (𝓡 n) n M)
    (fiberRestriction :
      ∀ b : M,
        tangentThomReducedCohomology H (n : ℤ) →ₗ[ℤ]
          reducedCohomology H (n : ℤ)
            (compactifiedFiberSphere ((TangentSpace (𝓡 n) : TopCat.of M → Type _) b)))
    (mu : ThomClass H fiberRestriction)
    (fiberKroneckerPairing :
      ∀ b : M,
        reducedCohomology H (n : ℤ)
            (compactifiedFiberSphere ((TangentSpace (𝓡 n) : TopCat.of M → Type _) b)) →ₗ[ℤ]
          localTopHomologyGroup ℤ n M b →ₗ[ℤ] ℤ) : Prop :=
  ∀ (b : M) (U : LocalTopHomologyTrivialization ℤ n M),
    ∀ (hU : U ∈ o.atlas) (hb : b ∈ U.domain),
      fiberKroneckerPairing b (fiberRestriction b mu)
          ((U.identify ⟨b, hb⟩).inv (1 : constantCoefficientModule ℤ)) =
        1

/-- The integral tangent Euler class obtained from the source definition
`e(τM) = Φ_μ⁻¹(μ ∪ μ)`, transported along an equality identifying the chosen
pair-cohomology group with canonical integral singular cohomology. -/
noncomputable def integralTangentEulerClassFromThomData
    (H : MultiplicativePairCohomologyTheory ℤ)
    (fiberRestriction :
      ∀ b : M,
        tangentThomReducedCohomology H (n : ℤ) →ₗ[ℤ]
          reducedCohomology H (n : ℤ)
            (compactifiedFiberSphere ((TangentSpace (𝓡 n) : TopCat.of M → Type _) b)))
    (mu : ThomClass H fiberRestriction)
    (thomEquiv :
      H (n : ℤ) (TopCat.of M) (∅ : Set M) ≃ₗ[ℤ]
        tangentThomReducedCohomology H ((n : ℤ) + (n : ℤ)))
    (integralCohomology :
      H (n : ℤ) (TopCat.of M) (∅ : Set M) =
        (integralSingularCohomology (TopCat.of M) n : Type)) :
    integralSingularCohomology (TopCat.of M) n :=
  cast integralCohomology
    (thomEquiv.symm (tangentThomClassSquare H fiberRestriction mu))

/-- Theorem 23.7.9. Let `M` be a smooth closed oriented `n`-manifold, let `z` be the integral
fundamental class for its chosen orientation, and let `mu` be the compatible integral Thom class
of its tangent bundle. If `thomEquiv` is the canonical Thom isomorphism and the displayed
Kronecker pairing is the canonical integral one, then
`chi(M) = ⟨e(τM), z⟩`. -/
theorem manifoldEulerCharacteristic_eq_eulerCharacteristicNumber
    (H : MultiplicativePairCohomologyTheory ℤ)
    (o : ROrientedManifold ℤ (𝓡 n) n M)
    (fundamentalClass : rSingularHomology ℤ n (TopCat.of M))
    (hFundamental : IsRFundamentalClassFor o fundamentalClass)
    (fiberRestriction :
      ∀ b : M,
        tangentThomReducedCohomology H (n : ℤ) →ₗ[ℤ]
          reducedCohomology H (n : ℤ)
            (compactifiedFiberSphere ((TangentSpace (𝓡 n) : TopCat.of M → Type _) b)))
    (mu : ThomClass H fiberRestriction)
    (fiberKroneckerPairing :
      ∀ b : M,
        reducedCohomology H (n : ℤ)
            (compactifiedFiberSphere ((TangentSpace (𝓡 n) : TopCat.of M → Type _) b)) →ₗ[ℤ]
          localTopHomologyGroup ℤ n M b →ₗ[ℤ] ℤ)
    (hOrientation :
      ThomClass.IsCompatibleWithManifoldOrientation
        H o fiberRestriction mu fiberKroneckerPairing)
    (comparison : ThomComparison H (n : ℤ) mu)
    (thomEquiv :
      H (n : ℤ) (TopCat.of M) (∅ : Set M) ≃ₗ[ℤ]
        tangentThomReducedCohomology H ((n : ℤ) + (n : ℤ)))
    (hThomEquiv :
      ∀ x : H (n : ℤ) (TopCat.of M) (∅ : Set M),
        thomEquiv x = comparison.toLinearMap x)
    (integralCohomology :
      H (n : ℤ) (TopCat.of M) (∅ : Set M) =
        (integralSingularCohomology (TopCat.of M) n : Type))
    (kroneckerPairing :
      integralSingularCohomology (TopCat.of M) n →ₗ[ℤ]
        rSingularHomology ℤ n (TopCat.of M) →ₗ[ℤ] ℤ)
    (hKronecker :
      IsCanonicalIntegralKroneckerPairing (TopCat.of M) n kroneckerPairing) :
    manifoldEulerCharacteristic K M =
      kroneckerPairing
        (integralTangentEulerClassFromThomData
          H fiberRestriction mu thomEquiv integralCohomology)
        fundamentalClass := by
  sorry

end
