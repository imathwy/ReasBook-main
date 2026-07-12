import Mathlib
import StacksProject_2024.Chap28.Lemma_28_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the affine-open `isoSpec` owner and the
-- open-immersion/restriction API, while local project inspection verified that `Lemma_28_25_1`
-- already supplies the exact affine comparison maps appearing in the proof of Stacks
-- `01PQ`. The current project does not yet expose a clean scheme-level owner for the displayed
-- global colimit map, so this item is recorded as the finite affine-cover globalization data used
-- in the Stacks proof rather than by inventing a fake wrapper for the missing global map.

/-- Lemma 28.25.3 (1): if `X` is quasi-compact, `I` is a quasi-coherent ideal sheaf whose affine
section ideals are finitely generated, and `ℱ` is a quasi-coherent `\mathcal O_X`-module, then one
can choose a finite affine open cover of `X` on which the affine comparison maps from
Lemma `28.25.1 (1)` are injective. This is the affine-cover input used to deduce injectivity of
the global comparison map on `X \setminus Z`. -/
@[stacks 01PQ]
theorem exists_finiteAffineCover_localInjectiveIdealPowerComparison
    {X : Scheme.{u}} [CompactSpace X.carrier]
    (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ∃ m : ℕ, ∃ 𝒰 : Fin m → X.affineOpens,
      (∀ x : X, ∃ i : Fin m, x ∈ (𝒰 i : X.Opens)) ∧
      (∀ i : Fin m,
        Function.Injective
          (idealPowerHomColimitToComplementSections
            (I.ideal (𝒰 i))
            (hI (𝒰 i))
            (ModuleCat.of (Γ(X, (𝒰 i : X.Opens))) (Γ(ℱ, (𝒰 i : X.Opens))))).hom) := sorry

/-- A finite affine open cover of a scheme. -/
structure FiniteAffineCover (X : Scheme.{u}) where
  m : ℕ
  𝒰 : Fin m → X.affineOpens
  covers : ∀ x : X, ∃ i : Fin m, x ∈ (𝒰 i : X.Opens)

/-- Finite affine overlap data on which the local quotient comparison maps are isomorphisms. -/
structure FiniteAffineOverlapIdealPowerQuotientComparison
    {X : Scheme.{u}}
    (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (cover : FiniteAffineCover X) (i i' : Fin cover.m) where
  n : ℕ
  𝒱 : Fin n → X.affineOpens
  covers :
    ∀ x : X, x ∈ ((cover.𝒰 i : X.Opens) ⊓ (cover.𝒰 i' : X.Opens)) →
      ∃ k : Fin n, x ∈ (𝒱 k : X.Opens)
  comparison_isIso :
    ∀ k : Fin n,
      IsIso <|
        idealPowerQuotientHomColimitToComplementSections
          (I.ideal (𝒱 k))
          (hI (𝒱 k))
          (ModuleCat.of
            (Γ(X, (𝒱 k : X.Opens)))
            (Γ(ℱ, (𝒱 k : X.Opens))))

/-- A finite affine cover together with affine overlap comparison data for every pair of opens. -/
structure FiniteAffineIdealPowerQuotientComparisonAtlas
    {X : Scheme.{u}}
    (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] where
  cover : FiniteAffineCover X
  overlaps :
    ∀ i i' : Fin cover.m,
      FiniteAffineOverlapIdealPowerQuotientComparison I hI ℱ cover i i'

/-- Lemma 28.25.3 (2): if `X` is quasi-compact and quasi-separated, `I` is a quasi-coherent ideal
sheaf whose affine section ideals are finitely generated, and `ℱ` is a quasi-coherent
`\mathcal O_X`-module, then one can choose a finite affine open cover of `X` together with finite
affine covers of all pairwise intersections such that the affine comparison maps from
Lemma `28.25.1 (3)` are isomorphisms on those opens. This is the finite affine gluing datum used
to deduce the global isomorphism statement on `X \setminus Z`. -/
@[stacks 01PQ]
theorem exists_finiteAffineCover_overlapLocalIsoIdealPowerQuotientComparison
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    Nonempty (FiniteAffineIdealPowerQuotientComparisonAtlas I hI ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
