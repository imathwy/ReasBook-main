import Mathlib
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap15.Lemma_15_76_7

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.78.6:
- primary domain: pseudo-coherent derived complexes over a flat local ring map, with perfection
  and tor-amplitude detected on the closed-fiber residue field;
- sampled owner declarations:
  `K.IsPerfect`,
  `HasTorAmplitudeIn`,
  `primeResidueFieldDerivedHomology`,
  `hasGlobalDimensionLE_of_isRegularLocalRing`;
- best owner abstraction: the core/canonical owners are `K.IsPerfect`, `HasTorAmplitudeIn`, and
  the residue-field-fiber bridge `primeResidueFieldDerivedHomology`; this file is only a
  `source-facing` local closed-fiber specialization, so it should reuse those owners rather than
  restating the derived special fiber entrywise;
- primitive vs. derived:
  primitive data are the pseudo-coherent object `K`, the local closed-fiber regularity hypothesis,
  the dimension bound `ringKrullDim ((maximalIdeal A).Fiber B) = d`, and the closed-point
  residue-field homology vanishing of the restriction of scalars of `K` to `D(A)`;
  derived API is the conjunction `K.IsPerfect ∧ HasTorAmplitudeIn K (a - d) b` and the thin
  bridge from tor-amplitude over `A` to the closed-point vanishing hypothesis;
- source/core/bridge triage:
  `source-facing`: the two local closed-fiber criteria below;
  `core/canonical`: `K.IsPerfect`, `HasTorAmplitudeIn`, and
    `primeResidueFieldDerivedHomology`;
  `bridge/view`: restriction of scalars along `A → B`.
-/

-- Proof sketch: identify the derived tensor with `κ(maximalIdeal A)` as a complex over the closed
-- fiber `(maximalIdeal A).Fiber B`, use the regular-local hypothesis and Proposition `10.110.1`
-- to bound the global dimension of that fiber by `d`, and then apply Lemma `15.67.19` to shift
-- the homology support from `[a, b]` to `[(a - d), b]`. Finally use the maximal-ideal case of
-- Lemma `15.78.2` for the local ring `B`.
/-- A weaker sufficient hypothesis for Lemma `15.78.6`: it is enough to assume that the derived
special fiber `K^• \otimes_A^{\mathbf L} κ(\mathfrak m_A)` has vanishing homology outside
`[a, b]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_baseResidueFieldDerivedHomology_vanishing_of_closedFiber_isRegularLocalRing
    (K : DModB) (a b : ℤ) (d : ℕ)
    [IsRegularLocalRing ((maximalIdeal A).Fiber B)]
    (hdim : ringKrullDim ((maximalIdeal A).Fiber B) = d)
    (hKpc : K.IsPseudoCoherent)
    (hKκ :
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero
          (primeResidueFieldDerivedHomology
            (closedPoint A)
            ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
            i)) :
    K.IsPerfect ∧ HasTorAmplitudeIn K (a - (d : ℤ)) b := sorry

-- Proof sketch: tor-amplitude over `A` implies the required vanishing of the derived special
-- fiber over `κ(maximalIdeal A)`. Apply the residue-field criterion above to obtain perfection of
-- `K` over `B` and tor-amplitude in `[(a - d), b]`.
/-- Lemma 15.78.6: let `A → B` be a flat local ring homomorphism, let `d ≥ 0`, and let `K^•` be a
pseudo-coherent object of `D(B)`. If the closed fiber `(maximalIdeal A).Fiber B`, equivalently
`B ⧸ (Ideal.map (algebraMap A B) (maximalIdeal A))`, is a regular local ring of dimension `d`,
and `K^•`, viewed over `A`, has tor-amplitude in `[a, b]`, then `K^•` is perfect over `B` with
tor-amplitude in `[(a - d), b]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_closedFiber_isRegularLocalRing
    (K : DModB) (a b : ℤ) (d : ℕ)
    [IsRegularLocalRing ((maximalIdeal A).Fiber B)]
    (hdim : ringKrullDim ((maximalIdeal A).Fiber B) = d)
    (hKpc : K.IsPseudoCoherent)
    (hKamp :
      HasTorAmplitudeIn
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
        a b) :
    K.IsPerfect ∧ HasTorAmplitudeIn K (a - (d : ℤ)) b := sorry

end

end CategoryTheory
