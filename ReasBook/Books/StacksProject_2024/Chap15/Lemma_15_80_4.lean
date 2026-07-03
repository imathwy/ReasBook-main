import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksProject_2024.Chap10.Lemma_10_110_8
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_77_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R] [IsRegularRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling:
- primary domain: perfect objects in `D(R)` over a regular ring of finite Krull dimension, and
  splitting of the canonical truncation triangle along a cohomology gap;
- sampled owner declarations:
  `IsRegularRing`,
  `ringKrullDim`,
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ`,
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
- best owner abstraction: the ring-side core owner is `[IsRegularRing R]`, and the finite
  Krull-dimension clause should stay as the direct bridge datum `ringKrullDim R = d`; this item is
  the `source-facing`
  perfect-complex specialization of the split-triangle owner
  `exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ`
  applied to the canonical truncation triangle; the compatibility data should stay in the
  owner theorem's native pair of equations rather than a repackaged local predicate;
- primitive data: `d`, the owner instance `[IsRegularRing R]`, the bridge datum
  `hdim : ringKrullDim R = d`, the perfectness of `K`, and the cohomology-gap hypothesis;
- derived API: the compatible biproduct decomposition of `K` into the lower and upper truncations.

Source/core/bridge triage:
- `source-facing`: the specific truncation-gap splitting statement below;
- `core/canonical`: `[IsRegularRing R]` for the ring-side hypothesis and the split-triangle
  owner from Lemma `15.77.1`;
- `bridge/view`: the regular-ring/perfect specialization supplying the projective-amplitude input
  needed by that owner.
-/

-- Proof sketch: apply the canonical owner
-- `exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ`
-- to the truncation triangle
-- `τ_{\le k - d + 1} K ⟶ K ⟶ τ_{\ge k + 1} K ⟶ τ_{\le k - d + 1} K⟦1⟧`.
-- The upper truncation has projective amplitude starting in degree `k + 1` because `K` is
-- perfect over the regular ring `R`; the equality `ringKrullDim R = d` is a separate bridge
-- datum, and Lemma `15.80.3` gives the required vanishing of maps
-- into the shifted lower truncation from the stated cohomology gap.
/-- Lemma 15.80.4: over a regular ring `R` of Krull dimension `d`, a perfect
object `K` of `D(R)` whose cohomology vanishes in degrees `k - d + 2, \ldots, k` admits a direct
sum decomposition
`K ≅ τ_{\le k - d + 1} K ⊞ τ_{\ge k + 1} K`
compatible with the canonical truncation maps. -/
theorem exists_truncation_gap_biprod_of_isPerfect_of_homology_vanishing
    (d : ℕ) (hdim : ringKrullDim R = d) (K : DMod) (k : ℤ)
    (hperfect : K.IsPerfect)
    (hvanish : ∀ i : ℤ, k - d + 2 ≤ i → i ≤ k → IsZero ((H i).obj K)) :
    ∃ e : K ≅ (t.truncLE (k - d + 1)).obj K ⊞ (t.truncGE (k + 1)).obj K,
      ((t.truncLEι (k - d + 1)).app K) ≫ e.hom = biprod.inl ∧
        e.hom ≫ biprod.snd = ((t.truncGEπ (k + 1)).app K) := sorry

end
