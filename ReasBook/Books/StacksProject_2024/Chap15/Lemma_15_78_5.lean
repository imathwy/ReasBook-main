import Mathlib
import StacksProject_2024.Chap10.Definition_10_109_10
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.78.5:
- primary domain: perfectness and tor-amplitude for pseudo-coherent derived complexes under flat
  restriction of scalars, detected on residue-field fibers of `A → B`;
- sampled owner declarations:
  `K.IsPseudoCoherent`,
  `K.IsPerfect`,
  `HasTorAmplitudeIn`,
  `HasGlobalDimensionLE`,
  `HasWeakDimensionLE`;
- best owner abstraction: the theorem is source-facing and should conclude in the canonical owner
  language `K.IsPerfect ∧ HasTorAmplitudeIn K (a - d) b`; on the ring side, the primitive
  derived-category conclusion is driven by the weak-dimension owner `HasWeakDimensionLE`, while
  the source hypothesis `HasGlobalDimensionLE (p.asIdeal.Fiber B) d` is a stronger bridge input
  reused via the upstream instance `HasGlobalDimensionLE ⟹ HasWeakDimensionLE`;
- primitive vs. derived:
  primitive data are the flat map `A → B`, the pseudo-coherent object `K : D(B)`, the interval
  bounds `a, b`, and the uniform fiberwise global-dimension bound;
  derived API is the perfectness/tor-amplitude conclusion for `K` over `B`, together with the
  restricted object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K : DModA)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, matching the textbook hypothesis in terms of global
  dimension of every fiber ring;
- `core/canonical`: `K.IsPseudoCoherent`, `K.IsPerfect`, and `HasTorAmplitudeIn`;
- `bridge/view`: the restricted derived object over `A`, and the ring-side implication from
  `HasGlobalDimensionLE` on each fiber to the weak-dimension owner used by Lemma `15.67.19`.
-/

-- Proof sketch: use the flatness of `A → B` to compare tor-amplitude over `A` with the homology
-- of the fibers over `B ⊗[A] κ(p)`. For each prime `p`, the fiber ring has global dimension at
-- most `d`, so Lemma `15.67.19` upgrades the fiberwise amplitude interval from `[a, b]` to
-- `[a - d, b]`. Then apply Lemma `15.78.2` to the pseudo-coherent `B`-complex `K` to conclude
-- that `K` is perfect over `B` with tor-amplitude in the same interval.
/-- Lemma 15.78.5: let `A → B` be a flat ring map, let `d ≥ 0`, and let `K^•` be a
pseudo-coherent object of `D(B)`. If every fiber ring `B ⊗[A] κ(\mathfrak p)` has global
dimension at most `d` and `K^•`, viewed over `A`, has tor-amplitude in `[a, b]`, then `K^•` is
perfect over `B` and has tor-amplitude in `[a - d, b]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_fiber_hasGlobalDimensionLE
    (K : DModB) (a b : ℤ) (d : ℕ)
    (hfiber :
      ∀ p : PrimeSpectrum A, HasGlobalDimensionLE (p.asIdeal.Fiber B) d)
    (hKpc : K.IsPseudoCoherent)
    (hKamp :
      HasTorAmplitudeIn
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
        a b) :
    K.IsPerfect ∧ HasTorAmplitudeIn K (a - (d : ℤ)) b := sorry

end

end CategoryTheory
