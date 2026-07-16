import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_109_10
import StacksProject_2024.stacks_project.Chap10.Lemma_10_109_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

section

variable (A : Type u) [CommRing A]

/-
Domain-style sampling:
- primary domain: weak dimension of commutative rings, viewed as a uniform tor-dimension bound on
  modules;
- sampled owner declarations:
  `CategoryTheory.ModuleHasTorDimensionLE`,
  `ModuleCat.HasFiniteFlatResolutionLengthLE`,
  `ModuleCat.hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE`,
  `HasGlobalDimensionLE`;
- best owner abstraction: `HasWeakDimensionLE A d` remains the source-facing ring-level owner, but
  its primitive field should be the canonical module owner `ModuleHasTorDimensionLE` rather than
  the derived flat-resolution presentation;
- primitive vs. derived:
  primitive data is the uniform tor-dimension bound on all `A`-modules;
  derived API is the finite-flat-resolution formulation supplied by Lemma `15.67.6`.
-/

/-- Definition 15.105.3: a ring `A` has weak dimension at most `d` if every `A`-module admits a
finite flat resolution of length at most `d`, equivalently has tor dimension at most `d`. -/
class HasWeakDimensionLE (d : ℕ) : Prop where
  hasTorDimensionLE (M : ModuleCat.{u} A) : ModuleHasTorDimensionLE M d

/-- Over a ring of weak dimension at most `d`, every `A`-module has tor dimension at most `d`. -/
instance (d : ℕ) [HasWeakDimensionLE A d] (M : ModuleCat.{u} A) :
    ModuleHasTorDimensionLE M d :=
  HasWeakDimensionLE.hasTorDimensionLE M

/-- Over a ring of weak dimension at most `d`, every `A`-module admits a finite flat resolution of
length at most `d`. -/
instance (d : ℕ) [HasWeakDimensionLE A d] (M : ModuleCat.{u} A) :
    ModuleCat.HasFiniteFlatResolutionLengthLE M d := by
  let hwd : HasWeakDimensionLE A d := inferInstance
  have hM : ModuleHasTorDimensionLE M d := hwd.hasTorDimensionLE M
  exact ModuleCat.ModuleHasTorDimensionLE.hasFiniteFlatResolutionLengthLE M hM

/-- Helper for Definition 15.105.3: a projective object of `ModuleCat A` is flat as an
`A`-module. -/
theorem flat_of_projective_moduleCat {M : ModuleCat.{u} A} (hM : Projective M) :
    Module.Flat A M := by
  -- Use the standard `ModuleCat` instance translating categorical projectivity to module projectivity.
  letI : Projective M := hM
  exact Module.Flat.of_projective

/-- Helper for Definition 15.105.3: a finite projective resolution of bounded length can be
viewed as a finite flat resolution of the same length. -/
theorem hasFiniteFlatResolutionLengthLE_of_hasFiniteProjectiveResolutionLengthLE
    {M : ModuleCat.{u} A} {d : ℕ} (hM : HasFiniteProjectiveResolutionLengthLE M d) :
    ModuleCat.HasFiniteFlatResolutionLengthLE M d := by
  cases d with
  | zero =>
      -- In length `0`, the projective and flat formulations are exactly projectivity and flatness.
      simpa [HasFiniteProjectiveResolutionLengthLE, ModuleCat.HasFiniteFlatResolutionLengthLE] using
        flat_of_projective_moduleCat (A := A) hM
  | succ n =>
      -- For positive length, keep the same resolution and forget projectivity termwise to flatness.
      rcases hM with ⟨P, hproj, δ, π, hsurj, hExact₀, hExact, hInj⟩
      have hflat : ∀ i, Module.Flat A (P i) := by
        intro i
        exact flat_of_projective_moduleCat (A := A) (hproj i)
      exact ⟨P, hflat, δ, π, hsurj, hExact₀, hExact, hInj⟩

/-- Helper for Definition 15.105.3: a projective-dimension bound on an `A`-module gives the same
tor-dimension bound. -/
theorem hasTorDimensionLE_of_hasProjectiveDimensionLE
    {M : ModuleCat.{u} A} {d : ℕ} (hM : HasProjectiveDimensionLE M d) :
    ModuleHasTorDimensionLE M d := by
  -- Translate the projective-dimension bound into the finite projective-resolution owner.
  let hTFAE := projectiveDimensionLE_tfae_resolution_conditions (M := M) d
  have hprojResolution : HasFiniteProjectiveResolutionLengthLE M d := (hTFAE.out 0 1).mp hM
  -- Forget projectivity termwise to obtain the parallel finite flat resolution.
  have hflatResolution : ModuleCat.HasFiniteFlatResolutionLengthLE M d :=
    hasFiniteFlatResolutionLengthLE_of_hasFiniteProjectiveResolutionLengthLE (A := A) hprojResolution
  -- The Chapter 15 bridge turns that flat resolution into the desired tor-dimension bound.
  exact ModuleCat.HasFiniteFlatResolutionLengthLE.hasTorDimensionLE (M := M) hflatResolution

/-- A ring of global dimension at most `d` has weak dimension at most `d`. -/
instance (d : ℕ) [HasGlobalDimensionLE A d] : HasWeakDimensionLE A d where
  hasTorDimensionLE M := by
    -- A global-dimension bound provides the matching projective-dimension bound on every module.
    let hgd : HasGlobalDimensionLE A d := inferInstance
    have hpd : HasProjectiveDimensionLE M d := hgd.hasProjectiveDimensionLE M
    exact hasTorDimensionLE_of_hasProjectiveDimensionLE (A := A) hpd

end
