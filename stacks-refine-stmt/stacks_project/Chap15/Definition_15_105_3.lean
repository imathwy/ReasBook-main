import Mathlib
import stacks_project.Chap10.Definition_10_109_10
import stacks_project.Chap15.Lemma_15_67_6

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

/-- A ring of global dimension at most `d` has weak dimension at most `d`. -/
instance (d : ℕ) [HasGlobalDimensionLE A d] : HasWeakDimensionLE A d where
  hasTorDimensionLE M := by
    sorry

end
