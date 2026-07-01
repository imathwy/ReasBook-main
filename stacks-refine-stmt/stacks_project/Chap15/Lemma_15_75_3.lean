import Mathlib
import stacks_project.Chap10.Lemma_10_109_6
import stacks_project.Chap15.Lemma_15_67_6
import stacks_project.Chap15.Definition_15_75_1
import stacks_project.Chap15.Lemma_15_75_2

universe u

open CategoryTheory

section

variable {R : Type u} [CommRing R]

namespace ModuleCat

/- The module-level perfectness owner is the degree-zero specialization of the derived owner
`DerivedCategory.IsPerfect`, so the canonical characterization from Lemma `15.75.2` should be
available directly at this owner level. -/
/-- An `R`-module is perfect exactly when it is pseudo-coherent and has finite tor dimension. -/
theorem isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
    (M : ModuleCat R) :
    M.IsPerfect ↔ M.IsPseudoCoherent ∧ ModuleHasFiniteTorDimension M := by
  simpa [ModuleCat.IsPerfect, ModuleCat.IsPseudoCoherent, ModuleHasFiniteTorDimension] using
    (CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
      (ModuleCat.single0Functor.obj M))

/- Domain-style sampling for Lemma 15.75.3:
- primary domain: perfect modules over a commutative ring, compared with bounded finite
  projective resolutions;
- sampled owner declarations:
  `ModuleCat.IsPerfect`,
  `CategoryTheory.HasProjectiveDimensionLE`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`,
  `CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: the source-facing owner remains `M.IsPerfect`, while the concrete
  finite-resolution side should reuse the existing Chapter 10 owner
  `HasFiniteProjectiveResolutionLengthLEWithFiniteTerms` rather than a new local wrapper;
- primitive vs. derived:
  primitive data are the module `M` and the chosen resolution length `d`;
  the finite-projective resolution itself is owned upstream in Chapter 10, and the perfectness
  predicate is owned by Definition `15.75.1`;
- source/core/bridge triage:
  `source-facing`: the equivalence below;
  `core/canonical`: `ModuleCat.IsPerfect` and
    `HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`;
  `bridge/view`: Chapter 10's projective-dimension interface sitting behind the proof.

This file should therefore keep the textbook equivalence, but phrase it directly in terms of the
existing owners instead of introducing any parallel resolution packaging.
-/

-- Proof sketch: identify perfect modules with pseudo-coherent modules of finite tor dimension via
-- Lemma `15.75.2`; then use the finite-free resolution description of pseudo-coherence together
-- with the truncation argument from the text to replace the leftmost sufficiently high syzygy by a
-- finite projective module, producing a finite projective resolution. Conversely, a finite
-- projective resolution is a bounded finite-projective complex representing `M[0]`, hence `M` is
-- perfect.
/-- Lemma 15.75.3: an `R`-module is perfect if and only if there exists a finite resolution
`0 ⟶ F_d ⟶ ⋯ ⟶ F₁ ⟶ F₀ ⟶ M ⟶ 0` in which every `Fᵢ` is a finite projective `R`-module. -/
theorem isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
    (M : ModuleCat R) :
    M.IsPerfect ↔ ∃ d : ℕ, HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M d := sorry

-- Proof sketch: choose the finite projective resolution supplied by the previous equivalence and
-- forget the projective structure to obtain a finite flat resolution of the same length. Then use
-- the canonical tor-dimension/flat-resolution bridge from Lemma `15.67.6`.
/-- A perfect `R`-module has tor dimension at most some finite integer. -/
theorem exists_moduleHasTorDimensionLE_of_isPerfect
    (M : ModuleCat R) (hM : M.IsPerfect) :
    ∃ d : ℕ, ModuleHasTorDimensionLE M d := by
  rcases
      (isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms M).1 hM with
    ⟨d, hd⟩
  refine ⟨d, ?_⟩
  apply ModuleCat.HasFiniteFlatResolutionLengthLE.hasTorDimensionLE
  cases d with
  | zero =>
      change Module.Flat R M
      let _ : Module.Projective R M := by
        simpa [ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms] using hd.1
      infer_instance
  | succ n =>
      rcases hd with ⟨P, δ, π, hπ, hδπ, hδ, hinj⟩
      refine ⟨fun i ↦ (P i).obj, ?_, ⟨fun i ↦ (δ i).hom, π, hπ, hδπ, hδ, hinj⟩⟩
      intro i
      let _ : Module.Projective R (P i).obj := (P i).property.2
      infer_instance

end ModuleCat

end
