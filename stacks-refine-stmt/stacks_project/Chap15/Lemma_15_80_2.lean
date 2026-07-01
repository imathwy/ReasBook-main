import Mathlib
import stacks_project.Chap10.Definition_10_110_7
import stacks_project.Chap15.Lemma_15_79_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-
Domain-style sampling for Lemma 15.80.2:
- primary domain: strong generators in the perfect derived category of a Noetherian ring and the
  Chapter 10 owner API for regular rings of finite Krull dimension;
- sampled owner declarations:
  `IsStrongGenerator`,
  `ringSingleInPerfectDerived`,
  `IsRegularRing`,
  `finiteGlobalDimension_regularRing_localizations_tfae`;
- best owner abstraction: the ring-side owner inside the conclusion is `IsRegularRing R`, but the
  source-facing main theorem must keep the combined finite-dimensional regularity conclusion
  `∃ n : ℕ, IsRegularRing R ∧ ringKrullDim R = n`;
- primitive vs. derived: primitive data here is only the strong-generation hypothesis on `R[0]`
  in `D_{perf}(R)`; the source-facing combined existential conclusion is the full derived API; the
  regularity owner `IsRegularRing R` and the explicit dimension witness remain logically derived
  consequences rather than separate public declarations;
- source/core/bridge triage:
  `source-facing`: the implication from strong generation of `R[0]` to the existence of a finite
    Krull-dimension witness together with `IsRegularRing R`;
  `core/canonical`: `IsRegularRing R`;
  `bridge/view`: any downstream extraction of the explicit equality `ringKrullDim R = n` from the
    source-facing existential conclusion.
-/

-- Proof sketch: apply the strong-generation hypothesis to the canonical object `R[0]` in
-- `D_{perf}(R)` and use Lemma `15.80.1` to force vanishing of composites of sufficiently many
-- ghosts. Represent finite modules by bounded finite free complexes in `D_{perf}(R)` to deduce
-- vanishing of high `Ext`, hence finite global dimension by Lemma `10.109.12`, and then conclude
-- with Lemma `10.110.8` that `R` is regular of some finite Krull dimension.
/-- Lemma 15.80.2: if the canonical object `R[0]` is a strong generator of the perfect derived
category `D_{perf}(R)`, then `R` is a regular ring of finite Krull dimension. -/
theorem exists_regularRing_and_ringKrullDim_eq_of_ringSingleInPerfectDerived_isStrongGenerator
    (hstrong : IsStrongGenerator (ringSingleInPerfectDerived R)) :
    ∃ n : ℕ, IsRegularRing R ∧ ringKrullDim R = n := sorry

end

end CategoryTheory
