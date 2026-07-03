import Mathlib
import stacks_project.Chap10.Lemma_10_90_4
import stacks_project.Chap15.Lemma_15_65_4
import stacks_project.Chap15.Lemma_15_65_6
import stacks_project.Chap15.Lemma_15_65_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [Ring R] [Module.Coherent R R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Domain sampling:
-- * primary domain: pseudo-coherence for bounded-above derived complexes of `R`-modules over a
--   coherent ring;
-- * sampled owner API: `DerivedCategory.IsMPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`,
--   `DerivedCategory.homologyFunctor`, `boundedAbove_isMPseudoCoherent_of_homology`,
--   `isPseudoCoherent_iff_forall_isMPseudoCoherent`,
--   `moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation`, and
--   `module_coherent_iff_finitePresentation`;
-- * layer triage: the source-facing statements below reformulate the canonical derived-category
--   owners in terms of cohomology coherence / finite presentation, so the bounded-above complex is
--   primitive data while the cohomology predicates are derived companion views.
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

-- Degree-zero bridge: over a coherent ring, pseudo-coherent modules are exactly coherent modules.
-- The forward implication factors through finite presentation via Lemma `15.65.4` and
-- Lemma `10.90.4`; the reverse implication is the reusable module-level input for the bounded-above
-- homology criterion below.
/-- Over a coherent ring, an `R`-module is pseudo-coherent exactly when it is coherent. -/
theorem _root_.Module.isPseudoCoherent_iff_coherent :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Coherent R M := sorry

-- Proof sketch: the second and third conditions differ only by Lemma `10.90.4`, which identifies
-- coherent and finitely presented modules over a coherent ring. For the implication to
-- `m`-pseudo-coherence, first use that coherent modules over a coherent ring are pseudo-coherent,
-- upgrade this to all `m` with `isPseudoCoherent_iff_forall_isMPseudoCoherent`, and then apply
-- `boundedAbove_isMPseudoCoherent_of_homology`; the finiteness of `H^m(K)` is the degree-`m`
-- clause recorded separately in the source statement.
/-- Lemma 15.65.18: for a bounded-above derived `R`-complex over a coherent ring, the following
are equivalent: `K` is `m`-pseudo-coherent; `H^m(K)` is finite and all higher cohomology modules
are coherent; and `H^m(K)` is finite and all higher cohomology modules are finitely presented. -/
theorem boundedAbove_isMPseudoCoherent_tfae_of_coherentRing
    (K : DModMinus) (m : ℤ) :
    ([ K.obj.IsMPseudoCoherent m
      , Module.Finite R ((H m).obj K.obj) ∧
          ∀ i : ℤ, m < i → Module.Coherent R ((H i).obj K.obj)
      , Module.Finite R ((H m).obj K.obj) ∧
          ∀ i : ℤ, m < i → Module.FinitePresentation R ((H i).obj K.obj)
      ] : List Prop).TFAE := sorry

-- Proof sketch: apply the previous equivalence for every `m`. If `K` is pseudo-coherent, then it
-- is `m`-pseudo-coherent for all `m`, so each cohomology module is coherent. Conversely, if every
-- cohomology module is coherent, then for each `m` the second clause of the previous theorem
-- holds, so `K` is `m`-pseudo-coherent for every `m`; now use the canonical owner theorem
-- `isPseudoCoherent_iff_forall_isMPseudoCoherent` to recover `K.obj.IsPseudoCoherent`.
/-- A bounded-above derived complex over a coherent ring is pseudo-coherent exactly when all of
its cohomology modules are coherent. -/
theorem boundedAbove_isPseudoCoherent_iff_homology_coherent
    (K : DModMinus) :
    K.obj.IsPseudoCoherent ↔
      ∀ i : ℤ, Module.Coherent R ((H i).obj K.obj) := sorry

end
