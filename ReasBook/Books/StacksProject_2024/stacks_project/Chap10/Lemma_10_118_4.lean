import StacksProject_2024.stacks_project.Chap10.«10_118_3_2»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum GenericFlatness

/-
Domain-style sampling:
* primary domain: generic flatness on `Spec R`, with the short exact sequence treated through the
  chapter's canonical owner `ShortComplex (ModuleCat S)`.
* inspected owner declarations:
  `GenericFlatness.goodLocus`,
  `CategoryTheory.ShortComplex.ShortExact.flat_X₂`,
  `Module.FinitePresentation.of_exact`,
  `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`.
* best owner abstraction: a short exact complex `T : ShortComplex (ModuleCat S)`.
* layer triage: the short exact complex is `core/canonical`; the textbook inclusion of good loci
  remains `source-facing`.
* primitive data: `T` and `hT : T.ShortExact`.
* derived API: the inclusion
  `goodLocus R S T.X₁ ∩ goodLocus R S T.X₃ ⊆ goodLocus R S T.X₂`.
-/

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {T : ShortComplex (ModuleCat.{max u v} S)}

-- Proof sketch: let `u` lie in both good loci. Choose basic opens around `u` coming from elements
-- `f1, f3 : R` witnessing the generic-flatness condition for `T.X₁` and `T.X₃`, and replace them by
-- the common refinement `f1 * f3`. Localizing the short exact sequence at that element preserves
-- exactness; then the endpoint assumptions imply the middle localized module is finitely presented
-- by Lemma `10.5.3`, and freeness is preserved under extensions. Hence the same basic open is
-- contained in the good locus of `T.X₂`.
/-- Lemma 10.118.4: for a short exact sequence `0 → M1 → M2 → M3 → 0` of `S`-modules, the
intersection of the generic-flatness good loci of the outer terms is contained in the good locus
of the middle term. -/
theorem goodLocus_inter_subset_of_shortExact
    (hT : T.ShortExact) :
    goodLocus R S T.X₁ ∩ goodLocus R S T.X₃ ⊆ goodLocus R S T.X₂ := sorry

end

end ShortExact
end ShortComplex
end CategoryTheory
