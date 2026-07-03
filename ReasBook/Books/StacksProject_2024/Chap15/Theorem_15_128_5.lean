import Mathlib
import StacksProject_2024.Chap15.Proposition_15_128_4

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped ClosedPointFiber

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/- Domain-style sampling:
- primary domain: closed-point fibres of finitely presented modules, their visible quotients `V(x)`,
  and the codimension-controlled section-construction of Proposition `15.128.4`;
- inspected owner declarations in this domain:
  `closedPointFiberVisibleQuotient`,
  `selectedSections_splitAfterInverting_iff_linearIndependent_visibleClasses`,
  `section_dependence_locus`,
  `exists_section_with_prescribed_values_and_codim_controlled_dependence_locus`;
- best owner abstraction: the local free-summand hypothesis of the source theorem is canonically
  consumed in this chapter through the visible quotient owner `V(x)` and the numerical bound
  `Module.finrank (κ(x)) (V(x))`; the explicit localized split-map package is therefore a
  bridge/view, not the right public core for this file;
- inspected ambient-dimension owner declarations:
  `topologicalKrullDim`,
  `Order.coheight_le_krullDim`,
  `topologicalKrullDim_eq_iSup_topologicalKrullDimAt`;
- source/core/bridge triage:
  `source-facing`: the global conclusion that `R` splits off `M`;
  `core/canonical`: the visible quotient `V(x)` and its fibre dimension;
  `bridge/view`: the equivalence from Lemma `15.128.2` between local split free summands and
  linear independence in `V(x)`.
- primitive data: the upper dimension bound `topologicalKrullDim Ω ≤ d` and the pointwise
  fibre-dimension inequality;
- derived API: the codimension-controlled section from Proposition `15.128.4`, followed by the
  split-inclusion conclusion. -/

local notation "Ω" => closedPoints (PrimeSpectrum R)
local notation "V(" x ")" => closedPointFiberVisibleQuotient M x

-- Proof sketch: this is the chapter's canonical reformulation of the source local-splitting
-- hypothesis via Lemma `15.128.2`, so the input is stated directly as `d < finrank V(x)`. Apply
-- Proposition `15.128.4` with `h = 0`, `k = d + 1`, no prescribed values, and empty bad locus to
-- obtain a section `s : M` whose dependence locus is contained in a closed subset all of whose
-- irreducible components have codimension at least `d + 1`. Since `topologicalKrullDim Ω ≤ d`,
-- that closed subset is empty, so `s` is fibrewise visible at every closed point. The resulting map
-- `R → M` is therefore split after localizing at every closed point, hence universally injective,
-- and the algebra lemmas cited in the text upgrade it to a split inclusion.
/-- Theorem 15.128.5: let `Ω` be the closed-point space of `Spec R`. If `Ω` is a Noetherian
topological space of dimension at most `d`, `M` is finitely presented, and equivalently to the source
local-splitting hypothesis every visible quotient `V(x)` has dimension `> d`, then there exists a
split `R`-linear inclusion `R → M`; equivalently, `M ≅ R ⊕ M'` for some `R`-module `M'`. -/
theorem exists_split_inclusion_of_visibleQuotient_finrank_gt_dimension
    {d : ℕ} [NoetherianSpace Ω] (hdim : topologicalKrullDim Ω ≤ d)
    (hV : ∀ x : Ω, d < Module.finrank (κ(x)) (V(x))) :
    ∃ (s : R →ₗ[R] M) (ρ : M →ₗ[R] R), ρ.comp s = LinearMap.id := sorry

end
