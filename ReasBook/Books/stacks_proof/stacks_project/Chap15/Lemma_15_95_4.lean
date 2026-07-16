import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_96_4
import stacks_proof.stacks_project.Chap15.Lemma_15_92_6
import stacks_proof.stacks_project.Chap15.Lemma_15_95_5
import stacks_proof.stacks_project.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open AdicCompletion
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling for Lemma 15.95.4:
- primary domain: cohomology of derived `I`-adic completion in `DerivedCategory (ModuleCat A)`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletionOf`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty`,
  `AdicCompletion`,
  `AdicCompletion.mapToComplete`,
  `Ideal.fg_of_isNoetherianRing`;
- best owner abstraction: this is a `source-facing` comparison theorem whose core owners are the
  chapter derived-completion object `K^∧[I, hI]`, the chapter cohomology owner `H^i`, and the module-side
  completion owner `AdicCompletion I`;
- primitive vs. derived:
  primitive data are the ideal `I`, the derived object `K`, the degree `n`, and the finite
  cohomology hypothesis on `K`;
  derived API is the canonical comparison morphism from
  `AdicCompletion I (H^n(K))` to `H^n(K^∧[I, hI])` and the resulting isomorphism. -/

private theorem homology_derivedCompletionOf_isDerivedComplete
    (I : Ideal A) (K : DMod) (n : ℤ) :
    ((H n).obj (K^∧[I, I.fg_of_isNoetherianRing])).IsDerivedCompleteWithRespectTo I := by
  have hcomplete :
      (K^∧[I, I.fg_of_isNoetherianRing]).IsDerivedCompleteWithRespectTo I :=
    derivedCompletionOf_isDerivedComplete I I.fg_of_isNoetherianRing K
  exact
    (isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty I
      (K^∧[I, I.fg_of_isNoetherianRing])).mp hcomplete n

/- The target module of the canonical completion comparison is `I`-adically complete. This is the
module-level owner needed to define the comparison map via `AdicCompletion.mapToComplete`. -/
theorem isAdicComplete_homology_derivedCompletionOf
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    IsAdicComplete I ((H n).obj (K^∧[I, I.fg_of_isNoetherianRing])) := by
  sorry

/-- The canonical comparison morphism
`(H^n(K))^∧ → H^n(K^∧)` from ordinary `I`-adic completion to the `n`th cohomology of derived
completion. -/
noncomputable abbrev homologyCompletionComparison
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    ModuleCat.of A (AdicCompletion I ((H n).obj K)) ⟶
      (H n).obj (K^∧[I, I.fg_of_isNoetherianRing]) :=
  let _ :
      IsAdicComplete I ((H n).obj (K^∧[I, I.fg_of_isNoetherianRing])) :=
    isAdicComplete_homology_derivedCompletionOf I K n hK
  ModuleCat.ofHom <|
    mapToComplete I ((H n).map (toDerivedCompletion I I.fg_of_isNoetherianRing K)).hom

-- Proof sketch: truncate `K` above a fixed degree `n`, use pseudo-coherence of the truncation from
-- the finite-cohomology hypothesis over the Noetherian ring `A`, represent it by a bounded-above
-- finite free complex, and compute derived completion termwise. Exactness of `I`-adic completion
-- on finite modules identifies the resulting degree-`n` cohomology with the completion of
-- `H^n(K)`, and the finite cohomological dimension of derived completion removes the truncation.
/-- Lemma 15.95.4: if `A` is Noetherian, `I ⊆ A` is an ideal, and every cohomology module of
`K ∈ D(A)` is finite, then the canonical comparison morphism
`(H^n(K))^∧ → H^n(K^∧[I, hI])` is an isomorphism. -/
@[stacks 0A06]
theorem homologyCompletionComparison_isIso
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    IsIso (homologyCompletionComparison I K n hK) := by
  sorry

/-- Lemma 15.95.4, isomorphism form: if every cohomology module of `K` is finite, then
`H^n(K^∧[I, hI])` is canonically isomorphic to the ordinary `I`-adic completion of `H^n(K)`. -/
@[stacks 0A06]
noncomputable abbrev homology_derivedCompletionOf_iso_adicCompletion
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    (H n).obj (K^∧[I, I.fg_of_isNoetherianRing]) ≅
      ModuleCat.of A (AdicCompletion I ((H n).obj K)) :=
  let _ := homologyCompletionComparison_isIso I K n hK
  (asIso (homologyCompletionComparison I K n hK)).symm

end

end DerivedCategory
