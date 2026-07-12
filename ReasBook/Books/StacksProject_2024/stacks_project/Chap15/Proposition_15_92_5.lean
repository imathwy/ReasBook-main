import Mathlib
import StacksProject_2024.Chap15.Lemma_15_92_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

/- Domain-style sampling:
- primary domain: adic completeness, derived completeness, and `I`-adic separatedness for
  modules;
- sampled owner-side declarations:
  `IsAdicComplete`,
  `IsHausdorff`,
  `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete`,
  `ModuleCat.surjective_adicCompletion_of_isDerivedCompleteWithRespectTo`,
  `AdicCompletion.of`;
- best owner abstraction: the canonical completion owner `IsAdicComplete I M`, together with the
  owner-side separatedness predicate `IsHausdorff I M`;
- derived API: Lemma `15.92.3` supplies the two generatorwise bridges, and
  `IsHausdorff.iInf_pow_smul` converts the owner predicate to the source-facing intersection
  formula. -/

/-- Helper for Proposition 15.92.5: `I`-adic Hausdorffness is exactly injectivity of the
completion map. -/
lemma injective_adicCompletion_of_isHausdorff
    {I : Ideal A} {M : ModuleCat.{u, u} A} (hhaus : IsHausdorff I M) :
    Function.Injective (AdicCompletion.of I M) := by
  -- Proof comment: this is the canonical owner-side injectivity criterion for completion maps.
  exact (AdicCompletion.of_injective_iff).mpr hhaus

/-- Helper for Proposition 15.92.5: derived completeness plus `I`-adic Hausdorffness makes the
completion map bijective. -/
lemma adicCompletion_of_bijective_of_isDerivedCompleteWithRespectTo_and_isHausdorff
    {I : Ideal A} {M : ModuleCat.{u, u} A} (hI : I.FG)
    (hderived : M.IsDerivedCompleteWithRespectTo I) (hhaus : IsHausdorff I M) :
    Function.Bijective (AdicCompletion.of I M) := by
  -- Proof comment: Lemma `15.92.3` gives surjectivity, and Hausdorffness gives injectivity of
  -- the same completion map.
  refine ⟨injective_adicCompletion_of_isHausdorff hhaus, ?_⟩
  exact
    surjective_adicCompletion_of_isDerivedCompleteWithRespectTo
      (A := A) (I := I) (M := M) hI hderived

/-- Proposition 15.92.5, owner-facing form: for a finitely generated ideal `I`, an `A`-module `M`
is `I`-adically complete if and only if it is derived complete with respect to `I` and
`I`-adically Hausdorff. -/
theorem isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff
    {I : Ideal A} {M : ModuleCat.{u, u} A} (hI : I.FG) :
    IsAdicComplete I M ↔
      M.IsDerivedCompleteWithRespectTo I ∧ IsHausdorff I M := by
  constructor
  · intro hcomplete
    -- Proof comment: Lemma `15.92.3` gives derived completeness, and completeness is always
    -- Hausdorff.
    exact
      ⟨isDerivedCompleteWithRespectTo_of_isAdicComplete (A := A) (I := I) (M := M) hcomplete,
        hcomplete.toIsHausdorff⟩
  · rintro ⟨hderived, hhaus⟩
    -- Proof comment: bijectivity of the completion map is exactly the owner criterion for adic
    -- completeness.
    exact (AdicCompletion.of_bijective_iff).mp
      (adicCompletion_of_bijective_of_isDerivedCompleteWithRespectTo_and_isHausdorff
        hI hderived hhaus)

/-- Helper for Proposition 15.92.5: the source-facing separatedness formula is exactly the
Hausdorff criterion. -/
lemma isHausdorff_of_iInf_pow_smul_eq_bot
    {I : Ideal A} {M : ModuleCat.{u, u} A}
    (hsep : (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A M) : Submodule A M) = ⊥) :
    IsHausdorff I M := by
  -- Proof comment: membership in the infimum is the same as vanishing in every `I^n M`, so the
  -- equality with `⊥` gives the Hausdorff conclusion directly.
  refine ⟨fun x hx ↦ ?_⟩
  have hx' : x ∈ (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A M) : Submodule A M) := by
    simpa [SModEq.zero] using hx
  simpa [hsep] using hx'

/-- Proposition 15.92.5: for a finitely generated ideal `I`, an `A`-module `M` is `I`-adically
complete if and only if it is derived complete with respect to `I` and is `I`-adically
separated, i.e. `⋂ n, I ^ n M = 0`. -/
theorem isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_iInf_pow_smul_eq_bot
    {I : Ideal A} {M : ModuleCat.{u, u} A} (hI : I.FG) :
    IsAdicComplete I M ↔
      M.IsDerivedCompleteWithRespectTo I ∧
        (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A M) : Submodule A M) = ⊥ := by
  constructor
  · intro hcomplete
    -- Proof comment: combine the owner-facing equivalence above with the standard separatedness
    -- formula for Hausdorff modules.
    obtain ⟨hderived, hhaus⟩ :=
      (isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff hI).mp hcomplete
    exact ⟨hderived, IsHausdorff.iInf_pow_smul hhaus⟩
  · rintro ⟨hderived, hsep⟩
    -- Proof comment: rebuild Hausdorffness from the intersection formula, then apply the
    -- owner-facing equivalence.
    exact (isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff hI).mpr
      ⟨hderived, isHausdorff_of_iInf_pow_smul_eq_bot hsep⟩

end ModuleCat

end
