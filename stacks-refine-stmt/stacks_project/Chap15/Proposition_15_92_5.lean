import Mathlib
import stacks_project.Chap15.Lemma_15_92_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

/- Domain-style sampling:
- primary domain: adic completeness, derived completeness, and `I`-adic separatedness for modules;
- sampled owner-side declarations:
  `IsAdicComplete`,
  `IsHausdorff`,
  `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete`,
  `ModuleCat.surjective_adicCompletion_of_isDerivedCompleteWithRespectTo`;
- best owner abstraction: the canonical separatedness owner `IsHausdorff I M` together with the
  completeness owner `IsAdicComplete I M`;
- primitive data: the module `M`, the ideal `I`, and the completion map `AdicCompletion.of I M`;
- derived API: the source-facing intersection formula
  `(⨅ n, I ^ n • (⊤ : Submodule A M)) = ⊥` via `isHausdorff_iff`. -/

-- Proof sketch: Lemma `15.92.3` gives derived completeness from `I`-adic completeness and, for
-- finitely generated `I`, surjectivity of the completion map from derived completeness. Combine
-- that surjectivity with the canonical `IsHausdorff` owner for injectivity of the completion map.
/-- Proposition 15.92.5, owner-facing form: for a finitely generated ideal `I`, an `A`-module `M`
is `I`-adically complete if and only if it is derived complete with respect to `I` and
`I`-adically Hausdorff. -/
theorem isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff
    {I : Ideal A} {M : ModuleCat A} (hI : I.FG) :
    IsAdicComplete I M ↔
      M.IsDerivedCompleteWithRespectTo I ∧ IsHausdorff I M := by
  constructor
  · intro hcomplete
    exact ⟨isDerivedCompleteWithRespectTo_of_isAdicComplete M hcomplete, hcomplete.toIsHausdorff⟩
  · rintro ⟨hderived, hhaus⟩
    have hsurj : Function.Surjective (AdicCompletion.of I M) :=
      surjective_adicCompletion_of_isDerivedCompleteWithRespectTo M hI hderived
    exact (AdicCompletion.of_bijective_iff).mp
      ⟨(AdicCompletion.of_injective_iff).mpr hhaus, hsurj⟩

-- Proof sketch: this is the source-facing restatement of the preceding owner-level theorem, using
-- the standard criterion `isHausdorff_iff` for `I`-adic separatedness.
/-- Proposition 15.92.5: for a finitely generated ideal `I`, an `A`-module `M` is `I`-adically
complete if and only if it is derived complete with respect to `I` and is `I`-adically
separated, i.e. `⋂ n, I ^ n M = 0`. -/
theorem isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_iInf_pow_smul_eq_bot
    {I : Ideal A} {M : ModuleCat A} (hI : I.FG) :
    IsAdicComplete I M ↔
      M.IsDerivedCompleteWithRespectTo I ∧
        (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A M) : Submodule A M) = ⊥ := by
  constructor
  · intro hcomplete
    obtain ⟨hderived, hhaus⟩ :=
      (isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff hI).mp hcomplete
    exact ⟨hderived, IsHausdorff.iInf_pow_smul hhaus⟩
  · rintro ⟨hderived, hsep⟩
    have hhaus : IsHausdorff I M := by
      refine ⟨fun x hx ↦ ?_⟩
      have hx' : x ∈ (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A M) : Submodule A M) := by
        simpa [SModEq.zero] using hx
      simpa [hsep] using hx'
    exact (isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff hI).mpr
      ⟨hderived, hhaus⟩

end ModuleCat

end
