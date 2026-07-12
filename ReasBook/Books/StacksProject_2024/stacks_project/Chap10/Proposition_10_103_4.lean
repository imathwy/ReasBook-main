import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory Sequence IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module

/- 
Source/core/bridge triage:
* source-facing: Proposition `10.103.4` is the textbook criterion that a sequence in the maximal
  ideal of a Cohen-Macaulay local module is regular, and hence extends to a maximal regular
  sequence, once the quotient has the expected support dimension;
* core/canonical: `CohenMacaulay R M`, `supportDim R M`, and `RingTheory.Sequence.IsRegular M`;
* bridge/view: the quotient module `M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))`.

Primitive data are only the maximal-ideal membership of `gs`, the ambient support dimension of
`M`, and the owner-level additive equality
`supportDim R (M ⧸ (Ideal.ofList gs • ⊤)) + gs.length = supportDim R M`. The maximal extension is
derived from the existing regular-sequence extension theorem to depth, so this file should not
repackage that owner API through a separate truncated-subtraction condition.
-/

-- Proof sketch: compare the support dimensions of the successive quotients by the prefixes of
-- `gs` using the one-step bound from Lemma `10.60.13`; the hypothesis `hquot` forces each step to
-- drop the support dimension by exactly one. Apply Lemma `10.103.3` inductively to show that each
-- element of `gs` is a nonzerodivisor on the preceding quotient, hence `gs` is `M`-regular.
-- Then use prime avoidance to choose further elements of `maximalIdeal R` that keep lowering the
-- support dimension until the sequence has length `d`, which is maximal because `M` is
-- Cohen-Macaulay and `hMdim` identifies `d` with `dim (Supp M)`.
/-- Proposition 10.103.4: if `M` is a Cohen-Macaulay module over a Noetherian local ring `R`,
`gs` is a list of elements of `maximalIdeal R`, `dim (Supp M) = d`, and the quotient by the
submodule `(g₁, …, g_c)M`, written as `M ⧸ (Ideal.ofList gs • ⊤)`, has support dimension
`dim (Supp M) - c` in the canonical owner form
`supportDim R (M ⧸ (Ideal.ofList gs • ⊤)) + gs.length = supportDim R M`, then `gs` extends to an
`M`-regular sequence of length `d`. In a local ring, containment of the extended sequence in
`maximalIdeal R` is recovered from regularity by the auxiliary companion
`IsRegular.ofList_le_maximalIdeal`. Since `M` is
Cohen-Macaulay, this is a maximal `M`-regular sequence. -/
theorem exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay
    [CohenMacaulay R M] {gs : List R} {d : ℕ} (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hMdim : Module.supportDim R M = d)
    (hquot :
      Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))) + gs.length =
        Module.supportDim R M) :
    ∃ gs' : List R,
      IsRegular M (gs ++ gs') ∧ d = (gs ++ gs').length := sorry

-- Proof sketch: apply
-- `exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay`
-- then pass from regularity of the appended sequence to regularity of its initial segment `gs`.
/-- If the quotient by `(g₁, …, g_c)M` has the expected support dimension drop in a
Cohen-Macaulay module, then `gs` itself is an `M`-regular sequence. -/
theorem isRegular_of_supportDim_quotient_add_length_eq_of_cohenMacaulay [CohenMacaulay R M]
    {gs : List R} {d : ℕ} (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hMdim : Module.supportDim R M = d)
    (hquot :
      Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))) + gs.length =
        Module.supportDim R M) :
    IsRegular M gs := sorry

end Module

end
