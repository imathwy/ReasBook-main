import Mathlib
import stacks_project.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- 
Source/core/bridge triage:
* primary domain: commutative algebra of depth, regular sequences, and localization at primes;
* sampled owner API: `Ideal.depth`, `Ideal.regularSequenceLengths`,
  `Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top` from the local chapter owner file, together
  with mathlib's `Module.supportDim_add_length_eq_supportDim_of_isRegular`;
* layer: `source-facing`, since this item is a finiteness consequence for the existing owner
  object `Ideal.depth`, not a new definition of depth data;
* primitive vs derived split: the primitive data are only the ideal `I`, the finite module `M`,
  and the owner predicate `Sequence.IsRegular M rs`; finiteness is a derived theorem, so this file
  should stay a thin companion to the owner abstraction instead of introducing a parallel wrapper.
-/

-- Proof sketch: `I • ⊤ ≠ ⊤` already forces `M` to be nontrivial; otherwise `⊤ = ⊥`, hence
-- `I • ⊤ = ⊤`. The quotient `M ⧸ I • ⊤` is then nonzero, so choose a prime in its support and
-- localize there. Any `M`-regular sequence in `I` localizes to an `M_𝔭`-regular sequence in
-- `I_𝔭`, so `depth I M` is bounded by the depth of the localized module, which is finite by
-- Lemma 10.72.3.
/-- Lemma 10.72.4: if `R` is Noetherian, `I ⊆ R` is an ideal, and `M` is a finite `R`-module
with `IM ≠ M`, then the `I`-depth of `M` is finite. -/
theorem depth_lt_top_of_smul_top_ne_top (I : Ideal R)
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    I.depth M < ⊤ := by
  letI : Nontrivial M := by
    by_contra hM
    letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    have htop : (⊤ : Submodule R M) = ⊥ := (⊤ : Submodule R M).eq_bot_of_subsingleton
    exact hIM <| by rw [htop, Submodule.smul_bot]
  sorry

end Ideal
