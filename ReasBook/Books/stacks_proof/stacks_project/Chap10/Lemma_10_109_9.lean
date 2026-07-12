import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

variable {R : Type u} [Ring R] {S : ShortComplex (ModuleCat.{v} R)}

/- Domain-style sampling:
* primary domain: projective dimension in the abelian category `ModuleCat R`, specialized to short
  exact sequences;
* sampled owner declarations:
  `HasProjectiveDimensionLE`,
  `HasProjectiveDimensionLT`,
  `ShortExact.hasProjectiveDimensionLT_X₁`,
  `ShortExact.hasProjectiveDimensionLT_X₂`,
  `ShortExact.hasProjectiveDimensionLT_X₃`;
* best owner abstraction: the canonical owner data is `hS : S.ShortExact`, and the `LT` lemmas are
  the core/canonical API;
* layer triage:
  the three `hasProjectiveDimensionLE_Xᵢ` theorems below are `bridge/view` declarations translating
  the source-facing `≤ n` formulation into the canonical `LT` owner lemmas;
* primitive data: `hS : S.ShortExact`;
* derived API: the `LE` bounds, obtained from the owner lemmas via
  `HasProjectiveDimensionLE X n = HasProjectiveDimensionLT X (n + 1)`.
-/

-- Proof sketch: rewrite the hypotheses and conclusion from `HasProjectiveDimensionLE` to
-- `HasProjectiveDimensionLT` using the successor shift, then apply the canonical short-exact
-- lemma `hS.hasProjectiveDimensionLT_X₁`.
/-- Lemma 10.109.9 (1): in a short exact sequence `0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules, if the
middle term has projective dimension at most `n` and the cokernel has projective dimension at most
`n + 1`, then the kernel has projective dimension at most `n`. -/
@[stacks 065S]
theorem hasProjectiveDimensionLE_X₁ (hS : S.ShortExact) (n : ℕ)
    (h₂ : HasProjectiveDimensionLE S.X₂ n)
    (h₃ : HasProjectiveDimensionLE S.X₃ (n + 1)) :
    HasProjectiveDimensionLE S.X₁ n := by
  simpa [HasProjectiveDimensionLE] using hS.hasProjectiveDimensionLT_X₁ (n + 1) h₂ h₃

-- Proof sketch: convert both hypotheses and the conclusion to the corresponding
-- `HasProjectiveDimensionLT` bounds and apply the canonical short-exact lemma
-- `hS.hasProjectiveDimensionLT_X₂`.
/-- Lemma 10.109.9 (2): in a short exact sequence `0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules, if the
kernel and cokernel both have projective dimension at most `n`, then the middle term has
projective dimension at most `n`. -/
@[stacks 065S]
theorem hasProjectiveDimensionLE_X₂ (hS : S.ShortExact) (n : ℕ)
    (h₁ : HasProjectiveDimensionLE S.X₁ n)
    (h₃ : HasProjectiveDimensionLE S.X₃ n) :
    HasProjectiveDimensionLE S.X₂ n := by
  simpa [HasProjectiveDimensionLE] using hS.hasProjectiveDimensionLT_X₂ (n + 1) h₁ h₃

-- Proof sketch: view `HasProjectiveDimensionLE S.X₁ n` as
-- `HasProjectiveDimensionLT S.X₁ (n + 1)` and `HasProjectiveDimensionLE S.X₂ (n + 1)` as
-- `HasProjectiveDimensionLT S.X₂ (n + 2)`, then apply `hS.hasProjectiveDimensionLT_X₃ (n + 1)`.
/-- Lemma 10.109.9 (3): in a short exact sequence `0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules, if the
kernel has projective dimension at most `n` and the middle term has projective dimension at most
`n + 1`, then the cokernel has projective dimension at most `n + 1`. -/
@[stacks 065S]
theorem hasProjectiveDimensionLE_X₃ (hS : S.ShortExact) (n : ℕ)
    (h₁ : HasProjectiveDimensionLE S.X₁ n)
    (h₂ : HasProjectiveDimensionLE S.X₂ (n + 1)) :
    HasProjectiveDimensionLE S.X₃ (n + 1) := by
  simpa [HasProjectiveDimensionLE] using hS.hasProjectiveDimensionLT_X₃ (n + 1) h₁ h₂

end ShortExact
end ShortComplex
end CategoryTheory
