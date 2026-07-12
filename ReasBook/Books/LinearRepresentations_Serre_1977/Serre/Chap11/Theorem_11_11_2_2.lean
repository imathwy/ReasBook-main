import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace Representation

open scoped Representation

section FrobeniusTheorem

variable {G : Type u} [Group G] [Finite G]

-- Source/core/bridge triage:
-- * source-facing: the weighted Adams transform of the conjugacy-class indicator `c.indicator`.
-- * core/canonical: the owner theorem on `classFunctionSubmodule A G`, specialized along the
--   canonical datum `c.indicatorClassFunctionSubmodule`.
-- * bridge/view: membership in `characterRingScalarExtension A G`.

-- Proof sketch: apply Theorem `11-11.2-1` to the class function `f_c = c.indicator`;
-- the previous lemma provides the needed conjugacy-invariance hypothesis.
/-- Theorem 11-11.2-2: for each conjugacy class `c` of `G`, if `A` contains the
`Nat.card G`-th roots of unity as in Serre's source convention, the globally weighted Adams
transform of `f_c` belongs to Serre's `A ⊗ R(G)`.

This is Serre's Theorem 23' with the global multiplier `|G| / (|G|, n)`, not the stronger
pointwise multiplier `orderOf g / (orderOf g, n)`. -/
theorem weighted_adamsOperator_conjClassIndicator_lifts_to_tensorCharacterRing
    (A : Type v) [CommRing A] [Algebra A ℂ] (n : ℕ+) (c : ConjClasses G)
    (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    ∃ χ : A ⊗R(G),
      χ =
        fun g ↦
          algebraMap A ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
              Ψ^n(c.indicator) g) := by
  let f : classFunctionSubmodule A G := c.indicatorClassFunctionSubmodule
  simpa using
    frobenius_weighted_adamsOperator_lifts_to_tensorCharacterRing n f hroots

/-- Companion bridge form of Theorem 11-11.2-2 in the realized span
`characterRingScalarExtension A G`. -/
theorem weighted_adamsOperator_conjClassIndicator_mem_characterRingScalarExtension
    (A : Type v) [CommRing A] [Algebra A ℂ] (n : ℕ+) (c : ConjClasses G)
    (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    (fun g ↦
      algebraMap A ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
          Ψ^n(c.indicator) g)) ∈
      characterRingScalarExtension A G := by
  let f : classFunctionSubmodule A G := c.indicatorClassFunctionSubmodule
  simpa using
    frobenius_weighted_adamsOperator_mem_characterRingScalarExtension n f hroots

end FrobeniusTheorem

end Representation
