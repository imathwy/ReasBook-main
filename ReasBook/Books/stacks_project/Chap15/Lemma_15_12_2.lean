import Mathlib
import stacks_project.Chap15.Lemma_15_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

namespace RingPairCat

section

variable (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint]

/-
Domain-style sampling:
- primary domain: henselization of commutative ring pairs `(A, I)` and its canonical algebraic
  consequences on ideals and quotient rings;
- sampled owner declarations of the same kind:
  `toHenselization`,
  `henselizationIdeal`,
  `RingHom.Flat`,
  `Ideal.quotientMap`;
- best owner abstraction: this file is `source-facing` for the basic properties of the canonical
  map `(A, I) → (A^h, I^h)`, while the quotient comparison itself is already owned by
  `Ideal.quotientMap` and should be stated on the source-facing ideal owner `henselizationIdeal`;
- primitive data: the chosen henselization owner from `Lemma_15_12_1`;
- derived API: flatness of `toHenselization X`, identification of `I^h` with the mapped ideal,
  and bijectivity of the induced quotient map; the power-identification transport needed to build
  the quotient comparison is implementation-level and not kept as a parallel public theorem.

Source/core/bridge triage:
- `source-facing`: `toHenselization_flat`, `henselizationIdeal_eq_map`,
  `quotientPowToHenselization_bijective`;
- `core/canonical`: `toHenselization`, `henselizationIdeal`, `RingHom.Flat`, `Ideal.map`,
  `Ideal.quotientMap`;
- `bridge/view`: the quotient comparison is transported across the canonical equality
  `(henselizationIdeal X) ^ n = Ideal.map (toHenselization X) (X.ideal ^ n)` coming from
  `henselizationIdeal_eq_map` and `Ideal.map_pow`, rather than exposed as a second public
  owner-level theorem.
-/

-- Proof sketch: in Lemma `15.12.1`, the henselization pair is constructed as a filtered colimit
-- of étale neighborhoods of `(A, I)` with unchanged special fiber. Étale morphisms are flat, and
-- filtered colimits of flat algebras remain flat.
/-- Lemma 15.12.2 (1): for a pair `X = (A, I)`, the canonical map from `A` to its henselization
`A^h` is flat. -/
theorem toHenselization_flat :
    RingHom.Flat (toHenselization X) := sorry

-- Proof sketch: each stage in the filtered system used to construct the henselization has ideal
-- equal to the extension of `I`, and this equality is preserved when passing to the colimit.
/-- Lemma 15.12.2 (2): for a pair `X = (A, I)`, the distinguished ideal `I^h` of the henselization
is exactly the extension of `I` along the canonical map `A → A^h`. -/
theorem henselizationIdeal_eq_map :
    henselizationIdeal X = Ideal.map (toHenselization X) X.ideal := sorry

-- Proof sketch: the étale neighborhoods in the construction of `A^h` are flat over `A`, hence
-- reduction modulo `I ^ n` is unchanged at every stage. Passing to the filtered colimit gives a
-- bijection on the quotient rings, written directly on the source-facing henselization quotient
-- `A^h / (I^h)^n`; the mapped-ideal quotient presentation is recovered from
-- `henselizationIdeal_eq_map` together with `Ideal.map_pow`.
/-- Lemma 15.12.2 (3): for every `n`, the canonical map `A / I^n → A^h / (I^h)^n` is bijective. -/
theorem quotientPowToHenselization_bijective (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        ((henselizationIdeal X) ^ n)
        (toHenselization X)
        (by
          simpa [henselizationIdeal_eq_map X, ← Ideal.map_pow] using
            (Ideal.le_comap_map :
              X.ideal ^ n ≤
                Ideal.comap (toHenselization X)
                  (Ideal.map (toHenselization X) (X.ideal ^ n))))) := sorry

end

end RingPairCat
