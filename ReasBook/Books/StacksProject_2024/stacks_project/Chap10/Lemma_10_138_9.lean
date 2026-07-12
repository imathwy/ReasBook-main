import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: the transitivity sequence for Kähler differentials over a tower
  `A → B → C`, under the formal-smoothness hypothesis on `B → C`;
- sampled owner declarations:
  - `KaehlerDifferential.mapBaseChange`,
  - `KaehlerDifferential.map`,
  - `KaehlerDifferential.exact_mapBaseChange_map`,
  - `Algebra.formallySmooth_iff`;
- best owner abstraction: the canonical `KaehlerDifferential` maps in the transitivity sequence,
  with projectivity/subsingleton data supplied by `Algebra.formallySmooth_iff`;
- primitive data: a tower of commutative rings `A → B → C` and the formal smoothness of `B → C`;
- derived API: injectivity of `KaehlerDifferential.mapBaseChange A B C` and a `C`-linear section
  of `KaehlerDifferential.map A B C C`;
- layer triage:
  - `source-facing`: split exactness of the transitivity sequence
    `0 → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`;
  - `core/canonical`: the owner maps `KaehlerDifferential.mapBaseChange A B C` and
    `KaehlerDifferential.map A B C C`, together with the upstream exactness/surjectivity and
    formal-smoothness characterizations;
  - `bridge/view`: the source-facing split statement below, phrased directly as injectivity of the
    left map and a section of the right map.

The previous theorem used `Function.RightInverse`, which is less canonical than the linear-map
section equation already used throughout this chapter. The refined statement keeps the same
mathematics while exposing the split data in the owner-facing form
`(KaehlerDifferential.map A B C C).comp s = LinearMap.id`.
-/

-- Proof sketch: formal smoothness of `B → C` gives `Module.Projective C Ω[C⁄B]`, so the
-- surjection `KaehlerDifferential.map A B C C` from Lemma `10.131.7` splits by
-- `Module.Projective.iff_split_of_projective`. The Jacobi-Zariski exact sequence of
-- Lemma `10.134.4` and the subsingleton property of `H¹(L_{C/B})` coming from formal smoothness
-- force `KaehlerDifferential.mapBaseChange A B C` to be injective.
/-- Lemma 10.138.9: if `B → C` is formally smooth, then in the canonical sequence
`0 → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`
of Lemma `10.131.7`, the left map is injective and the right map admits a `C`-linear section.
Equivalently, this sequence is split short exact. -/
theorem kaehlerDifferential_transitivity_sequence_splits_of_formallySmooth
    [Algebra.FormallySmooth B C] :
    Function.Injective (KaehlerDifferential.mapBaseChange A B C) ∧
      ∃ s : Ω[C⁄B] →ₗ[C] Ω[C⁄A],
        (KaehlerDifferential.map A B C C).comp s = LinearMap.id := sorry

end
