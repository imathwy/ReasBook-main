import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_151_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for Lemma 10.151.8:
- primary domain: étale and unramified commutative algebra over a base ring;
- sampled owner declarations:
  `Algebra.Etale`,
  `Algebra.Etale.of_formallyUnramified_of_flat`,
  `RingHom.Etale.iff_flat_and_formallyUnramified`,
  `Algebra.Unramified`;
- best owner abstraction: the canonical owner predicate `Algebra.Etale R S`, with the chapter-local
  bridge predicate `Algebra.GUnramified R S` encoding the source's "unramified of finite
  presentation";
- primitive data vs derived API: the primitive owner data are the canonical classes
  `Algebra.Etale`, `Algebra.Unramified`, `Algebra.FinitePresentation`, and `Module.Flat`. The
  chapter-local predicate `GUnramified` is bridge data extending `Unramified` and
  `FinitePresentation`, so this file should reuse those owners directly rather than keep any
  parallel wrapper API.

Source/core/bridge triage:
- `source-facing`: the Stacks equivalence "étale iff flat and G-unramified";
- `core/canonical`: `Algebra.Etale R S`;
- `bridge/view`: `Algebra.GUnramified R S`, relating the source wording to
  `Algebra.Unramified R S` and `Algebra.FinitePresentation R S`.
-/

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: this is the direct constructor/eliminator equivalence for the class
-- `Algebra.GUnramified R S`.
/-- A `GUnramified` algebra is equivalently an unramified algebra of finite presentation. -/
theorem gUnramified_iff_unramified_and_finitePresentation :
    GUnramified R S ↔ Unramified R S ∧ FinitePresentation R S := by
  constructor
  · intro h
    exact ⟨h.toUnramified, h.toFinitePresentation⟩
  · rintro ⟨hunramified, hfp⟩
    letI : Unramified R S := hunramified
    letI : FinitePresentation R S := hfp
    exact inferInstance

-- Proof sketch: `GUnramified` packages the owner predicate `Algebra.Unramified` together with
-- finite presentation. For `(1) ↔ (2)`, combine the standard facts that an étale algebra is flat,
-- unramified, and finitely presented with the criterion
-- `Algebra.Etale.of_formallyUnramified_of_flat`. Clause `(2) ↔ (3)` is exactly the source-facing
-- expansion of `GUnramified`.
/-- Lemma 10.151.8: for a ring map `R → S`, the following are equivalent: `R → S` is étale,
`R → S` is flat and G-unramified, and `R → S` is flat, unramified, and of finite presentation. -/
@[stacks 08WD]
theorem etale_tfae_flat_gUnramified_unramified_finitePresentation :
    List.TFAE
      [ Etale R S
      , Module.Flat R S ∧ GUnramified R S
      , Module.Flat R S ∧ Unramified R S ∧ FinitePresentation R S
      ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      letI : Etale R S := h
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hflat, hg⟩
      letI : Module.Flat R S := hflat
      letI : GUnramified R S := hg
      exact Etale.of_formallyUnramified_of_flat
  tfae_have 2 ↔ 3 := by
    rw [gUnramified_iff_unramified_and_finitePresentation]
  tfae_finish

/-- Étaleness is equivalent to flatness and G-unramifiedness. -/
theorem etale_iff_flat_and_gUnramified :
    Etale R S ↔ Module.Flat R S ∧ GUnramified R S :=
  etale_tfae_flat_gUnramified_unramified_finitePresentation.out 0 1

/-- Flatness and G-unramifiedness are equivalent to flatness, unramifiedness, and finite
presentation. -/
theorem flat_and_gUnramified_iff_flat_and_unramified_and_finitePresentation :
    Module.Flat R S ∧ GUnramified R S ↔
      Module.Flat R S ∧ Unramified R S ∧ FinitePresentation R S :=
  etale_tfae_flat_gUnramified_unramified_finitePresentation.out 1 2

end

end Algebra
