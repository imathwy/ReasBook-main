import Mathlib
import stacks_project.Chap16.Lemma_16_5_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [Module.Flat R Λ]

/- Domain-style sampling for PT across nilpotent thickenings:
* primary domain: commutative algebra of filtered colimits of smooth algebras and nilpotent
  thickenings;
* sampled owner declarations:
  `RingHom.IsFilteredColimitOfSmooth`,
  `exists_smooth_quotient_factorization_of_square_zero`,
  `exists_smooth_factorization_killing_ideal_of_square_zero`,
  `Ideal.IsNilpotent`;
* best owner abstraction: `(algebraMap R Λ).IsFilteredColimitOfSmooth`;
* primitive data: the nilpotent ideal `I`, flatness of `R → Λ`, and the PT hypothesis on the
  quotient map;
* derived API: any chosen filtered diagram presenting PT and the square-zero induction step used
  in the proof.

Source/core/bridge triage:
* `source-facing`: the nilpotent-thickening lifting statement of Proposition `16.5.3`;
* `core/canonical`: `RingHom.IsFilteredColimitOfSmooth`;
* `bridge/view`: the square-zero factorization results from Lemmas `16.5.1` and `16.5.2`.

This item stays source-facing, but its public statement should be phrased directly in the canonical
owner `RingHom.IsFilteredColimitOfSmooth` rather than through any auxiliary presentation data.
-/

-- Proof sketch: choose `n` with `I ^ n = ⊥` and argue by induction on `n`, reducing to the
-- square-zero case. To apply the factorization criterion for filtered colimits of smooth
-- algebras, start from a finitely presented `R`-algebra mapping to `Λ`, use Lemma `16.5.1` to
-- write it as a quotient `B ⧸ J` of a smooth `R`-algebra with `J ⊆ IB` finitely generated, and
-- then apply Lemma `16.5.2` to kill `J` after passing to another smooth `R`-algebra. The map
-- from the finitely presented algebra then factors through a smooth `R`-algebra, which is the
-- desired factorization criterion.
/-- Proposition 16.5.3: let `R → Λ` be a flat ring map and `I ⊂ R` a nilpotent ideal. If
`Λ ⧸ IΛ` is a filtered colimit of smooth `(R ⧸ I)`-algebras, then `Λ` is a filtered colimit of
smooth `R`-algebras. -/
theorem isFilteredColimitOfSmooth_of_nilpotent_quotient
    (I : Ideal R) (hI : IsNilpotent I)
    (hquot : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth) :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := sorry

end

end Algebra
