import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Cardinal
open PrimeSpectrum

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: commutative algebra of flat and faithfully flat algebra maps;
* source-facing owner: the `Subalgebra`-property
  `Subalgebra.IsFlatOfBoundedCardinality`, indexed canonically by the subtype
  `{S : Subalgebra A B // S.IsFlatOfBoundedCardinality}`;
* bridge/view owner for faithful flatness: `PrimeSpectrum.comap`, with faithful flatness recovered
  from `Module.FaithfullyFlat.of_comap_surjective`.

Sampled owner-style API in this domain:
* `Subalgebra.coe_iSup_of_directed`, the canonical lattice owner for directed unions of
  subalgebras;
* `Algebra.exists_directed_globalCompleteIntersection_subalgebra_family` and
  `Algebra.exists_directed_smooth_subalgebra_family`, nearby project theorems stated directly on
  chosen subalgebra families;
* `Algebra.isGeometricallyRegular_of_directed_iSup_subfields`, a neighboring theorem stated
  directly in terms of `Directed` and `iSup`.

Layer triage:
* `source-facing`: the canonical subtype of bounded flat `A`-subalgebras of `B`;
* `bridge/view`: faithful flatness of a flat subalgebra, expressed through the canonical owner map
  on prime spectra.

Primitive data for the source-facing statement are exactly the subalgebras `S : Subalgebra A B`
with `S.IsFlatOfBoundedCardinality`; directedness and the supremum statement are derived properties
of the resulting subtype-indexed family, so no auxiliary wrapper owner is kept.
-/

namespace Subalgebra

/-- An `A`-subalgebra of `B` that is flat over `A` and has cardinality at most `max (|A|, ℵ₀)`. -/
def IsFlatOfBoundedCardinality (S : Subalgebra A B) : Prop :=
  Module.Flat A S ∧ #S ≤ #A ⊔ ℵ₀

end Subalgebra

-- Proof sketch: start from each finite subset of `B`, take the `A`-subalgebra it generates, and
-- enlarge it inductively using the equational criterion of flatness so that every relation over
-- the current stage becomes trivial in the next stage. The union of the resulting countable tower
-- is flat, still has cardinality at most `max (|A|, ℵ₀)`, and every element of `B` lies in some
-- such stage, yielding a directed family with supremum `⊤`.
namespace Subalgebra

/-- Lemma 10.159.4: the canonical family of flat `A`-subalgebras of `B` of cardinality at most
`max (|A|, ℵ₀)` is directed by inclusion. -/
theorem directed_flatSubalgebras_of_boundedCardinality [Module.Flat A B] :
    Directed (· ≤ ·)
      (Subtype.val : { S : Subalgebra A B // S.IsFlatOfBoundedCardinality } → Subalgebra A B) :=
  sorry

/-- Lemma 10.159.4: the supremum of the canonical family of flat `A`-subalgebras of `B` of
cardinality at most `max (|A|, ℵ₀)` is `⊤`. Equivalently, the flat `A`-algebra `B` is the
filtered colimit of its flat `A`-subalgebras of bounded cardinality. -/
theorem iSup_flatSubalgebras_of_boundedCardinality_eq_top [Module.Flat A B] :
    iSup
        (Subtype.val :
          { S : Subalgebra A B // S.IsFlatOfBoundedCardinality } → Subalgebra A B) =
      (⊤ : Subalgebra A B) := sorry

end Subalgebra

-- Proof sketch: the owner theorem `PrimeSpectrum.comap_surjective_of_faithfullyFlat` gives a
-- prime of `B` over every prime of `A`. Contracting that prime along the inclusion `S ↪ B` shows
-- that `Spec S → Spec A` is surjective. Together with the flatness hypothesis on `S`, this gives
-- faithful flatness by the standard criterion
-- `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`.
/-- A flat `A`-subalgebra of a faithfully flat `A`-algebra is faithfully flat over `A`. -/
theorem faithfullyFlat_of_flat_subalgebra [Module.FaithfullyFlat A B] (S : Subalgebra A B)
    [Module.Flat A S] :
    Module.FaithfullyFlat A S := by
  refine Module.FaithfullyFlat.of_comap_surjective fun p ↦ ?_
  have hsurj : Function.Surjective (comap (algebraMap A B)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  obtain ⟨q, rfl⟩ := hsurj p
  exact ⟨comap S.val q, by rw [← comap_comp_apply, S.val.comp_algebraMap]⟩

end
