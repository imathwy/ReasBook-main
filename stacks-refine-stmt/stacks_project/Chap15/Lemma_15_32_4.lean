import Mathlib
import stacks_project.Chap15.Definition_15_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

namespace Ideal

/-
Domain-style sampling:
* primary domain: faithfully flat descent for local ideal-regularity predicates in commutative
  algebra;
* sampled owner declarations:
  `Ideal.IsKoszulRegularIdeal`,
  `Ideal.IsH1RegularIdeal`,
  `Ideal.IsQuasiRegularIdeal`,
  `RingHom.FaithfullyFlat`,
  `RingHom.faithfullyFlat_algebraMap_iff`;
* best owner abstraction: the chapter owner predicates
  `Ideal.IsKoszulRegularIdeal`, `Ideal.IsH1RegularIdeal`, and `Ideal.IsQuasiRegularIdeal` from
  `Definition_15_32_1`, together with the canonical faithfully flat owner
  `(algebraMap A B).FaithfullyFlat`; the mapped ideal `I.map (algebraMap A B)` and the localized
  generating sequences in the proof sketches are derived bridge data, not new public owners;
* primitive vs. derived split:
  the primitive inputs are the faithfully flatness witness `hff : (algebraMap A B).FaithfullyFlat`
  and the owner predicate on `I.map (algebraMap A B)`;
  lying-over primes, localizations, and descended finite generating sequences are derived proof
  data;
* layer: `bridge/view`, because this file transports existing owner predicates along a faithfully
  flat algebra map rather than defining a new notion.
-/

namespace IsKoszulRegularIdeal

-- Proof sketch: unwind `IsKoszulRegularIdeal` on the extended ideal `I.map (algebraMap A B)`.
-- For a prime `p ⊇ I`, choose a prime of `B` above `p` by faithful flatness, use the local
-- generation of the extended ideal by a finite Koszul-regular sequence near that prime, and then
-- descend the localized sequence back along the induced faithfully flat local map.
/-- Lemma 15.32.4 (1): if `A → B` is faithfully flat and the extended ideal `IB` is
Koszul-regular in `B`, then `I` is Koszul-regular in `A`. -/
theorem of_faithfullyFlat {I : Ideal A} (hff : (algebraMap A B).FaithfullyFlat)
    (hIB : (I.map (algebraMap A B)).IsKoszulRegularIdeal) : I.IsKoszulRegularIdeal := by
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hff
  letI : Module.FaithfullyFlat A B := hff
  sorry

end IsKoszulRegularIdeal

namespace IsH1RegularIdeal

-- Proof sketch: as in the Koszul-regular case, work primewise on `Spec A`, lift a prime
-- containing `I` to one of `B`, obtain a local finite `H_1`-regular generating sequence for the
-- extended ideal, and descend `H_1`-regularity through the resulting faithfully flat local map.
/-- Lemma 15.32.4 (2): if `A → B` is faithfully flat and the extended ideal `IB` is
`H_1`-regular in `B`, then `I` is `H_1`-regular in `A`. -/
theorem of_faithfullyFlat {I : Ideal A} (hff : (algebraMap A B).FaithfullyFlat)
    (hIB : (I.map (algebraMap A B)).IsH1RegularIdeal) : I.IsH1RegularIdeal := by
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hff
  letI : Module.FaithfullyFlat A B := hff
  sorry

end IsH1RegularIdeal

namespace IsQuasiRegularIdeal

-- Proof sketch: first use faithful flat descent of finite generation and finite projectivity on
-- the conormal module to obtain local generators of `I`. Then descend the defining symmetric-power
-- isomorphisms for quasi-regularity from the faithfully flat base change `B`, again working
-- Zariski-locally near each prime of `A` containing `I`.
/-- Lemma 15.32.4 (3): if `A → B` is faithfully flat and the extended ideal `IB` is
quasi-regular in `B`, then `I` is quasi-regular in `A`. -/
theorem of_faithfullyFlat {I : Ideal A} (hff : (algebraMap A B).FaithfullyFlat)
    (hIB : (I.map (algebraMap A B)).IsQuasiRegularIdeal) : I.IsQuasiRegularIdeal := by
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hff
  letI : Module.FaithfullyFlat A B := hff
  sorry

end IsQuasiRegularIdeal

end Ideal

end
