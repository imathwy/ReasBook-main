import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Layering for this item:
* source-facing: `faithfullyFlat_iff_closedPoints_subset_range`, the textbook closed-point
  criterion for faithful flatness;
* core/canonical owner: `RingHom.FaithfullyFlat`, `PrimeSpectrum.comap`,
  `StableUnderGeneralization`, and `closedPoints`;
* bridge/view: `specComap_surjective_iff_closedPoints_subset_range`, which rewrites the
  source criterion through the owner theorem
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`.
-/

-- Proof sketch: for the forward direction, surjectivity obviously implies that every closed point
-- lies in the image. For the converse, the image of `Spec(S) → Spec(R)` is stable under
-- generalization for a flat map, so containing all closed points forces surjectivity.
/-- Lemma 10.39.16, clauses (2) and (3): for a flat ring map `f : R →+* S`, the induced map
`Spec(S) → Spec(R)` is surjective if and only if every closed point of `Spec(R)` lies in its
image. -/
theorem specComap_surjective_iff_closedPoints_subset_range (f : R →+* S) (hf : f.Flat) :
    Function.Surjective (comap f) ↔ closedPoints (PrimeSpectrum R) ⊆ Set.range (comap f) := by
  constructor
  · intro h x hx
    exact Set.mem_range.mpr (h x)
  · intro hclosed x
    let image : Set (PrimeSpectrum R) := Set.range (comap f)
    have himage : StableUnderGeneralization image :=
      (RingHom.Flat.generalizingMap_comap hf).stableUnderGeneralization_range
    obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.2.1
    let xMax : PrimeSpectrum R := ⟨m, hm.isPrime⟩
    have hxMax : xMax ∈ image := by
      apply hclosed
      simpa [closedPoints] using
        (isClosed_singleton_iff_isMaximal xMax).2 hm
    exact himage ((le_iff_specializes x xMax).mp hxm) hxMax

/-- Lemma 10.39.16: for a flat ring map `f : R →+* S`, `f` is faithfully flat if and only if
every closed point of `Spec(R)` lies in the image of `Spec(S) → Spec(R)`. Together with the
canonical theorem `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`, this recovers the
textbook three-way equivalence with surjectivity of `Spec(S) → Spec(R)`. -/
theorem faithfullyFlat_iff_closedPoints_subset_range (f : R →+* S) (hf : f.Flat) :
    f.FaithfullyFlat ↔ closedPoints (PrimeSpectrum R) ⊆ Set.range (comap f) := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective,
    specComap_surjective_iff_closedPoints_subset_range f hf]
  exact and_iff_right hf

end
