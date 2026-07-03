import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Spectrum.Prime.RingHom

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_19_1 (from Chap10) -/
universe u

section

open Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Lemma 10.19.1: an ideal `I` is contained in the Jacobson radical of `R` if and only if every
element of `1 + I` is a unit of `R`. -/
-- Proof sketch: rewrite `Ring.jacobson R` as `Ideal.jacobson (⊥ : Ideal R)`. The forward
-- direction evaluates the owner characterization `Ideal.mem_jacobson_bot` at `y = 1`;
-- conversely, use `Ideal.mem_jacobson_bot` and test `f` against the elements `f * y`.
theorem ideal_le_ring_jacobson_iff_isUnit_one_add :
    I ≤ Ring.jacobson R ↔ ∀ f ∈ I, IsUnit (1 + f) := by
  rw [← jacobson_bot]
  constructor
  · intro h f hf
    simpa [add_comm] using (mem_jacobson_bot.mp (h hf)) 1
  · intro h f hf
    exact mem_jacobson_bot.2 fun y ↦ by
      simpa [add_comm] using h (f * y) (I.mul_mem_right y hf)

end

/-! ### Lemma_10_19_2 (from Chap10) -/
universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.19.2: if the induced map `Spec S → Spec R` is surjective, then an element `x : R`
is a unit if and only if its image `φ x : S` is a unit. -/
-- Proof sketch: surjectivity of `PrimeSpectrum.comap φ` upgrades `φ` to the canonical owner
-- abstraction `IsLocalHom φ` via `IsLocalHom.of_comap_surjective`; then `isUnit_map_iff` is
-- exactly the needed equivalence, modulo the textbook order of the two sides.
theorem isUnit_iff_isUnit_map_of_comap_surjective
    (φ : R →+* S) (hφ : Function.Surjective (PrimeSpectrum.comap φ)) (x : R) :
    IsUnit x ↔ IsUnit (φ x) := by
  haveI : IsLocalHom φ := IsLocalHom.of_comap_surjective φ hφ
  exact (isUnit_map_iff φ x).symm
