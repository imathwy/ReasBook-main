import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- Lemma 10.18.4: for a ring map `φ : R →+* S` between local rings, the following are
equivalent: `φ` is a local ring homomorphism, the image of the maximal ideal of `R` is contained
in the maximal ideal of `S`, the preimage of the maximal ideal of `S` is the maximal ideal of
`R`, and every element of `R` whose image is a unit in `S` is already a unit in `R`. -/
-- Proof sketch: clauses `(1)`, `(2)`, and `(3)` are exactly clauses `(1)`, `(2)`, and `(5)` of
-- the canonical owner theorem `IsLocalRing.local_hom_TFAE φ`; clause `(4)` is the primitive
-- unit-reflection field of `IsLocalHom φ`.
@[stacks 07BJ]
theorem local_ring_hom_tfae (φ : R →+* S) :
    List.TFAE
      [IsLocalHom φ,
        φ '' maximalIdeal R ⊆ maximalIdeal S,
        (maximalIdeal S).comap φ = maximalIdeal R,
        ∀ x : R, IsUnit (φ x) → IsUnit x] := by
  have hφ := local_hom_TFAE φ
  tfae_have 1 ↔ 2 := hφ.out 0 1
  tfae_have 1 ↔ 3 := hφ.out 0 4
  tfae_have 1 ↔ 4 := by
    constructor
    · intro h x hx
      letI := h
      exact IsUnit.of_map φ x hx
    · intro h
      exact ⟨h⟩
  tfae_finish

end
