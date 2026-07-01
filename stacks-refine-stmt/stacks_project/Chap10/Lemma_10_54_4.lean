import stacks_project.Chap10.Definition_10_54_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsArtinianRing S] [IsLocalRing S]

omit [IsArtinianRing S] in
private theorem residue_finite : (residue S).Finite :=
  RingHom.Finite.of_surjective _ residue_surjective

omit [IsArtinianRing S] in
private theorem residue_finiteType : (residue S).FiniteType :=
  RingHom.FiniteType.of_surjective _ residue_surjective

omit [IsArtinianRing S] in
private theorem residue_essFiniteType : (residue S).EssFiniteType :=
  residue_finiteType.essFiniteType

-- Proof sketch: the forward implication is stability of finiteness under passage to the residue
-- field via the canonical composition theorem `RingHom.Finite.comp`. For the reverse implication,
-- use that an Artinian local ring has finite length over itself with successive quotients
-- isomorphic to `ResidueField S`, then deduce finite generation over `R` by induction on the
-- filtration length.
/-- Lemma 10.54.4 (1): for a ring map `R → S` with `S` an Artinian local ring, the map is finite
if and only if the induced map to the residue field of `S` is finite. -/
theorem finite_iff_finite_residue (f : R →+* S) :
    f.Finite ↔ ((residue S).comp f).Finite := by
  constructor
  · intro hf
    exact residue_finite.comp hf
  · intro h
    sorry

-- Proof sketch: the forward implication is stability of finite type under passage to the residue
-- field via the canonical composition theorem `RingHom.FiniteType.comp`. For the reverse
-- implication, choose lifts in `S` of generators of `ResidueField S`, map a polynomial ring over
-- `R` onto those lifts, and then apply part (1) to show the polynomial algebra maps finitely to
-- `S`, which makes `R → S` finite type.
/-- Lemma 10.54.4 (2): for a ring map `R → S` with `S` an Artinian local ring, the map is of
finite type if and only if the induced map to the residue field of `S` is of finite type. -/
theorem finiteType_iff_finiteType_residue (f : R →+* S) :
    f.FiniteType ↔ ((residue S).comp f).FiniteType := by
  constructor
  · intro hf
    exact residue_finiteType.comp hf
  · intro h
    sorry

-- Proof sketch: the forward implication is stability of essential finite type under composition,
-- applied to the essentially finite type residue map. For the reverse implication, present
-- `ResidueField S` as a localization of a finite type `R`-algebra, lift the chosen generators to
-- `S`, form the induced finite type subalgebra `A ⊆ S`, and apply part (1) to the local map
-- `A_(A ∩ maximalIdeal S) → S`.
/-- Lemma 10.54.4 (3): for a ring map `R → S` with `S` an Artinian local ring, the map is
essentially of finite type if and only if the induced map to the residue field of `S` is
essentially of finite type. -/
theorem essFiniteType_iff_essFiniteType_residue (f : R →+* S) :
    f.EssFiniteType ↔ ((residue S).comp f).EssFiniteType := by
  constructor
  · intro hf
    exact hf.comp residue_essFiniteType
  · intro h
    sorry

end
