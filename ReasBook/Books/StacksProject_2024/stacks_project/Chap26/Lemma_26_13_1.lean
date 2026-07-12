import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the exact canonical mathlib owner
-- `AlgebraicGeometry.SpecToEquivOfLocalRing`, with projection lemmas
-- `SpecToEquivOfLocalRing_apply_fst` and `SpecToEquivOfLocalRing_apply_snd_coe`.

/- Lemma 26.13.1: for a scheme `X` and a local ring `R`, morphisms `Spec(R) ⟶ X`
are in bijection with pairs consisting of a point `x : X` and a local homomorphism
`𝒪_{X,x} ⟶ R`. In mathlib this is exactly
`AlgebraicGeometry.SpecToEquivOfLocalRing`, so this item is recorded as a pure
canonical recall. -/
recall AlgebraicGeometry.SpecToEquivOfLocalRing

section

variable (X : Scheme) (R : CommRingCat) [IsLocalRing R]

#check (SpecToEquivOfLocalRing X R :
    (Spec R ⟶ X) ≃ (x : X) × { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom })

end
