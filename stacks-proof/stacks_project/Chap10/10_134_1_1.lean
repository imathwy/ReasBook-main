import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

variable {R S R' S' : CommRingCat.{u}}
variable (α : R ⟶ S) (ρ : R ⟶ R') (β : R' ⟶ S') (φ : S ⟶ S')

/- Domain triage:
* primary domain: categorical commutative squares in `CommRingCat`;
* sampled owner API: `CategoryTheory.CommSq`, the earlier chapter recall in `10_131_4_1`,
  `CommRingCat.KaehlerDifferential.map`, and `CommRingCat.KaehlerDifferential.map_d`;
* source-facing layer: the displayed commutative square of commutative rings;
* core/canonical owner: `CategoryTheory.CommSq`;
* bridge/view: constructions on top of a ring square, such as the induced map on Kähler
  differentials.

The primitive data are just the four arrows in `CommRingCat`. Rewrapping underlying `RingHom`s by
`CommRingCat.ofHom` is derived presentation-level noise, so this file should use the same owner
surface already used earlier in the chapter. -/

/- 10.134.1.1: the displayed diagram is the commutative square of commutative rings with top map
`ρ : R ⟶ R'`, bottom map `φ : S ⟶ S'`, and vertical maps `α : R ⟶ S` and `β : R' ⟶ S'`. -/
#check CommSq ρ α β φ
