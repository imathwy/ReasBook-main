import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

variable {R S R' S' : CommRingCat.{u}}
variable (α : R ⟶ S) (β : R' ⟶ S') (ψ : R ⟶ R') (φ : S ⟶ S')

/- Domain triage:
* primary domain: categorical commutative squares in `CommRingCat`;
* sampled owner API: `CategoryTheory.CommSq`, `NatTrans.commSq`, `IsPullback.toCommSq`, and the
  downstream ring-theoretic bridge `CommRingCat.KaehlerDifferential.map`;
* source-facing layer: the displayed commutative square of commutative rings;
* core/canonical owner: `CategoryTheory.CommSq`;
* bridge/view: constructions built from a commutative ring square, such as the induced map on
  Kähler differentials in `10_131_4_2`.

The primitive data are only the four ring maps. The square itself is already canonically owned by
`CommSq`, so this file should stay a direct owner recall rather than introducing any ring-specific
wrapper or local duplicate.
-/

/- 10.131.4.1: The ring maps `α : R → S`, `β : R' → S'`, `ψ : R → R'`, and
`φ : S → S'` form a commutative square of commutative rings. This is exactly the canonical
`CommRingCat` specialization of `CategoryTheory.CommSq`. -/
#check
  CommSq ψ α β φ
