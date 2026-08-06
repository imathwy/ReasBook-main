import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

open CategoryTheory

-- Semantic recall via `lean_leansearch`: `groupHomologyIsoTor` in
-- `Mathlib.RepresentationTheory.Homological.GroupHomology.Basic` is the canonical owner for the
-- identification of the universal-cover chain model of `K(π, 1)` with `Tor`.

variable {π : Type} [Group π] [DecidableEq π] (A : Rep ℤ π) (n : ℕ)

/- Problem 16.6.2. The canonical recall for this item is the isomorphism
`groupHomology A n ≅ ((Rep.Tor ℤ π n).obj A).obj (Rep.trivial ℤ π ℤ)`.
This is mathlib's `Torₙ(A, ℤ)` packaging, corresponding to the textbook
`Tor_*^{ℤ[π]}(ℤ, A)` after translating left/right `π`-module conventions. -/
#check (groupHomologyIsoTor A n :
    groupHomology A n ≅ ((Rep.Tor ℤ π n).obj A).obj (Rep.trivial ℤ π ℤ))
