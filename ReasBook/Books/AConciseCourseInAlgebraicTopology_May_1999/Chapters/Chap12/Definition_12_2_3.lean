import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.Recall

open CategoryTheory

universe u

variable (R : Type u) [CommRing R]
variable {X X' : ChainComplex (ModuleCat R) ℕ}
variable {f g : X ⟶ X'}

-- Semantic recall via direct mathlib inspection: `Homotopy` is the canonical owner for chain
-- homotopies, and the chain-complex specializations of `dNext` and `prevD` expose the textbook
-- degreewise identity.

/- Definition 12.2.3. For chain maps `f g : X ⟶ X'`, a chain homotopy is the canonical
mathlib structure `Homotopy f g`. Its degree-`i` map is the component
`s.hom i (i + 1) : X.X i ⟶ X'.X (i + 1)`, `s.zero` records that the off-diagonal components
vanish, and `s.comm` is the homotopy identity. For chain complexes on `ℕ`, the lemmas
`Homotopy.dNext_succ_chainComplex`, `Homotopy.dNext_zero_chainComplex`, and
`Homotopy.prevD_chainComplex` rewrite `s.comm` into the textbook formula `d' s + s d = f - g`
degreewise. -/
#check (Homotopy f g)

/- A chain homotopy has degreewise components `s.hom i j`. -/
recall Homotopy.hom

/- Off-diagonal components of a chain homotopy vanish. -/
recall Homotopy.zero

/- The defining degreewise homotopy identity is `Homotopy.comm`. -/
recall Homotopy.comm

/- In positive degree, `dNext` is the left differential term `d ≫ s`. -/
recall Homotopy.dNext_succ_chainComplex

/- In degree `0`, the `dNext` contribution vanishes. -/
recall Homotopy.dNext_zero_chainComplex

/- The `prevD` term is the right differential contribution `s ≫ d`. -/
recall Homotopy.prevD_chainComplex
