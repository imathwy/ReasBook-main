import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape
open HomologicalComplex₂

universe v u

section

variable {V : Type u} [Category.{v} V] [Limits.HasZeroMorphisms V]

/- Definition 12.18.1 is a core/canonical recall item in the bicomplex domain. In the source's
additive setting, the owner abstraction is already the mathlib bicomplex type
`HomologicalComplex₂ V (up ℤ) (up ℤ)`, and it only needs zero morphisms. Its primitive data are
the objects `(K.X p).X q` with horizontal differentials `(K.d p (p + 1)).f q` and vertical
differentials `(K.X p).d q (q + 1)`. The square-zero and commutation relations are derived owner
API, recalled below. -/
#check (HomologicalComplex₂ V (up ℤ) (up ℤ))

/- Companion recall: the horizontal differential squares to zero by the owner lemma
`HomologicalComplex₂.d_f_comp_d_f`. -/
recall d_f_comp_d_f

/- Companion recall: for each fixed horizontal degree `p`, the vertical differential squares to
zero in the column complex `K.X p` by `HomologicalComplex.d_comp_d`. -/
recall HomologicalComplex.d_comp_d

/- Companion recall: the horizontal and vertical differentials commute on each elementary square
by the owner lemma `HomologicalComplex₂.d_comm`. -/
recall d_comm

end
