import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

/- Definition 2.3.3: the free abelian group functor is left adjoint to the forgetful functor
from abelian groups to sets, meaning that morphisms from the free abelian group on a set `S`
to an abelian group `A` are naturally identified with functions from `S` to the underlying set
of `A`. -/
recall AddCommGrpCat.adj : AddCommGrpCat.free ⊣ forget AddCommGrpCat.{u}

variable (S : Type u) (A : AddCommGrpCat.{u})

/- Concretely, the adjunction identifies morphisms from the free abelian group on `S` to `A`
with functions from `S` to the underlying type of `A`. -/
#check ((AddCommGrpCat.adj.homEquiv S A) : (AddCommGrpCat.free.obj S ⟶ A) ≃ (S → A))
