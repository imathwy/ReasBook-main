import Mathlib.AlgebraicTopology.SingularSet
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_2_1

open CategoryTheory

noncomputable section

universe u

variable (X : TopCat.{u})

-- Semantic recall via `lean_leansearch`: `sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet` is the
-- canonical owner for the realization/singular-set adjunction, and its counit at `X` is the
-- canonical map `SSet.toTop.obj (TopCat.toSSet.obj X) ⟶ X`.

/- Construction 16.2.2: the canonical evaluation map `Γ X ⟶ X`, with
`Γ X = gammaRealization X`, is the counit of the geometric
realization/singular-set adjunction. On a representative `|f, u|` it sends the singular simplex
`f : Δ^n ⟶ X` evaluated at the point `u ∈ Δ^n` to `f u`. -/
#check (sSetTopAdj.counit.app X : gammaRealization X ⟶ X)

/-- The adjoint transpose of `sSetTopAdj.counit.app X` is the identity of the singular simplicial
set `TopCat.toSSet.obj X`; equivalently, the counit restricts on each singular simplex to the
original map `Δ^n ⟶ X`, which is the formal content of the rule `|f, u| ↦ f u`. -/
theorem singularRealizationEvaluation_spec :
    sSetTopAdj.homEquiv (TopCat.toSSet.obj X) X (sSetTopAdj.counit.app X) = 𝟙 _ := by
  rw [Adjunction.homEquiv_unit]
  simpa using sSetTopAdj.right_triangle_components X
