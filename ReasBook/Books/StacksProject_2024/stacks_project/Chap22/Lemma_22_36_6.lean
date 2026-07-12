import StacksProject_2024.Chap22.ModuleCatHasDerivedCategory
import StacksProject_2024.Chap22.Remark_22_36_1
import StacksProject_2024.Chap22.Remark_22_36_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory DerivedCategory HomotopyCategory

noncomputable section

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "KQ" => HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)
local notation "Q" => (DerivedCategory.Q : DGMod ⥤ DMod)

-- Semantic recall hits: `CochainComplex.IsKProjective.Qh_map_bijective` and the local
-- `homotopyToDerivedBijective` owner identify the source Hom-comparison condition. In the current
-- Chapter 22 cochain-complex model, the source-facing owners here depend only on the underlying
-- ring `A`, so the bounded differential graded algebra hypothesis stays in the explanatory prose
-- rather than as a redundant theorem binder.

/-- Lemma 22.36.6: for a bounded differential graded algebra `(A, d)`, an object `E` of
`D(A, d)` is compact if and only if it is represented by a differential graded `A`-module `P`
which is finite projective as a graded `A`-module and whose morphisms to every differential graded
module are computed equally in the homotopy and derived categories. In the current Chapter 22
model, differential graded `A`-modules are represented by cochain complexes of modules over the
underlying ring `A`, and the bounded differential graded algebra hypothesis does not add extra
Lean data beyond that underlying ring in this source-facing formulation. -/
@[stacks 09RB]
theorem derivedCompactObject_iff_exists_finiteGradedProjective_homotopyToDerivedBijective
    (E : DMod) :
    derivedCompactObject E ↔
      ∃ P : DGMod,
        finiteGradedProjective P ∧
          homotopyToDerivedBijective (ModuleCat A) ((KQ).obj P) ∧
            IsIsomorphic E (Q.obj P) := sorry

end

end CochainComplex
