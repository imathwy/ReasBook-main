import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Principle_1_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_2

noncomputable section

open CategoryTheory
open scoped Topology

universe u w

-- Semantic recall via `lean_leansearch` did not surface a dedicated owner for oriented
-- characteristic classes. Local Chapter 23 precedent uses contravariant cohomology functors on
-- `TopCat`, `Function.Bijective`, and the source-facing Chapter 23 owner
-- `OrientedRealPlaneBundle.classes n B` for oriented real `n`-plane bundles.

namespace OrientedRealPlaneBundle

/-- Pullback along a map of base spaces on oriented real `n`-plane bundle classes. This is the
source-facing specialization of pullback on principal `SO(n)`-bundle classes. -/
abbrev pullbackOnClasses (n : ℕ) {B B' : TopCat.{u}} (f : B' ⟶ B)
    (ξ : OrientedRealPlaneBundle.classes.{u, u} n B) :
    OrientedRealPlaneBundle.classes.{u, u} n B' :=
  PrincipalGBundle.pullbackOnClasses f.hom ξ

end OrientedRealPlaneBundle

section

variable {n q : ℕ}
variable {k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- A degree-`q` characteristic class of oriented real `n`-plane bundles is a natural assignment
from oriented bundle classes to the degree-`q` cohomology groups of their bases. In the local
Chapter 23 API, oriented bundles are represented by `OrientedRealPlaneBundle.classes n B`. -/
structure OrientedCharacteristicClass
    (n q : ℕ) (k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) where
  /-- The cohomology class assigned to an oriented real `n`-plane bundle class. -/
  value {B : TopCat.{u}} (ξ : OrientedRealPlaneBundle.classes.{u, u} n B) :
      (k q).obj (Opposite.op B)
  /-- Pulling back an oriented real `n`-plane bundle pulls back its characteristic class. -/
  natural {B B' : TopCat.{u}} (f : B' ⟶ B)
      (ξ : OrientedRealPlaneBundle.classes.{u, u} n B) :
      (k q).map f.op (value ξ) =
        value (OrientedRealPlaneBundle.pullbackOnClasses n f ξ)

/-- An oriented characteristic class evaluates on any oriented real `n`-plane bundle class. -/
instance orientedCharacteristicClassCoeFun :
    CoeFun (OrientedCharacteristicClass n q k) fun _ ↦
      ∀ {B : TopCat.{u}},
        OrientedRealPlaneBundle.classes.{u, u} n B →
          (k q).obj (Opposite.op B) where
  coe c := c.value

section

variable {ESO : Type u} [TopologicalSpace ESO]
variable [MulAction (SO(n)) ESO]
variable [ContinuousSMul (SO(n)) ESO]

/-- Evaluating an oriented characteristic class on the universal oriented real `n`-plane bundle
`ESO → BSO(n)`. In the current chapter API, the universal oriented bundle is the class
`universalOrientedRealPlaneBundleClass hBSO`. -/
def orientedCharacteristicClassEvalOnUniversalBundle
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO])) :
    OrientedCharacteristicClass n q k →
      (k q).obj
        (Opposite.op (TopCat.of BSO[n, ESO])) :=
  fun c ↦
    c ((universalOrientedRealPlaneBundleClass hBSO) :
      OrientedRealPlaneBundle.classes.{u, u} n (TopCat.of BSO[n, ESO]))

/-- Lemma 23.7.4. Evaluation on the universal oriented bundle `ESO → BSO(n)` identifies degree-`q`
characteristic classes of oriented real `n`-plane bundles with `k^q(BSO(n))`. In the local API,
oriented bundles are recorded by `OrientedRealPlaneBundle.classes n B`, and the identification is
the bijectivity of evaluation on the universal oriented bundle class. -/
theorem orientedCharacteristicClassEvalOnUniversalBundle_bijective [ContractibleSpace ESO]
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO]))
    [(k q).rightOp.IsHomotopyInvariant] :
    Function.Bijective
      ((orientedCharacteristicClassEvalOnUniversalBundle hBSO) :
        OrientedCharacteristicClass n q k →
          (k q).obj (Opposite.op (TopCat.of BSO[n, ESO]))) := sorry

end
end
