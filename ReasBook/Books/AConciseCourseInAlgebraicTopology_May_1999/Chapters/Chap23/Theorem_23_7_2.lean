import Mathlib.LinearAlgebra.UnitaryGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Lemma_22_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_8_2

noncomputable section

open scoped Topology

universe u v

-- Semantic recall via `lean_leansearch`: `Matrix.specialOrthogonalGroup (Fin n) ℝ` is the
-- canonical owner for the structure group `SO(n)`, and
-- `universalPrincipalBundle_classifying_bijective` is the chapter's classifying theorem for
-- principal bundles.

namespace OrientedRealPlaneBundle

/-- The canonical structure group `SO(n)` of oriented real `n`-plane bundles. -/
abbrev StructureGroup (n : ℕ) :=
  Matrix.specialOrthogonalGroup (Fin n) ℝ

/-- Source-facing notation for the structure group `SO(n)` of oriented real `n`-plane bundles. -/
notation "SO(" n ")" => StructureGroup n

/-- The chapter owner for oriented real `n`-plane bundles over `B`, implemented by the equivalent
principal `SO(n)`-bundle classes. -/
abbrev classes (n : ℕ) (B : Type _) [TopologicalSpace B] :=
  PrincipalGBundle.classes (SO(n)) B

end OrientedRealPlaneBundle

section

variable {n : ℕ}
variable {ESO : Type v} [TopologicalSpace ESO]
variable [MulAction (SO(n)) ESO]
variable [ContinuousSMul (SO(n)) ESO]
variable {X : Type v} [TopologicalSpace X]

/-- The quotient `ESO / SO(n)` presenting the classifying space `BSO(n)` attached to a universal
principal `SO(n)`-bundle. -/
abbrev orientedRealPlaneBundleClassifyingSpace (n : ℕ) (ESO : Type v)
    [TopologicalSpace ESO] [MulAction (SO(n)) ESO] [ContinuousSMul (SO(n)) ESO] : Type v :=
  ESO /[SO(n)]

/-- Source-facing notation for the quotient-model classifying space `BSO(n)`. -/
notation "BSO[" n ", " ESO "]" => orientedRealPlaneBundleClassifyingSpace n ESO

/-- The universal oriented real `n`-plane bundle over the quotient-model classifying space
`BSO(n)`, recorded in the chapter API as the corresponding principal `SO(n)`-bundle class. -/
def universalOrientedRealPlaneBundleClass
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO])) :
    OrientedRealPlaneBundle.classes n BSO[n, ESO] :=
  PrincipalGBundle.classOf (orbitPrincipalGBundle hBSO)

/-- The classifying assignment `[X, BSO(n)] → Ẽ_n^+(X)` sending a homotopy class of maps to the
corresponding oriented real `n`-plane bundle class. The underlying canonical bridge is the
universal principal `SO(n)`-bundle classifying map. -/
def orientedRealPlaneBundleClassifyingMap
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO]))
    (X : Type v) [TopologicalSpace X] :
    homotopyClasses X BSO[n, ESO] → OrientedRealPlaneBundle.classes n X :=
  universalPrincipalBundleClassifyingMap hBSO X

/-- Evaluating the oriented classifying map on a representative `f : X ⟶ BSO(n)` gives the class
of the pullback of the universal oriented bundle along `f`. -/
@[simp] theorem orientedRealPlaneBundleClassifyingMap_mk
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO]))
    (f : C(X, BSO[n, ESO])) :
    orientedRealPlaneBundleClassifyingMap hBSO X ⟦f⟧ =
      (PrincipalGBundle.classOf ((orbitPrincipalGBundle hBSO).pullback f) :
        OrientedRealPlaneBundle.classes n X) := by
  exact universalPrincipalBundleClassifyingMap_mk hBSO f

/-- Theorem 23.7.2. `BSO(n)` classifies oriented real `n`-plane bundles by homotopy classes of
maps. The public source-facing owner is `OrientedRealPlaneBundle.classes n X`, and the underlying
canonical bridge is the equivalent principal `SO(n)`-bundle classifying map. -/
theorem orientedRealPlaneBundleClassifyingMap_bijective [ContractibleSpace ESO]
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO])) :
    Function.Bijective (orientedRealPlaneBundleClassifyingMap hBSO X) := by
  simpa [orientedRealPlaneBundleClassifyingMap] using
    universalPrincipalBundle_classifying_bijective hBSO

end
