import Mathlib.Data.PNat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_2

noncomputable section

open CategoryTheory
open scoped Topology Topology.Homotopy unitInterval

-- The public API in this file is source-facing: only the antipodal sphere self-map and its degree
-- statement remain public. The supporting suspension step is kept private and records the same
-- sign convention as the Chapter 8 suspension construction, but on the Chapter 11/13
-- `PointedCompactlyGenerated` suspension owner.

universe u w

/-- The reduced-suspension sign step on the Chapter 11/13 owner: on representatives it applies
`f` in the space coordinate and reverses the suspension coordinate. -/
private def signedSuspensionMap
    {X : PointedCompactlyGenerated.{u, w}} (f : X ⟶ X) :
    suspensionSpace X ⟶ suspensionSpace X :=
  let signedMap :
      C((reducedSuspension X).toCompactlyGenerated, (reducedSuspension X).toCompactlyGenerated) :=
    { toFun :=
        show (reducedSuspension X).toCompactlyGenerated →
            (reducedSuspension X).toCompactlyGenerated from
          Quotient.map
            (fun p : X.toCompactlyGenerated × I ↦
              (CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom f) p.1,
                unitInterval.symm p.2))
            (by
              intro p q hpq
              sorry)
      continuous_toFun := by
        sorry }
  Under.homMk
    (ConcreteCategory.ofHom signedMap)
    (by
      sorry)

/-- The recursive based representative of the textbook antipodal homotopy class on the
positive-dimensional Chapter 11 sphere owners `suspensionSphere (n + 1)`. It starts from
`𝟙 : S¹ ⟶ S¹` and adds one signed suspension step at each stage. -/
private def sphereAntipodeRepresentativeNat :
    (n : ℕ) → suspensionSphere (n + 1) ⟶ suspensionSphere (n + 1) :=
  fun
  | 0 => 𝟙 _
  | n + 1 => signedSuspensionMap (sphereAntipodeRepresentativeNat n)

/-- The recursive representative on `suspensionSphere (n + 2)` is obtained from the previous one
by one more signed suspension step. -/
private theorem sphereAntipodeRepresentativeNat_succ (n : ℕ) :
    sphereAntipodeRepresentativeNat (n + 1) =
      signedSuspensionMap (sphereAntipodeRepresentativeNat n) := rfl

/-- The Chapter 11 based representative of the textbook antipodal homotopy class on
`suspensionSphere n` for positive `n`. The `S⁰` endpoint is outside the positive-degree owner
from Definition 13.2.2. -/
private def sphereAntipodeRepresentative (n : ℕ+) : SphereBasedSelfMap n :=
  match n with
  | ⟨Nat.succ k, _⟩ => sphereAntipodeRepresentativeNat k

/-- The textbook antipodal based self-map `a_n : S^n → S^n` on the chosen sphere owner
`suspensionSphere n`, realized by the recursive signed suspension construction. -/
def sphereAntipode (n : ℕ+) : SphereBasedSelfMap n :=
  sphereAntipodeRepresentative n

/-- Lemma 13.5.5. The antipodal map `a_n : S^n → S^n`, realized on the chosen sphere owner
`suspensionSphere n` by the underlying continuous map of `sphereAntipode n`, has degree
`(-1) ^ ((n : ℕ) + 1)` in the sense of Definition 13.2.2. -/
theorem sphereAntipode_hasDegree (n : ℕ+) :
    SphereSelfMap.HasDegree n
      (sphereAntipode n).toContinuousMap
      ((-1 : ℤ) ^ ((n : ℕ) + 1)) := sorry
