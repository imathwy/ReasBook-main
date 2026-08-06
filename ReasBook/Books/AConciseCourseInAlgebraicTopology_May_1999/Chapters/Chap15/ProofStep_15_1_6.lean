import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Lemma_15_1_4.PositiveDegree
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Lemma_15_1_4.Wedge

open scoped Topology Topology.Homotopy

-- The item-local foundations already own the Chapter 15 wedge model and the reusable
-- positive-degree `π_ n` wrappers, so this file keeps only the cofiber-specific specializations.

namespace HomotopyCofiberTargetInclusion

/-- Proof step 15.1.6 (1): in the simply connected case, if `X` is the cofiber of a based map
`f : K ⟶ L` between wedges of `n`-spheres with `1 < n`, then the top row
`π_ n(K) ⟶ π_ n(L) ⟶ π_ n(X) ⟶ 0` is exact at `π_ n(L)`. Here `K` and `L` are the Chapter 15
wedge models `basedWedgeOfNSpheres n ι` and `basedWedgeOfNSpheres n κ`, `X` is
`homotopyCofiber f`, and the two displayed arrows are induced by `f` and by the canonical
cofiber inclusion `L ⟶ X`. -/
theorem exactAtMiddle_of_simplyConnected
    (n : ℕ) (h_n : 1 < n) {ι κ : Type}
    (f : basedWedgeOfNSpheres n ι ⟶ basedWedgeOfNSpheres n κ)
    [SimplyConnectedSpace (homotopyCofiber f).right] :
    Function.Exact
        (positiveDegreeBasedHomotopyGroupHom n h_n f)
        (positiveDegreeBasedHomotopyGroupHom n h_n (homotopyCofiberTargetInclusion f)) := sorry

/-- Proof step 15.1.6 (2): in the simply connected case, if `X` is the cofiber of a based map
`f : K ⟶ L` between wedges of `n`-spheres with `1 < n`, then the terminal part
`π_ n(L) ⟶ π_ n(X) ⟶ 0` of the top row is exact. Equivalently, for the Chapter 15 wedge models
`K = basedWedgeOfNSpheres n ι`, `L = basedWedgeOfNSpheres n κ`, and
`X = homotopyCofiber f`, the map on `π_ n` induced by the canonical cofiber inclusion
`L ⟶ X` is surjective. -/
theorem surjective_of_simplyConnected
    (n : ℕ) (h_n : 1 < n) {ι κ : Type}
    (f : basedWedgeOfNSpheres n ι ⟶ basedWedgeOfNSpheres n κ)
    [SimplyConnectedSpace (homotopyCofiber f).right] :
    Function.Surjective
      (positiveDegreeBasedHomotopyGroupHom n h_n (homotopyCofiberTargetInclusion f)) := sorry

end HomotopyCofiberTargetInclusion
