import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.SuspensionSphere

noncomputable section

open scoped Topology Topology.Homotopy

-- Semantic recall: `lean_leansearch` surfaced `HomotopyGroup.Pi` as the canonical owner for
-- homotopy groups, Chapter 11 fixes `suspensionPiMap`, and `SuspensionSphere` exports the
-- reusable sphere model `suspensionSphere n := Σ^n S⁰` used throughout the chapter.

/-- Remark 11.2.4 (1): in the suspension-sphere model `S^n := suspensionSphere n`, the
Freudenthal suspension homomorphism `π_ 3(S^2) → π_ 4(S^3)` is surjective. -/
theorem sphereTwoSuspensionHomomorphism_surjective :
    Function.Surjective (suspensionHomomorphism 3 (suspensionSphere 2)) := sorry

/-- Remark 11.2.4 (2): in the suspension-sphere model `S^n := suspensionSphere n`, the
Freudenthal suspension homomorphism `π_ 3(S^2) → π_ 4(S^3)` is not injective, so at this
endpoint of the range it is only an epimorphism. -/
theorem sphereTwoSuspensionHomomorphism_notInjective :
    ¬ Function.Injective (suspensionHomomorphism 3 (suspensionSphere 2)) := sorry

/-- Remark 11.2.4 (3): in the suspension-sphere model `S^n := suspensionSphere n`, the fourth
homotopy group `π_ 4(S^3)` is the cyclic group of order `2`. -/
theorem suspensionSphereThree_pi4_mulEquiv_zmodTwo :
    Nonempty
      (π_ 4 (suspensionSphere 3).toCompactlyGenerated (suspensionSphere 3).point ≃*
        Multiplicative (ZMod 2)) := sorry
