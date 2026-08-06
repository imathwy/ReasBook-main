import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Problem_10_8_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.ManifoldEulerCharacteristic

open Topology
open scoped ContinuousMap Topology.CWComplex

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced `ContinuousMap.HomotopyEquiv` as the canonical
-- owner for homotopy equivalences. In the current repository, Chapter 21 already uses
-- `manifoldEulerCharacteristic` and `manifoldBettiNumber`, Chapter 10 provides
-- `χ((Set.univ : Set X))` for finite CW models, and Chapter 13 relates the finite CW Euler
-- characteristic to singular-homology Euler characteristic.

section

variable {K : Type} [Field K]
variable {M : Type} [TopologicalSpace M]

/-- Definition 21.1.1 (1). For a compact manifold `M`, the Euler characteristic `χ(M)` over the
field `K` is the alternating sum of the Betti numbers `manifoldBettiNumber K i M`. In this
chapter this is formalized by the chapter-local owner `manifoldEulerCharacteristic K M`. -/
theorem manifoldEulerCharacteristic_eq_finsum_betti :
    manifoldEulerCharacteristic K M =
      ∑ᶠ i : ℕ, Int.negOnePow i * (manifoldBettiNumber K i M : ℤ) :=
  by
    let e : ModuleCat.of K (ULift K) ≅ ModuleCat.of K K :=
      LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift K ≃ₗ[K] K)
    have hfinrank (i : ℕ) :
        Module.finrank K ((fieldTopologicalSingularChains K (TopCat.of M)).homology i) =
          manifoldBettiNumber K i M := by
      simpa [manifoldBettiNumber, fieldTopologicalSingularChains,
        AlgebraicTopology.singularHomologyFunctor] using
        LinearEquiv.finrank_eq
          ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat K) i).mapIso e).app
            (TopCat.of M)).toLinearEquiv)
    apply finsum_congr
    intro i
    rw [hfinrank i]
    rfl

end

section

variable {K : Type} [Field K]
variable {M : Type} [TopologicalSpace M]

/-- Definition 21.1.1 (2). Equivalently, if `X` is a finite CW model for `M` in the sense of a
homotopy equivalence `M ≃ₕ X`, then `χ(M)` agrees with the Euler characteristic of that finite CW
model, formalized as `χ((Set.univ : Set X))`. -/
theorem manifoldEulerCharacteristic_eq_finiteCWEulerCharacteristic_of_homotopyEquiv
    {X : Type} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    [CWComplex.Finite (Set.univ : Set X)] (e : M ≃ₕ X) :
    manifoldEulerCharacteristic K M = χ((Set.univ : Set X)) := sorry

end
