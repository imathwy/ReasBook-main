import Mathlib.Data.ZMod.QuotientGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_2

open scoped ComplexKTheory

noncomputable section

universe u v

section

variable {X : Type u} [TopologicalSpace X] {x₀ : X}
variable {A : Type v} [AddCommGroup A]

/-- If the reduced Chern character identifies `K̃(X, x₀)` with a chosen integral lattice, then
viewing it with codomain restricted to that lattice gives a bijection. -/
theorem reducedChernCharacter_bijective_of_range_eq
    (integralLattice : AddSubgroup A) (ch : K̃(X, x₀) →+ A)
    (h_inj : Function.Injective ch) (h_range : ch.range = integralLattice) :
    Function.Bijective
      (ch.codRestrict integralLattice fun ξ ↦ by
        rw [← h_range]
        exact ⟨ξ, rfl⟩) := by
  constructor
  · intro ξ η hξη
    exact h_inj (congrArg Subtype.val hξη)
  · intro a
    have ha : (a : A) ∈ ch.range := by
      rw [h_range]
      exact a.2
    rcases ha with ⟨ξ, hξ⟩
    refine ⟨ξ, ?_⟩
    exact Subtype.ext hξ

end

section Sphere

variable (n : ℕ)
variable {A : Type v}
variable [AddCommGroup A]

/-- Under the source-facing hypotheses of Lemma 24.4.5, the reduced Chern character on `S^(2n)`
is a bijection onto the specified integral lattice in the chosen degree-`2 * n` summand. -/
theorem sphereReducedChernCharacter_bijective
    (topDegree : AddSubgroup A) (integralLattice : AddSubgroup topDegree)
    (ch :
      K̃((basedSphere (2 * n)).right, underTopBasepoint (basedSphere (2 * n))) →+ topDegree)
    (h_inj : Function.Injective ch) (h_range : ch.range = integralLattice) :
    Function.Bijective
      (ch.codRestrict integralLattice fun ξ ↦ by
        rw [← h_range]
        exact ⟨ξ, rfl⟩) :=
  reducedChernCharacter_bijective_of_range_eq integralLattice ch h_inj h_range

/-- If the top Chern class on `K̃(S^(2n))` has image `(n - 1)! ℤ`, then its cokernel is the
canonical cyclic group `ℤ/(n - 1)!`. -/
def sphereTopChernClassCokernelEquiv
    (cTop :
      K̃((basedSphere (2 * n)).right, underTopBasepoint (basedSphere (2 * n))) →+ ℤ)
    (h_range : cTop.range = AddSubgroup.zmultiples (Nat.factorial (n - 1) : ℤ)) :
    ℤ ⧸ cTop.range ≃+ ZMod (Nat.factorial (n - 1)) := by
  exact (QuotientAddGroup.quotientAddEquivOfEq h_range).trans
    (Int.quotientZMultiplesNatEquivZMod (Nat.factorial (n - 1)))

/- Lemma 24.4.5. The source text identifies the reduced Chern character on `K̃(S^(2n))` with an
integral lattice in the degree-`2 * n` rational cohomology summand and says that the top Chern
class has image `(n - 1)! ℤ`, hence cokernel `ℤ/(n - 1)!`. The current Chapter 24 API does not
yet expose a public owner for that top-degree summand, its integral lattice, or the corresponding
reduced/top Chern-character maps. This item therefore remains a labeled recall block, with the
thin reusable bridges `sphereReducedChernCharacter_bijective` and
`sphereTopChernClassCokernelEquiv` for any explicit choice of those ingredients. -/
#check sphereReducedChernCharacter_bijective
#check sphereTopChernClassCokernelEquiv

end Sphere
