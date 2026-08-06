import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_2

open scoped ComplexKTheory

universe u

-- This file keeps the source-facing stable-equivalence quotient of honest bundle classes and
-- relates it to the canonical reduced `K`-theory owner `K̃(X, x₀)`.

noncomputable section

namespace ComplexVectorBundle

variable {X : Type u} [TopologicalSpace X]

/-- Two honest bundle classes are stably equivalent if they become equal after adding trivial
line-bundle summands of possibly different ranks. -/
def StableEquivalent (a b : classes X) : Prop :=
  ∃ m n : ℕ, a + m • (1 : classes X) = b + n • (1 : classes X)

/-- Stable equivalence of honest bundle classes is reflexive. -/
theorem stableEquivalent_refl (a : classes X) :
    StableEquivalent a a := sorry

/-- Stable equivalence of honest bundle classes is symmetric. -/
theorem stableEquivalent_symm {a b : classes X} (h : StableEquivalent a b) :
    StableEquivalent b a := sorry

/-- Stable equivalence of honest bundle classes is transitive. -/
theorem stableEquivalent_trans {a b c : classes X}
    (hab : StableEquivalent a b) (hbc : StableEquivalent b c) :
    StableEquivalent a c := sorry

/-- Stable equivalence defines the quotient of honest complex vector-bundle classes used in
Corollary 24.1.5. -/
def stableSetoid (X : Type u) [TopologicalSpace X] : Setoid (classes X) where
  r := StableEquivalent
  iseqv := ⟨stableEquivalent_refl, stableEquivalent_symm, stableEquivalent_trans⟩

/-- The stable equivalence classes of honest complex vector bundles over `X`. -/
abbrev StableClasses (X : Type u) [TopologicalSpace X] :=
  Quotient (stableSetoid X)

/-- Equality in `StableClasses X` is exactly stable equivalence of honest bundle classes. -/
theorem stableClasses_mk_eq_iff {a b : classes X} :
    ((Quotient.mk (stableSetoid X) a : StableClasses X) =
      Quotient.mk (stableSetoid X) b) ↔
        StableEquivalent a b := sorry

/-- The based dimension map sends an honest bundle class to its fiber dimension at `x₀`. -/
theorem complexKTheoryDimensionAt_of_classes (x₀ : X) (a : classes X) :
    complexKTheoryDimensionAt X x₀ (Algebra.GrothendieckAddGroup.of a) =
      classesDimensionAt X x₀ a := sorry

private theorem stableClassToReducedComplexKTheory_wellDefined (x₀ : X) {a b : classes X}
    (h : StableEquivalent a b) :
    (complexKTheoryToReducedProdInt X x₀ (Algebra.GrothendieckAddGroup.of a)).1 =
      (complexKTheoryToReducedProdInt X x₀ (Algebra.GrothendieckAddGroup.of b)).1 := sorry

/-- Stable equivalence classes of honest bundles map naturally to reduced `K`-theory through the
canonical reduced-part projection from `complexKTheoryToReducedProdInt X x₀`. -/
def stableClassToReducedComplexKTheory (x₀ : X) : StableClasses X → K̃(X, x₀) :=
  Quotient.lift
    (fun a ↦ (complexKTheoryToReducedProdInt X x₀ (Algebra.GrothendieckAddGroup.of a)).1)
    (fun _ _ h ↦ stableClassToReducedComplexKTheory_wellDefined x₀ h)

/-- `stableClassToReducedComplexKTheory x₀` sends the stable class of an honest bundle class to
the reduced part of its virtual class under `complexKTheoryToReducedProdInt X x₀`. -/
theorem stableClassToReducedComplexKTheory_mk (x₀ : X) (a : classes X) :
    stableClassToReducedComplexKTheory x₀ (Quotient.mk (stableSetoid X) a) =
      (complexKTheoryToReducedProdInt X x₀ (Algebra.GrothendieckAddGroup.of a)).1 := rfl

/-- On an honest bundle class, `stableClassToReducedComplexKTheory x₀` is represented by
subtracting the trivial rank summand from its virtual class. -/
theorem stableClassToReducedComplexKTheory_mk_coe (x₀ : X) (a : classes X) :
    ((stableClassToReducedComplexKTheory x₀ (Quotient.mk (stableSetoid X) a) : K̃(X, x₀)) :
        complexKTheory X) =
      Algebra.GrothendieckAddGroup.of a -
        complexKTheoryIntSection X (classesDimensionAt X x₀ a) := by
  have hcoe :
      (((complexKTheoryToReducedProdInt X x₀ (Algebra.GrothendieckAddGroup.of a)).1 :
          K̃(X, x₀)) : complexKTheory X) =
        Algebra.GrothendieckAddGroup.of a -
          complexKTheoryIntSection X
            (complexKTheoryDimensionAt X x₀ (Algebra.GrothendieckAddGroup.of a)) :=
    complexKTheoryToReducedProdInt_fst_coe (Algebra.GrothendieckAddGroup.of a)
  rw [complexKTheoryDimensionAt_of_classes x₀ a] at hcoe
  simpa [stableClassToReducedComplexKTheory_mk] using hcoe

variable [CompactSpace X]

/-- Corollary 24.1.5: for a compact space `X` with chosen basepoint `x₀`, stable equivalence
classes of honest complex vector bundles over `X` identify naturally with `K̃(X, x₀)` via
`stableClassToReducedComplexKTheory x₀`. -/
theorem stableClassToReducedComplexKTheory_bijective (x₀ : X) :
    Function.Bijective (stableClassToReducedComplexKTheory x₀) := sorry

end ComplexVectorBundle

end
