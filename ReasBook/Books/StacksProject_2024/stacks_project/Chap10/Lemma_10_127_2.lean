import StacksProject_2024.stacks_project.Chap10.Lemma_10_127_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v

section

variable (R : Type u) [CommRing R]
variable (A : Type u) [CommRing A] [Algebra R A]

/-- The canonical diagram of finitely presented `R`-algebras over `A`, viewed in `CommAlgCat R`.
-/
abbrev finitelyPresentedAlgebrasOverDiagram :=
  selectedAlgebrasOverTargetDiagram (finitelyPresentedAlgebrasOverProperty R A)

-- Proof sketch: apply the directed-set refinement of filtered colimits from Lemma 4.21.5 to the
-- finite-presentation approximation of `A` from Lemma 10.127.1. Equivalently, present `A` by the
-- directed system of quotients `R[X_s; s ∈ S] / (E)` attached to finite sets of generators and
-- finitely many polynomial relations among them.
/-- Lemma 10.127.2 (1): every `R`-algebra `A` is isomorphic to the colimit of a directed system of
`R`-algebras of finite presentation. -/
theorem exists_directed_system_of_finitelyPresented_algebras :
    ∃ (I : Type v) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (F : I ⥤ finitelyPresentedAlgebrasOver R A),
      Nonempty
          (IsColimit
            ((finitelyPresentedAlgebrasOverCocone R A).whisker
              F)) := sorry

-- Proof sketch: choose a finite generating set of `A` over `R`. Restrict the directed system from
-- the first clause to stages built from that fixed finite set of generators and varying finite sets
-- of relations; enlarging the relation set gives quotient maps, hence all transition maps are
-- surjective, and the restricted system still has colimit `A`.
/-- Lemma 10.127.2 (2): if `A` is of finite type over `R`, then `A` is isomorphic to the colimit
of a directed system of finitely presented `R`-algebras whose transition maps are all
surjective. -/
theorem exists_directed_system_of_finitelyPresented_algebras_with_surjective_transition_maps
    [Algebra.FiniteType R A] :
    ∃ (I : Type v) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (F : I ⥤ finitelyPresentedAlgebrasOver R A),
      (∀ ⦃i j : I⦄, (hij : i ≤ j) →
        Function.Surjective
          ((F ⋙ finitelyPresentedAlgebrasOverDiagram R A).map (homOfLE hij))) ∧
        Nonempty
          (IsColimit
            ((finitelyPresentedAlgebrasOverCocone R A).whisker
              F)) := sorry

end
