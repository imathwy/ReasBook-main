import stacks_project.Chap20.Lemma_20_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe wI w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The index type of the degree-`n` iterated Čech intersections of a covering `cover` of `U`. -/
abbrev cechCoverIntersectionIndex {U : C} [HasFiniteProducts (Over U)]
    (cover : FormalCoproduct (Over U)) (n : ℕ) :=
  (cover.cech.obj (op (SimplexCategory.mk n))).I

/-- The underlying object of `C` of the `i`-th degree-`n` Čech intersection of a covering
`cover` of `U`; this is the iterated fibre product of the corresponding members of the covering
over `U`. -/
abbrev cechCoverIntersectionObject {U : C} [HasFiniteProducts (Over U)]
    (cover : FormalCoproduct (Over U)) (n : ℕ)
    (i : cechCoverIntersectionIndex cover n) : C :=
  ((cover.cech.obj (op (SimplexCategory.mk n))).obj i).left

namespace Sheaf

variable {J : GrothendieckTopology C}
variable {I : Type wI} [Category.{wI} I] [IsFiltered I]
variable [HasFiniteWidePullbacks C]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Cᵒᵖ ⥤ AddCommGrpCat.{v})]

-- Proof sketch: argue by induction on `p`. For `p = 0`, the chosen finite cofinal coverings force
-- the objects of `B` to satisfy the quasi-compactness criterion used to commute sections with
-- filtered colimits. For the inductive step, embed the filtered diagram into a filtered diagram of
-- injective sheaves, use exactness of filtered colimits to pass to cokernels, and reduce via the
-- long exact cohomology sequence. The injective-colimit term is acyclic in positive degree because
-- the finite chosen coverings keep all Čech intersections inside `B`, so degree-zero commutation
-- identifies the Čech complex of the colimit with the filtered colimit of the injective Čech
-- complexes, which are acyclic by Lemma `21.10.2`; then Lemma `21.10.9` upgrades this Čech
-- vanishing to vanishing of higher cohomology over every `U ∈ B`.
/-- Lemma 21.16.1: let `B` be a collection of objects of the site `(\mathcal C, J)` and, for each
`U`, let `Cov` be a set of coverings of `U` formalized as a set of `FormalCoproduct (Over U)`.
Assume that every selected covering in `Cov` is finite, has target in `B`, all of its members lie
in `B`, and every iterated Čech intersection of its members lies in `B`. Assume moreover that for
every `U ∈ B`, the coverings of `U` occurring in `Cov` form a cofinal system among all coverings
of `U`. Then for every filtered diagram of abelian sheaves, every `p : ℕ`, and every `U ∈ B`, the
canonical map `\operatorname{colim}_i H^p(U, \mathcal F_i) \to H^p(U, \operatorname{colim}_i
\mathcal F_i)` is an isomorphism. -/
theorem cohomologyOverColimitComparison_isIso_of_cofinal_finite_coverings
    (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct (Over U)))
    (hCov_cover : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → (J.over U).CoversTop cover.obj)
    (hCov_finite : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → Finite cover.I)
    (hCov_target : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → U ∈ B)
    (hCov_members : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → ∀ i : cover.I, (cover.obj i).left ∈ B)
    (hCov_intersections : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → ∀ n : ℕ, ∀ i : cechCoverIntersectionIndex cover n,
        cechCoverIntersectionObject cover n i ∈ B)
    (hCofinal : ∀ ⦃U : C⦄, U ∈ B → ∀ ⦃ι : Type w⦄ (family : ι → Over U),
      (J.over U).CoversTop family →
        ∃ cover : FormalCoproduct (Over U),
          cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family))
    (ℱ : I ⥤ Sheaf J AddCommGrpCat.{v}) (p : ℕ) {U : C} (hU : U ∈ B) :
    IsIso ((colimit.post ℱ (cohomologyPresheafFunctor J p)).app (op U)) := sorry

end Sheaf
end CategoryTheory
