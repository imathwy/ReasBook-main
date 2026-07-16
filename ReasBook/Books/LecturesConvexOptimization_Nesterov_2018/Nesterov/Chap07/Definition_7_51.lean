import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u v

/- Definition 7.51 is a recall-only item in the chapter's real-valued whole-space
subdifferential domain.

Mandatory domain-style sampling before refinement:
- `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in
  `Nesterov.Chap03.Theorem_3_44`, the chapter owner for real-valued relative
  subdifferentials;
- the whole-space owner usage `∂[Set.univ] f(x)` in
  `Nesterov.Chap03.Theorem_3_42`;
- the analogous Chapter 7 whole-space specialization in
  `Nesterov.Chap07.Definition_7_11`.

Best owner abstraction:
- source-facing: the whole-space subdifferential of the partial map `x' ↦ Ψ u x'` with respect
  to the second argument;
- core/canonical: `∂[Set.univ] (fun x' ↦ Ψ u x')(x)`;
- bridge/view: the specialization of `mem_subdifferentialWithin_iff` to `Set.univ`.

Primitive data:
- a parameter `u : U`;
- the partial map `fun x' ↦ Ψ u x' : X → ℝ`;
- the base point `x : X`.

Derived API:
- the global affine lower-support inequality for the partial map;
- the source wording “with respect to the second argument,” expressed as a companion bridge rather
  than a second owner abbreviation.

The former local presentation still made the membership characterization theorem the main public
entry, even though the numbered item is just the chapter owner itself specialized to the second
argument. This file therefore keeps the owner surface
`∂[Set.univ] (fun x' ↦ Ψ u x')(x)` as the main entry and demotes the affine inequality
to a companion bridge theorem. -/

variable {U : Type u} {X : Type v} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/- Definition 7.51: the subgradient with respect to the second argument of `Ψ` at `(u, x)` is a
member of the whole-space subdifferential of the partial map `x' ↦ Ψ u x'`, on the chapter
surface `∂[Q] f(x)`. -/
#check
  (fun (Ψ : U → X → ℝ) (u : U) (x : X) ↦
    (∂[Set.univ] (Ψ u)(x)))

/-- Membership in the whole-space second-argument subdifferential is exactly the global affine
lower-support inequality for the partial map `x' ↦ Ψ u x'`. -/
-- Proof sketch: specialize `mem_subdifferentialWithin_iff` to the whole-space constraint
-- `Set.univ`, then simplify away the feasibility clauses `x ∈ Set.univ` and `y ∈ Set.univ`.
theorem mem_secondArgumentSubdifferential_iff
    (Ψ : U → X → ℝ) (u : U) (x g : X) :
    g ∈ ∂[Set.univ] (Ψ u)(x) ↔
      ∀ y : X, Ψ u y ≥ Ψ u x + inner ℝ g (y - x) := sorry

end
