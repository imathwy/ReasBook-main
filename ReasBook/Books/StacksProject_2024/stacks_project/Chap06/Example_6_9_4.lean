import Mathlib
import StacksProject_2024.stacks_project.Chap06.Example_6_15_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe v

/- Domain-style sampling for Example 6.9.4:
- primary domain: sheaf conditions for `TopCat`-valued product presheaves on a discrete base and
  for the discrete-topology bridge obtained from the underlying type-valued owner;
- sampled owner API:
  `TopCat.presheafToTypes`,
  `TopCat.Presheaf.toTypes_isSheaf`,
  `pointwiseProductPresheaf`,
  `pointwiseProductPresheaf_isSheaf`;
- owner abstraction:
  the set-valued owner is the dependent-function presheaf `TopCat.presheafToTypes (TopCat.of ℕ) A`;
  the topological-space owner for the product-topology version is the chapter-level canonical
  `pointwiseProductPresheaf` specialized to the discrete fibers `TopCat.discrete.obj (A i)`;
  the sectionwise-discrete topology is only the bridge/view given by composition with
  `TopCat.discrete`;
- primitive-vs-derived split:
  primitive data are only the fibres `A : ℕ → Type v`;
  the product-topology presheaf is derived from the canonical `TopCat` product owner
  `pointwiseProductPresheaf`, the underlying set-valued sheaf condition is derived from
  `TopCat.Presheaf.toTypes_isSheaf`, and the sheaf failure is attached only to the
  discrete-topology bridge;
- source/core/bridge triage:
  `source-facing`: the contrast that the product-topology presheaf is a sheaf of topological
    spaces, while the sectionwise-discrete-topology realization has a sheaf underlying presheaf of
    sets but is not itself a sheaf when each fibre has at least two elements;
  `core/canonical`: `TopCat.presheafToTypes` for the underlying set-valued owner and
    `pointwiseProductPresheaf` for the `TopCat`-valued product-topology owner;
  `bridge/view`: composition with `TopCat.discrete`.

The file should therefore reuse the chapter owner `pointwiseProductPresheaf` for the positive
topological statement, and use `TopCat.presheafToTypes` only for the underlying set-valued bridge
of the sectionwise-discrete presheaf.
-/

section

variable (A : ℕ → Type v)

/-- Example 6.9.4 (1): endowing each fibre `A i` with the discrete topology and each section space
`U ↦ ∏ i : U, A i` with the induced product topology gives a sheaf of topological spaces. This is
the source-facing positive sheaf statement on the canonical owner `pointwiseProductPresheaf`. -/
-- Proof sketch: specialize the chapter-level sheaf theorem for `pointwiseProductPresheaf` to the
-- discrete fibres `TopCat.discrete.obj (A i)`.
theorem pointwiseProductPresheaf_discrete_isSheaf :
    (pointwiseProductPresheaf
      (fun i : TopCat.of ℕ ↦ (TopCat.discrete.obj (A i) : TopCat.{v}))).IsSheaf := sorry

/-- Example 6.9.4 (2): after equipping each section space `U ↦ ∏ i : U, A i` with the discrete
topology, the underlying presheaf of sets is still the canonical dependent-function sheaf. -/
-- Proof sketch: identify the underlying presheaf of sets with `TopCat.presheafToTypes` and apply
-- `TopCat.Presheaf.toTypes_isSheaf`.
theorem presheafToTypes_discrete_underlying_isSheaf :
    TopCat.Presheaf.IsSheaf
      ((((TopCat.of ℕ).presheafToTypes A) ⋙ TopCat.discrete) ⋙ forget TopCat) := sorry

/-- Example 6.9.4 (3): if each fibre `A i` has at least two elements, then equipping
`U ↦ ∏ i : U, A i` with the discrete topology on each section space does not produce a sheaf of
topological spaces, even though the underlying presheaf of sets is a sheaf. -/
-- Proof sketch: combine the sheaf obstruction for the sectionwise-discrete topology with the
-- nontriviality hypothesis on each fibre.
theorem presheafToTypes_discrete_not_isSheaf (hA : ∀ i : ℕ, Nontrivial (A i)) :
    ¬ TopCat.Presheaf.IsSheaf (((TopCat.of ℕ).presheafToTypes A) ⋙ TopCat.discrete) := sorry

end
