import Mathlib
import StacksProject_2024.Chap05.Example_5_10_3
import StacksProject_2024.Chap20.Proposition_20_22_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

/-
Domain-style sampling for Lemma 20.22.3:
- primary domain: higher sheaf cohomology vanishing on spectral spaces and its profinite
  specialization;
- same-domain owner declarations inspected:
  `Profinite`,
  `topologicalKrullDim_eq_zero_of_nonempty_t2`,
  `isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_eq`;
- best owner abstractions: the bundled topological owner `Profinite` for the source-facing
  specialization, and the spectral-space vanishing theorem as the core/canonical owner;
- primitive-vs-derived split: the primitive input here is only the profinite space `X`; the
  zero-dimensionality statement and the vanishing result are derived API, so this file should be a
  thin bridge from `Profinite` to the spectral-space owner rather than a parallel standalone
  vanishing theorem.

Layer triage:
- `source-facing`: vanishing of higher cohomology on a profinite space
- `core/canonical`: `isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_eq`
- `bridge/view`: specialization along `topologicalKrullDim_eq_zero_of_nonempty_t2`

Primitive data is just the profinite space itself. Clopen-refinement statements, unbundled
compact/Hausdorff/totally disconnected hypotheses, and zero-dimensional reformulations are all
derived topology-side API, so the public statement here should stay at the bundled `Profinite`
owner while its proof and surrounding commentary reuse the spectral-space owner directly.
-/

variable {X : Profinite.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- Lemma 20.22.3: if `X` is a profinite topological space, then every abelian sheaf on `X` has
vanishing higher global cohomology. -/
theorem isZero_higherCohomology_of_profinite
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) {q : ℕ} (hq : 0 < q) :
    IsZero (F.H' q (⊤ : Opens X)) := by
  simpa using
    (isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_eq
      (X := Profinite.toTopCat.obj X)
      (d := 0)
      (hXdim := topologicalKrullDim_eq_zero_of_nonempty_t2 X)
      (F := F)
      (hq := hq))

end Sheaf
end CategoryTheory
