import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Functors

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

namespace CategoryTheory
namespace Sheaf

/- Domain-style sampling for Proposition 20.20.7:
- primary domain: higher cohomology of abelian sheaves on Noetherian topological spaces, bounded by
  topological Krull dimension;
- sampled owner declarations:
  `CategoryTheory.Sheaf.H'`,
  `isZero_higherCohomology_of_acyclic_extensionByZeroConstantIntegerSheaf`,
  `isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_le`;
- best owner abstraction: the cohomology groups are already canonically owned by `Sheaf.H'`, so
  this proposition should stay a source-facing vanishing theorem rather than introduce a parallel
  cohomology wrapper;
- primitive data versus derived API: the primitive inputs are the Noetherian space `X`, the
  dimension bound `hXdim`, the sheaf `F`, and the degree inequality `hp`; the object
  `F.H' p (⊤ : Opens X)` is derived canonical API from the sheaf-cohomology owner.

Source/core/bridge triage:
- `source-facing`: Grothendieck's vanishing statement for arbitrary Noetherian spaces;
- `core/canonical`: `topologicalKrullDim` and `CategoryTheory.Sheaf.H'`;
- `bridge/view`: the later spectral-space theorem
  `isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_le`, which is a stronger
  specialization under different ambient hypotheses and therefore should not replace the present
  source-facing Noetherian-space statement. -/

variable {X : TopCat.{u}} [NoetherianSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]

-- Proof sketch: argue by induction on `d`. First use the finite decomposition of a Noetherian
-- space into irreducible components to reduce, via the short exact sequence for an open subset and
-- its closed complement together with Lemma `20.20.1`, to the case that `X` is irreducible. For
-- irreducible `X`, the case `d = 0` follows from Lemma `20.20.2`, and the case `d > 0` reduces by
-- Lemma `20.20.4` to extension-by-zero constant sheaves on opens, where the standard short exact
-- sequence with the constant sheaf on `X` and the induction hypothesis on the closed complement
-- gives the vanishing in degrees `p > d`.
/-- Proposition 20.20.7 (Grothendieck): if `X` is a Noetherian topological space of Krull
dimension at most `d`, then every abelian sheaf on `X` has vanishing global cohomology in degrees
strictly larger than `d`. -/
@[stacks 02UZ]
theorem isZero_higherCohomology_of_noetherianSpace_of_topologicalKrullDim_le
    (d : ℕ) (hXdim : topologicalKrullDim X ≤ d)
    (F : X.Sheaf AddCommGrpCat.{u}) {p : ℕ} (hp : d < p) :
    IsZero (F.H' p (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory
