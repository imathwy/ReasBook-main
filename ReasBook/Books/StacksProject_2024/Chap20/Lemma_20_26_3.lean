import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Definition_20_26_2
import StacksProject_2024.Chap15.Lemma_15_59_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 20.26.3:
- primary domain: K-flat complexes and quasi-isomorphisms in the homotopy category of
  `(RingedSpace.Modules X)`;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `tensor_left_homotopy_functor`,
  `tensorHom_right_quasiIso_of_isKFlat`;
- best owner abstraction: the Chapter 15 owner theorem
  `tensorHom_right_quasiIso_of_isKFlat`;
- primitive vs derived: the primitive data are a complex `K`, a proof `hK : K.IsKFlat`, a map
  `f`, and a proof that `f` is a quasi-isomorphism; the ringed-space statement is derived API by
  specializing the ambient category to `(RingedSpace.Modules X)`, not by introducing a second owner
  theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-space formulation of the Stacks Project lemma;
- `core/canonical`: `tensorHom_right_quasiIso_of_isKFlat`;
- `bridge/view`: this file, which records only the direct recall of that owner theorem for later
  specialization to `(RingedSpace.Modules X)`. -/

-- Proof sketch: by Lemma `20.26.1`, the fixed-right-factor tensor-totalization functor on
-- `K(\mathrm{Mod}(\mathcal O_X))` is triangulated. A quasi-isomorphism is characterized by its
-- cone being acyclic, and Definition `20.26.2` says that tensoring an acyclic complex with a
-- K-flat complex remains acyclic. Therefore the image cone is acyclic, so the image morphism is a
-- quasi-isomorphism.
/- Lemma 20.26.3 is the ringed-space specialization of the Chapter 15 owner theorem asserting
that totalized tensoring with a fixed K-flat right factor preserves quasi-isomorphisms in the
homotopy category. -/
recall tensorHom_right_quasiIso_of_isKFlat
