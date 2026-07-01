import Mathlib.Tactic.Recall
import stacks_project.Chap15.Lemma_15_59_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 21.17.3:
- primary domain: K-flat complexes and quasi-isomorphisms in the homotopy category of
  `ringedSiteModuleCategory J 𝒪`;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `tensor_left_homotopy_functor`,
  `tensorHom_right_quasiIso_of_isKFlat`;
- best owner abstraction: the Chapter 15 owner theorem
  `tensorHom_right_quasiIso_of_isKFlat`;
- primitive vs derived: the primitive data are a complex `K`, a proof `hK : K.IsKFlat`, a map
  `f`, and a proof that `f` is a quasi-isomorphism; the ringed-site statement is derived API by
  specializing the ambient category to `ringedSiteModuleCategory J 𝒪`, not by introducing a
  second owner theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-site formulation of the Stacks Project lemma;
- `core/canonical`: `tensorHom_right_quasiIso_of_isKFlat`;
- `bridge/view`: this file, which records only the direct specialization to
  `ringedSiteModuleCategory J 𝒪`. -/

-- Proof sketch: by Lemma `21.17.1`, the fixed-right-factor tensor-totalization functor on
-- `K(\mathrm{Mod}(\mathcal O))` is triangulated. A quasi-isomorphism is characterized by its
-- cone being acyclic, and Definition `21.17.2` says that tensoring an acyclic complex with a
-- K-flat complex remains acyclic. Therefore the image cone is acyclic, so the image morphism is a
-- quasi-isomorphism.
/- Lemma 21.17.3 is the ringed-site specialization of the Chapter 15 owner theorem asserting that
totalized tensoring with a fixed K-flat right factor preserves quasi-isomorphisms in the homotopy
category. -/
recall tensorHom_right_quasiIso_of_isKFlat

end SheafOfModules.RingedSite
