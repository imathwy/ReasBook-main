import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.26.3:
- primary domain: quasi-isomorphism preservation under totalized tensoring by a fixed K-flat
  complex of `𝒪_X`-modules;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `HomologicalComplex.tensorHom`,
  `tensorHom_right_quasiIso_of_isKFlat`;
- best owner abstraction: the Chapter 15 owner theorem
  `tensorHom_right_quasiIso_of_isKFlat`, whose source-facing map is already the canonical tensor
  morphism `tensorHom f (𝟙 K)`;
- primitive vs derived: the primitive data are a complex `K`, its K-flatness proof, a map `f`,
  and a proof that `f` is a quasi-isomorphism. The induced tensor map is derived API from the
  monoidal owner `tensorHom`.

Source/core/bridge triage:
- `source-facing`: Lemma 20.26.3 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: `tensorHom_right_quasiIso_of_isKFlat`;
- `bridge/view`: this file records only the ringed-space specialization, so it should be a direct
  recall rather than a second namespace theorem with the same interface. -/

/- Lemma 20.26.3: if `𝒦^•` is a K-flat complex of `𝒪_X`-modules on a ringed space `(X, 𝒪_X)`,
then tensoring any quasi-isomorphism with `𝒦^•` on the right again gives a quasi-isomorphism.
This is exactly the ringed-space specialization of the Chapter 15 owner theorem
`tensorHom_right_quasiIso_of_isKFlat`. -/
recall tensorHom_right_quasiIso_of_isKFlat

end AlgebraicGeometry.RingedSpace
