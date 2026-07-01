import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap18.Lemma_18_36_3

open CategoryTheory Limits AlgebraicGeometry Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u}) (x : X) (U : Opens X)

local notation "𝒪X" => (RingedSpace.ringCatSheaf X)

/- Domain-style sampling for Lemma 17.3.2:
- primary domain: categorical limits, colimits, filtered-colimit exactness, and stalk functors for
  sheaves of modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.forget`,
  `SheafOfModules.evaluation`,
  `Mod`,
  `PresheafOfModules.sheafification`,
  `CategoryTheory.point_sheaf_module_stalk_functor`;
- best owner abstraction: the source-facing owner notation `Mod(𝒪X)` on top of the canonical
  `SheafOfModules` owner `SheafOfModules (RingedSpace.ringCatSheaf X)`, with the site-point stalk
  functor as the core stalk owner and the ringed-space specialization below as the only needed
  bridge/view;
- primitive-vs-derived split:
  the primitive data are the structure sheaf `(RingedSpace.ringCatSheaf X)`, the source-facing
  owner `Mod(𝒪X)`, and the point `x`;
  all limit, colimit, `AB5`, and biproduct statements are derived owner-level API, while the
  module-valued stalk functor is the direct specialization of the canonical site-point stalk
  functor to `Opens.pointGrothendieckTopology x`.

Source/core/bridge triage:
- `source-facing`: the Stacks statements that `Mod(𝒪_X)` has limits/colimits, that sections over
  `U : Opens X` and stalks commute with those constructions, and that filtered colimits are exact;
- `core/canonical`: the canonical owner `SheafOfModules 𝒪X`, the source-facing notation `Mod(𝒪X)`,
  the anonymous mathlib instances on that owner, and the site-level owner
  `CategoryTheory.point_sheaf_module_stalk_functor`;
- `bridge/view`: the ringed-space specialization obtained by evaluating the site-point stalk
  functor at `Opens.pointGrothendieckTopology x`. -/

/- Lemma 17.3.2 (1): the category `Mod(𝒪_X)` of sheaves of `𝒪_X`-modules has all small limits. -/
#synth HasLimits (Mod(𝒪X))

/- Lemma 17.3.2 (2): limits in `Mod(𝒪_X)` agree with the corresponding limits of presheaves of
`𝒪_X`-modules after forgetting the sheaf condition. -/
#synth PreservesLimits (SheafOfModules.forget.{u} 𝒪X)

/- Lemma 17.3.2 (3): taking sections over any open set commutes with limits of
`𝒪_X`-modules. -/
#synth PreservesLimits (SheafOfModules.evaluation 𝒪X (op U))

/- Lemma 17.3.2 (4): the category `Mod(𝒪_X)` of sheaves of `𝒪_X`-modules has all small
colimits. -/
#synth HasColimits (Mod(𝒪X))

/- Lemma 17.3.2 (5): colimits in `Mod(𝒪_X)` are obtained by sheafifying the corresponding
colimits of presheaves of `𝒪_X`-modules. -/
#synth PreservesColimits
  (PresheafOfModules.sheafification (𝟙 (𝒪X).obj))

/- Lemma 17.3.2 (6): taking stalks commutes with colimits of `\mathcal O_X`-modules. This is the
ringed-space specialization of the canonical site-point module-stalk functor. -/
#synth PreservesColimits
  (point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) 𝒪X)

/- Lemma 17.3.2 (7): filtered colimits are exact in the category `Mod(𝒪_X)`. In canonical form,
this says that `Mod(𝒪_X)` satisfies `AB5`. -/
local instance : AB5 (Mod(𝒪X)) := by
  let _ : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  infer_instance

#synth AB5 (Mod(𝒪X))

/- Lemma 17.3.2 (8): finite direct sums of `𝒪_X`-modules are computed on the underlying
presheaves of modules. -/
#synth PreservesFiniteBiproducts (SheafOfModules.forget.{u} 𝒪X)

end

end AlgebraicGeometry.RingedSpace
