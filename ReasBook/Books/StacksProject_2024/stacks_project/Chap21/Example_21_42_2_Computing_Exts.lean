import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Ext

open CategoryTheory
open CochainComplex.HomComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {A : Type u} [Category.{u} A] [Abelian A] [HasExt A]

local notation "single0" => CochainComplex.singleFunctor A 0

/- Domain-style sampling for Example 21.42.2:
- primary domain: computation of `Ext` in an abelian category from projective or injective
  resolutions via the Hom complex, with Example 21.42.2 obtained by specializing to
  `A = Mod(𝒪)`;
- sampled owner declarations:
  `CategoryTheory.ProjectiveResolution.extAddEquivCohomologyClass`,
  `CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `stacks_project/Chap21/21_34_0_1.lean`;
- best owner abstraction: the source-facing computation is the canonical composite of the
  Ext-side owners `ProjectiveResolution.extAddEquivCohomologyClass` and
  `InjectiveResolution.extAddEquivCohomologyClass` with the bridge
  `CochainComplex.HomComplex.homologyAddEquiv`;
- primitive data: objects `G` and `F` of `A`, a chosen projective resolution `P` of `G` or
  injective resolution `I` of `F`, and a degree `n : ℕ`;
- derived API here: Example 21.42.2 is exactly the composition of those owner declarations, so
  the former local `IsIsomorphic` wrappers were duplicate wheel API, and a recall stopping at
  cohomology classes is still one bridge short of the textbook statement.

Source/core/bridge triage:
- `source-facing`: the textbook computation of `Ext^n(G, F)` by the explicit Hom complex,
  specialized in the chapter to `𝒪`-modules;
- `core/canonical`: `ProjectiveResolution.extAddEquivCohomologyClass` and
  `InjectiveResolution.extAddEquivCohomologyClass`;
- `bridge/view`: `CochainComplex.HomComplex.homologyAddEquiv`, already isolated as the canonical
  Hom-complex bridge in `21_34_0_1`;
- refinement target: expose the canonical Ext-to-homology composites directly instead of keeping
  parallel ringed-site-specific theorem wrappers or stopping at the intermediate cohomology-class
  owner. -/

/- Example 21.42.2 (projective-resolution computation): for `P : ProjectiveResolution G`, the
source-facing identification with the homology of `Hom^•(P^•, F[0])` is the direct canonical
composite from `Ext` to Hom-complex cohomology classes and then to degree-`n` homology;
specializing `A` to `Mod(𝒪)` recovers the textbook ringed-site statement. -/
variable (G F : A) (p : ProjectiveResolution G) (n : ℕ)

set_option linter.hashCommand false in
#check p.extAddEquivCohomologyClass.trans
  (homologyAddEquiv p.cochainComplex ((single0).obj F) n).symm

/- Example 21.42.2 (injective-resolution computation): for `I : InjectiveResolution F`, the dual
source-facing identification with the homology of `Hom^•(G[0], I^•)` is the direct canonical
composite from `Ext` to Hom-complex cohomology classes and then to degree-`n` homology;
specializing `A` to `Mod(𝒪)` recovers the textbook ringed-site statement. -/
variable (r : InjectiveResolution F)

set_option linter.hashCommand false in
#check r.extAddEquivCohomologyClass.trans
  (homologyAddEquiv ((single0).obj G) r.cochainComplex n).symm

end

end SheafOfModules.RingedSite
