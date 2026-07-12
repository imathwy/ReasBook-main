import StacksProject_2024.Chap21.Lemma_21_20_3
import StacksProject_2024.Chap21.Lemma_21_19_1_core

open CategoryTheory
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

open RingedSite.Hom
open scoped RingedSiteCohomology
open scoped RingedSiteDerived

namespace RingedSite.Hom

section

/- Domain-style sampling for Lemma 21.20.6:
- primary domain: objectwise derived cohomology presheaves and cohomology sheaves on ringed
  sites, together with their behavior under `Rf_*`;
- sampled owner declarations:
  `objectwiseCohomologyPresheaf`,
  `underlyingAbelianCohomologySheaf`,
  `modulePushforwardDerived`,
  `modulePushforwardToDerived`;
- best owner abstraction: the bundled ringed-site owners `𝓗'[i](X, K)` and `𝓗[i](X, K)` together
  with the canonical derived direct image owner `R(f)_*`; this file is the source-facing bridge
  expressing how objectwise cohomology compares across that owner;
- primitive data: a morphism of ringed sites `f : X ⟶ Y`, a derived `𝒪_X`-module `K`,
  and a degree `i`;
- derived API: the internal presheaf comparison bridge and the source-facing
  sheafification/cohomology-sheaf comparison below.

Source/core/bridge triage:
- `source-facing`: the sheafification/cohomology-sheaf comparison of Lemma `21.20.6`;
- `core/canonical`: `objectwiseCohomologyPresheaf`, `underlyingAbelianCohomologySheaf`, and
  `modulePushforwardDerived`;
- `bridge/view`: the internal presheaf-level comparison along `f.base.op`, used to derive the
  source-facing sheafification comparison from Lemma `21.20.3`. -/

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]

variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

-- Proof sketch: for each object `V : Y`, Lemma `21.20.5 (2)` identifies `RΓ(u(V), K)` with
-- `RΓ(V, R(f)_* K)` after restriction of scalars. Taking degree-`i` homology and forgetting the
-- module structure gives the required objectwise isomorphism of abelian presheaves.
/-- The source-side objectwise cohomology presheaf `V ↦ H^i(u(V), K)` is canonically isomorphic to
the objectwise cohomology presheaf of `R(f)_* K`. -/
theorem sourceObjectwiseCohomologyPresheaf_isomorphic_pushforwardObjectwiseCohomologyPresheaf
    (K : ModuleDerived X) (i : ℤ) :
    IsIsomorphic
      (f.base.op ⋙ 𝓗'[i](X, K))
      (𝓗'[i](Y, (R(f)_*).obj K)) := sorry

end

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

-- Proof sketch: first replace the presheaf `V ↦ H^i(u(V), K)` by the canonically isomorphic
-- presheaf `V ↦ H^i(V, R(f)_* K)` using the previous theorem. Then identify the sheafification of
-- that presheaf with the underlying abelian sheaf of the module-valued cohomology sheaf
-- `H^i(R(f)_* K)` on the target ringed site via Lemma `21.20.3`.
--
-- Here `HasSheafify Y.siteTopology AddCommGrpCat.{max u v}` is genuinely part of the target owner
-- `presheafToSheaf Y.siteTopology AddCommGrpCat.{max u v}`.
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]

/-- Lemma 21.20.6: for a morphism of ringed sites `f : X ⟶ Y` and `K : ModuleDerived X`, the
underlying abelian sheaf of the degree-`i` cohomology sheaf of `R(f)_* K` is canonically
isomorphic to the sheaf associated to the presheaf `V ↦ H^i(u(V), K)`. Equivalently, it is the
sheaf associated to `V ↦ H^i(V, R(f)_* K)`. This is the source-facing bridge to the owner theorem
of Lemma `21.20.3`, specialized to `R(f)_* K`. -/
@[stacks 0D6I]
theorem sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianCohomologySheaf
    (K : ModuleDerived X) (i : ℤ) :
    IsIsomorphic
      ((presheafToSheaf Y.siteTopology AddCommGrpCat.{max u v}).obj
        (f.base.op ⋙ 𝓗'[i](X, K)))
      (underlyingAbelianCohomologySheaf Y ((R(f)_*).obj K) i) := sorry

end

end RingedSite.Hom
