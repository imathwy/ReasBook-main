import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.stacks_project.Chap13.Definition_13_14_10
import StacksProject_2024.stacks_project.Chap19.Lemma_19_13_6
import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»
import StacksProject_2024.stacks_project.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- 
Domain-style sampling for Lemma 20.32.3:
- primary domain: objectwise hypercohomology presheaves and cohomology sheaves of derived
  `𝒪_X`-modules;
- sampled owner declarations:
  `moduleUnderlyingSheaf`,
  `moduleUnderlyingPresheaf`,
  `DerivedCategory.homologyFunctor`,
  `CategoryTheory.additiveFunctorTotalRightDerived`;
- best owner abstraction in the minimal compile closure: the canonical forgetful functor
  `moduleUnderlyingSheaf X` to additive sheaves, its composite
  `moduleUnderlyingPresheaf X` to additive presheaves, and the derived owner
  `additiveFunctorTotalRightDerived`;
- primitive data: a ringed space `X`, a derived object
  `K : DerivedCategory (RingedSpace.Modules X)`, and a degree
  `q : ℤ`;
- derived API here: the source-facing notation `𝓗'`/`𝓗` for the objectwise cohomology presheaf
  and cohomology sheaf, together with the source-facing sheafification comparison theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-space statement of Lemma 20.32.3;
- `core/canonical`: `moduleUnderlyingSheaf`, `moduleUnderlyingPresheaf`,
  `DerivedCategory.homologyFunctor`, and `CategoryTheory.additiveFunctorTotalRightDerived`;
- `bridge/view`: the source-facing ringed-space notation below, built directly from those
  canonical owners.
-/

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpaceCohomology

/- Textbook surface notation: `𝓗'[q](X, K)` denotes the underlined cohomology presheaf usually
written as `𝓗^q(K)`, while `𝓗[q](X, K)` denotes the cohomology sheaf `𝓗^q(K)`. -/
scoped notation:max "𝓗'[" q "](" X ", " K ")" =>
  CategoryTheory.Functor.obj
    (DerivedCategory.homologyFunctor (TopCat.Presheaf AddCommGrpCat X) q)
    (CategoryTheory.Functor.obj
      (CategoryTheory.additiveFunctorTotalRightDerived
        (AlgebraicGeometry.RingedSpace.moduleUnderlyingPresheaf X))
      K)

scoped notation:max "𝓗[" q "](" X ", " K ")" =>
  CategoryTheory.Functor.obj
    (AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf X)
    (CategoryTheory.Functor.obj
      (DerivedCategory.homologyFunctor (RingedSpace.Modules X) q)
      K)

end AlgebraicGeometry.RingedSpaceCohomology

namespace AlgebraicGeometry.RingedSpace

open scoped AlgebraicGeometry.RingedSpaceCohomology

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]

local notation "J" => Opens.grothendieckTopology X.carrier
local notation "AbPsh" => X.carrier.Presheaf AddCommGrpCat.{u}
local notation "AbSh" => X.carrier.Sheaf AddCommGrpCat.{u}
local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "PShSheafify" => presheafToSheaf J AddCommGrpCat.{u}
local notation "UnderlyingPsh" => moduleUnderlyingPresheaf X
local notation "UnderlyingSh" => moduleUnderlyingSheaf X
local notation "HMod" => DerivedCategory.homologyFunctor (RingedSpace.Modules X)
local notation "HSh" => DerivedCategory.homologyFunctor AbSh
local notation "RFp" => CategoryTheory.additiveFunctorTotalRightDerived UnderlyingPsh

/-- Helper for Lemma 20.32.3: the exact functor on the sheaf side is the sheafification of the
underlying additive presheaf. -/
private abbrev underlyingSheafificationFunctor :
    RingedSpace.Modules X ⥤ AbSh :=
  UnderlyingPsh ⋙ PShSheafify

/-- Helper for Lemma 20.32.3: sheafifying the underlying additive presheaf of an `𝒪_X`-module
recovers its underlying additive sheaf. -/
private noncomputable abbrev moduleUnderlyingPresheafSheafificationIso :
    underlyingSheafificationFunctor (X := X) ≅ UnderlyingSh := by
  -- Proof comment: `moduleUnderlyingPresheaf X` is the underlying additive sheaf followed by the
  -- sheaf inclusion, so the counit of sheafification contracts the extra `presheafToSheaf`.
  simpa [underlyingSheafificationFunctor, UnderlyingPsh, UnderlyingSh, moduleUnderlyingPresheaf,
    moduleUnderlyingSheaf] using
    (Functor.associator
      (moduleUnderlyingSheaf X)
      (sheafToPresheaf J AddCommGrpCat.{u})
      (presheafToSheaf J AddCommGrpCat.{u})) ≪≫
      Functor.isoWhiskerLeft
        (moduleUnderlyingSheaf X)
        (asIso ((sheafificationAdjunction J AddCommGrpCat.{u}).counit))

/-- Helper for Lemma 20.32.3: the sheafified underlying-presheaf functor is exact because it is
canonically isomorphic to `moduleUnderlyingSheaf X`. -/
private noncomputable instance moduleUnderlyingPresheafSheafification_preservesFiniteLimits :
    PreservesFiniteLimits (underlyingSheafificationFunctor (X := X)) := by
  -- Proof comment: transport finite-limit preservation across the underived comparison isomorphism.
  exact CategoryTheory.Limits.preservesFiniteLimits_of_natIso
    (moduleUnderlyingPresheafSheafificationIso (X := X))

/-- Helper for Lemma 20.32.3: the same comparison transports finite-colimit preservation to the
sheafified underlying-presheaf functor. -/
private noncomputable instance moduleUnderlyingPresheafSheafification_preservesFiniteColimits :
    PreservesFiniteColimits (underlyingSheafificationFunctor (X := X)) := by
  -- Proof comment: exactness on the target side is inherited from `moduleUnderlyingSheaf X`.
  exact CategoryTheory.Limits.preservesFiniteColimits_of_natIso
    (moduleUnderlyingPresheafSheafificationIso (X := X))

/-- Helper for Lemma 20.32.3: applying sheafification after the total right derived functor of the
underlying presheaf functor matches the exact derived functor of the sheafified composite. -/
private noncomputable def moduleUnderlyingPresheafSheafificationDerivedIso :
    RFp ⋙
        PShSheafify.mapDerivedCategory ≅
      (underlyingSheafificationFunctor (X := X)).mapDerivedCategory := by
  -- Route correction: the old proof jumped to the later Chapter 21 opens-site theorem. The local
  -- route compares two right derived functors of `UnderlyingPsh ⋙ PShSheafify` instead.
  -- TODO: build the right-derived comparison by showing the left-hand composite is a right
  -- derived functor of `UnderlyingSheafified` via exactness of `PShSheafify`, then apply
  -- `Functor.rightDerivedUnique` against `UnderlyingSheafified.mapDerivedCategory`.
  sorry

/-- Helper for Lemma 20.32.3: the exact sheafified-underlying functor carries the module-valued
cohomology sheaf to the corresponding sheaf-side homology object in the derived category. -/
private noncomputable abbrev moduleCohomologySheafToSheafifiedHomology
    (K : DModX) (q : ℤ) :
    (underlyingSheafificationFunctor (X := X)).obj ((HMod q).obj K) ≅
      (HSh q).obj ((underlyingSheafificationFunctor (X := X)).mapDerivedCategory.obj K) := by
  -- TODO: instantiate `exactFunctor_homology_iso_mapDerivedCategory` on the named owner
  -- `underlyingSheafificationFunctor (X := X)` and keep the resulting exact-functor normalization
  -- isolated from the closing theorem.
  sorry

/-- Helper for Lemma 20.32.3: sheafifying the objectwise cohomology presheaf is the same as
taking sheaf-side homology after applying sheafification on the derived level. -/
private noncomputable abbrev objectwiseCohomologyPresheafToSheafifiedHomology
    (K : DModX) (q : ℤ) :
    PShSheafify.obj (𝓗'[q](X, K)) ≅
      (HSh q).obj ((PShSheafify.mapDerivedCategory).obj (RFp.obj K)) := by
  -- TODO: apply the same exact-functor homology transport on the presheaf-side sheafification
  -- owner once the target-side normalization is stabilized.
  sorry

/-- Helper for Lemma 20.32.3: the cohomology sheaf is canonically isomorphic to the sheafification
of the objectwise cohomology presheaf. -/
private theorem objectwiseCohomologyPresheafSheafificationIso
    (K : DModX) (q : ℤ) :
    𝓗[q](X, K) ≅
      (PShSheafify.obj (𝓗'[q](X, K))) := by
  let eTarget :
      𝓗[q](X, K) ≅
        (HSh q).obj ((underlyingSheafificationFunctor (X := X)).mapDerivedCategory.obj K) := by
    -- Proof comment: normalize the target through the exact sheafified-underlying owner.
    exact
      ((moduleUnderlyingPresheafSheafificationIso (X := X)).app ((HMod q).obj K)).symm ≪≫
        moduleCohomologySheafToSheafifiedHomology (X := X) K q
  -- Proof comment: the middle comparison is the only genuinely derived step; once that is in
  -- place, the theorem is a short chain of exact-functor homology transports.
  exact
    eTarget ≪≫
      (HSh q).mapIso
        ((moduleUnderlyingPresheafSheafificationDerivedIso (X := X)).app K).symm ≪≫
      (objectwiseCohomologyPresheafToSheafifiedHomology (X := X) K q).symm

end

-- Proof sketch: identify the sheafified-underlying functor with `moduleUnderlyingSheaf X`,
-- transport objectwise cohomology across exact sheafification, and insert the single derived
-- comparison between `RF(moduleUnderlyingPresheaf X)` followed by sheafification and the exact
-- derived functor of the sheafified composite.
/-- Lemma 20.32.3: for a ringed space `(X, 𝒪_X)`, an object
`K : DerivedCategory (RingedSpace.Modules X)`, and an integer `q`, the sheaf associated to the
objectwise cohomology presheaf `𝓗'[q](X, K)` is canonically isomorphic to the degree-`q`
cohomology sheaf `𝓗[q](X, K)`. By Lemma `20.32.2`, the same comparison identifies `𝓗[q](X, K)`
with the sheaf associated to `U ↦ H^q(U, K|_U)`. -/
@[stacks 0BKJ]
theorem objectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    (K : DerivedCategory (RingedSpace.Modules X)) (q : ℤ) :
    IsIsomorphic
      (𝓗[q](X, K))
      ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (𝓗'[q](X, K))) := by
  -- Apply the opens-ringed-site comparison specialized back to the ringed-space owners.
  exact ⟨objectwiseCohomologyPresheafSheafificationIso (X := X) K q⟩

end AlgebraicGeometry.RingedSpace
