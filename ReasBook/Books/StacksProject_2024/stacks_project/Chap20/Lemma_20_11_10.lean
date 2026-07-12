import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap20.Lemma_20_11_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace AlgebraicGeometry RingedSpace.Hom
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

-- Proof sketch: pull the cover `𝒱` of `V` back along `f` to a cover of `f⁻¹(V)`. The underlying
-- additive presheaf of `f_* ℐ` evaluates on each Čech intersection as `ℐ` on the corresponding
-- pulled-back intersection, so its Čech complex identifies with the Čech complex of `ℐ` on the
-- pulled-back cover. Then apply injective Čech-acyclicity.
/-- Lemma 20.11.10 (1): if `f : X ⟶ Y` is a morphism of ringed spaces and `ℐ` is an
injective `𝒪_X`-module, then `f_* ℐ` has vanishing higher Čech cohomology on
every open covering of every open subset of `Y`. -/
@[stacks 01EX]
theorem hasVanishingHigherCechOnOpenCoverings_modulePushforward_of_injective
    (f : X ⟶ Y) (ℐ : X.Modules) [Injective ℐ] :
    HasVanishingHigherCechOnOpenCoverings ((f _*).obj ℐ) := sorry

/-- If `f : X ⟶ Y` is a morphism of ringed spaces and `ℐ` is an injective
`𝒪_X`-module, then the positive Čech cohomology of `f_* ℐ` vanishes for every
indexed family of opens of `Y`, equivalently for every open covering of its union. -/
theorem cech_cohomology_isZero_modulePushforward_of_injective
    (f : X ⟶ Y) (ℐ : X.Modules) [Injective ℐ]
    {ι : Type u} (𝒱 : ι → Opens Y.carrier)
    (p : ℕ) (hp : 0 < p) :
    IsZero (moduleCechCohomology 𝒱 ((f _*).obj ℐ) p) :=
  hasVanishingHigherCechOnOpenCoverings_modulePushforward_of_injective f ℐ 𝒱 p hp

/-- Typeclass form of positive-degree Čech acyclicity for the direct image of an injective
`𝒪_X`-module. -/
instance instIsZeroModuleCechCohomologyModulePushforwardOfInjective
    (f : X ⟶ Y) (ℐ : X.Modules) [Injective ℐ]
    {ι : Type u} (𝒱 : ι → Opens Y.carrier) (p : ℕ) [Fact (0 < p)] :
    IsZero (moduleCechCohomology 𝒱 ((f _*).obj ℐ) p) :=
  cech_cohomology_isZero_modulePushforward_of_injective f ℐ 𝒱 p Fact.out

-- Proof sketch: the first part gives vanishing of higher Čech cohomology for every open covering
-- of every open subset of `Y`. Apply the comparison from Čech cohomology to sheaf cohomology to
-- deduce the vanishing of `H^p(V, f_* ℐ)` for all `p > 0`.
/-- Lemma 20.11.10 (2): if `f : X ⟶ Y` is a morphism of ringed spaces and `ℐ` is an
injective `𝒪_X`-module, then `H^p(V, f_* ℐ) = 0` for every open subset
`V ⊆ Y` and every `p > 0`; equivalently, `f_* ℐ` is right acyclic for `Γ(V, -)`. -/
@[stacks 01EX]
theorem higherCohomology_isZero_modulePushforward_of_injective
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Y) (ℐ : X.Modules) [Injective ℐ]
    (V : Opens Y.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero (((moduleUnderlyingSheaf Y).obj ((f _*).obj ℐ)).H' p V) :=
  higherCohomology_isZero_of_vanishingHigherCech_on_openCoverings ((f _*).obj ℐ)
    (hasVanishingHigherCechOnOpenCoverings_modulePushforward_of_injective f ℐ) V p hp

/-- Typeclass form of the higher-cohomology vanishing of `f_* ℐ` in positive degree. -/
instance instIsZeroHigherCohomologyModulePushforwardOfInjective
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Y) (ℐ : X.Modules) [Injective ℐ]
    (V : Opens Y.carrier) (p : ℕ) [Fact (0 < p)] :
    IsZero (((moduleUnderlyingSheaf Y).obj ((f _*).obj ℐ)).H' p V) :=
  higherCohomology_isZero_modulePushforward_of_injective f ℐ V p Fact.out

end AlgebraicGeometry.RingedSpace
