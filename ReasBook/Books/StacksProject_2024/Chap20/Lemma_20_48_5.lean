import Mathlib
import Mathlib.Topology.Sheaves.Points
import stacks_project.Chap15.Definition_15_67_1
import stacks_project.Chap18.Lemma_18_36_3
import stacks_project.Chap20.Definition_20_48_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

local notation "DMod" => ModuleDerived X

/-- The commutative stalk ring `\mathcal O_{X, x}` packaged via the canonical site point
associated to `x`. -/
abbrev stalkCommRing (x : X) : CommRingCat :=
  (Opens.pointGrothendieckTopology x).presheafFiber.obj X.presheaf

/-- The forgotten ring-valued stalk identifies canonically with the commutative stalk ring at
`x`. -/
private abbrev stalkPointRingEquivCommRing (x : X) :
    ↑(CategoryTheory.point_stalk_ring (Opens.pointGrothendieckTopology x) (RingedSpace.ringCatSheaf X)) ≃+*
      ↑(stalkCommRing x) :=
  (((Opens.pointGrothendieckTopology x).presheafFiberCompIso
      (forget₂ CommRingCat RingCat)).app X.presheaf).ringCatIsoToRingEquiv

/-- The stalk functor on `\mathcal O_X`-modules at the point `x`. -/
private abbrev stalkModuleFunctor (x : X) :
    Modules X ⥤ ModuleCat (stalkCommRing x) :=
  CategoryTheory.point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x)
      (RingedSpace.ringCatSheaf X) ⋙
    ModuleCat.restrictScalars (stalkPointRingEquivCommRing x).symm.toRingHom

-- Proof sketch: specialize Lemma `18.36.3` to the canonical site point associated to `x` in the
-- topological space underlying `X`.
/-- The stalk functor on `\mathcal O_X`-modules at `x` is exact. -/
private theorem stalkModuleFunctor_exact (x : X) :
    exactFunctor (Modules X) (ModuleCat (stalkCommRing x))
      (stalkModuleFunctor x) := sorry

/-- The exact-functor package attached to the stalk functor on `\mathcal O_X`-modules at `x`. -/
private abbrev stalkModuleExactFunctor (x : X) :
    Modules X ⥤ₑ ModuleCat (stalkCommRing x) :=
  let _ : PreservesFiniteLimits (stalkModuleFunctor x) :=
    ((CategoryTheory.exactFunctor_iff (stalkModuleFunctor x)).mp
      (stalkModuleFunctor_exact x)).1
  let _ : PreservesFiniteColimits (stalkModuleFunctor x) :=
    ((CategoryTheory.exactFunctor_iff (stalkModuleFunctor x)).mp
      (stalkModuleFunctor_exact x)).2
  ExactFunctor.of (stalkModuleFunctor x)

-- Proof sketch: the site-theoretic stalk functor is additive, and restriction of scalars along a
-- ring isomorphism is additive, so their composite exact functor is additive as well.
/-- The exact stalk functor on `\mathcal O_X`-modules is additive. -/
private theorem stalkModuleExactFunctor_additive (x : X) :
    (stalkModuleExactFunctor x).obj.Additive := sorry

/-- The derived stalk functor `E ↦ E_x` from `D(\mathcal O_X)` to `D(\mathcal O_{X, x})`. -/
abbrev stalkDerived (x : X) :
    DMod ⥤ DerivedCategory (ModuleCat (stalkCommRing x)) :=
  let _ : (stalkModuleExactFunctor x).obj.Additive :=
    stalkModuleExactFunctor_additive x
  (stalkModuleExactFunctor x).obj.mapDerivedCategory

-- Proof sketch: for `(1) → (2)`, identify the derived stalk object with pullback along the point
-- morphism `({x}, \mathcal O_{X, x}) ⟶ (X, \mathcal O_X)` and apply Lemma `20.48.4`. For
-- `(2) → (1)`, test `E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F` on stalks; stalks commute
-- with tensor products by Lemma `17.16.1`, and Lemma `17.3.1` lets one detect vanishing by all
-- stalks.
/-- Lemma 20.48.5: an object `E` of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` if and only
if, for every point `x : X`, the derived stalk object `E_x` in `D(\mathcal O_{X, x})` has
tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_iff_forall_stalk
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ x : X, CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj E) a b := sorry

end

end AlgebraicGeometry.RingedSpace
