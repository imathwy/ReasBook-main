module

public import Topology_Munkres_2000.Book.Theorem_62_1.CechCompactum
public import Topology_Munkres_2000.Book.Theorem_62_1.GraphHomology
public import Topology_Munkres_2000.Book.Theorem_62_1.NerveHomotopy
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.LinearAlgebra.Dual.Defs

public section

namespace InvarianceOfDomainSupport

open CategoryTheory

universe u v

namespace CechFiniteOpenCover

/-- Helper for Theorem 62.1: a refinement choice induces the simplicial map
between the categorical nerves of the fine and coarse face posets. -/
def RefinementMap.faceNerveMap {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f : RefinementMap U V) :
    CategoryTheory.nerve V.NerveFace ⟶ CategoryTheory.nerve U.NerveFace :=
  CategoryTheory.nerveMap f.faceMap.toFunctor

/-- Helper for Theorem 62.1: the common union-face map induces a simplicial map
between the categorical face-poset nerves. -/
def RefinementMap.unionFaceNerveMap {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) :
    CategoryTheory.nerve V.NerveFace ⟶ CategoryTheory.nerve U.NerveFace :=
  CategoryTheory.nerveMap (f.unionFaceMap g).toFunctor

/-- Helper for Theorem 62.1: inclusion of the first image in the union image is
a natural transformation between face-poset functors. -/
def RefinementMap.faceMapToUnionNatTransLeft {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) :
    f.faceMap.toFunctor ⟶ (f.unionFaceMap g).toFunctor :=
  OrderHom.equivalenceFunctor.functor.map
    (CategoryTheory.homOfLE (f.faceMap_le_unionFaceMap_left g))

/-- Helper for Theorem 62.1: inclusion of the second image in the union image is
a natural transformation between face-poset functors. -/
def RefinementMap.faceMapToUnionNatTransRight {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) :
    g.faceMap.toFunctor ⟶ (f.unionFaceMap g).toFunctor :=
  OrderHom.equivalenceFunctor.functor.map
    (CategoryTheory.homOfLE (f.faceMap_le_unionFaceMap_right g))

/-- Helper for Theorem 62.1: the left comparison transformation is the
pointwise inclusion of a refinement image into the union image. -/
lemma RefinementMap.faceMapToUnionNatTransLeft_app {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) (s : V.NerveFace) :
    (f.faceMapToUnionNatTransLeft g).app s =
      CategoryTheory.homOfLE (f.faceMap_le_unionFaceMap_left g s) := by
  -- The preorder-to-functor equivalence retains the supplied pointwise inequality.
  rfl

/-- Helper for Theorem 62.1: the right comparison transformation is the
pointwise inclusion of a refinement image into the union image. -/
lemma RefinementMap.faceMapToUnionNatTransRight_app {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) (s : V.NerveFace) :
    (f.faceMapToUnionNatTransRight g).app s =
      CategoryTheory.homOfLE (f.faceMap_le_unionFaceMap_right g s) := by
  -- The preorder-to-functor equivalence retains the supplied pointwise inequality.
  rfl

end CechFiniteOpenCover

/-- Helper for Theorem 62.1: pushing a finitely supported chain along a function
preserves membership in the component-augmentation kernel. -/
lemma lmapDomain_mem_componentAugmentationKernel {I J : Type*} (q : I → J)
    (x : I →₀ ZMod 2)
    (hx : x ∈ LinearMap.ker (componentAugmentationModTwo I)) :
    Finsupp.lmapDomain (ZMod 2) (ZMod 2) q x ∈
      LinearMap.ker (componentAugmentationModTwo J) := by
  -- Evaluate augmentation naturality on the chain and finish with its kernel equation.
  rw [LinearMap.mem_ker] at hx ⊢
  have hAugmentation := LinearMap.congr_fun
    (componentAugmentationModTwo_comp_lmapDomain q) x
  exact hAugmentation.trans hx

/-- Helper for Theorem 62.1: a function on component indices pushes the
corresponding mod-two augmentation kernel forward. -/
noncomputable def componentAugmentationKernelMapOfFunction {I J : Type*}
    (q : I → J) :
    LinearMap.ker (componentAugmentationModTwo I) →ₗ[ZMod 2]
      LinearMap.ker (componentAugmentationModTwo J) :=
  ((Finsupp.lmapDomain (ZMod 2) (ZMod 2) q).domRestrict
      (LinearMap.ker (componentAugmentationModTwo I))).codRestrict _
    (fun x ↦ lmapDomain_mem_componentAugmentationKernel q x x.property)

/-- Helper for Theorem 62.1: coercing the kernel pushforward recovers ordinary
pushforward of finitely supported chains. -/
lemma componentAugmentationKernelMapOfFunction_apply {I J : Type*} (q : I → J)
    (x : LinearMap.ker (componentAugmentationModTwo I)) :
    ((componentAugmentationKernelMapOfFunction q x :
      LinearMap.ker (componentAugmentationModTwo J)) : J →₀ ZMod 2) =
        Finsupp.lmapDomain (ZMod 2) (ZMod 2) q x := by
  -- Cross the codomain restriction through its named computation rule.
  exact LinearMap.codRestrict_apply _ _ _

/-- Helper for Theorem 62.1: pointwise equal functions induce equal maps on
component-augmentation kernels. -/
lemma componentAugmentationKernelMapOfFunction_congr {I J : Type*}
    {q r : I → J} (h : ∀ i, q i = r i) :
    componentAugmentationKernelMapOfFunction q =
      componentAugmentationKernelMapOfFunction r := by
  -- Coerce to ambient chains, where map-domain congruence is pointwise.
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [componentAugmentationKernelMapOfFunction_apply,
    componentAugmentationKernelMapOfFunction_apply]
  exact Finsupp.mapDomain_congr (fun i _ ↦ h i)

/-- Helper for Theorem 62.1: the identity function induces the identity map on
the component-augmentation kernel. -/
lemma componentAugmentationKernelMapOfFunction_id (I : Type*) :
    componentAugmentationKernelMapOfFunction (id : I → I) = LinearMap.id := by
  -- Coerce to ambient chains and use the identity law for map-domain.
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [componentAugmentationKernelMapOfFunction_apply, LinearMap.id_apply]
  exact Finsupp.mapDomain_id

/-- Helper for Theorem 62.1: pushforward on component-augmentation kernels
respects composition of functions. -/
lemma componentAugmentationKernelMapOfFunction_comp {I J K : Type*}
    (q : I → J) (r : J → K) :
    componentAugmentationKernelMapOfFunction (r ∘ q) =
      (componentAugmentationKernelMapOfFunction r).comp
        (componentAugmentationKernelMapOfFunction q) := by
  -- Coerce to ambient chains and apply the composition law for map-domain.
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [componentAugmentationKernelMapOfFunction_apply, LinearMap.comp_apply,
    componentAugmentationKernelMapOfFunction_apply,
    componentAugmentationKernelMapOfFunction_apply]
  exact Finsupp.mapDomain_comp

namespace CechFiniteOpenCover

/-- Helper for Theorem 62.1: the identity refinement induces the identity map
of the categorical face-poset nerve. -/
lemma RefinementMap.faceNerveMap_id {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) [DecidableEq U.Index] :
    (RefinementMap.id U).faceNerveMap =
      𝟙 (CategoryTheory.nerve U.NerveFace) := by
  -- Rewrite the underlying monotone map to the identity before applying the nerve.
  rw [faceNerveMap, RefinementMap.faceMap_id]
  rfl

/-- Helper for Theorem 62.1: simplicial face-nerve maps respect composition of
refinement choices. -/
lemma RefinementMap.faceNerveMap_comp {X : Type u} [TopologicalSpace X]
    {U V W : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] [DecidableEq V.Index]
    (f : RefinementMap U V) (g : RefinementMap V W) :
    (f.comp g).faceNerveMap = g.faceNerveMap ≫ f.faceNerveMap := by
  -- Rewrite to composition of order maps; the categorical nerve then computes directly.
  rw [faceNerveMap, faceNerveMap, faceNerveMap, RefinementMap.faceMap_comp]
  rfl

/-- Helper for Theorem 62.1: the mod-two coefficient module is lifted to the
universe of the finite cover's index type. -/
noncomputable abbrev nerveCoefficientModTwo : ModuleCat.{v} (ZMod 2) :=
  ModuleCat.of (ZMod 2) (ULift.{v} (ZMod 2))

/-- Helper for Theorem 62.1: simplicial homology of a finite-cover face nerve
with mod-two coefficients. -/
noncomputable abbrev faceNerveHomology {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) (q : ℕ) : ModuleCat.{v} (ZMod 2) :=
  (CategoryTheory.nerve U.NerveFace).homology nerveCoefficientModTwo q

/-- Helper for Theorem 62.1: a chosen cover refinement induces the covariant
map on mod-two homology of finite-cover face nerves. -/
noncomputable abbrev RefinementMap.faceNerveHomologyMap
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f : RefinementMap U V) (q : ℕ) :
    faceNerveHomology V q ⟶ faceNerveHomology U q :=
  SSet.homologyMap f.faceNerveMap nerveCoefficientModTwo q

/-- Helper for Theorem 62.1: the identity refinement induces the identity on
mod-two homology of a finite-cover face nerve. -/
lemma RefinementMap.faceNerveHomologyMap_id {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) [DecidableEq U.Index] (q : ℕ) :
    (RefinementMap.id U).faceNerveHomologyMap q = 𝟙 _ := by
  -- Normalize the underlying simplicial map before applying homology functoriality.
  rw [faceNerveHomologyMap, RefinementMap.faceNerveMap_id]
  exact SSet.homologyMap_id _ _ q

/-- Helper for Theorem 62.1: mod-two face-nerve homology maps preserve
composition of chosen cover refinements. -/
lemma RefinementMap.faceNerveHomologyMap_comp {X : Type u} [TopologicalSpace X]
    {U V W : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] [DecidableEq V.Index]
    (f : RefinementMap U V) (g : RefinementMap V W) (q : ℕ) :
    (f.comp g).faceNerveHomologyMap q =
      g.faceNerveHomologyMap q ≫ f.faceNerveHomologyMap q := by
  -- Normalize the composite simplicial map, then use homology functoriality.
  rw [faceNerveHomologyMap, RefinementMap.faceNerveMap_comp]
  exact SSet.homologyMap_comp
    (CategoryTheory.nerve W.NerveFace) (CategoryTheory.nerve V.NerveFace)
    (CategoryTheory.nerve U.NerveFace) g.faceNerveMap f.faceNerveMap
    nerveCoefficientModTwo q

/-- Helper for Theorem 62.1: simplicial homotopies from two refinement choices
to their common union-face map imply equality of the induced homology maps. -/
lemma RefinementMap.faceNerveHomologyMap_eq_of_homotopies
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) (q : ℕ)
    (hLeft : CategoryTheory.SimplicialObject.Homotopy
      f.faceNerveMap (f.unionFaceNerveMap g))
    (hRight : CategoryTheory.SimplicialObject.Homotopy
      g.faceNerveMap (f.unionFaceNerveMap g)) :
    f.faceNerveHomologyMap q = g.faceNerveHomologyMap q := by
  -- Compare both choices with the union-face map by homotopy invariance.
  calc
    f.faceNerveHomologyMap q =
        SSet.homologyMap (f.unionFaceNerveMap g)
          nerveCoefficientModTwo q :=
      hLeft.congr_sSetHomologyMap _ q
    _ = g.faceNerveHomologyMap q :=
      (hRight.congr_sSetHomologyMap _ q).symm

/-- Helper for Theorem 62.1: two choices for the same cover refinement induce
the same map on mod-two homology of their categorical face-poset nerves. -/
lemma RefinementMap.faceNerveHomologyMap_eq
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) (q : ℕ) :
    f.faceNerveHomologyMap q = g.faceNerveHomologyMap q := by
  -- The union-face map is pointwise above both choices, so the two prism
  -- homotopies compare their homology maps through one common map.
  obtain ⟨hLeft⟩ := CategoryTheory.OrderHom.nerveMapHomotopyOfPointwiseLE
    f.faceMap (f.unionFaceMap g) (f.faceMap_le_unionFaceMap_left g)
  obtain ⟨hRight⟩ := CategoryTheory.OrderHom.nerveMapHomotopyOfPointwiseLE
    g.faceMap (f.unionFaceMap g) (f.faceMap_le_unionFaceMap_right g)
  exact f.faceNerveHomologyMap_eq_of_homotopies g q hLeft hRight

/-- Helper for Theorem 62.1: finite-stage mod-two cohomology is the linear dual
of homology of the categorical finite-cover face nerve. -/
noncomputable abbrev faceNerveCohomology {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) (q : ℕ) :=
  Module.Dual (ZMod 2) (faceNerveHomology U q)

/-- Helper for Theorem 62.1: a chosen cover refinement induces the
contravariant map on finite-stage mod-two face-nerve cohomology. -/
noncomputable def RefinementMap.faceNerveCohomologyMap
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f : RefinementMap U V) (q : ℕ) :
    faceNerveCohomology U q →ₗ[ZMod 2] faceNerveCohomology V q :=
  (f.faceNerveHomologyMap q).hom.dualMap

/-- Helper for Theorem 62.1: the finite-stage mod-two cohomology map is
independent of the chosen parent map witnessing a cover refinement. -/
lemma RefinementMap.faceNerveCohomologyMap_eq
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) (q : ℕ) :
    f.faceNerveCohomologyMap q = g.faceNerveCohomologyMap q := by
  -- Apply linear duality to the established choice-independent homology map.
  exact congrArg (fun h ↦ h.hom.dualMap) (f.faceNerveHomologyMap_eq g q)

/-- Helper for Theorem 62.1: the identity cover refinement induces the
identity on finite-stage mod-two face-nerve cohomology. -/
lemma RefinementMap.faceNerveCohomologyMap_id
    {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) [DecidableEq U.Index] (q : ℕ) :
    (RefinementMap.id U).faceNerveCohomologyMap q = LinearMap.id := by
  -- Dualize the identity law for the corresponding homology map.
  rw [faceNerveCohomologyMap, RefinementMap.faceNerveHomologyMap_id,
    ModuleCat.hom_id]
  exact LinearMap.dualMap_id

/-- Helper for Theorem 62.1: finite-stage mod-two cohomology maps reverse the
composition of chosen cover refinements. -/
lemma RefinementMap.faceNerveCohomologyMap_comp
    {X : Type u} [TopologicalSpace X]
    {U V W : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] [DecidableEq V.Index]
    (f : RefinementMap U V) (g : RefinementMap V W) (q : ℕ) :
    (f.comp g).faceNerveCohomologyMap q =
      (g.faceNerveCohomologyMap q).comp (f.faceNerveCohomologyMap q) := by
  -- Convert categorical composition to linear-map composition before dualizing.
  rw [faceNerveCohomologyMap, RefinementMap.faceNerveHomologyMap_comp,
    ModuleCat.hom_comp]
  exact (LinearMap.dualMap_comp_dualMap (g.faceNerveHomologyMap q).hom
    (f.faceNerveHomologyMap q).hom).symm

/-- Helper for Theorem 62.1: two choices for the same cover refinement induce
the same function on components of the categorical face-poset nerves. -/
lemma RefinementMap.faceNerveComponentMap_eq {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) :
    SSet.mapπ₀ f.faceNerveMap = SSet.mapπ₀ g.faceNerveMap := by
  -- Compare both choices with their common union-face map through the two
  -- natural transformations already constructed above.
  have hLeft := CategoryTheory.NatTrans.nerveMap_mapπ₀_eq
    (f.faceMapToUnionNatTransLeft g)
  have hRight := CategoryTheory.NatTrans.nerveMap_mapπ₀_eq
    (f.faceMapToUnionNatTransRight g)
  exact hLeft.trans hRight.symm

/-- Helper for Theorem 62.1: the identity refinement induces the identity
function on components of the categorical face-poset nerve. -/
lemma RefinementMap.faceNerveComponentMap_id {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) [DecidableEq U.Index] :
    SSet.mapπ₀ (RefinementMap.id U).faceNerveMap = _root_.id := by
  -- Reduce to functoriality of connected components on the identity simplicial map.
  rw [RefinementMap.faceNerveMap_id]
  funext z
  exact SSet.mapπ₀_id_apply z

/-- Helper for Theorem 62.1: component functions of face-poset nerve maps
respect composition of refinement choices. -/
lemma RefinementMap.faceNerveComponentMap_comp {X : Type u} [TopologicalSpace X]
    {U V W : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] [DecidableEq V.Index]
    (f : RefinementMap U V) (g : RefinementMap V W) :
    SSet.mapπ₀ (f.comp g).faceNerveMap =
      SSet.mapπ₀ f.faceNerveMap ∘ SSet.mapπ₀ g.faceNerveMap := by
  -- Reduce to functoriality of connected components on a composite simplicial map.
  rw [RefinementMap.faceNerveMap_comp]
  funext z
  exact SSet.mapπ₀_comp_apply g.faceNerveMap f.faceNerveMap z

/-- Helper for Theorem 62.1: a refinement choice pushes reduced degree-zero
face-nerve homology through the augmentation kernels of component chains. -/
noncomputable def RefinementMap.reducedNerveHomologyZeroMap
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f : RefinementMap U V) :
    LinearMap.ker
        (componentAugmentationModTwo (SSet.π₀ (CategoryTheory.nerve V.NerveFace))) →ₗ[ZMod 2]
      LinearMap.ker
        (componentAugmentationModTwo (SSet.π₀ (CategoryTheory.nerve U.NerveFace))) :=
  componentAugmentationKernelMapOfFunction (SSet.mapπ₀ f.faceNerveMap)

/-- Helper for Theorem 62.1: the reduced degree-zero face-nerve homology map is
independent of the chosen parent for each member of a refinement. -/
lemma RefinementMap.reducedNerveHomologyZeroMap_eq
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) :
    f.reducedNerveHomologyZeroMap = g.reducedNerveHomologyZeroMap := by
  -- Apply function-congruence of augmentation-kernel pushforward to component equality.
  apply componentAugmentationKernelMapOfFunction_congr
  intro z
  exact congrFun (f.faceNerveComponentMap_eq g) z

/-- Helper for Theorem 62.1: the identity refinement induces the identity on
reduced degree-zero face-nerve homology. -/
lemma RefinementMap.reducedNerveHomologyZeroMap_id
    {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) [DecidableEq U.Index] :
    (RefinementMap.id U).reducedNerveHomologyZeroMap = LinearMap.id := by
  -- Normalize the component function, then apply the kernel pushforward identity law.
  rw [reducedNerveHomologyZeroMap, RefinementMap.faceNerveComponentMap_id]
  exact componentAugmentationKernelMapOfFunction_id _

/-- Helper for Theorem 62.1: reduced degree-zero face-nerve homology maps
respect composition of refinement choices. -/
lemma RefinementMap.reducedNerveHomologyZeroMap_comp
    {X : Type u} [TopologicalSpace X]
    {U V W : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] [DecidableEq V.Index]
    (f : RefinementMap U V) (g : RefinementMap V W) :
    (f.comp g).reducedNerveHomologyZeroMap =
      f.reducedNerveHomologyZeroMap.comp g.reducedNerveHomologyZeroMap := by
  -- Normalize the component function, then apply the kernel pushforward composition law.
  rw [reducedNerveHomologyZeroMap, reducedNerveHomologyZeroMap,
    reducedNerveHomologyZeroMap, RefinementMap.faceNerveComponentMap_comp]
  exact componentAugmentationKernelMapOfFunction_comp _ _

/-- Helper for Theorem 62.1: reduced degree-zero cohomology of a finite-cover
face nerve is the linear dual of its component-augmentation kernel. -/
abbrev reducedNerveCohomologyZero {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) :=
  Module.Dual (ZMod 2)
    (LinearMap.ker
      (componentAugmentationModTwo (SSet.π₀ (CategoryTheory.nerve U.NerveFace))))

/-- Helper for Theorem 62.1: a chosen refinement induces the contravariant map
on reduced degree-zero cohomology of finite-cover face nerves. -/
noncomputable def RefinementMap.reducedNerveCohomologyZeroMap
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f : RefinementMap U V) :
    reducedNerveCohomologyZero U →ₗ[ZMod 2] reducedNerveCohomologyZero V :=
  f.reducedNerveHomologyZeroMap.dualMap

/-- Helper for Theorem 62.1: the reduced degree-zero cohomology map is
independent of the chosen parent map witnessing a cover refinement. -/
lemma RefinementMap.reducedNerveCohomologyZeroMap_eq
    {X : Type u} [TopologicalSpace X]
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) :
    f.reducedNerveCohomologyZeroMap = g.reducedNerveCohomologyZeroMap := by
  -- Dualization transports the already-proved choice independence on homology.
  exact congrArg LinearMap.dualMap (f.reducedNerveHomologyZeroMap_eq g)

/-- Helper for Theorem 62.1: the identity refinement induces the identity on
reduced degree-zero cohomology of a finite-cover face nerve. -/
lemma RefinementMap.reducedNerveCohomologyZeroMap_id
    {X : Type u} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{u, v} X) [DecidableEq U.Index] :
    (RefinementMap.id U).reducedNerveCohomologyZeroMap = LinearMap.id := by
  -- Normalize the homology map first, then use that dualization preserves identity.
  rw [reducedNerveCohomologyZeroMap, RefinementMap.reducedNerveHomologyZeroMap_id]
  exact LinearMap.dualMap_id

/-- Helper for Theorem 62.1: reduced degree-zero cohomology maps reverse the
composition of chosen cover refinements. -/
lemma RefinementMap.reducedNerveCohomologyZeroMap_comp
    {X : Type u} [TopologicalSpace X]
    {U V W : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] [DecidableEq V.Index]
    (f : RefinementMap U V) (g : RefinementMap V W) :
    (f.comp g).reducedNerveCohomologyZeroMap =
      g.reducedNerveCohomologyZeroMap.comp f.reducedNerveCohomologyZeroMap := by
  -- The homology composite dualizes to the reversed composite of dual maps.
  rw [reducedNerveCohomologyZeroMap, RefinementMap.reducedNerveHomologyZeroMap_comp]
  exact (LinearMap.dualMap_comp_dualMap g.reducedNerveHomologyZeroMap
    f.reducedNerveHomologyZeroMap).symm

end CechFiniteOpenCover

end InvarianceOfDomainSupport

end
