module

public import Topology_Munkres_2000.Book.Theorem_62_1.GraphHomology
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Topology.Connected.LocallyPathConnected

public section

namespace InvarianceOfDomainSupport

open CategoryTheory CategoryTheory.Limits

/-- Helper for Theorem 62.1: reduced mod-two singular homology in degree zero is the
kernel of the canonical augmentation. -/
noncomputable abbrev reducedHomologyZeroModTwo (X : TopCat) :=
  kernel (X.singularHomology₀ε (ModuleCat.of (ZMod 2) (ZMod 2)))

/-- Helper for Theorem 62.1: the mod-two component augmentation is injective exactly
when its indexing type has at most one element. -/
lemma componentAugmentationModTwo_injective_iff_subsingleton (i : Type*) :
    Function.Injective (componentAugmentationModTwo i) ↔ Subsingleton i := by
  constructor
  · intro h
    -- Equal augmentation values of the two unit chains force their indices to agree.
    refine ⟨fun x y ↦ Finsupp.single_left_injective (one_ne_zero : (1 : ZMod 2) ≠ 0) ?_⟩
    apply h
    simp only [componentAugmentationModTwo, Finsupp.lsum_single, LinearMap.id_apply]
  · intro h
    -- With a unique possible index, augmentation is evaluation at that index.
    letI : Subsingleton i := h
    intro x y hxy
    ext j
    have hsum (z : i →₀ ZMod 2) : componentAugmentationModTwo i z = z j := by
      classical
      rw [componentAugmentationModTwo, Finsupp.lsum_apply]
      exact Finsupp.sum_eq_single j (fun k _ hkj ↦ (hkj (Subsingleton.elim k j)).elim)
        fun _ ↦ LinearMap.map_zero _
    rw [← hsum x, ← hsum y, hxy]

/-- Helper for Theorem 62.1: a linear map has a subsingleton kernel exactly when it
is injective. -/
lemma subsingleton_ker_iff_injective {R M N : Type*} [Ring R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    Subsingleton (LinearMap.ker f) ↔ Function.Injective f := by
  -- A submodule is subsingleton exactly when it is bottom, and kernels detect injectivity.
  rw [Submodule.subsingleton_iff_eq_bot, LinearMap.ker_eq_bot]

/-- Helper for Theorem 62.1: in a locally path-connected space, preconnectedness is
equivalent to having at most one path component. -/
lemma preconnectedSpace_iff_subsingleton_zerothHomotopy (X : Type*) [TopologicalSpace X]
    [LocallyPathConnectedSpace X] :
    PreconnectedSpace X ↔ Subsingleton (ZerothHomotopy X) := by
  -- Locally path-connected spaces have the same connected and path components.
  rw [← (connectedComponentsEquivZerothHomotopy (X := X)).subsingleton_congr]
  constructor
  · intro h
    letI : PreconnectedSpace X := h
    exact inferInstance
  · intro h
    letI : Subsingleton (ConnectedComponents X) := h
    rw [preconnectedSpace_iff_connectedComponent]
    intro x
    apply Set.eq_univ_of_forall
    intro y
    exact ConnectedComponents.coe_eq_coe'.mp (h.elim ⟦y⟧ ⟦x⟧)

/-- Helper for Theorem 62.1: singular homology in degree zero is the finitely
supported mod-two module on path components. -/
noncomputable def singularHomologyZeroIsoFinsuppModTwo (X : TopCat) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat (ZMod 2)) 0).obj
        (ModuleCat.of (ZMod 2) (ZMod 2))).obj X ≅
      ModuleCat.of (ZMod 2) (ZerothHomotopy X →₀ ZMod 2) :=
  letI := Classical.decEq (ZerothHomotopy X)
  TopCat.singularHomology₀Iso X (ModuleCat.of (ZMod 2) (ZMod 2)) ≪≫
    ModuleCat.coprodIsoDirectSum
      (fun _ : ZerothHomotopy X ↦ ModuleCat.of (ZMod 2) (ZMod 2)) ≪≫
      (finsuppLEquivDirectSum (ZMod 2) (ZMod 2) (ZerothHomotopy X)).symm.toModuleIso

/-- Helper for Theorem 62.1: the coproduct-to-Finsupp identification carries the
coproduct fold to the mod-two coefficient sum. -/
lemma coprodIsoDirectSum_hom_comp_componentAugmentationModTwo
    (i : Type) [DecidableEq i] :
    (ModuleCat.coprodIsoDirectSum
        (fun _ : i ↦ ModuleCat.of (ZMod 2) (ZMod 2))).hom ≫
        (finsuppLEquivDirectSum (ZMod 2) (ZMod 2) i).symm.toModuleIso.hom ≫
          ModuleCat.ofHom (componentAugmentationModTwo i) =
      Sigma.desc (fun _ : i ↦ 𝟙 (ModuleCat.of (ZMod 2) (ZMod 2))) := by
  -- Compare the two maps on every coproduct generator.
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom, Sigma.ι_desc]
  ext
  simp [finsuppLEquivDirectSum_symm_lof, componentAugmentationModTwo]

/-- Helper for Theorem 62.1: the normalized singular-H₀ isomorphism intertwines
the canonical augmentation with summation of component coefficients. -/
lemma singularHomologyZeroIsoFinsuppModTwo_hom_comp_augmentation (X : TopCat) :
    (singularHomologyZeroIsoFinsuppModTwo X).hom ≫
        ModuleCat.ofHom (componentAugmentationModTwo (ZerothHomotopy X)) =
      X.singularHomology₀ε (ModuleCat.of (ZMod 2) (ZMod 2)) := by
  -- Normalize first to a coproduct, then identify the fold map with augmentation.
  classical
  rw [singularHomologyZeroIsoFinsuppModTwo, Iso.trans_hom, Iso.trans_hom]
  rw [Category.assoc, Category.assoc,
    coprodIsoDirectSum_hom_comp_componentAugmentationModTwo]
  rw [TopCat.singularHomology₀Iso_sigma_desc_id]

/-- Helper for Theorem 62.1: canonical reduced mod-two H₀ is linearly equivalent
to the kernel of augmentation on finitely supported path-component chains. -/
lemma nonempty_reducedHomologyZeroModTwo_linearEquiv_componentKernel (X : TopCat) :
    Nonempty
      (reducedHomologyZeroModTwo X ≃ₗ[ZMod 2]
        LinearMap.ker (componentAugmentationModTwo (ZerothHomotopy X))) := by
  -- Transport the categorical kernel across the normalized singular-H₀ isomorphism.
  let epsilon := X.singularHomology₀ε (ModuleCat.of (ZMod 2) (ZMod 2))
  let sigma := ModuleCat.ofHom (componentAugmentationModTwo (ZerothHomotopy X))
  have hcompat : epsilon ≫ (Iso.refl _).hom =
      (singularHomologyZeroIsoFinsuppModTwo X).hom ≫ sigma := by
    simpa [epsilon, sigma] using
      (singularHomologyZeroIsoFinsuppModTwo_hom_comp_augmentation X).symm
  exact
    ⟨(kernel.mapIso epsilon sigma (singularHomologyZeroIsoFinsuppModTwo X)
        (Iso.refl _) hcompat ≪≫ ModuleCat.kernelIsoKer sigma).toLinearEquiv⟩

/-- Helper for Theorem 62.1: a continuous map sends path components to path
components. -/
def zerothHomotopyMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (ZerothHomotopy.mk ∘ f)
    (fun _ _ p ↦ ZerothHomotopy.sound (p.map hf))

/-- Helper for Theorem 62.1: the path-component map of a continuous function is
computed on point representatives. -/
@[simp] lemma zerothHomotopyMap_mk {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) (x : X) :
    zerothHomotopyMap f hf (ZerothHomotopy.mk x) = ZerothHomotopy.mk (f x) := by
  -- Unfold the quotient lift at a point representative.
  rw [zerothHomotopyMap, ZerothHomotopy.lift_mk]
  rfl

/-- Helper for Theorem 62.1: a homeomorphism induces a bijection on path
components. -/
lemma zerothHomotopyMap_bijective_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Function.Bijective (zerothHomotopyMap e e.continuous) := by
  -- The map induced by the inverse is a two-sided inverse on quotient representatives.
  refine Function.bijective_iff_has_inverse.mpr ⟨zerothHomotopyMap e.symm e.symm.continuous,
    ?_, ?_⟩
  · intro q
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective q
    simp only [zerothHomotopyMap_mk, e.symm_apply_apply]
  · intro q
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective q
    simp only [zerothHomotopyMap_mk, e.apply_symm_apply]

/-- Helper for Theorem 62.1: a homeomorphism induces an equivalence on path
components. -/
noncomputable def zerothHomotopyEquivOfHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : ZerothHomotopy X ≃ ZerothHomotopy Y :=
  Equiv.ofBijective (zerothHomotopyMap e e.continuous)
    (zerothHomotopyMap_bijective_of_homeomorph e)

/-- Helper for Theorem 62.1: reduced mod-two singular H₀ is invariant under
homeomorphism. -/
lemma reducedHomologyZeroModTwoIsoOfHomeomorph {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Nonempty
      (reducedHomologyZeroModTwo (TopCat.of X) ≃ₗ[ZMod 2]
        reducedHomologyZeroModTwo (TopCat.of Y)) := by
  -- Normalize both reduced homology modules to component-augmentation kernels.
  obtain ⟨eX⟩ :=
    nonempty_reducedHomologyZeroModTwo_linearEquiv_componentKernel (TopCat.of X)
  obtain ⟨eY⟩ :=
    nonempty_reducedHomologyZeroModTwo_linearEquiv_componentKernel (TopCat.of Y)
  -- Reindex the middle kernel by the component equivalence induced by the homeomorphism.
  exact ⟨eX.trans
    ((componentAugmentationKernelLinearEquiv
      (zerothHomotopyEquivOfHomeomorph e)).trans eY.symm)⟩

/-- Helper for Theorem 62.1: for an open subset of a locally path-connected space,
preconnectedness is equivalent to vanishing reduced mod-two singular H₀. -/
lemma isPreconnected_iff_isZero_reducedHomologyZeroModTwo
    {X : Type} [TopologicalSpace X] [LocallyPathConnectedSpace X] (S : Set X)
    (hS : IsOpen S) :
    IsPreconnected S ↔
      IsZero (reducedHomologyZeroModTwo (TopCat.of S)) := by
  -- Openness supplies local path-connectedness on the subtype.
  letI : LocallyPathConnectedSpace S := hS.locallyPathConnectedSpace
  obtain ⟨e⟩ :=
    nonempty_reducedHomologyZeroModTwo_linearEquiv_componentKernel (TopCat.of S)
  calc
    IsPreconnected S ↔ PreconnectedSpace S := isPreconnected_iff_preconnectedSpace
    _ ↔ Subsingleton (ZerothHomotopy S) :=
      preconnectedSpace_iff_subsingleton_zerothHomotopy S
    _ ↔ Function.Injective
        (componentAugmentationModTwo (ZerothHomotopy S)) :=
      (componentAugmentationModTwo_injective_iff_subsingleton _).symm
    _ ↔ Subsingleton
        (LinearMap.ker (componentAugmentationModTwo (ZerothHomotopy S))) :=
      (subsingleton_ker_iff_injective _).symm
    _ ↔ Subsingleton (reducedHomologyZeroModTwo (TopCat.of S)) :=
      e.toEquiv.subsingleton_congr.symm
    _ ↔ IsZero (reducedHomologyZeroModTwo (TopCat.of S)) :=
      ModuleCat.isZero_iff_subsingleton.symm

end InvarianceOfDomainSupport

end
