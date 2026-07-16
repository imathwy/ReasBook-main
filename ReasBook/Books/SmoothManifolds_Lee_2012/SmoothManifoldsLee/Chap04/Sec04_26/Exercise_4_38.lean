import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_26.Definition_4_26_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_22.Proposition_4_6
import Mathlib.Topology.Homeomorph.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

section

universe u𝕜 uι uVE uVM uHE uHM uE uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {ι : Type uι} [Fintype ι]
variable {VE : ι → Type uVE} [∀ i, NormedAddCommGroup (VE i)] [∀ i, NormedSpace 𝕜 (VE i)]
variable {VM : ι → Type uVM} [∀ i, NormedAddCommGroup (VM i)] [∀ i, NormedSpace 𝕜 (VM i)]
variable {HE : ι → Type uHE} [∀ i, TopologicalSpace (HE i)]
variable {HM : ι → Type uHM} [∀ i, TopologicalSpace (HM i)]
variable {E : ι → Type uE} [∀ i, TopologicalSpace (E i)] [∀ i, ChartedSpace (HE i) (E i)]
variable {M : ι → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (HM i) (M i)]
variable {IE : ∀ i, ModelWithCorners 𝕜 (VE i) (HE i)}
variable {IM : ∀ i, ModelWithCorners 𝕜 (VM i) (HM i)}
variable {π : ∀ i, E i → M i}

namespace Manifold.IsSmoothCoveringMap

/-- Helper for Exercise 4.38: the canonical map from a `Set.pi` subtype to the dependent product
of its coordinate subtypes is continuous. -/
theorem set_pi_homeomorph_continuous_toFun (s : ∀ i, Set (M i)) :
    Continuous (fun f : Set.pi Set.univ s ↦ fun i => (Equiv.Set.univPi s f) i) := by
  -- Each coordinate is just evaluation followed by the subtype projection.
  refine continuous_pi fun i ↦ ?_
  exact
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk fun f ↦ by
      have hf : ∀ j, (f : ∀ i, M i) j ∈ s j := Set.mem_univ_pi.mp f.2
      exact hf i

/-- Helper for Exercise 4.38: the inverse map from the dependent product of coordinate subtypes
back to the `Set.pi` subtype is continuous. -/
theorem set_pi_homeomorph_continuous_invFun (s : ∀ i, Set (M i)) :
    Continuous (fun f : (∀ i, s i) ↦ (Equiv.Set.univPi s).symm f) := by
  -- Reassembling a point of `Set.pi` from its coordinates is continuous coordinatewise.
  exact
    (continuous_pi fun i ↦ continuous_subtype_val.comp (continuous_apply i)).subtype_mk
      fun f i _ ↦ (f i).2

/-- Helper for Exercise 4.38: a product set `Set.pi Set.univ s` is homeomorphic to the dependent
product of its coordinate subtypes. -/
@[simps! apply symm_apply]
noncomputable def set_pi_homeomorph (s : ∀ i, Set (M i)) : (Set.pi Set.univ s) ≃ₜ ∀ i, s i :=
  { toEquiv := Equiv.Set.univPi s
    continuous_toFun := set_pi_homeomorph_continuous_toFun (s := s)
    continuous_invFun := set_pi_homeomorph_continuous_invFun (s := s) }

/-- Helper for Exercise 4.38: the coordinate projection map from a product of pairs to a pair of
products has a two-sided inverse. -/
theorem pi_prod_homeomorph_left_inv
    {A : ι → Type*} {B : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Function.LeftInverse
      (fun p : (∀ i, A i) × (∀ i, B i) ↦ fun i => (p.1 i, p.2 i))
      (fun f : ∀ i, A i × B i ↦ ((fun i => (f i).1), fun i => (f i).2)) := by
  -- Recovering the original family of pairs is coordinatewise tautological.
  intro f
  funext i
  simp [Prod.mk.eta]

/-- Helper for Exercise 4.38: the coordinate projection map from a product of pairs to a pair of
products is surjective with the evident inverse. -/
theorem pi_prod_homeomorph_right_inv
    {A : ι → Type*} {B : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Function.RightInverse
      (fun p : (∀ i, A i) × (∀ i, B i) ↦ fun i => (p.1 i, p.2 i))
      (fun f : ∀ i, A i × B i ↦ ((fun i => (f i).1), fun i => (f i).2)) := by
  -- Splitting and then recombining the two coordinate families is the identity.
  intro p
  cases p
  rfl

/-- Helper for Exercise 4.38: splitting a product of pairs into a pair of products is continuous. -/
theorem pi_prod_homeomorph_continuous_toFun
    {A : ι → Type*} {B : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Continuous (fun f : ∀ i, A i × B i ↦ ((fun i => (f i).1), fun i => (f i).2)) := by
  -- Both coordinate families are continuous by the continuity of evaluation and product
  -- projections.
  fun_prop

/-- Helper for Exercise 4.38: the inverse map from a pair of products to a product of pairs is
continuous. -/
theorem pi_prod_homeomorph_continuous_invFun
    {A : ι → Type*} {B : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Continuous (fun p : (∀ i, A i) × (∀ i, B i) ↦ fun i => (p.1 i, p.2 i)) := by
  -- Recombining the split coordinate families is continuous coordinatewise.
  fun_prop

/-- Helper for Exercise 4.38: a dependent product of coordinatewise products is homeomorphic to
the product of the two dependent products. -/
@[simps! apply symm_apply]
noncomputable def pi_prod_homeomorph
    (A : ι → Type*) (B : ι → Type*) [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    (∀ i, A i × B i) ≃ₜ (∀ i, A i) × (∀ i, B i) :=
  { toEquiv :=
      { toFun := fun f ↦ ((fun i => (f i).1), fun i => (f i).2)
        invFun := fun p i ↦ (p.1 i, p.2 i)
        left_inv := pi_prod_homeomorph_left_inv
        right_inv := pi_prod_homeomorph_right_inv }
    continuous_toFun := pi_prod_homeomorph_continuous_toFun
    continuous_invFun := pi_prod_homeomorph_continuous_invFun }

/-- Helper for Exercise 4.38: evenly covered neighborhoods multiply over finite products. -/
theorem isEvenlyCovered_pi {x : ∀ i, M i}
    (hx : ∀ i, IsEvenlyCovered (π i) (x i) ((π i) ⁻¹' {x i})) :
    IsEvenlyCovered (fun y : ∀ i, E i ↦ fun i ↦ π i (y i)) x
      (∀ i, (π i) ⁻¹' {x i}) := by
  classical
  have hx' :
      ∀ i, ∃ U : Set (M i), x i ∈ U ∧ IsOpen U ∧ IsOpen ((π i) ⁻¹' U) ∧
        ∃ H : (π i) ⁻¹' U ≃ₜ U × ((π i) ⁻¹' {x i}),
          ∀ y : (π i) ⁻¹' U, (H y).1.1 = π i y := fun i ↦ (hx i).2
  choose U hxU hU hpre H hH using hx'
  letI : ∀ i, DiscreteTopology ((π i) ⁻¹' {x i}) := fun i ↦ (hx i).1
  let g : (∀ i, E i) → ∀ i, M i := fun y i ↦ π i (y i)
  have hpreimage :
      g ⁻¹' Set.pi Set.univ U = Set.pi Set.univ (fun i ↦ (π i) ⁻¹' U i) := by
    -- Membership in the product neighborhood is equivalent to coordinatewise membership.
    ext y
    simp [g, Set.mem_pi]
  let Hpi :
      g ⁻¹' Set.pi Set.univ U ≃ₜ Set.pi Set.univ U × (∀ i, (π i) ⁻¹' {x i}) :=
    (Homeomorph.setCongr hpreimage).trans <|
      (set_pi_homeomorph fun i ↦ (π i) ⁻¹' U i).trans <|
        (Homeomorph.piCongrRight H).trans <|
          (pi_prod_homeomorph (fun i ↦ U i) fun i ↦ (π i) ⁻¹' {x i}).trans <|
            (set_pi_homeomorph U).symm.prodCongr
              (Homeomorph.refl (∀ i, (π i) ⁻¹' {x i}))
  refine ⟨inferInstance, Set.pi Set.univ U, ?_, ?_, ?_, Hpi, ?_⟩
  · -- Each component neighborhood contains the corresponding base point, so their product contains
    -- the full point `x`.
    intro i _
    exact hxU i
  · -- Finite products of open coordinate neighborhoods are open.
    simpa using isOpen_set_pi Set.finite_univ fun i _ ↦ hU i
  · -- The preimage is the product of the coordinate preimages, hence open as well.
    rw [hpreimage]
    simpa using isOpen_set_pi Set.finite_univ fun i _ ↦ hpre i
  · -- By construction, the first component of the product trivialization is exactly the product
    -- map `g`.
    intro y
    have hy :
        ((((Homeomorph.setCongr hpreimage) y : Set.pi Set.univ fun i ↦ (π i) ⁻¹' U i) :
          ∀ i, E i)) = y := rfl
    ext i
    simp [Hpi, g, hH, hy]

/-- Helper for Exercise 4.38: the coordinatewise product of covering maps is a covering map. -/
theorem isCoveringMap_pi (hcov : ∀ i, IsCoveringMap (π i)) :
    IsCoveringMap (fun y : ∀ i, E i ↦ fun i ↦ π i (y i)) := by
  -- Each fiber point has a product evenly covered neighborhood, and then we convert to the actual
  -- fiber expected by `IsCoveringMap`.
  intro x
  exact (isEvenlyCovered_pi (π := π) fun i ↦ hcov i (x i)).to_isEvenlyCovered_preimage

/-- Exercise 4.38: a finite product of smooth covering maps is again a smooth covering map. -/
-- Proof sketch: the pointwise product map is surjective because each `π i` is surjective, it is a
-- covering map because evenly covered neighborhoods and trivializations multiply over finite
-- products, and it is a smooth local diffeomorphism by `isLocalDiffeomorph_pi`.
theorem pi (hπ : ∀ i, IsSmoothCoveringMap (IE i) (IM i) (π i)) :
    IsSmoothCoveringMap (ModelWithCorners.pi IE) (ModelWithCorners.pi IM)
      (fun x : ∀ i, E i ↦ fun i ↦ π i (x i)) := by
  -- Package the three defining fields separately: covering-map structure, surjectivity, and local
  -- diffeomorphism.
  refine ⟨isCoveringMap_pi (π := π) fun i ↦ (hπ i).isCoveringMap, ?_, ?_⟩
  · -- Surjectivity is coordinatewise.
    simpa using Function.Surjective.piMap fun i ↦ (hπ i).surjective
  · -- The finite product of smooth local diffeomorphisms is a smooth local diffeomorphism.
    simpa using isLocalDiffeomorph_pi (f := π) fun i ↦ (hπ i).isLocalDiffeomorph

end Manifold.IsSmoothCoveringMap

end
