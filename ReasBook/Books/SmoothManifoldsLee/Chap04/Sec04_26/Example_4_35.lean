import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Covering.Basic
import SmoothManifoldsLee.Chap01.Sec01.Example_1_5
import SmoothManifoldsLee.Chap01.Sec01_07.Problem_1_8
import SmoothManifoldsLee.Chap04.Sec04_22.Proposition_4_6

-- Declarations for this item will be appended below by the statement pipeline.

namespace Manifold

open scoped ContDiff

universe u𝕜 uE uE' uH uH' uM uM'

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {M' : Type uM'} [TopologicalSpace M'] [ChartedSpace H' M']

/-- Helper for Example 4.35: a smooth covering map is a covering map that is surjective and a
smooth local diffeomorphism. -/
def IsSmoothCoveringMap
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') (π : M → M') : Prop :=
  IsCoveringMap π ∧ Function.Surjective π ∧ IsLocalDiffeomorph I I' (∞ : ℕ∞ω) π

namespace IsSmoothCoveringMap

/-- Helper for Example 4.35: a smooth covering map is surjective. -/
theorem surjective
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsSmoothCoveringMap I I' π) : Function.Surjective π :=
  hπ.2.1

/-- Helper for Example 4.35: a smooth covering map is a covering map. -/
theorem isCoveringMap
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsSmoothCoveringMap I I' π) : IsCoveringMap π :=
  hπ.1

/-- Helper for Example 4.35: a smooth covering map is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsSmoothCoveringMap I I' π) : IsLocalDiffeomorph I I' (∞ : ℕ∞ω) π :=
  hπ.2.2

end IsSmoothCoveringMap
end Manifold

noncomputable section

open Projectivization
open scoped LinearAlgebra.Projectivization Manifold ContDiff

/-- Helper for Example 4.35: the `n`-torus is the finite product of `n` copies of the circle. -/
abbrev n_torus (n : ℕ) := Fin n → Circle

scoped[Torus] notation "𝕋^{" n:max "}" => n_torus n

open scoped Torus

/-- The coordinatewise exponential covering map from `ℝⁿ` to the `n`-torus. -/
def standardTorusCovering (n : ℕ) : EuclideanSpace ℝ (Fin n) → 𝕋^{n} :=
  fun x i ↦ Circle.exp (x i)

/-- The quotient map from the unit sphere to real projective space. -/
abbrev sphereToRealProjectiveSpace (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → RealProjectiveSpace n :=
  fun x ↦
    Projectivization.mk ℝ (x : EuclideanSpace ℝ (Fin (n + 1)))
      (Metric.ne_of_mem_sphere x.property one_ne_zero)

/-- Helper for Example 4.35: every projective point in `ℝPⁿ` is represented by a unit vector on
the sphere `Sⁿ`. -/
theorem sphereToRealProjectiveSpace_surjective (n : ℕ) :
    Function.Surjective (sphereToRealProjectiveSpace n) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  intro x
  -- Normalize the canonical representative `x.rep` to unit length.
  have hx_norm_ne : ‖(x.rep : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.rep_nonzero
  refine ⟨⟨‖(x.rep : E)‖⁻¹ • x.rep, by
    simpa [mem_sphere_zero_iff_norm] using
      calc
        ‖‖(x.rep : E)‖⁻¹ • x.rep‖ = ‖‖(x.rep : E)‖⁻¹‖ * ‖(x.rep : E)‖ := norm_smul _ _
        _ = ‖(x.rep : E)‖⁻¹ * ‖(x.rep : E)‖ := by rw [norm_inv, norm_norm]
        _ = 1 := inv_mul_cancel₀ hx_norm_ne⟩, ?_⟩
  -- Projectivization does not change when we rescale by a nonzero scalar.
  change
    Projectivization.mk ℝ (‖(x.rep : E)‖⁻¹ • x.rep)
      (smul_ne_zero (inv_ne_zero hx_norm_ne) x.rep_nonzero) = x
  have hmk :
      Projectivization.mk ℝ (‖(x.rep : E)‖⁻¹ • x.rep)
        (smul_ne_zero (inv_ne_zero hx_norm_ne) x.rep_nonzero) =
        Projectivization.mk ℝ x.rep x.rep_nonzero := by
    exact (Projectivization.mk_eq_mk_iff' ℝ _ _ (smul_ne_zero (inv_ne_zero hx_norm_ne)
      x.rep_nonzero) x.rep_nonzero).2 ⟨‖(x.rep : E)‖⁻¹, rfl⟩
  simpa [x.mk_rep] using hmk

/-- Helper for Example 4.35: two unit vectors define the same projective point exactly when they
are equal or antipodal. -/
theorem same_projective_point_on_unit_sphere_iff_eq_or_eq_neg (n : ℕ)
    (y z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    sphereToRealProjectiveSpace n y = sphereToRealProjectiveSpace n z ↔ z = y ∨ z = -y := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  have hy_ne : (y : E) ≠ 0 := Metric.ne_of_mem_sphere y.property one_ne_zero
  have hz_ne : (z : E) ≠ 0 := Metric.ne_of_mem_sphere z.property one_ne_zero
  have hy_norm : ‖(y : E)‖ = 1 := by
    exact mem_sphere_zero_iff_norm.mp y.property
  have hz_norm : ‖(z : E)‖ = 1 := by
    exact mem_sphere_zero_iff_norm.mp z.property
  constructor
  · intro h
    -- Equal projective classes differ by a scalar; unit-norm forces that scalar to be `±1`.
    change Projectivization.mk ℝ (y : E) hy_ne = Projectivization.mk ℝ (z : E) hz_ne at h
    rw [Projectivization.mk_eq_mk_iff' ℝ _ _ hy_ne hz_ne] at h
    rcases h with ⟨a, ha⟩
    have ha_abs : |a| = 1 := by
      calc
        |a| = |a| * 1 := by ring
        _ = |a| * ‖(z : E)‖ := by rw [hz_norm]
        _ = ‖a • (z : E)‖ := by
          symm
          exact norm_smul a (z : E)
        _ = ‖(y : E)‖ := by simp [ha]
        _ = 1 := hy_norm
    have ha_sq : a ^ 2 = 1 := by
      have hsq : a ^ 2 = |a| ^ 2 := by
        exact (sq_abs a).symm
      rw [ha_abs] at hsq
      simpa using hsq
    rcases sq_eq_one_iff.mp ha_sq with ha_one | ha_neg
    · left
      apply Subtype.ext
      simpa [ha_one] using ha
    · right
      apply Subtype.ext
      have hneg : -((z : E)) = (y : E) := by
        simpa [ha_neg] using ha
      simpa using congrArg Neg.neg hneg
  · intro h
    rcases h with rfl | hz
    · rfl
    · rw [hz]
      -- The antipodal pair differs by the nonzero scalar `-1`, so the projective classes agree.
      change
        Projectivization.mk ℝ (y : E) hy_ne =
          Projectivization.mk ℝ ((-y : Metric.sphere (0 : E) 1) : E)
            (Metric.ne_of_mem_sphere (-y).property one_ne_zero)
      exact (Projectivization.mk_eq_mk_iff' ℝ _ _ hy_ne
        (Metric.ne_of_mem_sphere (-y).property one_ne_zero)).2 ⟨(-1 : ℝ), by simp⟩

/-- Helper for Example 4.35: a point on the unit sphere in `ℝ^(n+1)` is nonzero. -/
theorem unit_sphere_point_ne_zero (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ((x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0) := by
  -- The radius-one sphere omits the origin.
  exact Metric.ne_of_mem_sphere x.property one_ne_zero

/-- Helper for Example 4.35: shifting an angle function by an integer multiple of `2π` preserves
the angle-function identities. -/
theorem IsAngleFunction.sub_int_mul_two_pi {U : TopologicalSpace.Opens Circle} {θ : U → ℝ}
    (hθ : IsAngleFunction θ) (m : ℤ) :
    IsAngleFunction (fun z ↦ θ z - m * (2 * Real.pi)) := by
  constructor
  · -- Subtracting a constant keeps the branch continuous.
    exact hθ.1.sub continuous_const
  · intro z
    -- Exponentiating changes by an integral multiple of `2π`, hence leaves the circle point fixed.
    calc
      Circle.exp (θ z - m * (2 * Real.pi))
          = Circle.exp (θ z) / Circle.exp (m * (2 * Real.pi)) := by
            rw [Circle.exp_sub]
      _ = Circle.exp (θ z) / 1 := by
            rw [Circle.exp_int_mul_two_pi]
      _ = Circle.exp (θ z) := by simp
      _ = z := hθ.2 z

/-- Helper for Example 4.35: around `Circle.exp x`, one can choose an angle branch whose value at
that point is exactly `x`. -/
theorem exists_angleFunction_through_exp (x : ℝ) :
    ∃ (U : TopologicalSpace.Opens Circle) (hxU : Circle.exp x ∈ U) (θ : U → ℝ),
      IsAngleFunction θ ∧ θ ⟨Circle.exp x, hxU⟩ = x := by
  let U : TopologicalSpace.Opens Circle :=
    ⟨{z : Circle | z ≠ -Circle.exp x}, isOpen_compl_singleton⟩
  have hxU : Circle.exp x ∈ U := by
    -- The antipode of a circle point is never the point itself.
    change Circle.exp x ≠ -Circle.exp x
    simpa [eq_comm] using Circle.neg_ne_self (Circle.exp x)
  have hmissing : -Circle.exp x ∉ U := by
    -- The deleted antipode is the unique point excluded from the open set.
    simp [U]
  rcases exists_angleFunction_of_missing_point (U := U) (c := -Circle.exp x) hmissing with
    ⟨θ₀, hθ₀⟩
  let z₀ : U := ⟨Circle.exp x, hxU⟩
  have hθ₀x : Circle.exp (θ₀ z₀) = Circle.exp x := by
    simpa using hθ₀.2 z₀
  rcases Circle.exp_eq_exp.mp hθ₀x with ⟨m, hm⟩
  let θ : U → ℝ := fun z ↦ θ₀ z - m * (2 * Real.pi)
  have hθ : IsAngleFunction θ := hθ₀.sub_int_mul_two_pi m
  refine ⟨U, hxU, θ, hθ, ?_⟩
  -- The chosen shift forces the branch to take the prescribed value `x` at `Circle.exp x`.
  have hshift : θ₀ z₀ - m * (2 * Real.pi) = x := by
    linarith
  simpa [θ] using hshift

/-- Helper for Example 4.35: extend an angle branch by `0` outside its domain so that it can be
used as the inverse function of a partial diffeomorphism on the ambient circle. -/
noncomputable def angleFunction_extension {U : TopologicalSpace.Opens Circle} (θ : U → ℝ) :
    Circle → ℝ :=
  let _ : DecidablePred fun z : Circle ↦ z ∈ U := Classical.decPred _
  fun z ↦ if hz : z ∈ U then θ ⟨z, hz⟩ else 0

/-- Helper for Example 4.35: an angle branch determines a partial diffeomorphism whose forward map
is `Circle.exp` on the branch image and whose inverse map is the chosen branch. -/
noncomputable def angleFunction_partialDiffeomorph {U : TopologicalSpace.Opens Circle}
    {θ : U → ℝ} (hθ : IsAngleFunction θ) :
    PartialDiffeomorph (𝓘(ℝ)) (𝓡 1) ℝ Circle (∞ : ℕ∞ω) where
  toPartialEquiv :=
    { toFun := Circle.exp
      invFun := angleFunction_extension θ
      source := hθ.openImage
      target := U
      map_source' := fun {y} hy ↦ hθ.mapsTo_circleExp_openImage hy
      map_target' := by
        intro z hz
        -- On the target, the ambient extension reduces to the original angle branch.
        by_cases h : z ∈ U
        · refine ⟨⟨z, h⟩, ?_⟩
          simp [angleFunction_extension, h]
        · exact (h hz).elim
      left_inv' := by
        intro y hy
        -- On the open image, the chosen branch is a left inverse to `Circle.exp`.
        have hyU : Circle.exp y ∈ U := hθ.mapsTo_circleExp_openImage hy
        have hbranch :=
          congrArg (fun f : hθ.openImage → ℝ ↦ f ⟨y, hy⟩) hθ.theta_comp_circleExpOpenImage
        simpa [Function.comp, angleFunction_extension, IsAngleFunction.circleExpOpenImage, hyU]
          using hbranch
      right_inv' := by
        intro z hz
        -- On the target open set, the branch evaluates to a genuine angle for `z`.
        by_cases h : z ∈ U
        · simpa [angleFunction_extension, h] using hθ.2 ⟨z, h⟩
        · exact (h hz).elim }
  open_source := hθ.openImage.2
  open_target := U.2
  contMDiffOn_toFun := by
    -- The forward map is the ambient smooth circle exponential restricted to the branch image.
    simpa using (contMDiff_circleExp).contMDiffOn
  contMDiffOn_invFun := by
    intro z hz
    -- Near a target point, the piecewise inverse agrees with the smooth branch `θ`.
    have hθz :
        ContMDiffAt (I := 𝓡 1) (I' := 𝓘(ℝ)) (n := (∞ : ℕ∞ω))
          (angleFunction_extension θ) z := by
      rw [← contMDiffAt_subtype_iff
        (U := U)
        (f := angleFunction_extension θ)
        (x := ⟨z, hz⟩)]
      simpa [angleFunction_extension] using hθ.contMDiff ⟨z, hz⟩
    exact hθz.contMDiffWithinAt

/-- Helper for Example 4.35: the standard exponential map `Circle.exp` is a smooth local
diffeomorphism, obtained by packaging a local angle branch as a partial diffeomorphism. -/
theorem circle_exp_isLocalDiffeomorph_from_angle_branch :
    IsLocalDiffeomorph (𝓘(ℝ)) (𝓡 1) (∞ : ℕ∞ω) Circle.exp := by
  intro x
  obtain ⟨U, hxU, θ, hθ, hθx⟩ := exists_angleFunction_through_exp x
  -- The normalized angle branch through `Circle.exp x` gives the local inverse data at `x`.
  refine ⟨angleFunction_partialDiffeomorph hθ, ?_, ?_⟩
  · change x ∈ hθ.openImage
    exact ⟨⟨Circle.exp x, hxU⟩, hθx⟩
  · intro y _hy
    rfl

namespace Manifold.IsSmoothCoveringMap

/-- Helper for Example 4.35: the canonical map from a `Set.pi` subtype to the dependent product of
its coordinate subtypes is continuous. -/
theorem set_pi_homeomorph_continuous_toFun
    {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
    (s : ∀ i, Set (M i)) :
    Continuous (fun f : Set.pi Set.univ s ↦ fun i => (Equiv.Set.univPi s f) i) := by
  -- Each coordinate is evaluation followed by the corresponding subtype projection.
  refine continuous_pi fun i ↦ ?_
  exact
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk fun f ↦ by
      have hf : ∀ j, (f : ∀ i, M i) j ∈ s j := Set.mem_univ_pi.mp f.2
      exact hf i

/-- Helper for Example 4.35: the inverse map from the dependent product of coordinate subtypes back
to the `Set.pi` subtype is continuous. -/
theorem set_pi_homeomorph_continuous_invFun
    {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
    (s : ∀ i, Set (M i)) :
    Continuous (fun f : (∀ i, s i) ↦ (Equiv.Set.univPi s).symm f) := by
  -- Reassembling the product point is continuous coordinatewise.
  exact
    (continuous_pi fun i ↦ continuous_subtype_val.comp (continuous_apply i)).subtype_mk
      fun f i _ ↦ (f i).2

/-- Helper for Example 4.35: a product set `Set.pi Set.univ s` is homeomorphic to the dependent
product of its coordinate subtypes. -/
@[simps! apply symm_apply]
noncomputable def set_pi_homeomorph
    {ι : Type*} [Fintype ι] {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
    (s : ∀ i, Set (M i)) : (Set.pi Set.univ s) ≃ₜ ∀ i, s i :=
  { toEquiv := Equiv.Set.univPi s
    continuous_toFun := set_pi_homeomorph_continuous_toFun s
    continuous_invFun := set_pi_homeomorph_continuous_invFun s }

/-- Helper for Example 4.35: splitting a product of coordinatewise pairs into a pair of products
has the evident left inverse. -/
theorem pi_prod_homeomorph_left_inv
    {ι : Type*} {A : ι → Type*} {B : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Function.LeftInverse
      (fun p : (∀ i, A i) × (∀ i, B i) ↦ fun i => (p.1 i, p.2 i))
      (fun f : ∀ i, A i × B i ↦ ((fun i => (f i).1), fun i => (f i).2)) := by
  -- Coordinatewise splitting and recombination is tautological.
  intro f
  funext i
  simp [Prod.mk.eta]

/-- Helper for Example 4.35: the inverse recombination map for products of pairs is a right
inverse. -/
theorem pi_prod_homeomorph_right_inv
    {ι : Type*} {A : ι → Type*} {B : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Function.RightInverse
      (fun p : (∀ i, A i) × (∀ i, B i) ↦ fun i => (p.1 i, p.2 i))
      (fun f : ∀ i, A i × B i ↦ ((fun i => (f i).1), fun i => (f i).2)) := by
  -- Splitting and then recombining yields the original pair of products.
  intro p
  cases p
  rfl

/-- Helper for Example 4.35: splitting a dependent product of pairs is continuous. -/
theorem pi_prod_homeomorph_continuous_toFun
    {ι : Type*} {A : ι → Type*} {B : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Continuous (fun f : ∀ i, A i × B i ↦ ((fun i => (f i).1), fun i => (f i).2)) := by
  -- Both coordinate families are continuous by the continuity of evaluation and projections.
  fun_prop

/-- Helper for Example 4.35: recombining a pair of dependent products into a product of pairs is
continuous. -/
theorem pi_prod_homeomorph_continuous_invFun
    {ι : Type*} {A : ι → Type*} {B : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Continuous (fun p : (∀ i, A i) × (∀ i, B i) ↦ fun i => (p.1 i, p.2 i)) := by
  -- Recombination is continuous coordinatewise.
  fun_prop

/-- Helper for Example 4.35: a dependent product of coordinatewise products is homeomorphic to the
product of the two dependent products. -/
@[simps! apply symm_apply]
noncomputable def pi_prod_homeomorph
    {ι : Type*} [Fintype ι] (A : ι → Type*) (B : ι → Type*)
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    (∀ i, A i × B i) ≃ₜ (∀ i, A i) × (∀ i, B i) :=
  { toEquiv :=
      { toFun := fun f ↦ ((fun i => (f i).1), fun i => (f i).2)
        invFun := fun p i ↦ (p.1 i, p.2 i)
        left_inv := pi_prod_homeomorph_left_inv
        right_inv := pi_prod_homeomorph_right_inv }
    continuous_toFun := pi_prod_homeomorph_continuous_toFun
    continuous_invFun := pi_prod_homeomorph_continuous_invFun }

/-- Helper for Example 4.35: evenly covered neighborhoods multiply over finite products. -/
theorem isEvenlyCovered_pi
    {ι : Type*} [Finite ι]
    {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
    {π : ∀ i, E i → M i} {x : ∀ i, M i}
    (hx : ∀ i, IsEvenlyCovered (π i) (x i) ((π i) ⁻¹' {x i})) :
    IsEvenlyCovered (fun y : ∀ i, E i ↦ fun i ↦ π i (y i)) x
      (∀ i, (π i) ⁻¹' {x i}) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
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
  · -- Each coordinate neighborhood contains the chosen point.
    intro i _
    exact hxU i
  · -- Finite products of open coordinate neighborhoods are open.
    simpa using isOpen_set_pi Set.finite_univ fun i _ ↦ hU i
  · -- The preimage is the corresponding product of open preimages.
    rw [hpreimage]
    simpa using isOpen_set_pi Set.finite_univ fun i _ ↦ hpre i
  · -- The first projection of the trivialization is the coordinatewise product map.
    intro y
    have hy :
        ((((Homeomorph.setCongr hpreimage) y : Set.pi Set.univ fun i ↦ (π i) ⁻¹' U i) :
          ∀ i, E i)) = y := rfl
    ext i
    simp [Hpi, g, hH, hy]

/-- Helper for Example 4.35: the coordinatewise product of covering maps is a covering map. -/
theorem isCoveringMap_pi
    {ι : Type*} [Finite ι]
    {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
    {π : ∀ i, E i → M i}
    (hcov : ∀ i, IsCoveringMap (π i)) :
    IsCoveringMap (fun y : ∀ i, E i ↦ fun i ↦ π i (y i)) := by
  -- Multiply evenly covered neighborhoods coordinatewise and then identify the resulting fiber.
  intro x
  exact (isEvenlyCovered_pi fun i ↦ hcov i (x i)).to_isEvenlyCovered_preimage

end Manifold.IsSmoothCoveringMap

/-- Helper for Example 4.35: the sphere-to-projective quotient map is continuous. -/
theorem sphereToRealProjectiveSpace_continuous (n : ℕ) :
    Continuous (sphereToRealProjectiveSpace n) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let liftToNonzero :
      Metric.sphere (0 : E) 1 → {v : E // v ≠ 0} := fun x ↦
        ⟨(x : E), unit_sphere_point_ne_zero n x⟩
  have hlift : Continuous liftToNonzero := by
    -- Forgetting from the sphere to the punctured ambient space is continuous.
    exact continuous_subtype_val.subtype_mk fun x ↦ unit_sphere_point_ne_zero n x
  have hmk :
      Continuous
        (Projectivization.mk' ℝ :
          {v : E // v ≠ 0} → RealProjectiveSpace n) := by
    -- The projectivization quotient map is continuous by construction.
    simpa [Projectivization.mk'] using
      (continuous_quotient_mk' :
        Continuous
          (@Quotient.mk'
            {v : E // v ≠ 0}
            (projectivizationSetoid ℝ E)))
  have hcomp :
      sphereToRealProjectiveSpace n = (Projectivization.mk' ℝ) ∘ liftToNonzero := by
    -- Both descriptions send a sphere point to its projective class.
    funext x
    simp [sphereToRealProjectiveSpace, liftToNonzero, Projectivization.mk'_eq_mk]
  rw [hcomp]
  exact hmk.comp hlift

/-- Helper for Example 4.35: on the unit sphere, belonging to the `i`th standard projective chart
domain is exactly the nonvanishing of the `i`th coordinate. -/
theorem sphereToRealProjectiveSpace_mem_realProjectiveChartDomain_iff (n : ℕ)
    (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i : Fin (n + 1)) :
    sphereToRealProjectiveSpace n y ∈ realProjectiveChartDomain n i ↔
      ((y : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0) := by
  -- Rewrite chart membership on the projectivized sphere point using the standard chart-domain API.
  change
    Projectivization.mk ℝ (y : EuclideanSpace ℝ (Fin (n + 1)))
        (unit_sphere_point_ne_zero n y) ∈ realProjectiveChartDomain n i ↔
      ((y : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0)
  exact realProjectiveChartDomain_mk n i
    (y : EuclideanSpace ℝ (Fin (n + 1)))
    (unit_sphere_point_ne_zero n y)

/-- Helper for Example 4.35: the `i`th affine chart chooses a canonical nonzero homogeneous
representative before normalization to the sphere. -/
def sphereToRealProjectiveSpace_chart_lift_vector (n : ℕ) (i : Fin (n + 1))
    (x : realProjectiveChartDomain n i) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  realProjectiveChartInvVector n i (realProjectiveChart n i x)

/-- Helper for Example 4.35: the canonical chart-side homogeneous representative is nonzero. -/
theorem sphereToRealProjectiveSpace_chart_lift_vector_ne_zero (n : ℕ) (i : Fin (n + 1))
    (x : realProjectiveChartDomain n i) :
    sphereToRealProjectiveSpace_chart_lift_vector n i x ≠ 0 := by
  -- The standard inverse chart inserts the distinguished coordinate `1`.
  simpa [sphereToRealProjectiveSpace_chart_lift_vector] using
    realProjectiveChartInvVector_ne_zero n i (realProjectiveChart n i x)

/-- Helper for Example 4.35: normalize the canonical chart representative to obtain a unit vector
lying over the given projective point. -/
def sphereToRealProjectiveSpace_chart_unit_lift (n : ℕ) (i : Fin (n + 1))
    (x : realProjectiveChartDomain n i) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  let v := sphereToRealProjectiveSpace_chart_lift_vector n i x
  let hv : v ≠ 0 := sphereToRealProjectiveSpace_chart_lift_vector_ne_zero n i x
  let hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  ⟨‖v‖⁻¹ • v, by
    -- Normalizing a nonzero vector produces a point on the radius-one sphere.
    simpa [mem_sphere_zero_iff_norm] using
      calc
        ‖‖v‖⁻¹ • v‖ = ‖‖v‖⁻¹‖ * ‖v‖ := norm_smul _ _
        _ = ‖v‖⁻¹ * ‖v‖ := by rw [norm_inv, norm_norm]
        _ = 1 := inv_mul_cancel₀ hvnorm⟩

/-- Helper for Example 4.35: the affine-chart homogeneous lift varies continuously on the chart
domain. -/
theorem sphereToRealProjectiveSpace_chart_lift_vector_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (sphereToRealProjectiveSpace_chart_lift_vector n i) := by
  have hchart :
      Continuous fun x : realProjectiveChartDomain n i ↦ realProjectiveChart n i x := by
    -- Restrict the standard projective chart to its source subtype.
    simpa [continuousOn_iff_continuous_restrict] using
      (realProjectiveChart n i).continuousOn_toFun
  have hOfLp :
      Continuous (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) :=
    PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin n ↦ ℝ)
  have hToLp :
      Continuous
        (WithLp.toLp (p := (2 : ENNReal)) :
          (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))) :=
    PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin (n + 1) ↦ ℝ)
  have hinsert :
      Continuous fun u : EuclideanSpace ℝ (Fin n) ↦
        i.insertNth (α := fun _ : Fin (n + 1) ↦ ℝ) (1 : ℝ) (fun j ↦ u j) := by
    -- The inverse chart inserts the constant coordinate `1` into the affine vector.
    simpa using
      (continuous_const.finInsertNth i hOfLp)
  have hInv : Continuous (realProjectiveChartInvVector n i) := by
    -- Converting the inserted coordinate function back to Euclidean space is continuous.
    simpa [realProjectiveChartInvVector] using hToLp.comp hinsert
  exact hInv.comp hchart

/-- Helper for Example 4.35: the normalized positive chart lift is continuous on each standard
chart domain. -/
theorem sphereToRealProjectiveSpace_chart_unit_lift_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (sphereToRealProjectiveSpace_chart_unit_lift n i) := by
  have hscale : Continuous fun x : realProjectiveChartDomain n i ↦
      ‖sphereToRealProjectiveSpace_chart_lift_vector n i x‖⁻¹ := by
    -- The norm of the chart representative never vanishes, so inversion is continuous.
    refine (sphereToRealProjectiveSpace_chart_lift_vector_continuous n i).norm.inv₀ ?_
    intro x
    exact norm_ne_zero_iff.mpr (sphereToRealProjectiveSpace_chart_lift_vector_ne_zero n i x)
  -- Package the continuous normalized ambient vector into the sphere subtype.
  refine Continuous.subtype_mk ?_ (fun x ↦ (sphereToRealProjectiveSpace_chart_unit_lift n i x).2)
  simpa [sphereToRealProjectiveSpace_chart_unit_lift] using
    hscale.smul (sphereToRealProjectiveSpace_chart_lift_vector_continuous n i)

/-- Helper for Example 4.35: the normalized chart lift has positive `i`th coordinate. -/
theorem sphereToRealProjectiveSpace_chart_unit_lift_apply_self (n : ℕ) (i : Fin (n + 1))
    (x : realProjectiveChartDomain n i) :
    ((sphereToRealProjectiveSpace_chart_unit_lift n i x :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
      EuclideanSpace ℝ (Fin (n + 1))) i =
      ‖sphereToRealProjectiveSpace_chart_lift_vector n i x‖⁻¹ := by
  -- The distinguished coordinate stays equal to `1` before normalization.
  change
    ‖sphereToRealProjectiveSpace_chart_lift_vector n i x‖⁻¹ *
        (sphereToRealProjectiveSpace_chart_lift_vector n i x).ofLp i =
      ‖sphereToRealProjectiveSpace_chart_lift_vector n i x‖⁻¹
  have hi :
      (sphereToRealProjectiveSpace_chart_lift_vector n i x).ofLp i = 1 := by
    simp [sphereToRealProjectiveSpace_chart_lift_vector, realProjectiveChartInvVector]
  rw [hi, mul_one]

/-- Helper for Example 4.35: the normalized chart lift lies on the positive sheet over the
`i`th chart. -/
theorem sphereToRealProjectiveSpace_chart_unit_lift_apply_self_pos (n : ℕ) (i : Fin (n + 1))
    (x : realProjectiveChartDomain n i) :
    0 < ((sphereToRealProjectiveSpace_chart_unit_lift n i x :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
      EuclideanSpace ℝ (Fin (n + 1))) i := by
  -- The `i`th coordinate is `1 / ‖v‖`, hence positive because the chart representative is nonzero.
  rw [sphereToRealProjectiveSpace_chart_unit_lift_apply_self]
  exact inv_pos.mpr <|
    norm_pos_iff.mpr (sphereToRealProjectiveSpace_chart_lift_vector_ne_zero n i x)

/-- Helper for Example 4.35: normalizing the standard chart representative does not change the
projective point. -/
theorem sphereToRealProjectiveSpace_chart_unit_lift_proj (n : ℕ) (i : Fin (n + 1))
    (x : realProjectiveChartDomain n i) :
    sphereToRealProjectiveSpace n (sphereToRealProjectiveSpace_chart_unit_lift n i x) = x := by
  let v := sphereToRealProjectiveSpace_chart_lift_vector n i x
  have hv : v ≠ 0 := sphereToRealProjectiveSpace_chart_lift_vector_ne_zero n i x
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  -- Compare the normalized representative with the standard inverse chart representative.
  change Projectivization.mk ℝ (‖v‖⁻¹ • v) (smul_ne_zero (inv_ne_zero hvnorm) hv) = x
  rw [← (realProjectiveChart n i).left_inv x.2, realProjectiveChart_symm_apply]
  change
    Projectivization.mk ℝ (‖v‖⁻¹ • v) (smul_ne_zero (inv_ne_zero hvnorm) hv) =
      Projectivization.mk ℝ v hv
  exact (Projectivization.mk_eq_mk_iff' ℝ _ _ (smul_ne_zero (inv_ne_zero hvnorm) hv) hv).2
    ⟨‖v‖⁻¹, rfl⟩

/-- Helper for Example 4.35: the antipodal normalized chart lift represents the same projective
point. -/
theorem sphereToRealProjectiveSpace_neg_chart_unit_lift_proj (n : ℕ) (i : Fin (n + 1))
    (x : realProjectiveChartDomain n i) :
    sphereToRealProjectiveSpace n (-sphereToRealProjectiveSpace_chart_unit_lift n i x) = x := by
  -- Antipodal unit vectors project to the same point in real projective space.
  have hsame :
      sphereToRealProjectiveSpace n (sphereToRealProjectiveSpace_chart_unit_lift n i x) =
        sphereToRealProjectiveSpace n (-sphereToRealProjectiveSpace_chart_unit_lift n i x) := by
    exact (same_projective_point_on_unit_sphere_iff_eq_or_eq_neg n
      (sphereToRealProjectiveSpace_chart_unit_lift n i x)
      (-sphereToRealProjectiveSpace_chart_unit_lift n i x)).mpr (Or.inr rfl)
  exact hsame.symm.trans (sphereToRealProjectiveSpace_chart_unit_lift_proj n i x)

/-- Helper for Example 4.35: over one projective chart, the sphere splits into the positive and
negative sheets determined by the `i`th coordinate. -/
def sphereToRealProjectiveSpace_signed_sheet (n : ℕ) (i : Fin (n + 1)) (σ : Fin 2) :
    Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  if σ = 0 then
    {y | 0 < ((y : EuclideanSpace ℝ (Fin (n + 1))) i)}
  else
    {y | ((y : EuclideanSpace ℝ (Fin (n + 1))) i) < 0}

/-- Helper for Example 4.35: each ambient coordinate function is continuous on the unit sphere. -/
theorem unit_sphere_coordinate_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous fun y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      ((y : EuclideanSpace ℝ (Fin (n + 1))) i) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  have hOfLp : Continuous (WithLp.ofLp : E → (Fin (n + 1) → ℝ)) :=
    PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin (n + 1) ↦ ℝ)
  -- A sphere coordinate is evaluation after forgetting the subtype and the `PiLp` wrapper.
  exact ((continuous_apply i).comp hOfLp).comp continuous_subtype_val

/-- Helper for Example 4.35: each signed sheet is open in the sphere. -/
theorem sphereToRealProjectiveSpace_signed_sheet_isOpen (n : ℕ) (i : Fin (n + 1))
    (σ : Fin 2) :
    IsOpen (sphereToRealProjectiveSpace_signed_sheet n i σ) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  have hcoord : Continuous fun y : Metric.sphere (0 : E) 1 ↦ ((y : E) i) :=
    unit_sphere_coordinate_continuous n i
  fin_cases σ
  · -- The positive sheet is the preimage of the open ray `(0, ∞)`.
    simpa [sphereToRealProjectiveSpace_signed_sheet] using
      hcoord.isOpen_preimage {t : ℝ | 0 < t} isOpen_Ioi
  · -- The negative sheet is the preimage of the open ray `(-∞, 0)`.
    simpa [sphereToRealProjectiveSpace_signed_sheet] using
      hcoord.isOpen_preimage {t : ℝ | t < 0} isOpen_Iio

/-- Helper for Example 4.35: on a fixed chart, choose the positive normalized lift for the first
sheet and its antipode for the second sheet. -/
def sphereToRealProjectiveSpace_signed_lift (n : ℕ) (i : Fin (n + 1)) (σ : Fin 2)
    (x : realProjectiveChartDomain n i) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  if σ = 0 then
    sphereToRealProjectiveSpace_chart_unit_lift n i x
  else
    -sphereToRealProjectiveSpace_chart_unit_lift n i x

/-- Helper for Example 4.35: every signed sheet lies over the corresponding projective chart
domain. -/
theorem sphereToRealProjectiveSpace_signed_sheet_subset_preimage_chartDomain (n : ℕ)
    (i : Fin (n + 1)) (σ : Fin 2) :
    sphereToRealProjectiveSpace_signed_sheet n i σ ⊆
      sphereToRealProjectiveSpace n ⁻¹' realProjectiveChartDomain n i := by
  intro y hy
  fin_cases σ
  · -- Positive `i`th coordinate implies membership in the chart domain.
    have hy' : 0 < ((y : EuclideanSpace ℝ (Fin (n + 1))) i) := by
      simpa [sphereToRealProjectiveSpace_signed_sheet] using hy
    exact (sphereToRealProjectiveSpace_mem_realProjectiveChartDomain_iff n y i).2 hy'.ne'
  · -- Negative `i`th coordinate also implies the coordinate is nonzero.
    have hy' : ((y : EuclideanSpace ℝ (Fin (n + 1))) i) < 0 := by
      simpa [sphereToRealProjectiveSpace_signed_sheet] using hy
    exact (sphereToRealProjectiveSpace_mem_realProjectiveChartDomain_iff n y i).2 hy'.ne

/-- Helper for Example 4.35: the chosen signed lift lands in the corresponding signed sheet. -/
theorem sphereToRealProjectiveSpace_signed_lift_mem_sheet (n : ℕ) (i : Fin (n + 1))
    (σ : Fin 2) (x : realProjectiveChartDomain n i) :
    sphereToRealProjectiveSpace_signed_lift n i σ x ∈
      sphereToRealProjectiveSpace_signed_sheet n i σ := by
  fin_cases σ
  · -- The positive branch has strictly positive distinguished coordinate.
    simpa [sphereToRealProjectiveSpace_signed_lift, sphereToRealProjectiveSpace_signed_sheet] using
      sphereToRealProjectiveSpace_chart_unit_lift_apply_self_pos n i x
  · -- The antipodal branch has strictly negative distinguished coordinate.
    have hneg :
        (((-sphereToRealProjectiveSpace_chart_unit_lift n i x :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
          EuclideanSpace ℝ (Fin (n + 1))) i) < 0 := by
      simpa using neg_neg_iff_pos.mpr
        (sphereToRealProjectiveSpace_chart_unit_lift_apply_self_pos n i x)
    simpa [sphereToRealProjectiveSpace_signed_lift, sphereToRealProjectiveSpace_signed_sheet] using
      hneg

/-- Helper for Example 4.35: each signed lift is a right inverse to the quotient map over the
chosen chart. -/
theorem sphereToRealProjectiveSpace_signed_lift_proj (n : ℕ) (i : Fin (n + 1))
    (σ : Fin 2) (x : realProjectiveChartDomain n i) :
    sphereToRealProjectiveSpace n (sphereToRealProjectiveSpace_signed_lift n i σ x) = x := by
  fin_cases σ
  · -- The first sheet uses the positive normalized lift.
    simpa [sphereToRealProjectiveSpace_signed_lift] using
      sphereToRealProjectiveSpace_chart_unit_lift_proj n i x
  · -- The second sheet uses the antipodal normalized lift.
    simpa [sphereToRealProjectiveSpace_signed_lift] using
      sphereToRealProjectiveSpace_neg_chart_unit_lift_proj n i x

/-- Helper for Example 4.35: over a fixed chart, the quotient map is injective on each signed
sheet. -/
theorem sphereToRealProjectiveSpace_injOn_signed_sheet (n : ℕ) (i : Fin (n + 1)) (σ : Fin 2) :
    Set.InjOn (sphereToRealProjectiveSpace n) (sphereToRealProjectiveSpace_signed_sheet n i σ) := by
  intro y hy z hz hproj
  -- The only alternative to equality is the antipodal case, ruled out by the sign condition.
  rcases (same_projective_point_on_unit_sphere_iff_eq_or_eq_neg n y z).mp hproj with rfl | hneg
  · rfl
  · fin_cases σ
    · have hy' : 0 < ((y : EuclideanSpace ℝ (Fin (n + 1))) i) := by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hy
      have hz' : 0 < ((z : EuclideanSpace ℝ (Fin (n + 1))) i) := by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hz
      have hcoord :
          ((z : EuclideanSpace ℝ (Fin (n + 1))) i) =
            -((y : EuclideanSpace ℝ (Fin (n + 1))) i) := by
        simpa using congrArg
          (fun w : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
            ((w : EuclideanSpace ℝ (Fin (n + 1))) i)) hneg
      have hzneg : -((y : EuclideanSpace ℝ (Fin (n + 1))) i) > 0 := by
        simpa [hcoord] using hz'
      linarith
    · have hy' : ((y : EuclideanSpace ℝ (Fin (n + 1))) i) < 0 := by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hy
      have hz' : ((z : EuclideanSpace ℝ (Fin (n + 1))) i) < 0 := by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hz
      have hcoord :
          ((z : EuclideanSpace ℝ (Fin (n + 1))) i) =
            -((y : EuclideanSpace ℝ (Fin (n + 1))) i) := by
        simpa using congrArg
          (fun w : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
            ((w : EuclideanSpace ℝ (Fin (n + 1))) i)) hneg
      have hzneg : -((y : EuclideanSpace ℝ (Fin (n + 1))) i) < 0 := by
        simpa [hcoord] using hz'
      linarith

/-- Helper for Example 4.35: each signed sheet surjects onto the chosen projective chart domain. -/
theorem sphereToRealProjectiveSpace_signed_sheet_surjOn (n : ℕ) (i : Fin (n + 1)) (σ : Fin 2) :
    Set.SurjOn (sphereToRealProjectiveSpace n)
      (sphereToRealProjectiveSpace_signed_sheet n i σ)
      (realProjectiveChartDomain n i) := by
  intro x hx
  refine ⟨sphereToRealProjectiveSpace_signed_lift n i σ ⟨x, hx⟩, ?_, ?_⟩
  · -- The chosen signed lift lands on the requested sheet.
    exact sphereToRealProjectiveSpace_signed_lift_mem_sheet n i σ ⟨x, hx⟩
  · -- The signed lift projects back to the original chart-domain point.
    simpa using sphereToRealProjectiveSpace_signed_lift_proj n i σ ⟨x, hx⟩

/-- Helper for Example 4.35: the signed chart lifts vary continuously on each standard chart
domain. -/
theorem sphereToRealProjectiveSpace_signed_lift_continuous (n : ℕ) (i : Fin (n + 1))
    (σ : Fin 2) :
    Continuous (sphereToRealProjectiveSpace_signed_lift n i σ) := by
  fin_cases σ
  · -- The positive branch is the normalized chart lift.
    simpa [sphereToRealProjectiveSpace_signed_lift] using
      sphereToRealProjectiveSpace_chart_unit_lift_continuous n i
  · -- The negative branch is obtained by composing with the antipodal map.
    simpa [sphereToRealProjectiveSpace_signed_lift] using
      continuous_neg.comp (sphereToRealProjectiveSpace_chart_unit_lift_continuous n i)

/-- Helper for Example 4.35: pulling the signed sheet over a chart back along the corresponding
signed lift recovers exactly the chosen chart-domain subset. -/
theorem sphereToRealProjectiveSpace_signed_lift_preimage_eq (n : ℕ) (i : Fin (n + 1))
    (σ : Fin 2) (W : Set (RealProjectiveSpace n)) :
    (sphereToRealProjectiveSpace_signed_lift n i σ) ⁻¹'
        ((sphereToRealProjectiveSpace n) ⁻¹' W ∩ sphereToRealProjectiveSpace_signed_sheet n i σ) =
      ((↑) : realProjectiveChartDomain n i → RealProjectiveSpace n) ⁻¹' W := by
  ext x
  constructor
  · intro hx
    -- Projecting the signed lift lands back at the original chart-domain point.
    simpa [sphereToRealProjectiveSpace_signed_lift_proj n i σ x] using hx.1
  · intro hx
    -- Membership in the subset lifts to the corresponding signed sheet by construction.
    refine ⟨?_, sphereToRealProjectiveSpace_signed_lift_mem_sheet n i σ x⟩
    simpa [sphereToRealProjectiveSpace_signed_lift_proj n i σ x] using hx

/-- Helper for Example 4.35: over one standard projective chart, openness is detected on either
signed sheet by pulling back along the corresponding signed lift. -/
theorem sphereToRealProjectiveSpace_signed_sheet_open_iff (n : ℕ) (i : Fin (n + 1))
    (σ : Fin 2) (W : Set (RealProjectiveSpace n)) (hW : W ⊆ realProjectiveChartDomain n i) :
    IsOpen W ↔ IsOpen ((sphereToRealProjectiveSpace n) ⁻¹' W ∩
      sphereToRealProjectiveSpace_signed_sheet n i σ) := by
  constructor
  · intro hOpen
    -- Pull back an open chart-domain subset through the quotient map and intersect with one sheet.
    exact ((sphereToRealProjectiveSpace_continuous n).isOpen_preimage _ hOpen).inter
      (sphereToRealProjectiveSpace_signed_sheet_isOpen n i σ)
  · intro hOpen
    have hLift :
        IsOpen
          ((sphereToRealProjectiveSpace_signed_lift n i σ) ⁻¹'
            ((sphereToRealProjectiveSpace n) ⁻¹' W ∩
              sphereToRealProjectiveSpace_signed_sheet n i σ)) := by
      -- Pull the open subset back to the chart domain along the continuous signed inverse branch.
      exact (sphereToRealProjectiveSpace_signed_lift_continuous n i σ).isOpen_preimage _ hOpen
    rw [sphereToRealProjectiveSpace_signed_lift_preimage_eq n i σ W] at hLift
    have hIntersect :
        IsOpen (realProjectiveChartDomain n i ∩ W) := by
      simpa using
        (IsOpen.inter_preimage_val_iff
          (s := realProjectiveChartDomain n i)
          (t := W)
          (realProjectiveChartDomain_isOpen n i)).1 hLift
    simpa [Set.inter_eq_right.mpr hW] using hIntersect

/-- Helper for Example 4.35: each projective point admits a two-sheet trivialization by one
standard chart domain and its positive/negative sphere sheets. -/
theorem sphereToRealProjectiveSpace_chart_trivialization (n : ℕ) (x : RealProjectiveSpace n) :
    ∃ t : Bundle.Trivialization (Fin 2) (sphereToRealProjectiveSpace n), x ∈ t.baseSet := by
  classical
  obtain ⟨i, hx⟩ := real_projective_space_has_standard_chart n x
  let defaultPoint : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    sphereToRealProjectiveSpace_chart_unit_lift n i
      ⟨(realProjectiveChart n i).symm 0, realProjectiveChart_symm_mem_domain n i 0⟩
  let _ :
      Nonempty (RealProjectiveSpace n →
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := ⟨fun _ ↦ defaultPoint⟩
  have hDisjoint :
      Pairwise
        (fun σ τ : Fin 2 ↦
          Disjoint
            (sphereToRealProjectiveSpace_signed_sheet n i σ)
            (sphereToRealProjectiveSpace_signed_sheet n i τ)) := by
    intro σ τ hστ
    fin_cases σ <;> fin_cases τ
    · exact (hστ rfl).elim
    · refine Set.disjoint_left.mpr ?_
      intro y hy0 hy1
      have hyPos : 0 < ((y : EuclideanSpace ℝ (Fin (n + 1))) i) := by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hy0
      have hyNeg : ((y : EuclideanSpace ℝ (Fin (n + 1))) i) < 0 := by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hy1
      linarith
    · refine Set.disjoint_left.mpr ?_
      intro y hy1 hy0
      have hyNeg : ((y : EuclideanSpace ℝ (Fin (n + 1))) i) < 0 := by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hy1
      have hyPos : 0 < ((y : EuclideanSpace ℝ (Fin (n + 1))) i) := by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hy0
      linarith
    · exact (hστ rfl).elim
  have hExhaustive :
      sphereToRealProjectiveSpace n ⁻¹' realProjectiveChartDomain n i ⊆
        ⋃ σ : Fin 2, sphereToRealProjectiveSpace_signed_sheet n i σ := by
    intro y hy
    have hyCoord :
        ((y : EuclideanSpace ℝ (Fin (n + 1))) i) ≠ 0 :=
      (sphereToRealProjectiveSpace_mem_realProjectiveChartDomain_iff n y i).1 hy
    rcases lt_or_gt_of_ne hyCoord with hyNeg | hyPos
    · exact Set.mem_iUnion.mpr ⟨1, by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hyNeg⟩
    · exact Set.mem_iUnion.mpr ⟨0, by
        simpa [sphereToRealProjectiveSpace_signed_sheet] using hyPos⟩
  refine ⟨(realProjectiveChartDomain_isOpen n i).trivializationDiscrete
      (fun σ : Fin 2 ↦ sphereToRealProjectiveSpace_signed_sheet n i σ)
      (realProjectiveChartDomain n i)
      (fun σ W hW ↦ sphereToRealProjectiveSpace_signed_sheet_open_iff n i σ W hW)
      (fun σ ↦ sphereToRealProjectiveSpace_injOn_signed_sheet n i σ)
      (fun σ ↦ sphereToRealProjectiveSpace_signed_sheet_surjOn n i σ)
      hDisjoint
      hExhaustive, ?_⟩
  -- The chosen standard chart domain is the base set of the resulting discrete trivialization.
  simpa using hx

-- Proof sketch: this is exactly the canonical smooth-covering structure coming from the standard
-- covering map `Circle.exp : ℝ → S¹`; package the covering, surjectivity, and local
-- diffeomorphism data into `IsSmoothCoveringMap`.
/-- Example 4.35 (1): the map `ε : ℝ → S¹`, realized as `Circle.exp`, is a smooth covering
map. -/
theorem circle_exp_isSmoothCoveringMap :
    Manifold.IsSmoothCoveringMap (𝓘(ℝ)) (𝓡 1) Circle.exp := by
  -- The source proof packages the topological covering with the local angle branches.
  refine ⟨Circle.isCoveringMap_exp, Circle.exp_surjective, ?_⟩
  exact circle_exp_isLocalDiffeomorph_from_angle_branch

/-- Helper for Example 4.35: the coordinatewise product of the circle exponential covering maps
is a smooth covering map on the raw function model. -/
theorem coordinatewise_circle_exp_isSmoothCoveringMap (n : ℕ) :
    Manifold.IsSmoothCoveringMap
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1))
      (fun y : (Fin n → ℝ) ↦ fun i ↦ Circle.exp (y i)) := by
  -- The product route follows the source proof exactly: multiply the circle covering data and the
  -- local angle-branch diffeomorphisms coordinatewise.
  refine ⟨Manifold.IsSmoothCoveringMap.isCoveringMap_pi (π := fun _ : Fin n ↦ Circle.exp)
      fun _ ↦ circle_exp_isSmoothCoveringMap.isCoveringMap, ?_, ?_⟩
  · -- Surjectivity is coordinatewise because each circle point has a real angle lift.
    simpa using Function.Surjective.piMap
      (fun _ : Fin n ↦ circle_exp_isSmoothCoveringMap.surjective)
  · -- The product of the local circle branches is again a local diffeomorphism.
    simpa using isLocalDiffeomorph_pi (f := fun _ : Fin n ↦ Circle.exp)
      (fun _ : Fin n ↦ circle_exp_isSmoothCoveringMap.isLocalDiffeomorph)

/-- Helper for Example 4.35: the canonical smooth model on `Fin n → ℝ` agrees with the finite
product model of `n` copies of the real line. -/
theorem modelWithCornersSelf_fin_fun_eq_pi (n : ℕ) :
    (𝓘(ℝ, Fin n → ℝ)) = ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)) := by
  -- Both models are built from the identity partial equivalence on each coordinate.
  ext x <;>
    simp [ModelWithCorners.pi, modelWithCornersSelf_partialEquiv, PartialEquiv.pi_refl]

/-- Helper for Example 4.35: the finite product charted-space on `Fin n → ℝ` agrees with the
self-charted-space. -/
theorem chartedSpaceSelf_fin_fun_eq_pi (n : ℕ) :
    piChartedSpace (fun _ : Fin n ↦ ℝ) (fun _ : Fin n ↦ ℝ) =
      chartedSpaceSelf (Fin n → ℝ) := by
  have hpiRefl :
      OpenPartialHomeomorph.pi (fun _ : Fin n ↦ OpenPartialHomeomorph.refl ℝ) =
        OpenPartialHomeomorph.refl (Fin n → ℝ) := by
    refine OpenPartialHomeomorph.ext _ _ (fun x ↦ rfl) (fun x ↦ rfl) ?_
    ext x
    simp [OpenPartialHomeomorph.pi]
  ext1
  · ext e
    constructor
    · rintro ⟨f, hf, rfl⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies] at hf
      have hconst : f = fun _ : Fin n ↦ OpenPartialHomeomorph.refl ℝ := by
        funext i
        simpa using hf i
      subst hconst
      exact hpiRefl
    · intro he
      subst he
      exact ⟨fun _ : Fin n ↦ OpenPartialHomeomorph.refl ℝ, by simp, hpiRefl⟩
  · funext x
    simp [ChartedSpace.chartAt, hpiRefl]

/-- Helper for Example 4.35: the `PiLp` coordinate-forgetting map is smooth for the product model
on `Fin n → ℝ`. -/
theorem euclidean_pi_real_contMDiff_toFun_pi_model (n : ℕ) :
    ContMDiff (𝓡 n) (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ))) (∞ : ℕ∞ω)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)) := by
  -- Rewrite the product charted-space and model to the self model, where a continuous linear
  -- equivalence is smooth.
  rw [chartedSpaceSelf_fin_fun_eq_pi n]
  rw [← modelWithCornersSelf_fin_fun_eq_pi n]
  simpa using
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).contDiff.contMDiff

/-- Helper for Example 4.35: the inverse `PiLp` coordinate-forgetting map is smooth for the
product model on `Fin n → ℝ`. -/
theorem euclidean_pi_real_contMDiff_invFun_pi_model (n : ℕ) :
    ContMDiff (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ))) (𝓡 n) (∞ : ℕ∞ω)
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm) := by
  -- After rewriting the source model, smoothness reduces to the inverse continuous linear
  -- equivalence between the two finite-dimensional real vector spaces.
  rw [chartedSpaceSelf_fin_fun_eq_pi n]
  rw [← modelWithCornersSelf_fin_fun_eq_pi n]
  simpa using
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm).contDiff.contMDiff

/-- Helper for Example 4.35: the canonical `PiLp` equivalence identifies Euclidean space with the
raw function model equipped with the finite-product smooth structure. -/
noncomputable def euclidean_pi_real_product_diffeomorph (n : ℕ) :
    Diffeomorph (𝓡 n) (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (EuclideanSpace ℝ (Fin n)) (Fin n → ℝ) (∞ : ℕ∞ω) :=
  { toEquiv := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toLinearEquiv.toEquiv
    contMDiff_toFun := euclidean_pi_real_contMDiff_toFun_pi_model n
    contMDiff_invFun := euclidean_pi_real_contMDiff_invFun_pi_model n }

/-- Helper for Example 4.35: `standardTorusCovering n` is the coordinatewise exponential map
precomposed with the canonical `PiLp` identification of Euclidean space with raw functions. -/
theorem standardTorusCovering_eq_coordinatewise_circle_exp_comp (n : ℕ) :
    standardTorusCovering n =
      (fun y : (Fin n → ℝ) ↦ fun i ↦ Circle.exp (y i)) ∘
        (euclidean_pi_real_product_diffeomorph n : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) := by
  -- Both sides evaluate a Euclidean point coordinatewise after forgetting the `PiLp` wrapper.
  funext x i
  rfl

-- Proof sketch: identify `εⁿ` with the coordinatewise product of `n` copies of `Circle.exp` and
-- combine the product covering-map and product local-diffeomorphism constructions.
/-- Example 4.35 (2): the map `εⁿ : ℝⁿ → 𝕋ⁿ`, given coordinatewise by `Circle.exp`, is a smooth
covering map. -/
theorem standard_torus_covering_isSmoothCoveringMap (n : ℕ) :
    Manifold.IsSmoothCoveringMap (𝓡 n) (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1))
      (standardTorusCovering n) := by
  let g : (Fin n → ℝ) → 𝕋^{n} := fun y i ↦ Circle.exp (y i)
  have hg : Manifold.IsSmoothCoveringMap
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1)) g := by
    simpa [g] using coordinatewise_circle_exp_isSmoothCoveringMap n
  have he : IsLocalDiffeomorph (𝓡 n) (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (∞ : ℕ∞ω)
      (euclidean_pi_real_product_diffeomorph n) :=
    (euclidean_pi_real_product_diffeomorph n).isLocalDiffeomorph
  -- Route correction: the finite-product covering lives on the raw function model, so we transport
  -- it once along the canonical `PiLp` diffeomorphism back to `EuclideanSpace`.
  refine ⟨?_, ?_, ?_⟩
  · -- Covering-map structure is preserved under precomposition with a homeomorphism.
    rw [standardTorusCovering_eq_coordinatewise_circle_exp_comp]
    simpa [g] using
      hg.isCoveringMap.comp_homeomorph (euclidean_pi_real_product_diffeomorph n).toHomeomorph
  · -- Surjectivity transports across the inverse `PiLp` equivalence.
    intro x
    rcases hg.surjective x with ⟨y, rfl⟩
    refine ⟨(euclidean_pi_real_product_diffeomorph n).symm y, ?_⟩
    rw [standardTorusCovering_eq_coordinatewise_circle_exp_comp]
    simp [g]
  · -- Local diffeomorphism structure also transports by composition with the diffeomorphism.
    rw [standardTorusCovering_eq_coordinatewise_circle_exp_comp]
    simpa [g] using isLocalDiffeomorph_comp hg.isLocalDiffeomorph he

-- Proof sketch: `sphereToRealProjectiveSpace n` is the quotient by the antipodal action on the
-- sphere, and the classical projective-space chart description shows this quotient map is evenly
-- covered by the standard affine charts on `ℝPⁿ`.
/-- Example 4.35 (3): the quotient map `q : Sⁿ → ℝPⁿ` is a covering map. -/
theorem sphere_to_realProjectiveSpace_isCoveringMap (n : ℕ) :
    IsCoveringMap (sphereToRealProjectiveSpace n) := by
  -- Route correction: use the standard affine chart domain exactly as in the source proof, then
  -- split its sphere preimage into the positive and negative coordinate sheets.
  classical
  refine IsCoveringMap.mk (f := sphereToRealProjectiveSpace n)
    (fun _ : RealProjectiveSpace n ↦ Fin 2)
    (fun x ↦ Classical.choose (sphereToRealProjectiveSpace_chart_trivialization n x)) ?_
  -- Each projective point lies in the base set of the trivialization built from one standard chart.
  intro x
  exact Classical.choose_spec (sphereToRealProjectiveSpace_chart_trivialization n x)

-- Proof sketch: every projective point is represented by a unit vector `y`, and the only unit
-- vectors representing the same line are the antipodal pair `y` and `-y`.
/-- Example 4.35 (4): each fiber of `q : Sⁿ → ℝPⁿ` is exactly an antipodal pair, expressing that
`q` is two-sheeted. -/
theorem sphere_to_realProjectiveSpace_fiber_eq_antipodal_pair (n : ℕ)
    (x : RealProjectiveSpace n) :
    ∃ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      {z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
          sphereToRealProjectiveSpace n z = x} =
        ({y, -y} : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
  -- Choose a unit representative of `x`, then identify the fiber using the antipodal-orbit lemma.
  rcases sphereToRealProjectiveSpace_surjective n x with ⟨y, rfl⟩
  refine ⟨y, ?_⟩
  ext z
  constructor
  · intro hz
    have hz' := (same_projective_point_on_unit_sphere_iff_eq_or_eq_neg n y z).mp hz.symm
    simpa using hz'
  · intro hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · rfl
    · have hz' : z = -y := by simpa [Set.mem_singleton_iff] using hz
      exact ((same_projective_point_on_unit_sphere_iff_eq_or_eq_neg n y z).mpr (Or.inr hz')).symm
