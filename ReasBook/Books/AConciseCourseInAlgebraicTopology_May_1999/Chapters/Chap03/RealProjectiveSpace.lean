import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Category.TopCat.Sphere

noncomputable section

open scoped TopCat

namespace TopCat

/-- The concrete Euclidean unit-sphere model underlying `𝕊 n`. -/
abbrev SphereModel (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The standard sphere `𝕊 n` is homeomorphic to its concrete Euclidean sphere model. -/
abbrev sphereModelHomeomorph (n : ℕ) : 𝕊 n ≃ₜ SphereModel n := Homeomorph.ulift

end TopCat

open TopCat (SphereModel sphereModelHomeomorph)

private instance sphere_t2Space (n : ℕ) : T2Space (𝕊 n) :=
  (sphereModelHomeomorph n).symm.t2Space

private instance sphere_locallyCompactSpace (n : ℕ) : LocallyCompactSpace (𝕊 n) :=
  (sphereModelHomeomorph n).isOpenEmbedding.locallyCompactSpace

/-- The antipodal map on `𝕊 n`. -/
private def sphereModelAntipode (n : ℕ) (x : SphereModel n) : SphereModel n :=
  ⟨-x.1, by
    simpa [SphereModel, Metric.mem_sphere, dist_eq_norm] using x.2⟩

/-- The antipodal map on `𝕊 n`. -/
private def sphereAntipode (n : ℕ) (x : 𝕊 n) : 𝕊 n :=
  ULift.up (sphereModelAntipode n x.down)

/-- The antipodal map gives the canonical negation on `S^n`. -/
instance (n : ℕ) : Neg (𝕊 n) where
  neg := sphereAntipode n

private theorem sphereModel_ne_zero (n : ℕ) (x : SphereModel n) :
    x.1 ≠ (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
  intro hx
  have hxnorm : ‖x.1‖ = 1 := by
    simpa [SphereModel, Metric.mem_sphere, dist_eq_norm] using x.2
  simp [hx] at hxnorm

private theorem sphereAntipode_ne_self (n : ℕ) (x : 𝕊 n) :
    sphereAntipode n x ≠ x := by
  intro hx
  have hx' : -(x.down.1) = x.down.1 := by
    simpa [sphereAntipode] using congrArg (fun y : 𝕊 n ↦ y.down.1) hx
  have hsum : x.down.1 + x.down.1 = (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
    calc
      x.down.1 + x.down.1 = -x.down.1 + x.down.1 := by
        simpa using congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z + x.down.1) hx'.symm
      _ = 0 := by simp
  have htwo : (2 : ℝ) • x.down.1 = (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa [two_smul] using hsum
  have hx0 : x.down.1 = (0 : EuclideanSpace ℝ (Fin (n + 1))) :=
    (smul_eq_zero.mp htwo).resolve_left two_ne_zero
  exact sphereModel_ne_zero n x.down hx0

/-- The antipodal involution has no fixed points on `S^n`. -/
theorem sphere_neg_ne_self (n : ℕ) (x : 𝕊 n) : (-x : 𝕊 n) ≠ x :=
  sphereAntipode_ne_self n x

private theorem sphereAntipode_involutive (n : ℕ) (x : 𝕊 n) :
    sphereAntipode n (sphereAntipode n x) = x := by
  apply ULift.ext
  apply Subtype.ext
  simp [sphereAntipode, sphereModelAntipode]

private inductive AntipodalSymmetry where
  | one
  | neg
deriving DecidableEq, Fintype

private instance : One AntipodalSymmetry := ⟨AntipodalSymmetry.one⟩

private instance : Mul AntipodalSymmetry where
  mul g h :=
    match g, h with
    | .one, h => h
    | .neg, .one => .neg
    | .neg, .neg => .one

private instance : Inv AntipodalSymmetry where
  inv g := g

private instance : Group AntipodalSymmetry where
  one_mul g := by cases g <;> rfl
  mul_one g := by cases g <;> rfl
  mul_assoc g h k := by cases g <;> cases h <;> cases k <;> rfl
  inv_mul_cancel g := by cases g <;> rfl

private instance : TopologicalSpace AntipodalSymmetry := ⊥

private instance : DiscreteTopology AntipodalSymmetry := ⟨rfl⟩

private def sphereAntipodalSMul (n : ℕ) (g : AntipodalSymmetry) (x : 𝕊 n) : 𝕊 n :=
  match g with
  | .one => x
  | .neg => sphereAntipode n x

private instance sphereAntipodalSMulInst (n : ℕ) : SMul AntipodalSymmetry (𝕊 n) where
  smul := sphereAntipodalSMul n

private instance sphereAntipodalMulAction (n : ℕ) : MulAction AntipodalSymmetry (𝕊 n) where
  one_smul x := by
    rfl
  mul_smul g h x := by
    change sphereAntipodalSMul n (g * h) x = sphereAntipodalSMul n g (sphereAntipodalSMul n h x)
    cases g <;> cases h <;> simp [sphereAntipodalSMul, sphereAntipode_involutive]

private instance sphereAntipodalContinuousConstSMul (n : ℕ) :
    ContinuousConstSMul AntipodalSymmetry (𝕊 n) where
  continuous_const_smul g := by
    cases g
    · simpa [sphereAntipodalSMul] using (continuous_id : Continuous fun x : 𝕊 n ↦ x)
    · simpa [sphereAntipodalSMul, sphereAntipode] using
        (continuous_uliftUp.comp
          ((Continuous.subtype_mk
              (continuous_neg.comp continuous_subtype_val)
              fun x ↦ by
                simpa [sphereModelAntipode, SphereModel, Metric.mem_sphere, dist_eq_norm]
                  using x.2).comp continuous_uliftDown) :
          Continuous fun x : 𝕊 n ↦ ULift.up (sphereModelAntipode n x.down))

private instance sphereAntipodalIsCancelSMul (n : ℕ) :
    IsCancelSMul AntipodalSymmetry (𝕊 n) where
  right_cancel' g h x hgh := by
    change sphereAntipodalSMul n g x = sphereAntipodalSMul n h x at hgh
    cases g <;> cases h
    · rfl
    · exfalso
      exact sphereAntipode_ne_self n x (by simpa [sphereAntipodalSMul] using hgh.symm)
    · exfalso
      exact sphereAntipode_ne_self n x (by simpa [sphereAntipodalSMul] using hgh)
    · rfl

private theorem sphere_eq_or_neg_eq_iff_orbitRel (n : ℕ) {x y : 𝕊 n} :
    x = y ∨ x = -y ↔ MulAction.orbitRel AntipodalSymmetry (𝕊 n) x y := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · intro hxy
    rcases hxy with rfl | hxy
    · exact ⟨1, by simp⟩
    · exact ⟨AntipodalSymmetry.neg, by simpa [sphereAntipodalSMul] using hxy.symm⟩
  · rintro ⟨g, hg⟩
    cases g
    · exact Or.inl (by simpa using hg.symm)
    · exact Or.inr (by simpa [sphereAntipodalSMul] using hg.symm)

/-- The quotient of `S^n` by the antipodal action, used as the standard model of `RP^n`. -/
abbrev RealProjectiveSpace (n : ℕ) : Type :=
  MulAction.orbitRel.Quotient AntipodalSymmetry (𝕊 n)

instance (n : ℕ) : CompactSpace (RealProjectiveSpace n) := by
  sorry

/-- Real projective space is Hausdorff because it is the quotient of `S^n` by the properly
discontinuous antipodal action. -/
instance (n : ℕ) : T2Space (RealProjectiveSpace n) := by
  let _ : ProperSMul AntipodalSymmetry (𝕊 n) :=
    (properlyDiscontinuousSMul_iff_properSMul (G := AntipodalSymmetry) (X := 𝕊 n)).mp inferInstance
  dsimp [RealProjectiveSpace]
  infer_instance

/-- The canonical quotient map from `S^n` to `RP^n`. -/
def sphereToRealProjectiveSpace (n : ℕ) : 𝕊 n → RealProjectiveSpace n :=
  Quotient.mk''

@[simp] theorem sphereToRealProjectiveSpace_eq_iff (n : ℕ) {x y : 𝕊 n} :
    sphereToRealProjectiveSpace n x = sphereToRealProjectiveSpace n y ↔ x = y ∨ x = -y := by
  change Quotient.mk'' x = (Quotient.mk'' y : MulAction.orbitRel.Quotient AntipodalSymmetry (𝕊 n)) ↔
    x = y ∨ x = -y
  rw [Quotient.eq'']
  exact (sphere_eq_or_neg_eq_iff_orbitRel n).symm

/-- The antipodal quotient map `S^n → RP^n` is a covering map. -/
theorem sphereToRealProjectiveSpace_isCoveringMap (n : ℕ) :
    IsCoveringMap (sphereToRealProjectiveSpace n) := by
  simpa [RealProjectiveSpace, sphereToRealProjectiveSpace] using
    ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (G := AntipodalSymmetry) (E := 𝕊 n)).isCoveringMap)

/-- The canonical quotient map `S^n → RP^n` as a continuous map. -/
noncomputable abbrev sphereToRealProjectiveSpaceMap (n : ℕ) :
    C(𝕊 n, RealProjectiveSpace n) :=
  ⟨sphereToRealProjectiveSpace n, (sphereToRealProjectiveSpace_isCoveringMap n).continuous⟩
