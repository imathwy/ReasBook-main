module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Homotopy.Product

public section

universe u

namespace Path

variable {G : Type u} [TopologicalSpace G] [Group G] [hG : IsTopologicalGroup G]

/-- Pointwise multiplication of loops based at the identity of a topological group. -/
noncomputable def pointwiseMul (f g : Path (1 : G) 1) : Path (1 : G) 1 :=
  (f.mul g).cast (mul_one 1).symm (mul_one 1).symm

@[inherit_doc] scoped[LoopPointwise] infixl:70 " ⊗ " => Path.pointwiseMul

open scoped LoopPointwise

/-- Pointwise multiplication of identity-based loops is multiplication at every parameter. -/
theorem pointwiseMul_apply (f g : Path (1 : G) 1) (s : unitInterval) :
    (f ⊗ g) s = f s * g s := by
  -- The endpoint cast does not alter the underlying pointwise product.
  rfl

/-- The constant identity loop in a topological group. -/
noncomputable def pointwiseOne : Path (1 : G) 1 :=
  Path.refl 1

omit hG in
/-- Helper for Exercise 52.7: the constant identity loop evaluates to the identity. -/
theorem pointwiseOne_apply (s : unitInterval) : pointwiseOne (G := G) s = 1 := by
  -- Evaluation of the constant path is definitionally constant.
  rfl

/-- Pointwise inversion of a loop based at the identity of a topological group. -/
noncomputable def pointwiseInv (f : Path (1 : G) 1) : Path (1 : G) 1 :=
  f.inv.cast inv_one.symm inv_one.symm

/-- Helper for Exercise 52.7: pointwise inversion evaluates by inversion in the group. -/
theorem pointwiseInv_apply (f : Path (1 : G) 1) (s : unitInterval) :
    pointwiseInv f s = (f s)⁻¹ := by
  -- The endpoint cast leaves the underlying inverse path unchanged.
  rfl

/-- Pointwise multiplication of identity-based loops is associative. -/
theorem pointwiseMul_assoc (f g h : Path (1 : G) 1) :
    (f ⊗ g) ⊗ h = f ⊗ (g ⊗ h) := by
  -- Extensionality reduces the path identity to associativity in `G`.
  ext s
  simp only [pointwiseMul_apply, mul_assoc]

/-- The constant identity loop is a left identity for pointwise multiplication. -/
theorem pointwiseOne_mul (f : Path (1 : G) 1) : pointwiseOne ⊗ f = f := by
  -- Evaluate the constant loop and apply the left identity law in `G`.
  ext s
  simp only [pointwiseMul_apply, pointwiseOne_apply, one_mul]

/-- Pointwise inversion is a left inverse for identity-based loops. -/
theorem pointwiseInv_mul (f : Path (1 : G) 1) :
    pointwiseInv f ⊗ f = pointwiseOne := by
  -- Evaluate pointwise and apply the inverse law in `G`.
  ext s
  simp only [pointwiseMul_apply, pointwiseInv_apply, pointwiseOne_apply, inv_mul_cancel]

/-- Identity-based loops in a topological group form a group under pointwise multiplication. -/
noncomputable instance instGroupIdentityLoop : Group (Path (1 : G) 1) :=
  let _ : Mul (Path (1 : G) 1) := ⟨pointwiseMul⟩
  let _ : One (Path (1 : G) 1) := ⟨pointwiseOne⟩
  let _ : Inv (Path (1 : G) 1) := ⟨pointwiseInv⟩
  Group.ofLeftAxioms pointwiseMul_assoc pointwiseOne_mul pointwiseInv_mul

end Path

open scoped LoopPointwise

namespace FundamentalGroup

variable {G : Type u} [TopologicalSpace G] [Group G] [hG : IsTopologicalGroup G]

/-- Pointwise multiplication preserves endpoint-fixed path homotopy in both arguments. -/
theorem pointwiseMul_homotopic {f₀ f₁ g₀ g₁ : Path (1 : G) 1}
    (hf : f₀.Homotopic f₁) (hg : g₀.Homotopic g₁) :
    Path.Homotopic (f₀ ⊗ g₀) (f₁ ⊗ g₁) := by
  -- Product the two homotopies, map by multiplication, and restore the identity endpoints.
  exact Path.Homotopic.pathCast
    (Path.Homotopic.map (Nonempty.map2 Path.Homotopic.prodHomotopy hf hg)
      ⟨fun p : G × G ↦ p.1 * p.2, continuous_mul⟩)
    (mul_one 1).symm (mul_one 1).symm

/-- Pointwise inversion preserves endpoint-fixed path homotopy. -/
theorem pointwiseInv_homotopic {f g : Path (1 : G) 1} (h : f.Homotopic g) :
    (Path.pointwiseInv f).Homotopic (Path.pointwiseInv g) := by
  -- Map the homotopy by inversion and restore the identity endpoints.
  exact Path.Homotopic.pathCast
    (Path.Homotopic.map h ⟨fun x ↦ x⁻¹, continuous_inv⟩) inv_one.symm inv_one.symm

/-- Pointwise multiplication of identity-based loops, descended to the fundamental group. -/
noncomputable def pointwiseMul (a b : FundamentalGroup G 1) : FundamentalGroup G 1 :=
  Quotient.map₂ Path.pointwiseMul
    (fun _ _ hf _ _ hg ↦ pointwiseMul_homotopic hf hg) a b

@[inherit_doc] scoped[LoopPointwise] infixl:70 " ⊗ " => FundamentalGroup.pointwiseMul

open scoped LoopPointwise

/-- Pointwise multiplication of fundamental-group classes is represented pointwise. -/
theorem pointwiseMul_mk (f g : Path (1 : G) 1) :
    Path.Homotopic.Quotient.mk f ⊗ Path.Homotopic.Quotient.mk g =
      Path.Homotopic.Quotient.mk (f ⊗ g) := by
  -- Quotient multiplication computes directly on representatives.
  rfl

/-- The identity element for the pointwise group structure on the fundamental group. -/
noncomputable def pointwiseOne : FundamentalGroup G 1 :=
  Path.Homotopic.Quotient.mk Path.pointwiseOne

/-- Pointwise inversion, descended to the fundamental group. -/
noncomputable def pointwiseInv (a : FundamentalGroup G 1) : FundamentalGroup G 1 :=
  Quotient.map Path.pointwiseInv (fun _ _ hf ↦ pointwiseInv_homotopic hf) a

/-- Helper for Exercise 52.7: descended inversion computes on a path representative. -/
theorem pointwiseInv_mk (f : Path (1 : G) 1) :
    pointwiseInv (Path.Homotopic.Quotient.mk f) =
      Path.Homotopic.Quotient.mk (Path.pointwiseInv f) := by
  -- Quotient inversion computes directly on representatives.
  rfl

/-- Descended pointwise multiplication is associative. -/
theorem pointwiseMul_assoc (a b c : FundamentalGroup G 1) :
    (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c) := by
  -- Reduce all three classes to paths and use the path-level associativity law.
  induction a using Path.Homotopic.Quotient.ind with
  | mk f =>
    induction b using Path.Homotopic.Quotient.ind with
    | mk g =>
      induction c using Path.Homotopic.Quotient.ind with
      | mk h =>
        rw [pointwiseMul_mk, pointwiseMul_mk, pointwiseMul_mk, pointwiseMul_mk,
          Path.pointwiseMul_assoc]

/-- The descended constant loop is a left identity for pointwise multiplication. -/
theorem pointwiseOne_mul (a : FundamentalGroup G 1) : pointwiseOne ⊗ a = a := by
  -- Reduce to a representative and use the left identity for paths.
  induction a using Path.Homotopic.Quotient.ind with
  | mk f =>
    rw [pointwiseOne, pointwiseMul_mk, Path.pointwiseOne_mul]

/-- Descended pointwise inversion is a left inverse. -/
theorem pointwiseInv_mul (a : FundamentalGroup G 1) :
    pointwiseInv a ⊗ a = pointwiseOne := by
  -- Reduce to a representative and use the inverse law for paths.
  induction a using Path.Homotopic.Quotient.ind with
  | mk f =>
    rw [pointwiseInv_mk, pointwiseMul_mk, Path.pointwiseInv_mul, pointwiseOne]

/-- The explicit group structure on the fundamental group induced by pointwise loop
multiplication. -/
@[reducible] noncomputable def pointwiseGroup : Group (FundamentalGroup G 1) :=
  let _ : Mul (FundamentalGroup G 1) := ⟨pointwiseMul⟩
  let _ : One (FundamentalGroup G 1) := ⟨pointwiseOne⟩
  let _ : Inv (FundamentalGroup G 1) := ⟨pointwiseInv⟩
  Group.ofLeftAxioms pointwiseMul_assoc pointwiseOne_mul pointwiseInv_mul

/-- Helper for Exercise 52.7: pointwise multiplication commutes strictly with path concatenation. -/
theorem Path.pointwiseMul_trans (f₀ f₁ g₀ g₁ : Path (1 : G) 1) :
    (f₀.trans f₁) ⊗ (g₀.trans g₁) = (f₀ ⊗ g₀).trans (f₁ ⊗ g₁) := by
  -- Both sides choose the same half of the interval and then multiply pointwise.
  ext s
  simp only [Path.pointwiseMul_apply, Path.trans_apply]
  split_ifs
  · rfl
  · rfl

/-- Helper for Exercise 52.7: the ordinary and pointwise products satisfy interchange. -/
theorem pointwiseMul_interchange (a b c d : FundamentalGroup G 1) :
    (a * b) ⊗ (c * d) = (a ⊗ c) * (b ⊗ d) := by
  -- Choose representatives, normalize ordinary multiplication, and apply strict interchange.
  induction a using Path.Homotopic.Quotient.ind with
  | mk f =>
    induction b using Path.Homotopic.Quotient.ind with
    | mk g =>
      induction c using Path.Homotopic.Quotient.ind with
      | mk h =>
        induction d using Path.Homotopic.Quotient.ind with
        | mk i =>
          simp only [FundamentalGroup.mul_def, ← Path.Homotopic.Quotient.mk_trans,
            pointwiseMul_mk, Path.pointwiseMul_trans]

/-- Helper for Exercise 52.7: the descended constant loop is a right pointwise identity. -/
theorem pointwiseMul_one (a : FundamentalGroup G 1) : a ⊗ pointwiseOne = a := by
  -- Reduce to a representative and use the right identity law in `G` pointwise.
  induction a using Path.Homotopic.Quotient.ind with
  | mk f =>
    rw [pointwiseOne, pointwiseMul_mk]
    congr 1
    ext s
    simp only [Path.pointwiseMul_apply, Path.pointwiseOne_apply, mul_one]

/-- Pointwise multiplication agrees with the usual concatenation multiplication on `π₁(G, 1)`. -/
theorem pointwiseMul_eq_mul (a b : FundamentalGroup G 1) : a ⊗ b = a * b := by
  -- Identify the two units, then use interchange on `(a * 1) ⊗ (1 * b)`.
  have pointwiseOne_eq_one : pointwiseOne = (1 : FundamentalGroup G 1) := rfl
  calc
    a ⊗ b = (a * (1 : FundamentalGroup G 1)) ⊗ ((1 : FundamentalGroup G 1) * b) := by
      rw [mul_one, one_mul]
    _ = (a ⊗ (1 : FundamentalGroup G 1)) * ((1 : FundamentalGroup G 1) ⊗ b) :=
      pointwiseMul_interchange a 1 1 b
    _ = a * b := by
      rw [← pointwiseOne_eq_one, pointwiseMul_one, pointwiseOne_mul]

end FundamentalGroup
