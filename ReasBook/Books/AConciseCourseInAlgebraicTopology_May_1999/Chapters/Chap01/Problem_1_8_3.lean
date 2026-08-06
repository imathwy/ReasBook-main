import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Homotopy.Product

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Path.Homotopic.Quotient
open scoped unitInterval

section HSpace

variable {X : Type u} [TopologicalSpace X] [HSpace X]

/-- Helper for Problem 1.8.3: pointwise loop multiplication on homotopy classes induced by the
ambient `HSpace` structure. -/
def loop_hmul_class
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    Path.Homotopic.Quotient (HSpace.e : X) HSpace.e :=
  ((Path.Homotopic.prod p q).map HSpace.hmul).cast
    HSpace.hmul_e_e.symm
    HSpace.hmul_e_e.symm

/-- Helper for Problem 1.8.3: the left-unit homotopy coming from `HSpace.eHmul`. -/
lemma loop_map_homotopic_of_homotopyRel
    {f : C(X, X)} (h : f.HomotopyRel (ContinuousMap.id X) ({HSpace.e} : Set X))
    (γ : Path (HSpace.e : X) HSpace.e) :
    ((γ.map f.continuous).cast
      (h.fst_eq_snd (by simp)).symm
      (h.fst_eq_snd (by simp)).symm).Homotopic γ := by
  let he : f (HSpace.e : X) = HSpace.e := h.fst_eq_snd (by simp)
  refine ⟨{
    toFun := fun p ↦ h (p.1, γ p.2)
    continuous_toFun := by
      exact h.continuous_toFun.comp <|
        continuous_fst.prodMk (γ.continuous.comp continuous_snd)
    map_zero_left := by
      intro s
      simp [Path.cast]
    map_one_left := by
      intro s
      simp
    prop' := by
      intro t s hs
      have hmem : (HSpace.e : X) ∈ ({HSpace.e} : Set X) := by simp
      rcases hs with rfl | rfl <;>
        simpa [Path.cast, he] using h.eq_fst t hmem }⟩

/-- Helper for Problem 1.8.3: the left-unit homotopy coming from `HSpace.eHmul`. -/
lemma loop_hmul_refl_left_homotopic (γ : Path (HSpace.e : X) HSpace.e) :
    ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
      HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).Homotopic γ := by
  simpa [ContinuousMap.comp_apply, ContinuousMap.id_apply, ContinuousMap.prod_eval,
    Path.refl_apply] using
    loop_map_homotopic_of_homotopyRel HSpace.eHmul γ

/-- Helper for Problem 1.8.3: the right-unit homotopy coming from `HSpace.hmulE`. -/
lemma loop_hmul_refl_right_homotopic (γ : Path (HSpace.e : X) HSpace.e) :
    (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
      HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).Homotopic γ := by
  simpa [ContinuousMap.comp_apply, ContinuousMap.id_apply, ContinuousMap.prod_eval,
    Path.refl_apply] using
    loop_map_homotopic_of_homotopyRel HSpace.hmulE γ

/-- Helper for Problem 1.8.3: loop multiplication by `HSpace.hmul` has the constant loop as a left
unit on homotopy classes. -/
lemma loop_hmul_class_refl_left (q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    loop_hmul_class (refl HSpace.e) q = q := by
  induction q using Quotient.ind
  rename_i γ
  -- Reduce to the explicit left-unit homotopy on representatives.
  change mk
      ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) =
    mk γ
  rw [eq]
  exact loop_hmul_refl_left_homotopic γ

/-- Helper for Problem 1.8.3: loop multiplication by `HSpace.hmul` has the constant loop as a right
unit on homotopy classes. -/
lemma loop_hmul_class_refl_right (q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    loop_hmul_class q (refl HSpace.e) = q := by
  induction q using Quotient.ind
  rename_i γ
  -- Reduce to the explicit right-unit homotopy on representatives.
  change mk
      (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) =
    mk γ
  rw [eq]
  exact loop_hmul_refl_right_homotopic γ

/-- Helper for Problem 1.8.3: pointwise loop multiplication distributes over path composition on
homotopy classes. -/
lemma loop_hmul_class_interchange
    (p₁ q₁ p₂ q₂ : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    (loop_hmul_class p₁ q₁).trans (loop_hmul_class p₂ q₂) =
      loop_hmul_class (p₁.trans p₂) (q₁.trans q₂) := by
  induction p₁, q₁ using Quotient.ind₂
  rename_i a c
  induction p₂, q₂ using Quotient.ind₂
  rename_i b d
  change mk
      ((((a.prod c).map HSpace.hmul.continuous).cast
          HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).trans
        (((b.prod d).map HSpace.hmul.continuous).cast
          HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm)) =
    mk
      ((((a.trans b).prod (c.trans d)).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm)
  rw [eq]
  convert
      Path.Homotopic.refl
        ((((a.trans b).prod (c.trans d)).map HSpace.hmul.continuous).cast
          HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) using 1
  rw [← Path.cast_trans, ← Path.map_trans, Path.trans_prod_eq_prod_trans]

private lemma loop_trans_isUnital :
    EckmannHilton.IsUnital
      (trans :
        Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
          Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
            Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
      (refl HSpace.e) :=
  { left_id := refl_trans
    right_id := trans_refl }

private lemma loop_hmul_class_isUnital :
    EckmannHilton.IsUnital
      (loop_hmul_class :
        Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
          Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
            Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
      (refl HSpace.e) :=
  { left_id := loop_hmul_class_refl_left
    right_id := loop_hmul_class_refl_right }

/-- Helper for Problem 1.8.3: the `HSpace` loop product agrees with path composition on homotopy
classes. -/
lemma loop_hmul_class_eq_trans
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    loop_hmul_class p q = p.trans q := by
  -- Apply the abstract Eckmann-Hilton argument to the two loop operations.
  exact
    (congr_fun₂
      (EckmannHilton.mul loop_trans_isUnital loop_hmul_class_isUnital
        loop_hmul_class_interchange) p q).symm

namespace FundamentalGroup

/-- The `HSpace` loop product represents the product on `π₁(X, HSpace.e)`, with the usual order
reversal coming from `FundamentalGroup`. -/
theorem fromPath_loop_hmul_class
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    fromPath (loop_hmul_class p q) = fromPath q * fromPath p := by
  rw [loop_hmul_class_eq_trans]
  rfl

end FundamentalGroup

/-- Helper for Problem 1.8.3: path composition is commutative on loop classes at the `HSpace`
unit. -/
lemma loop_trans_comm
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    p.trans q = q.trans p := by
  -- Compare path composition to the `HSpace` loop product, then use its commutativity.
  calc
    p.trans q = loop_hmul_class p q := loop_hmul_class_eq_trans p q |>.symm
    _ = loop_hmul_class q p :=
      (EckmannHilton.mul_comm loop_trans_isUnital loop_hmul_class_isUnital
        loop_hmul_class_interchange).comm p q
    _ = q.trans p := loop_hmul_class_eq_trans q p

/-- Problem 1.8.3: multiplication on the fundamental group at the unit of an `HSpace` is
commutative. In particular, the fundamental group at the identity of a topological group is
commutative via `IsTopologicalGroup.hSpace`. -/
-- Proof sketch: use the `HSpace` multiplication on loops based at `HSpace.e`, compare it with path
-- composition at the level of homotopy classes, and conclude by the Eckmann-Hilton argument.
theorem fundamentalGroup_mul_comm (a b : FundamentalGroup X HSpace.e) :
    a * b = b * a := by
  -- Translate the group law into path composition of loop classes and use commutativity there.
  change (b : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e).trans
      (a : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) =
    (a : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e).trans
      (b : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
  exact loop_trans_comm _ _

/-- The fundamental group at the unit of an `HSpace` is abelian. In particular, the fundamental
group of a topological group at the identity is abelian via `IsTopologicalGroup.hSpace`. -/
instance fundamentalGroup_commGroup : CommGroup (FundamentalGroup X HSpace.e) :=
  { (inferInstance : Group (FundamentalGroup X HSpace.e)) with
      mul_comm := fundamentalGroup_mul_comm }

end HSpace

section ContinuousMul

variable {G : Type u} [TopologicalSpace G] [MulOneClass G] [ContinuousMul G]

/-- Problem 1.8.3: for loops based at the unit of a topological space with continuous
multiplication, pointwise multiplication is homotopic to path composition. In particular, this
applies to topological groups via `IsTopologicalGroup.hSpace`. -/
-- Proof sketch: consider the square `(s, t) ↦ γ s * δ t`; its diagonal recovers the identity-loop
-- specialization of `Path.mul`, while its boundary yields a reparametrization of `γ.trans δ`.
theorem loop_pointwise_mul_homotopic_trans (γ δ : Path (1 : G) 1) :
    ((γ.mul δ).cast (one_mul (1 : G)).symm (one_mul (1 : G)).symm).Homotopic (γ.trans δ) := by
  letI : HSpace G := IsTopologicalGroup.toHSpace G
  -- Route correction: specialize the abstract `HSpace` comparison instead of building a second
  -- square homotopy directly in the concrete multiplication case.
  rw [← eq]
  simpa [loop_hmul_class, IsTopologicalGroup.toHSpace, mk_cast, mk_map, mk_trans] using
    loop_hmul_class_eq_trans (mk γ) (mk δ)

/-- Specialization of `fundamentalGroup_mul_comm` to a topological space with continuous
multiplication and unit, using the canonical `HSpace` structure `IsTopologicalGroup.toHSpace`. -/
theorem fundamentalGroup_mul_comm_of_continuousMul (a b : FundamentalGroup G (1 : G)) :
    a * b = b * a := by
  letI : HSpace G := IsTopologicalGroup.toHSpace G
  simpa using fundamentalGroup_mul_comm a b

end ContinuousMul
