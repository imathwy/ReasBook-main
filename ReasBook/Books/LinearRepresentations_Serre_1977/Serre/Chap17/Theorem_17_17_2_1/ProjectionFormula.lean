import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra
open scoped Representation
open scoped TensorProduct
open scoped ZeroObject

namespace Representation

section
/-!
Helper lemmas toward the projection formula `Ind[H] a * y = Ind[H](a * Res[H] y)` on `R₀[k]`,
used in Serre's proof of Theorem 39 (Theorem 17-17.2-1).

This file currently contains the iso-invariance of the Grothendieck class; the full projection
formula additionally requires the representation-level projection-formula isomorphism
`Ind_H(V) ⊗ W ≅ Ind_H(V ⊗ Res_H W)`.
-/

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

/-- Isomorphic finite-dimensional representations have the same Grothendieck class in `R₀[k](G)`. -/
theorem finiteRepGrothendieckClass_eq_of_iso {V W : FDRep k G} (e : V ≅ W) :
    [V]₀ = [W]₀ := by
  -- The short exact sequence `0 → V →(e) W → 0 → 0` gives `[W]₀ = [V]₀ + [0]₀`.
  let S : ShortComplex (FDRep k G) :=
    ShortComplex.mk e.hom (0 : W ⟶ (0 : FDRep k G)) (by simp)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · -- Exact at `W`: the image of the iso `e.hom` is all of `W = ker (W → 0)`.
      exact (S.exact_iff_epi rfl).2 inferInstance
    · -- `e.hom` is a monomorphism since `e` is an isomorphism.
      exact inferInstance
    · -- The map `W → 0` is an epimorphism.
      exact inferInstance
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := G) S hS
  -- `hrelation : [W]₀ = [V]₀ + [0]₀`; simplify `[0]₀ = 0`.
  simpa [S, finiteRepGrothendieckClass_zero (L := k) (G := G)] using hrelation.symm

end

section ProjectionFormulaIso

open Representation TensorProduct Finsupp

variable {k : Type u} [CommRing k] {G : Type u} [Group G] (S : Subgroup G)
  (A : Rep k S) (B : Rep k G)

/-- The induced `G`-representation `Ind_S^G(A ⊗ Res_S B)` that is the codomain of the
projection-formula isomorphism `Ind_S^G(A) ⊗ B ≅ Ind_S^G(A ⊗ Res_S B)`. -/
local notation "AB" => MonoidalCategory.tensorObj A (Rep.res S.subtype B)

/-- Per-`g` bilinear core of the projection-formula forward map:
`a, b ↦ ⟦g ⊗ (a ⊗ ρ_B(g) b)⟧`. -/
noncomputable def projFwdCore (g : G) :
    A.V →ₗ[k] B.V →ₗ[k] Representation.IndV S.subtype (AB).ρ :=
  ((TensorProduct.mk k A.V (Rep.res S.subtype B).V).compl₂ (B.ρ g)).compr₂
    (Representation.IndV.mk S.subtype (AB).ρ g)

-- Proof sketch: the diagonal `G`-action of `s ∈ S` on `k[G] ⊗ (A ⊗ Res_S B)` sends the generator
-- `⟦g ⊗ (a ⊗ ρ_B(g) b)⟧` to `⟦(s·g) ⊗ (ρ_A(s) a ⊗ ρ_B(s·g) b)⟧`; computed factor by factor via
-- `tprod_apply` (kept cheap by working with the `tprod` form of `(A ⊗ Res B).ρ`).
set_option backward.isDefEq.respectTransparency false in
/-- Helper for the projection formula: the `S`-action transports the projection-formula generator
in the source of the induced coinvariants. -/
private lemma projFwd_action (s : S) (g : G) (a : A.V) (b : B.V) :
    (tprod ((leftRegular k G).comp S.subtype) (AB).ρ) s
        (Finsupp.single g (1 : k) ⊗ₜ[k] (a ⊗ₜ[k] B.ρ g b))
      = Finsupp.single ((s : G) * g) (1 : k) ⊗ₜ[k] (A.ρ s a ⊗ₜ[k] B.ρ ((s : G) * g) b) := by
  rw [tprod_apply, TensorProduct.map_tmul]
  congr 1
  · simp [MonoidHom.comp_apply, ofMulAction_single, Subgroup.subtype_apply]
  · show (A.ρ.tprod (Rep.res S.subtype B).ρ) s (a ⊗ₜ[k] B.ρ g b) = _
    rw [tprod_apply, TensorProduct.map_tmul]
    congr 1
    rw [Rep.coe_res_obj_ρ', ← Module.End.mul_apply, ← map_mul, Subgroup.subtype_apply]

-- Proof sketch: unfold `IndV.mk` to the coinvariants class, rewrite the transported generator
-- through `projFwd_action`, then collapse by the defining coinvariance relation
-- `Coinvariants.mk_self_apply`.
set_option backward.isDefEq.respectTransparency false in
/-- Helper for the projection formula: the two induced generators that appear in the
well-definedness of the forward map agree as coinvariant classes. -/
private lemma projFwd_mk_eq (s : S) (g : G) (a : A.V) (b : B.V) :
    Representation.IndV.mk S.subtype (AB).ρ ((s : G) * g) (A.ρ s a ⊗ₜ[k] B.ρ ((s : G) * g) b)
      = Representation.IndV.mk S.subtype (AB).ρ g (a ⊗ₜ[k] B.ρ g b) := by
  rw [show Representation.IndV.mk S.subtype (AB).ρ ((s : G) * g)
          (A.ρ s a ⊗ₜ[k] B.ρ ((s : G) * g) b)
        = Coinvariants.mk _
            (Finsupp.single ((s : G) * g) (1 : k) ⊗ₜ[k] (A.ρ s a ⊗ₜ[k] B.ρ ((s : G) * g) b))
        from rfl,
      ← projFwd_action S A B s g a b,
      show Representation.IndV.mk S.subtype (AB).ρ g (a ⊗ₜ[k] B.ρ g b)
        = Coinvariants.mk _ (Finsupp.single g (1 : k) ⊗ₜ[k] (a ⊗ₜ[k] B.ρ g b)) from rfl]
  exact Coinvariants.mk_self_apply _ s _

-- Proof sketch: assemble the forward map `⟦g ⊗ a⟧ ⊗ b ↦ ⟦g ⊗ (a ⊗ ρ_B(g) b)⟧` by layered lifts
-- (`Finsupp.lift` over `k[G]`, two `TensorProduct.lift`, one `Coinvariants.lift`); the
-- coinvariance side-condition reduces, on generators, to `projFwd_mk_eq`.
set_option backward.isDefEq.respectTransparency false in
/-- Underlying `k`-linear forward map of the projection-formula isomorphism
`Ind_S^G(A) ⊗ B → Ind_S^G(A ⊗ Res_S B)`, `⟦g ⊗ a⟧ ⊗ b ↦ ⟦g ⊗ (a ⊗ ρ_B(g) b)⟧`. -/
noncomputable def projFwdLin :
    (Rep.ind S.subtype A).V ⊗[k] B.V →ₗ[k] Representation.IndV S.subtype (AB).ρ :=
  TensorProduct.lift
    (Representation.Coinvariants.lift _
      (TensorProduct.lift (Finsupp.lift _ _ _ (projFwdCore S A B)))
      (by
        intro s
        refine TensorProduct.ext' fun x a => ?_
        refine LinearMap.ext fun b => ?_
        induction x using Finsupp.induction_linear with
        | zero =>
            simp only [TensorProduct.zero_tmul, map_zero, LinearMap.zero_apply]
        | add x y hx hy =>
            simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hx, hy]
        | single g c =>
            rw [LinearMap.comp_apply,
              show (tprod ((leftRegular k G).comp S.subtype) A.ρ) s
                    (Finsupp.single g c ⊗ₜ[k] a)
                  = Finsupp.single ((s : G) * g) c ⊗ₜ[k] A.ρ s a from by
                rw [tprod_apply, TensorProduct.map_tmul]; congr 1
                simp [MonoidHom.comp_apply, ofMulAction_single, Subgroup.subtype_apply]]
            simp only [TensorProduct.lift.tmul, Finsupp.lift_apply, Finsupp.sum_single_index,
              zero_smul, LinearMap.smul_apply, projFwdCore, LinearMap.compr₂_apply,
              LinearMap.compl₂_apply, TensorProduct.mk_apply]
            congr 1
            exact projFwd_mk_eq S A B s g a b))

/-- Per-`g` bilinear core of the projection-formula inverse map:
`a, b ↦ ⟦g ⊗ a⟧ ⊗ ρ_B(g⁻¹) b`. -/
noncomputable def projInvCore (g : G) :
    A.V →ₗ[k] (Rep.res S.subtype B).V →ₗ[k] (Rep.ind S.subtype A).V ⊗[k] B.V :=
  ((TensorProduct.mk k (Rep.ind S.subtype A).V B.V).comp
      (Representation.IndV.mk S.subtype A.ρ g)).compl₂
    (show (Rep.res S.subtype B).V →ₗ[k] B.V from B.ρ g⁻¹)

@[simp] lemma projInvCore_apply (g : G) (a : A.V) (b : (Rep.res S.subtype B).V) :
    projInvCore S A B g a b
      = Representation.IndV.mk S.subtype A.ρ g a ⊗ₜ[k] B.ρ g⁻¹ b := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Helper for the projection formula (inverse): the `S`-action on the `A`-induced coinvariants
source transports `⟦g ⊗ a⟧`. -/
private lemma projInv_A_action (s : S) (g : G) (a : A.V) :
    (tprod ((leftRegular k G).comp S.subtype) A.ρ) s (Finsupp.single g (1 : k) ⊗ₜ[k] a)
      = Finsupp.single ((s : G) * g) (1 : k) ⊗ₜ[k] A.ρ s a := by
  rw [tprod_apply, TensorProduct.map_tmul]; congr 1
  simp [MonoidHom.comp_apply, ofMulAction_single, Subgroup.subtype_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for the projection formula (inverse): `A`-induction coinvariance. -/
private lemma projInv_A_coinv (s : S) (g : G) (a : A.V) :
    Representation.IndV.mk S.subtype A.ρ ((s : G) * g) (A.ρ s a)
      = Representation.IndV.mk S.subtype A.ρ g a := by
  rw [show Representation.IndV.mk S.subtype A.ρ ((s : G) * g) (A.ρ s a)
        = Coinvariants.mk _ (Finsupp.single ((s : G) * g) (1 : k) ⊗ₜ[k] A.ρ s a) from rfl,
      ← projInv_A_action S A s g a,
      show Representation.IndV.mk S.subtype A.ρ g a
        = Coinvariants.mk _ (Finsupp.single g (1 : k) ⊗ₜ[k] a) from rfl]
  exact Coinvariants.mk_self_apply _ s _

/-- Helper for the projection formula (inverse): the `B`-factor transport identity. -/
private lemma projInv_B (s : S) (g : G) (b : (Rep.res S.subtype B).V) :
    B.ρ (((s : G) * g)⁻¹) ((Rep.res S.subtype B).ρ s b) = B.ρ g⁻¹ b := by
  rw [Rep.coe_res_obj_ρ', Subgroup.subtype_apply, ← Module.End.mul_apply, ← map_mul]
  congr 2; group

set_option backward.isDefEq.respectTransparency false in
/-- Helper for the projection formula (inverse): the `S`-action transports the generator in the
source of `Ind_S^G(A ⊗ Res_S B)`. -/
private lemma projAB_action (s : S) (g : G) (c : k) (a : A.V) (b : (Rep.res S.subtype B).V) :
    (tprod ((leftRegular k G).comp S.subtype) (AB).ρ) s (Finsupp.single g c ⊗ₜ[k] (a ⊗ₜ[k] b))
      = Finsupp.single ((s : G) * g) c ⊗ₜ[k]
          (A.ρ s a ⊗ₜ[k] (Rep.res S.subtype B).ρ s b) := by
  rw [tprod_apply, TensorProduct.map_tmul]; congr 1
  simp [MonoidHom.comp_apply, ofMulAction_single, Subgroup.subtype_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Underlying `k`-linear inverse map of the projection-formula isomorphism
`Ind_S^G(A ⊗ Res_S B) → Ind_S^G(A) ⊗ B`, `⟦g ⊗ (a ⊗ b)⟧ ↦ ⟦g ⊗ a⟧ ⊗ ρ_B(g⁻¹) b`. -/
noncomputable def projInvLin :
    Representation.IndV S.subtype (AB).ρ →ₗ[k] (Rep.ind S.subtype A).V ⊗[k] B.V :=
  Representation.Coinvariants.lift _
    (TensorProduct.lift (Finsupp.lift _ _ _ (fun g => TensorProduct.lift (projInvCore S A B g))))
    (by
      intro s
      refine TensorProduct.ext' fun x y => ?_
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add x1 x2 hx1 hx2 => simp only [TensorProduct.add_tmul, map_add, hx1, hx2]
      | single g c =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add y1 y2 hy1 hy2 => simp only [TensorProduct.tmul_add, map_add, hy1, hy2]
          | tmul a b =>
              rw [LinearMap.comp_apply, projAB_action S A B s g c a b]
              simp only [TensorProduct.lift.tmul, Finsupp.lift_apply, Finsupp.sum_single_index,
                zero_smul, LinearMap.smul_apply]
              erw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
              erw [projInvCore_apply, projInvCore_apply]
              rw [projInv_A_coinv S A s g a, projInv_B S B s g b])

set_option backward.isDefEq.respectTransparency false in
/-- The projection-formula forward map on a generator `⟦g ⊗ a⟧ ⊗ b`. -/
lemma projFwdLin_apply (g : G) (a : A.V) (b : B.V) :
    projFwdLin S A B (Representation.IndV.mk S.subtype A.ρ g a ⊗ₜ[k] b)
      = Representation.IndV.mk S.subtype (AB).ρ g (a ⊗ₜ[k] B.ρ g b) := by
  rw [projFwdLin, TensorProduct.lift.tmul,
    show Representation.IndV.mk S.subtype A.ρ g a
        = Coinvariants.mk _ (Finsupp.single g (1 : k) ⊗ₜ[k] a) from rfl,
    Coinvariants.lift_mk]
  simp only [TensorProduct.lift.tmul, Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul,
    one_smul, projFwdCore, LinearMap.compr₂_apply, LinearMap.compl₂_apply, TensorProduct.mk_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The projection-formula inverse map on a generator `⟦g ⊗ (a ⊗ b)⟧`. -/
lemma projInvLin_apply (g : G) (a : A.V) (b : (Rep.res S.subtype B).V) :
    projInvLin S A B (Representation.IndV.mk S.subtype (AB).ρ g (a ⊗ₜ[k] b))
      = Representation.IndV.mk S.subtype A.ρ g a ⊗ₜ[k] B.ρ g⁻¹ b := by
  rw [projInvLin,
    show Representation.IndV.mk S.subtype (AB).ρ g (a ⊗ₜ[k] b)
        = Coinvariants.mk _ (Finsupp.single g (1 : k) ⊗ₜ[k] (a ⊗ₜ[k] b)) from rfl]
  erw [Coinvariants.lift_mk]
  simp only [TensorProduct.lift.tmul, Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul,
    one_smul]
  erw [TensorProduct.lift.tmul]
  exact projInvCore_apply S A B g a b

/-- Helper: a coinvariant class of `single g c ⊗ a` is `c • ⟦g ⊗ a⟧`. -/
private lemma mk_single_smul (g : G) (c : k) (a : A.V) :
    Coinvariants.mk (tprod ((leftRegular k G).comp S.subtype) A.ρ)
        (Finsupp.single g c ⊗ₜ[k] a)
      = c • Representation.IndV.mk S.subtype A.ρ g a := by
  rw [show (Finsupp.single g c : G →₀ k) = c • Finsupp.single g (1 : k) from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul', map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The projection-formula inverse is a left inverse of the forward map. -/
lemma projInv_projFwd (x : (Rep.ind S.subtype A).V ⊗[k] B.V) :
    projInvLin S A B (projFwdLin S A B x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul u b' =>
    induction u using Coinvariants.induction_on with
    | _ v =>
      induction v using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.zero_tmul]
      | add v1 v2 hv1 hv2 =>
          rw [map_add, TensorProduct.add_tmul, map_add, map_add, hv1, hv2]
      | tmul fg a =>
          induction fg using Finsupp.induction_linear with
          | zero => simp only [map_zero, TensorProduct.zero_tmul]
          | add f1 f2 hf1 hf2 =>
              rw [TensorProduct.add_tmul, map_add, TensorProduct.add_tmul,
                map_add, map_add, hf1, hf2]
          | single g c =>
              rw [mk_single_smul, ← TensorProduct.smul_tmul', map_smul, map_smul,
                projFwdLin_apply, projInvLin_apply]
              congr 2
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                Module.End.one_apply]

/-- Helper: a coinvariant class of `single g c ⊗ w` in `Ind_S^G(A ⊗ Res_S B)` is `c • ⟦g ⊗ w⟧`. -/
private lemma mk_single_smul_AB (g : G) (c : k) (w : (AB).V) :
    Coinvariants.mk (tprod ((leftRegular k G).comp S.subtype) (AB).ρ)
        (Finsupp.single g c ⊗ₜ[k] w)
      = c • Representation.IndV.mk S.subtype (AB).ρ g w := by
  rw [show (Finsupp.single g c : G →₀ k) = c • Finsupp.single g (1 : k) from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul', map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The projection-formula inverse is a right inverse of the forward map. -/
lemma projFwd_projInv (y : Representation.IndV S.subtype (AB).ρ) :
    projFwdLin S A B (projInvLin S A B y) = y := by
  induction y using Coinvariants.induction_on with
  | _ v =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add v1 v2 hv1 hv2 => simp only [map_add, hv1, hv2]
    | tmul fg w =>
        induction fg using Finsupp.induction_linear with
        | zero => simp only [TensorProduct.zero_tmul, map_zero]
        | add f1 f2 hf1 hf2 => simp only [TensorProduct.add_tmul, map_add, hf1, hf2]
        | single g c =>
            induction w using TensorProduct.induction_on with
            | zero => simp only [TensorProduct.tmul_zero, map_zero]
            | add w1 w2 hw1 hw2 => simp only [TensorProduct.tmul_add, map_add, hw1, hw2]
            | tmul a b =>
                rw [mk_single_smul_AB, map_smul, map_smul, projInvLin_apply, projFwdLin_apply]
                congr 2
                rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
                  Module.End.one_apply]

/-- The projection-formula isomorphism `Ind_S^G(A) ⊗ B ≃ₗ Ind_S^G(A ⊗ Res_S B)` as a
`k`-linear equivalence. -/
noncomputable def projLinearEquiv :
    ((Rep.ind S.subtype A).V ⊗[k] B.V) ≃ₗ[k] Representation.IndV S.subtype (AB).ρ :=
  LinearEquiv.ofLinear (projFwdLin S A B) (projInvLin S A B)
    (LinearMap.ext fun y => projFwd_projInv S A B y)
    (LinearMap.ext fun x => projInv_projFwd S A B x)

set_option backward.isDefEq.respectTransparency false in
/-- Helper: `G`-equivariance of the projection-formula forward map on a generator. -/
private lemma projFwd_equivariant_gen (g g₀ : G) (a : A.V) (b' : B.V) :
    projFwdLin S A B ((MonoidalCategory.tensorObj (Rep.ind S.subtype A) B).ρ g
        (Representation.IndV.mk S.subtype A.ρ g₀ a ⊗ₜ[k] b'))
      = (Rep.ind S.subtype AB).ρ g
          (projFwdLin S A B (Representation.IndV.mk S.subtype A.ρ g₀ a ⊗ₜ[k] b')) := by
  have hdom : (MonoidalCategory.tensorObj (Rep.ind S.subtype A) B).ρ g
        (Representation.IndV.mk S.subtype A.ρ g₀ a ⊗ₜ[k] b')
      = Representation.IndV.mk S.subtype A.ρ (g₀ * g⁻¹) a ⊗ₜ[k] B.ρ g b' := by
    rw [Rep.tensor_ρ]; erw [Representation.tprod_apply, TensorProduct.map_tmul]
    rw [Representation.ind_mk]
  rw [hdom, projFwdLin_apply, projFwdLin_apply]
  erw [Representation.ind_mk]
  congr 2
  rw [← Module.End.mul_apply, ← map_mul]; congr 2; group

set_option backward.isDefEq.respectTransparency false in
/-- The projection-formula forward map is `G`-equivariant. -/
lemma projFwd_equivariant (g : G) (x : (Rep.ind S.subtype A).V ⊗[k] B.V) :
    projFwdLin S A B ((MonoidalCategory.tensorObj (Rep.ind S.subtype A) B).ρ g x)
      = (Rep.ind S.subtype AB).ρ g (projFwdLin S A B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul u b' =>
    induction u using Coinvariants.induction_on with
    | _ v =>
      induction v using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.zero_tmul]
      | add v1 v2 hv1 hv2 => simp only [map_add, TensorProduct.add_tmul, hv1, hv2]
      | tmul fg a =>
          induction fg using Finsupp.induction_linear with
          | zero => simp only [map_zero, TensorProduct.zero_tmul]
          | add f1 f2 hf1 hf2 => simp only [map_add, TensorProduct.add_tmul, hf1, hf2]
          | single g₀ c =>
              rw [mk_single_smul, ← TensorProduct.smul_tmul']
              simp only [map_smul]
              rw [projFwd_equivariant_gen]

/-- The projection-formula isomorphism as an equivalence of `G`-representations. -/
noncomputable def projRepEquiv :
    (MonoidalCategory.tensorObj (Rep.ind S.subtype A) B).ρ.Equiv (Rep.ind S.subtype AB).ρ :=
  Representation.Equiv.mk (projLinearEquiv S A B) (fun g => by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, projLinearEquiv,
      LinearEquiv.ofLinear_apply]
    exact projFwd_equivariant S A B g x)

/-- The projection-formula isomorphism `Ind_S^G(A) ⊗ B ≅ Ind_S^G(A ⊗ Res_S B)` in `Rep k G`. -/
noncomputable def projRepIso :
    Rep.of (MonoidalCategory.tensorObj (Rep.ind S.subtype A) B).ρ ≅
      Rep.of (Rep.ind S.subtype AB).ρ :=
  Rep.mkIso (projRepEquiv S A B)

end ProjectionFormulaIso

end Representation
