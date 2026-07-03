import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_2
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3.SplitExactBridge

noncomputable section

open Module
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra Representation TensorProduct
open TensorProduct

universe u w

namespace Representation

section ProjectiveGrothendieckGroup

variable {A : Type u} [CommRing A]
variable {G : Type u} [Group G]

open scoped Representation
open scoped ZeroObject

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Corollary 14-14.4-3: a `k`-linear functional on a `k[G]`-module determines a
`k[G]`-linear map to the regular module by reading coefficients after translating the input. -/
noncomputable def reconstruct_from_coeff_one_module
    {M : Type w} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (L : M →ₗ[k] k) : M →ₗ[k[G]] k[G] := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  refine
    { toFun := fun m => Finsupp.equivFunOnFinite.symm fun t => L ((MonoidAlgebra.of k G t⁻¹) • m)
      map_add' := by
        intro x y
        apply Finsupp.equivFunOnFinite.injective
        funext t
        simp [smul_add, map_add]
      map_smul' := ?_ }
  intro a m
  let h : k[G] := Finsupp.equivFunOnFinite.symm fun t => L ((MonoidAlgebra.of k G t⁻¹) • m)
  apply Finsupp.equivFunOnFinite.injective
  funext t
  let P : k[G] → Prop := fun b => L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) = (b * h) t
  have hPa : P a := by
    refine MonoidAlgebra.induction_on a ?_ ?_ ?_
    · intro g
      have hsmul :
          MonoidAlgebra.single t⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m =
            (MonoidAlgebra.single (t⁻¹ * g) (1 : k) : k[G]) • m := by
        simpa using
          (smul_assoc (MonoidAlgebra.single t⁻¹ (1 : k)) (MonoidAlgebra.single g (1 : k)) m).symm
      -- Read the translated coefficient on the basis vector `g`.
      calc
        L ((MonoidAlgebra.of k G t⁻¹) • ((MonoidAlgebra.of k G g) • m)) =
            L (MonoidAlgebra.single t⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m) := by
              simp [MonoidAlgebra.of_apply]
        _ = L ((MonoidAlgebra.single (t⁻¹ * g) (1 : k) : k[G]) • m) := by
              exact congrArg L hsmul
        _ = (((MonoidAlgebra.of k G g) * h : k[G]) t) := by
              simp [h, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply]
    · intro b c hb hc
      -- Additivity of the functional matches additivity of the reconstructed regular-module map.
      calc
        L ((MonoidAlgebra.of k G t⁻¹) • ((b + c) • m)) =
            L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) +
              L ((MonoidAlgebra.of k G t⁻¹) • (c • m)) := by
                simp [add_smul, map_add]
        _ = (b * h) t + (c * h) t := by rw [hb, hc]
        _ = ((b + c) * h) t := by simp [add_mul]
    · intro r b hb
      -- Scalar multiples commute with the translated coefficient reconstruction.
      calc
        L ((MonoidAlgebra.of k G t⁻¹) • ((r • b) • m)) =
            r * L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by
              have hs :
                  (MonoidAlgebra.of k G t⁻¹) • ((r • b) • m) =
                    r • ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by
                calc
                  (MonoidAlgebra.of k G t⁻¹) • ((r • b) • m) =
                      (((MonoidAlgebra.of k G t⁻¹) * (r • b)) : k[G]) • m := by
                        simpa using
                          (smul_assoc (MonoidAlgebra.of k G t⁻¹) (r • b) m).symm
                  _ = (r • (((MonoidAlgebra.of k G t⁻¹) * b : k[G]))) • m := by
                        rw [mul_smul_comm]
                  _ = r • ((((MonoidAlgebra.of k G t⁻¹) * b : k[G])) • m) := by
                        simpa using
                          (smul_assoc r (((MonoidAlgebra.of k G t⁻¹) * b : k[G])) m)
                  _ = r • ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by
                        simpa [smul_eq_mul] using
                          congrArg (fun x : M => r • x) (smul_assoc (MonoidAlgebra.of k G t⁻¹) b m)
              calc
                L ((MonoidAlgebra.of k G t⁻¹) • ((r • b) • m)) =
                    L (r • ((MonoidAlgebra.of k G t⁻¹) • (b • m))) := by
                      exact congrArg L hs
                _ = r * L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by simp
        _ = r * (b * h) t := by rw [hb]
        _ = ((r • b) * h) t := by simp
  exact hPa

/-- Helper for Corollary 14-14.4-3: evaluating the reconstructed regular-module map at `t`
recovers the chosen translated coefficient. -/
@[simp] theorem reconstruct_from_coeff_one_module_apply
    {M : Type w} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (L : M →ₗ[k] k) (m : M) (t : G) :
    reconstruct_from_coeff_one_module (G := G) (M := M) L m t =
      L ((MonoidAlgebra.of k G t⁻¹) • m) :=
  rfl

/-- Helper for Corollary 14-14.4-3: a nontrivial finite `k[G]`-module admits a nonzero map to the
regular module `k[G]`. -/
theorem exists_nonzero_map_to_regular_of_nontrivial
    {M : Type w} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    [Module.Finite k M] [Nontrivial M] :
    ∃ φ : M →ₗ[k[G]] k[G], φ ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hrepr_ne : b.repr m ≠ 0 := by
    intro hrepr
    exact hm ((LinearEquiv.map_eq_zero_iff b.repr).1 hrepr)
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.1 hrepr_ne
  let L : M →ₗ[k] k := (Finsupp.lapply t).comp b.repr.toLinearMap
  let φ : M →ₗ[k[G]] k[G] := reconstruct_from_coeff_one_module (G := G) L
  refine ⟨φ, ?_⟩
  intro hφ
  have hφm : φ m = 0 := by
    simpa [hφ]
  have hLm' : L ((MonoidAlgebra.of k G (1 : G)⁻¹) • m) = 0 := by
    simpa [φ, reconstruct_from_coeff_one_module_apply] using
      congrArg (fun z : k[G] => z 1) hφm
  have hof_one : (MonoidAlgebra.of k G ((1 : G)⁻¹) : k[G]) = 1 := by
    ext g
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.one_def]
  have hsingle_one_smul : (MonoidAlgebra.single 1 (1 : k) : k[G]) • m = m := by
    simpa [MonoidAlgebra.one_def] using (one_smul k[G] m)
  have hLm : L m = 0 := by
    have hLm'' : L ((MonoidAlgebra.single 1 (1 : k) : k[G]) • m) = 0 := by
      simpa [hof_one, MonoidAlgebra.one_def] using hLm'
    simpa [hsingle_one_smul] using hLm''
  exact ht (by simpa [L] using hLm)

/-- Helper for Corollary 14-14.4-3: the reduced map induced by an owner morphism is naturally
`k[G]`-linear once the tensor-product reduction is viewed in the reduced group-algebra category. -/
noncomputable def reduction_precompose_groupAlgebraLinear
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X) :
    (k ⊗[A] E.V) →ₗ[k[G]] (k ⊗[A] X.V) := by
  let ebar := (e.hom.hom.hom.restrictScalars A).baseChange k
  refine
    { toFun := ebar
      map_add' := by
        intro x y
        simp [ebar]
      map_smul' := ?_ }
  intro a z
  refine MonoidAlgebra.induction_on (p := fun a =>
      ebar (a • z) = a • ebar z) a ?_ ?_ ?_
  · intro g
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [ebar]
    · intro c m
      -- Check equivariance first on pure tensors, then extend by additivity.
      have hsmul :
          MonoidAlgebra.of k G g • (c ⊗ₜ[A] m : k ⊗[A] E.V) =
            (c ⊗ₜ[A] (MonoidAlgebra.of A G g • m) : k ⊗[A] E.V) := by
        have hunit :
            c • (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • m)) : k ⊗[A] E.V) =
              c • (MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] m) : k ⊗[A] E.V)) := by
          congr 1
          simpa [MonoidAlgebra.of_apply] using
            (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
              (Λ := A) (G := G) (P := E.V) g m)
        calc
          MonoidAlgebra.of k G g • (c ⊗ₜ[A] m : k ⊗[A] E.V)
              = MonoidAlgebra.of k G g •
                  (c • (((1 : k) ⊗ₜ[A] m) : k ⊗[A] E.V)) := by
                    rw [TensorProduct.smul_tmul']
                    simp
          _ = c • (MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] m) : k ⊗[A] E.V)) := by
                rw [smul_comm]
          _ = c • (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • m)) : k ⊗[A] E.V) := by
                rw [hunit]
          _ = (c ⊗ₜ[A] (MonoidAlgebra.of A G g • m) : k ⊗[A] E.V) := by
                rw [TensorProduct.smul_tmul']
                simp
      calc
        ebar (MonoidAlgebra.of k G g • (c ⊗ₜ[A] m : k ⊗[A] E.V))
            = ebar (c ⊗ₜ[A] (MonoidAlgebra.of A G g • m) : k ⊗[A] E.V) := by
                rw [hsmul]
        _ = (c ⊗ₜ[A] (e.hom.hom.hom (MonoidAlgebra.of A G g • m)) : k ⊗[A] X.V) := by
              simp [ebar, LinearMap.baseChange_tmul]
        _ = (c ⊗ₜ[A] (MonoidAlgebra.of A G g • e.hom.hom.hom m) : k ⊗[A] X.V) := by
              congr 2
              exact e.hom.hom.hom.map_smul _ _
        _ = MonoidAlgebra.of k G g • (c ⊗ₜ[A] e.hom.hom.hom m : k ⊗[A] X.V) := by
              symm
              have hsmul' :
                  MonoidAlgebra.of k G g • (c ⊗ₜ[A] e.hom.hom.hom m : k ⊗[A] X.V) =
                    (c ⊗ₜ[A]
                      (MonoidAlgebra.of A G g • e.hom.hom.hom m) : k ⊗[A] X.V) := by
                have hunit' :
                    c • (((1 : k) ⊗ₜ[A]
                        (MonoidAlgebra.of A G g • e.hom.hom.hom m)) : k ⊗[A] X.V) =
                      c • (MonoidAlgebra.of k G g •
                        (((1 : k) ⊗ₜ[A] e.hom.hom.hom m) : k ⊗[A] X.V)) := by
                  congr 1
                  simpa [MonoidAlgebra.of_apply] using
                    (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
                      (Λ := A) (G := G) (P := X.V) g (e.hom.hom.hom m))
                calc
                  MonoidAlgebra.of k G g •
                      (c ⊗ₜ[A] e.hom.hom.hom m : k ⊗[A] X.V)
                      = MonoidAlgebra.of k G g •
                          (c • (((1 : k) ⊗ₜ[A] e.hom.hom.hom m) : k ⊗[A] X.V)) := by
                            rw [TensorProduct.smul_tmul']
                            simp
                  _ = c • (MonoidAlgebra.of k G g •
                        (((1 : k) ⊗ₜ[A] e.hom.hom.hom m) : k ⊗[A] X.V)) := by
                          rw [smul_comm]
                  _ = c • (((1 : k) ⊗ₜ[A]
                        (MonoidAlgebra.of A G g • e.hom.hom.hom m)) : k ⊗[A] X.V) := by
                          rw [hunit']
                  _ = (c ⊗ₜ[A]
                        (MonoidAlgebra.of A G g • e.hom.hom.hom m) : k ⊗[A] X.V) := by
                          rw [TensorProduct.smul_tmul']
                          simp
              rw [hsmul']
        _ = MonoidAlgebra.of k G g • ebar (c ⊗ₜ[A] m) := by
              simp [ebar, LinearMap.baseChange_tmul]
    · intro z w hz hw
      rw [smul_add, map_add, hz, hw, ← smul_add]
      simp [map_add]
  · intro b c hb hc
    rw [add_smul, map_add, hb, hc, add_smul]
  · intro r b hb
    rw [smul_assoc, map_smul, hb, smul_assoc]

/-- Helper for Corollary 14-14.4-3: precomposition by an owner morphism acts linearly on regular
probes into the regular owner. -/
def regular_probe_precompose_linear
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X) :
    (X.V →ₗ[A[G]] A[G]) →ₗ[A] (E.V →ₗ[A[G]] A[G]) where
  toFun g := g.comp e.hom.hom.hom
  map_add' := by
    intro g h
    rfl
  map_smul' := by
    intro a g
    rfl

/-- Helper for Corollary 14-14.4-3: the reduced precomposition map is the same construction after
passing to the residue-field reduction `k ⊗[A] -`. -/
def regular_probe_precompose_linear_reduced
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X) :
    ((k ⊗[A] X.V) →ₗ[k[G]] k[G]) →ₗ[k] ((k ⊗[A] E.V) →ₗ[k[G]] k[G]) where
  toFun gbar := gbar.comp (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)
  map_add' := by
    intro gbar hbar
    rfl
  map_smul' := by
    intro a gbar
    rfl

/-- Helper for Corollary 14-14.4-3: evaluating the owner precomposition map simply composes the
probe with the underlying owner linear map. -/
@[simp] theorem regular_probe_precompose_linear_apply
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (g : X.V →ₗ[A[G]] A[G]) :
    regular_probe_precompose_linear (A := A) (G := G) e g = g.comp e.hom.hom.hom :=
  rfl

/-- Helper for Corollary 14-14.4-3: evaluating the reduced precomposition map simply composes the
reduced probe with the reduced owner linear map. -/
@[simp] theorem regular_probe_precompose_linear_reduced_apply
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (gbar : (k ⊗[A] X.V) →ₗ[k[G]] k[G]) :
    regular_probe_precompose_linear_reduced (A := A) (G := G) e gbar =
      gbar.comp (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e) :=
  rfl

/-- Helper for Corollary 14-14.4-3: if `e` is epi in the owner category, then precomposition by
`e` has trivial kernel on owner regular probes. -/
theorem regular_probe_precompose_linear_ker_eq_bot
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X) [Epi e] :
    LinearMap.ker (regular_probe_precompose_linear (A := A) (G := G) e) = ⊥ := by
  apply LinearMap.ker_eq_bot.2
  intro g₁ g₂ hEq
  have hg :
      regular_probe_precompose_linear (A := A) (G := G) e (g₁ - g₂) = 0 := by
    ext x t
    have hx :=
      congrArg (fun f : E.V →ₗ[A[G]] A[G] => f x) hEq
    have hx0 : g₁ (e.hom.hom.hom x) - g₂ (e.hom.hom.hom x) = 0 := sub_eq_zero.mpr hx
    have hx' := congrArg (fun z : A[G] => z t) hx0
    simpa [regular_probe_precompose_linear, LinearMap.sub_apply, LinearMap.comp_apply] using hx'
  let g : X.V →ₗ[A[G]] A[G] := g₁ - g₂
  let gMor : X ⟶ finiteProjective_regular_owner (A := A) (G := G) :=
    ObjectProperty.homMk (FGModuleCat.ofHom g)
  have hge : e ≫ gMor = 0 := by
    -- The kernel condition is exactly the vanishing of the composite owner morphism.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x t
    have hx' := congrArg (fun z : A[G] => z t) (LinearMap.congr_fun hg x)
    simpa [g, gMor, FGModuleCat.ofHom, regular_probe_precompose_linear, LinearMap.comp_apply] using
      hx'
  have hgMor_zero : gMor = 0 := by
    exact (cancel_epi e).1 (by simpa using hge)
  have hg_hom_zero : gMor.hom = 0 := by
    simpa using congrArg (fun f : X ⟶ finiteProjective_regular_owner (A := A) (G := G) ↦ f.hom)
      hgMor_zero
  rw [show gMor = ObjectProperty.homMk (FGModuleCat.ofHom g) by rfl] at hg_hom_zero
  have hg_zero : g = 0 := by
    apply LinearMap.ext
    intro x
    have h0 :=
      congrArg
        (fun f : X.obj ⟶ (finiteProjective_regular_owner (A := A) (G := G)).obj ↦ f.hom.hom x)
        hg_hom_zero
    simpa [g, FGModuleCat.ofHom, LinearMap.sub_apply] using h0
  exact sub_eq_zero.mp hg_zero

omit [IsLocalRing A] [Finite G] in
/-- Helper for Corollary 14-14.4-3: a monomorphism in the finite-projective owner category is
injective on the forgotten underlying `A[G]`-linear map. -/
theorem finiteProjective_underlying_injective_of_mono
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G)) (hS : S.ShortExact) :
    Function.Injective S.f.hom.hom := by
  intro x y hxy
  let ψ : finiteProjective_regular_owner (A := A) (G := G) ⟶ S.X₁ :=
    ObjectProperty.homMk
      (FGModuleCat.ofHom ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight (x - y)))
  have hψ_zero_lin :
      S.f.hom.hom.hom.comp ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight (x - y)) = 0 := by
    ext
    simp [hxy]
  have hψ_zero : ψ ≫ S.f = 0 := by
    -- Repackage the vanishing composite as an equality in the owner category.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    simpa [ψ, FGModuleCat.ofHom] using hψ_zero_lin
  letI : Mono S.f := hS.mono_f
  have hψ_eq_zero : ψ = 0 := by
    exact (cancel_mono S.f).1 (by simpa using hψ_zero)
  have hEval := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.hom) hψ_eq_zero) 1
  have hEval' :
      (ConcreteCategory.hom
          (FGModuleCat.ofHom ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight (x - y))).hom) 1 =
        0 := by
    -- Read the vanishing owner morphism at the regular-module generator `1`.
    simpa [ψ] using hEval
  have hEval'' :
      ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight (x - y)) 1 = 0 := by
    have hψ_eval :
        (ConcreteCategory.hom
            (FGModuleCat.ofHom
              ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight (x - y))).hom) 1 =
          ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight (x - y)) 1 := rfl
    exact hψ_eval.symm.trans hEval'
  have hdiff : x - y = 0 := by
    simpa [regular_module_generated_map_apply_one (A := A) (G := G) (x := x - y)] using hEval''
  exact sub_eq_zero.mp hdiff

/-- Helper for Corollary 14-14.4-3: an epimorphism in the finite-projective owner category should
already be surjective on the forgotten underlying `A[G]`-linear map. -/
theorem finiteProjective_underlying_tensor_range_top_of_reduction_surjective
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (hred :
      Function.Surjective ((e.hom.hom.hom.restrictScalars A).baseChange k)) :
    Submodule.map (TensorProduct.mk A k X.V 1)
      (LinearMap.range (e.hom.hom.hom.restrictScalars A)) = ⊤ := by
  -- Route correction: work in the canonical tensor-product reduction `k ⊗[A] -`, not in the
  -- quotient model `X / 𝔪X`, so the final lift back uses `IsLocalRing.map_tensorProduct_mk_eq_top`.
  apply top_unique
  intro z hz
  rcases hred z with ⟨w, hw⟩
  rcases TensorProduct.mk_surjective (R := A) (M := E.V) (S := k)
    Ideal.Quotient.mk_surjective w with ⟨y, hy⟩
  -- Choose a lift of the reduced source vector and rewrite the reduced image through base change.
  refine Submodule.mem_map.2 ?_
  refine ⟨e.hom.hom.hom y, ?_, ?_⟩
  · exact ⟨y, rfl⟩
  · change (TensorProduct.mk A k X.V 1) (e.hom.hom.hom y) = z
    calc
      (TensorProduct.mk A k X.V 1) (e.hom.hom.hom y)
          = ((e.hom.hom.hom.restrictScalars A).baseChange k) ((1 : k) ⊗ₜ[A] y) := by
              simp [LinearMap.baseChange_tmul]
      _ = ((e.hom.hom.hom.restrictScalars A).baseChange k) w := by
            simpa using congrArg ((e.hom.hom.hom.restrictScalars A).baseChange k) hy
      _ = z := hw

/-- Helper for Corollary 14-14.4-3: once the induced map on residue-field reductions is
surjective, local Nakayama upgrades the original map to a surjection. -/
theorem finiteProjective_underlying_surjective_of_reduction_surjective
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (hred :
      Function.Surjective ((e.hom.hom.hom.restrictScalars A).baseChange k)) :
    Function.Surjective e.hom.hom.hom := by
  have hmap :
      Submodule.map (TensorProduct.mk A k X.V 1)
        (LinearMap.range (e.hom.hom.hom.restrictScalars A)) = ⊤ :=
    finiteProjective_underlying_tensor_range_top_of_reduction_surjective
      (A := A) (G := G) e hred
  -- Nakayama identifies `range(e) = ⊤` from the fact that its reduction already fills `k ⊗ X`.
  have hrangeA : LinearMap.range (e.hom.hom.hom.restrictScalars A) = ⊤ := by
    exact
      (IsLocalRing.map_tensorProduct_mk_eq_top
        (R := A) (M := X.V) (N := LinearMap.range (e.hom.hom.hom.restrictScalars A))).1 hmap
  have hsurjA : Function.Surjective (e.hom.hom.hom.restrictScalars A) :=
    LinearMap.range_eq_top.1 hrangeA
  simpa using hsurjA

/-- Helper for Corollary 14-14.4-3: coefficientwise reduction on `A[G]` is the basis linear
combination map for the canonical `k[G]` basis indexed by `G`. -/
theorem groupAlgebra_reduction_eq_basis_linearCombination :
    (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
        A[G] →ₗ[A] k[G])) =
      Finsupp.linearCombination A (fun g : G => (MonoidAlgebra.basis G k) g) := by
  -- Compare the two `A`-linear maps on the canonical basis of `A[G]`.
  apply (MonoidAlgebra.basis G A).ext
  intro g
  rw [MonoidAlgebra.basis_apply]
  change
    (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
        A[G] →ₗ[A] k[G]) (Finsupp.single g (1 : A))) =
      (Finsupp.linearCombination A (fun g' : G => (MonoidAlgebra.basis G k) g'))
        (Finsupp.single g (1 : A))
  rw [Finsupp.linearCombination_single, MonoidAlgebra.basis_apply]
  simp [MonoidAlgebra.mapAlgHom_single, IsLocalRing.ResidueField.algebraMap_eq]

/-- Helper for Corollary 14-14.4-3: coefficientwise reduction `A[G] → k[G]` is itself a
residue-field base change. -/
theorem groupAlgebra_reduction_isBaseChange :
    IsBaseChange k
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
          A[G] →ₗ[A] k[G])) := by
  -- Rewrite the reduction map through the canonical `k[G]` basis, then apply the generic basis
  -- criterion for base change.
  rw [groupAlgebra_reduction_eq_basis_linearCombination (A := A) (G := G)]
  exact IsBaseChange.of_basis (A := A) (MonoidAlgebra.basis G k)

/-- Helper for Corollary 14-14.4-3: coefficientwise reduction `A[G] → k[G]` is surjective on the
underlying modules. -/
theorem groupAlgebra_reduction_surjective :
    Function.Surjective
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
          A[G] →ₗ[A] k[G])) := by
  -- The coefficientwise reduction map is a residue-field base change, so every element of `k[G]`
  -- comes from a pure tensor `1 ⊗ x` and hence from an actual element of `A[G]`.
  intro x
  obtain ⟨t, rfl⟩ := (groupAlgebra_reduction_isBaseChange (A := A) (G := G)).equiv.surjective x
  have hres :
      Function.Surjective (algebraMap A k) := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
  obtain ⟨y, hy⟩ := TensorProduct.mk_surjective
    (R := A) (S := k) (M := A[G]) hres t
  refine ⟨y, ?_⟩
  calc
    (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
        A[G] →ₗ[A] k[G])) y
        = (1 : k) •
            (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
                A[G] →ₗ[A] k[G])) y := by simp
    _ = (groupAlgebra_reduction_isBaseChange (A := A) (G := G)).equiv
          ((TensorProduct.mk A k A[G] 1) y) := by
            symm
            simpa using
              (groupAlgebra_reduction_isBaseChange (A := A) (G := G)).equiv_tmul (1 : k) y
    _ = (groupAlgebra_reduction_isBaseChange (A := A) (G := G)).equiv t := by rw [hy]

/-- Helper for Corollary 14-14.4-3: every reduced probe into the regular `k[G]`-module lifts to
an actual `A[G]`-linear map into the regular `A[G]`-module. -/
theorem lift_regular_probe_to_regular_owner
    {X : FiniteProjectiveGroupAlgebraModule A G}
    (gbar : (k ⊗[A] X.V) →ₗ[k[G]] k[G]) :
    ∃ g : X.V →ₗ[A[G]] A[G],
      ∀ x,
        (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
            A[G] →ₗ[A] k[G]) (g x)) =
          gbar ((TensorProduct.mk A k X.V 1) x) := by
  letI : Module A[G] (k ⊗[A] X.V) :=
    Module.compHom (k ⊗[A] X.V)
      (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toRingHom
  letI : IsScalarTower A A[G] (k ⊗[A] X.V) :=
    IsScalarTower.of_algebraMap_smul fun c z ↦ by
      change
        (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k))
            (MonoidAlgebra.single (1 : G) c) • z =
          c • z
      rw [MonoidAlgebra.mapAlgHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap k k[G] (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • z
            = (IsLocalRing.residue A c) • z := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) z)
        _ = c • z := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k c z)
  letI : Module A[G] k[G] :=
    Module.compHom k[G]
      (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toRingHom
  letI : IsScalarTower A A[G] k[G] :=
    IsScalarTower.of_algebraMap_smul fun c z ↦ by
      change
        (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k))
            (MonoidAlgebra.single (1 : G) c) • z =
          c • z
      rw [MonoidAlgebra.mapAlgHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap k k[G] (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • z
            = (IsLocalRing.residue A c) • z := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) z)
        _ = c • z := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k c z)
  let redGA : A[G] →ₗ[A[G]] k[G] :=
    { toFun := (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k))
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro a x
        change
          (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)) (a * x) =
            (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)) a *
              (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)) x
        simp }
  let fXGA : X.V →ₗ[A[G]] (k ⊗[A] X.V) :=
    { toFun := TensorProduct.mk A k X.V 1
      map_add' := by
        intro x y
        exact TensorProduct.tmul_add _ _ _
      map_smul' := by
        intro a x
        refine MonoidAlgebra.induction_on
          (p := fun b : A[G] =>
            (TensorProduct.mk A k X.V 1) (b • x) = b • (TensorProduct.mk A k X.V 1 x)) a ?_ ?_ ?_
        · intro s
          change
            (TensorProduct.mk A k X.V 1) (MonoidAlgebra.of A G s • x) =
              (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k) (MonoidAlgebra.of A G s)) •
                (TensorProduct.mk A k X.V 1 x)
          simpa [MonoidAlgebra.of_apply] using
            (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
              (Λ := A) (G := G) (P := X.V) s x)
        · intro b c hb hc
          calc
            (TensorProduct.mk A k X.V 1) ((b + c) • x)
                = (TensorProduct.mk A k X.V 1) (b • x + c • x) := by rw [add_smul]
            _ = (TensorProduct.mk A k X.V 1) (b • x) +
                  (TensorProduct.mk A k X.V 1) (c • x) := by
                simpa using
                  (TensorProduct.tmul_add (R := A) (1 : k) (b • x) (c • x))
            _ = b • (TensorProduct.mk A k X.V 1 x) +
                  c • (TensorProduct.mk A k X.V 1 x) := by rw [hb, hc]
            _ = (b + c) • (TensorProduct.mk A k X.V 1 x) := by rw [add_smul]
        · intro r b hb
          calc
            (TensorProduct.mk A k X.V 1) ((r • b) • x)
                = (TensorProduct.mk A k X.V 1) (r • (b • x)) := by
                    rw [smul_assoc]
            _ = r • (TensorProduct.mk A k X.V 1) (b • x) := by
                  simp
            _ = r • (b • (TensorProduct.mk A k X.V 1) x) := by rw [hb]
            _ = (r • b) • (TensorProduct.mk A k X.V 1) x := by
                  rw [smul_assoc] }
  let gbarGA : (k ⊗[A] X.V) →ₗ[A[G]] k[G] :=
    { toFun := gbar
      map_add' := gbar.map_add
      map_smul' := by
        intro a x
        change
          gbar ((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)) a • x) =
            (MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)) a • gbar x
        simpa using
          gbar.map_smul ((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)) a) x }
  have hsurj : Function.Surjective redGA := by
    simpa [redGA] using groupAlgebra_reduction_surjective (A := A) (G := G)
  -- Lift the reduced probe across the surjective reduction map on the regular module.
  obtain ⟨g, hg⟩ := Module.projective_lifting_property redGA (gbarGA.comp fXGA) hsurj
  refine ⟨g, ?_⟩
  -- Forget back to `A`-linearity: the lifted map reduces to the original probe on `1 ⊗ x`.
  intro x
  change redGA (g x) = gbarGA (fXGA x)
  exact LinearMap.congr_fun hg x

/-- Helper for Corollary 14-14.4-3: once an `A`-linear lift into the regular module has the
correct reduction, averaging it with a LinearRepresentations_Serre_1977 endomorphism preserves that reduction identity. -/
theorem averaged_regular_probe_preserves_reduction
    [Fintype G]
    {X : FiniteProjectiveGroupAlgebraModule A G}
    (gbar : (k ⊗[A] X.V) →ₗ[k[G]] k[G]) (ℓ : X.V →ₗ[A] A[G]) (u : Module.End A X.V)
    (hu : u.sumOfConjugates G = LinearMap.id)
    (hred : ∀ x,
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
          A[G] →ₗ[A] k[G]) (ℓ x)) =
        gbar ((TensorProduct.mk A k X.V 1) x)) :
    ∀ x,
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
          A[G] →ₗ[A] k[G]) (((ℓ.comp u).sumOfConjugatesEquivariant G) x)) =
        gbar ((TensorProduct.mk A k X.V 1) x) := by
  intro x
  -- Evaluate the averaged lift termwise, then move the equivariant maps `red` and `gbar`
  -- through the conjugation sum.
  calc
    (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
        A[G] →ₗ[A] k[G]) (((ℓ.comp u).sumOfConjugatesEquivariant G) x))
        = ∑ g : G,
            (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
                A[G] →ₗ[A] k[G]) ((ℓ.comp u).conjugate g x)) := by
              rw [LinearMap.sumOfConjugatesEquivariant_apply]
              simp
    _ = ∑ g : G, gbar ((TensorProduct.mk A k X.V 1) ((u.conjugate g) x)) := by
          refine Finset.sum_congr rfl ?_
          intro g _
          calc
            (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
                A[G] →ₗ[A] k[G]) ((ℓ.comp u).conjugate g x))
                = (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
                    A[G] →ₗ[A] k[G])
                    (MonoidAlgebra.single g⁻¹ (1 : A) • ℓ (u (MonoidAlgebra.single g (1 : A) • x)))) := by
                      rfl
            _ = MonoidAlgebra.single g⁻¹ (1 : k) •
                  (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
                      A[G] →ₗ[A] k[G]) (ℓ (u (MonoidAlgebra.single g (1 : A) • x)))) := by
                      simp [MonoidAlgebra.mapAlgHom_single]
            _ = MonoidAlgebra.single g⁻¹ (1 : k) •
                  gbar ((TensorProduct.mk A k X.V 1) (u (MonoidAlgebra.single g (1 : A) • x))) := by
                      rw [hred]
            _ = gbar
                  (MonoidAlgebra.single g⁻¹ (1 : k) •
                    ((TensorProduct.mk A k X.V 1) (u (MonoidAlgebra.single g (1 : A) • x)))) := by
                      symm
                      exact gbar.map_smul (MonoidAlgebra.single g⁻¹ (1 : k)) _
            _ = gbar
                  ((TensorProduct.mk A k X.V 1)
                    (MonoidAlgebra.single g⁻¹ (1 : A) •
                      u (MonoidAlgebra.single g (1 : A) • x))) := by
                      congr 1
                      simpa [MonoidAlgebra.of_apply] using
                        (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
                          (Λ := A) (G := G) (P := X.V) g⁻¹
                          (u (MonoidAlgebra.single g (1 : A) • x))).symm
            _ = gbar ((TensorProduct.mk A k X.V 1) ((u.conjugate g) x)) := by
                      rw [LinearMap.conjugate_apply]
    _ = gbar
          (∑ g : G, (TensorProduct.mk A k X.V 1) ((u.conjugate g) x)) := by
            symm
            rw [map_sum]
    _ = gbar ((TensorProduct.mk A k X.V 1) (∑ g : G, (u.conjugate g) x)) := by
          congr 1
          symm
          rw [map_sum]
    _ = gbar ((TensorProduct.mk A k X.V 1) ((u.sumOfConjugates G) x)) := by
          rw [LinearMap.sumOfConjugates_apply]
    _ = gbar ((TensorProduct.mk A k X.V 1) x) := by
          simpa [hu]

/-- Helper for Corollary 14-14.4-3: a reduced regular probe in the reduced precomposition kernel
factors through the actual reduced cokernel of `e`. -/
theorem reduced_regular_probe_factor_through_precompose_cokernel
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (gbar : (k ⊗[A] X.V) →ₗ[k[G]] k[G])
    (hker :
      gbar.comp (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e) = 0) :
    ∃ η :
        ((k ⊗[A] X.V) ⧸
          LinearMap.range (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)) →ₗ[k[G]]
          k[G],
      gbar =
        η.comp
          (LinearMap.range
            (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ := by
  let ebar : (k ⊗[A] E.V) →ₗ[k[G]] (k ⊗[A] X.V) :=
    reduction_precompose_groupAlgebraLinear (A := A) (G := G) e
  have hrange_ker : LinearMap.range ebar ≤ LinearMap.ker gbar := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    -- Evaluate the kernel hypothesis on a representative of the reduced image.
    simpa [LinearMap.mem_ker, ebar, LinearMap.comp_apply] using
      LinearMap.congr_fun hker x
  let η :
      (k ⊗[A] X.V) ⧸ LinearMap.range ebar →ₗ[k[G]] k[G] :=
    (LinearMap.range ebar).liftQ gbar hrange_ker
  refine ⟨η, ?_⟩
  -- The quotient descent is characterized by its values on quotient classes.
  ext x
  simpa [η, ebar, LinearMap.comp_apply] using
    (Submodule.liftQ_apply (p := LinearMap.range ebar) (f := gbar) (x := x))

/-- Helper for Corollary 14-14.4-3: the reduced cokernel of `e` admits a projective envelope, and
the reduced quotient map from `k ⊗ X` lifts to that projective cover. -/
theorem reduced_precompose_cokernel_projective_cover_data
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X) :
    ∃ (Pbar : ModuleCat k[G])
      (πbar :
        Pbar ⟶
          ModuleCat.of k[G]
            ((k ⊗[A] X.V) ⧸
              LinearMap.range (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)))
      (σbar : ModuleCat.of k[G] (k ⊗[A] X.V) ⟶ Pbar),
      πbar.hom.IsProjectiveEnvelope ∧
        πbar.hom.comp σbar.hom =
          (LinearMap.range
            (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ := by
  let ebar : (k ⊗[A] E.V) →ₗ[k[G]] (k ⊗[A] X.V) :=
    reduction_precompose_groupAlgebraLinear (A := A) (G := G) e
  let Qbar : ModuleCat k[G] :=
    ModuleCat.of k[G] ((k ⊗[A] X.V) ⧸ LinearMap.range ebar)
  let qbar : ModuleCat.of k[G] (k ⊗[A] X.V) ⟶ Qbar :=
    ModuleCat.ofHom (LinearMap.range ebar).mkQ
  obtain ⟨Pbar, πbar, hπbar⟩ := exists_isProjectiveEnvelope (M := Qbar)
  let XbarOwner : FiniteProjectiveGroupAlgebraModule k G := X.residueFieldReduction
  have hXbar_projective : Module.Projective k[G] (k ⊗[A] X.V) := by
    -- The intrinsic residue-field reduction of `X` is already projective over `k[G]`.
    simpa [XbarOwner, FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using
      (show Module.Projective k[G] XbarOwner.V from inferInstance)
  let _ : Module.Projective k[G] (ModuleCat.of k[G] (k ⊗[A] X.V)) := hXbar_projective
  obtain ⟨σbar, hσbar⟩ :=
    Module.projective_lifting_property πbar.hom qbar.hom hπbar.surjective
  refine ⟨Pbar, πbar, ModuleCat.ofHom σbar, hπbar, ?_⟩
  -- Record the lifted quotient map in the linear-map form used by the main proof.
  simpa [qbar] using hσbar

/-- Helper for Corollary 14-14.4-3: tensoring an `A[G]`-linear map with the residue field carries
the group action to the reduced group algebra. -/
noncomputable def baseChange_groupAlgebraLinear
    {M : Type w} [AddCommGroup M] [Module A M] [Module A[G] M] [IsScalarTower A A[G] M]
    {N : Type w} [AddCommGroup N] [Module A N] [Module A[G] N] [IsScalarTower A A[G] N]
    (f : M →ₗ[A[G]] N) :
    (k ⊗[A] M) →ₗ[k[G]] (k ⊗[A] N) := by
  let fbar := (f.restrictScalars A).baseChange k
  refine
    { toFun := fbar
      map_add' := by
        intro x y
        simp [fbar]
      map_smul' := ?_ }
  intro a z
  refine MonoidAlgebra.induction_on (p := fun a =>
      fbar (a • z) = a • fbar z) a ?_ ?_ ?_
  · intro g
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [fbar]
    · intro c m
      -- Check equivariance on pure tensors, then extend additively.
      have hsmul :
          MonoidAlgebra.of k G g • (c ⊗ₜ[A] m : k ⊗[A] M) =
            (c ⊗ₜ[A] (MonoidAlgebra.of A G g • m) : k ⊗[A] M) := by
        have hunit :
            c • (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • m)) : k ⊗[A] M) =
              c • (MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] m) : k ⊗[A] M)) := by
          congr 1
          simpa [MonoidAlgebra.of_apply] using
            (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
              (Λ := A) (G := G) (P := M) g m)
        calc
          MonoidAlgebra.of k G g • (c ⊗ₜ[A] m : k ⊗[A] M)
              = MonoidAlgebra.of k G g •
                  (c • (((1 : k) ⊗ₜ[A] m) : k ⊗[A] M)) := by
                    rw [TensorProduct.smul_tmul']
                    simp
          _ = c • (MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] m) : k ⊗[A] M)) := by
                rw [smul_comm]
          _ = c • (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • m)) : k ⊗[A] M) := by
                rw [hunit]
          _ = (c ⊗ₜ[A] (MonoidAlgebra.of A G g • m) : k ⊗[A] M) := by
                rw [TensorProduct.smul_tmul']
                simp
      calc
        fbar (MonoidAlgebra.of k G g • (c ⊗ₜ[A] m : k ⊗[A] M))
            = fbar (c ⊗ₜ[A] (MonoidAlgebra.of A G g • m) : k ⊗[A] M) := by
                rw [hsmul]
        _ = (c ⊗ₜ[A] (f (MonoidAlgebra.of A G g • m)) : k ⊗[A] N) := by
              simp [fbar, LinearMap.baseChange_tmul]
        _ = (c ⊗ₜ[A] (MonoidAlgebra.of A G g • f m) : k ⊗[A] N) := by
              congr 2
              exact f.map_smul _ _
        _ = MonoidAlgebra.of k G g • (c ⊗ₜ[A] f m : k ⊗[A] N) := by
              symm
              have hsmul' :
                  MonoidAlgebra.of k G g • (c ⊗ₜ[A] f m : k ⊗[A] N) =
                    (c ⊗ₜ[A] (MonoidAlgebra.of A G g • f m) : k ⊗[A] N) := by
                have hunit' :
                    c • (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • f m)) : k ⊗[A] N) =
                      c • (MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] f m) : k ⊗[A] N)) := by
                  congr 1
                  simpa [MonoidAlgebra.of_apply] using
                    (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
                      (Λ := A) (G := G) (P := N) g (f m))
                calc
                  MonoidAlgebra.of k G g • (c ⊗ₜ[A] f m : k ⊗[A] N)
                      = MonoidAlgebra.of k G g •
                          (c • (((1 : k) ⊗ₜ[A] f m) : k ⊗[A] N)) := by
                            rw [TensorProduct.smul_tmul']
                            simp
                  _ = c • (MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] f m) : k ⊗[A] N)) := by
                        rw [smul_comm]
                  _ = c • (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • f m)) : k ⊗[A] N) := by
                        rw [hunit']
                  _ = (c ⊗ₜ[A] (MonoidAlgebra.of A G g • f m) : k ⊗[A] N) := by
                        rw [TensorProduct.smul_tmul']
                        simp
              rw [hsmul']
        _ = MonoidAlgebra.of k G g • fbar (c ⊗ₜ[A] m) := by
              simp [fbar, LinearMap.baseChange_tmul]
    · intro z w hz hw
      rw [smul_add, map_add, hz, hw, ← smul_add]
      simp [map_add]
  · intro b c hb hc
    rw [add_smul, map_add, hb, hc, add_smul]
  · intro r b hb
    rw [smul_assoc, map_smul, hb, smul_assoc]

/-- Helper for Corollary 14-14.4-3: on pure tensors, the reduced base change of an
`A[G]`-linear map is given by applying the map to the tensor factor. -/
@[simp] theorem baseChange_groupAlgebraLinear_tmul
    {M : Type w} [AddCommGroup M] [Module A M] [Module A[G] M] [IsScalarTower A A[G] M]
    {N : Type w} [AddCommGroup N] [Module A N] [Module A[G] N] [IsScalarTower A A[G] N]
    (f : M →ₗ[A[G]] N) (c : k) (m : M) :
    baseChange_groupAlgebraLinear (A := A) (G := G) f (c ⊗ₜ[A] m) = c ⊗ₜ[A] f m := by
  -- The definition was built from the ordinary base-change map.
  simp [baseChange_groupAlgebraLinear, LinearMap.baseChange_tmul]

/-- Helper for Corollary 14-14.4-3: tensoring the actual cokernel `X / range(e)` with `k`
produces a canonical quotient of the reduced module `k ⊗ X`. -/
theorem actual_cokernel_reduction_comparison_local
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X) :
    ∃ cmp :
        ((k ⊗[A] X.V) ⧸
          LinearMap.range (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)) →ₗ[k[G]]
          (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)),
      cmp.comp
          (LinearMap.range
            (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ =
        baseChange_groupAlgebraLinear (A := A) (G := G)
          ((LinearMap.range e.hom.hom.hom).mkQ) := by
  let ebar : (k ⊗[A] E.V) →ₗ[k[G]] (k ⊗[A] X.V) :=
    reduction_precompose_groupAlgebraLinear (A := A) (G := G) e
  let qA : X.V →ₗ[A[G]] (X.V ⧸ LinearMap.range e.hom.hom.hom) :=
    (LinearMap.range e.hom.hom.hom).mkQ
  let qAred :
      (k ⊗[A] X.V) →ₗ[k[G]] (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)) :=
    baseChange_groupAlgebraLinear (A := A) (G := G) qA
  have hrange_ker : LinearMap.range ebar ≤ LinearMap.ker qAred := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    -- The actual quotient map kills the image of `e`, so its reduction kills the reduced image.
    change qAred (ebar x) = 0
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [ebar, qAred]
    · intro c m
      have hqA_zero : qA (e.hom.hom.hom m) = 0 := by
        simpa [qA, LinearMap.comp_apply] using
          LinearMap.congr_fun (LinearMap.range_mkQ_comp e.hom.hom.hom) m
      -- Evaluate both reduction maps on the pure tensor `c ⊗ e m`.
      change qAred (c ⊗ₜ[A] e.hom.hom.hom m) = 0
      rw [baseChange_groupAlgebraLinear_tmul]
      simp [hqA_zero]
    · intro z w hz hw
      -- Additivity reduces the kernel claim to the two inductive hypotheses.
      rw [map_add, map_add, hz, hw, add_zero]
  let cmp :
      ((k ⊗[A] X.V) ⧸ LinearMap.range ebar) →ₗ[k[G]]
        (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)) :=
    (LinearMap.range ebar).liftQ qAred hrange_ker
  refine ⟨cmp, ?_⟩
  -- Descend the reduced actual quotient map through the reduced cokernel of `e`.
  ext x
  simpa [cmp, ebar, qAred, qA, LinearMap.comp_apply] using
    (Submodule.liftQ_apply
      (p := LinearMap.range ebar) (f := qAred) (h := hrange_ker) (x := x))

/-- Helper for Corollary 14-14.4-3: tensoring the cokernel pair
`E.V ⟶ X.V ⟶ X.V ⧸ range(e)` with `k` is right exact, so the forward comparison from the reduced
quotient to `k ⊗ (X.V ⧸ range(e))` is in fact a `k[G]`-linear equivalence. -/
theorem actual_cokernel_reduction_linearEquiv_local
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X) :
    ∃ cmp :
      (((k ⊗[A] X.V) ⧸
        LinearMap.range (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)) ≃ₗ[k[G]]
        (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom))),
      cmp.toLinearMap.comp
          (LinearMap.range
            (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ =
        baseChange_groupAlgebraLinear (A := A) (G := G)
          ((LinearMap.range e.hom.hom.hom).mkQ) := by
  obtain ⟨cmp, hcmp⟩ :=
    actual_cokernel_reduction_comparison_local (A := A) (G := G) e
  let eA : E.V →ₗ[A] X.V := e.hom.hom.hom.restrictScalars A
  let qA : X.V →ₗ[A] X.V ⧸ LinearMap.range eA := (LinearMap.range eA).mkQ
  have hExact : Function.Exact eA ((LinearMap.range eA).mkQ) := by
    rw [LinearMap.exact_iff]
    ext y
    constructor
    · intro hy
      simpa [LinearMap.mem_ker] using hy
    · intro hy
      simpa [LinearMap.mem_ker] using hy
  have hSurj : Function.Surjective ((LinearMap.range eA).mkQ) :=
    Submodule.mkQ_surjective (LinearMap.range eA)
  let cmpA := lTensor.equiv (R := A) (Q := k) (f := eA) (g := qA) hExact hSurj
  have hEqFun :
      (fun x => cmp x) = fun x => cmpA x := by
    -- Both maps are the canonical descent of `qAred`, so it suffices to compare them on quotient
    -- representatives.
    funext x
    obtain ⟨y, rfl⟩ :=
      Submodule.mkQ_surjective
        (LinearMap.range (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)) x
    calc
      cmp
          ((LinearMap.range
            (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ y) =
          baseChange_groupAlgebraLinear (A := A) (G := G)
            ((LinearMap.range e.hom.hom.hom).mkQ) y := by
              simpa [LinearMap.comp_apply] using
                congrArg
                  (fun f : (k ⊗[A] X.V) →ₗ[k[G]] (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)) =>
                    f y)
                  hcmp
      _ =
          cmpA
            ((LinearMap.range
              (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ y) := by
                have hcmpA_apply :
                    cmpA
                        ((LinearMap.range
                          (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ y) =
                      baseChange_groupAlgebraLinear (A := A) (G := G)
                        ((LinearMap.range e.hom.hom.hom).mkQ) y := by
                          rfl
                symm
                exact hcmpA_apply
  have hBij : Function.Bijective cmp := by
    simpa [hEqFun] using cmpA.bijective
  refine ⟨LinearEquiv.ofBijective cmp hBij, ?_⟩
  exact hcmp

/-- Helper for Corollary 14-14.4-3: after identifying the reduced quotient with the reduction of
the actual cokernel, the given reduced projective cover transports to a projective envelope of
`k ⊗ (X.V ⧸ range(e))`, and the chosen reduced lift still factors the actual quotient map. -/
theorem transport_projective_cover_to_actual_cokernel_local
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (Pbar : ModuleCat k[G])
    (πbar :
      Pbar ⟶
        ModuleCat.of k[G]
          ((k ⊗[A] X.V) ⧸
            LinearMap.range (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)))
    (hπbar : πbar.hom.IsProjectiveEnvelope)
    (σbar : ModuleCat.of k[G] (k ⊗[A] X.V) ⟶ Pbar)
    (hσbar :
      πbar.hom.comp σbar.hom =
        (LinearMap.range
          (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ) :
    ∃ πCbar : Pbar →ₗ[k[G]] (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)),
      πCbar.IsProjectiveEnvelope ∧
        πCbar.comp σbar.hom =
          baseChange_groupAlgebraLinear (A := A) (G := G)
            ((LinearMap.range e.hom.hom.hom).mkQ) := by
  obtain ⟨cmp, hcmp⟩ :=
    actual_cokernel_reduction_linearEquiv_local (A := A) (G := G) e
  let πCbar : Pbar →ₗ[k[G]] (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)) :=
    cmp.toLinearMap.comp πbar.hom
  refine ⟨πCbar, ?_, ?_⟩
  · -- Conjugating the target of a projective envelope by a linear equivalence preserves the
    -- projective-envelope structure.
    simpa [πCbar, LinearMap.comp_assoc] using
      (LinearMap.isProjectiveEnvelope_iff_conj
        (R := k[G])
        (eP := LinearEquiv.refl k[G] Pbar)
        (eM := cmp)
        (f := πbar.hom)).2 hπbar
  · -- The transported cover still factors the reduced actual quotient map.
    calc
      πCbar.comp σbar.hom = cmp.toLinearMap.comp (πbar.hom.comp σbar.hom) := by
        simp [πCbar, LinearMap.comp_assoc]
      _ = cmp.toLinearMap.comp
          (LinearMap.range
            (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ := by
              rw [hσbar]
      _ = baseChange_groupAlgebraLinear (A := A) (G := G)
          ((LinearMap.range e.hom.hom.hom).mkQ) := hcmp

/-- Helper for Corollary 14-14.4-3: an essential quotient map forces any lift with surjective
composite to be surjective itself. -/
theorem surjective_of_comp_surjective_of_isEssential_local
    {R : Type u} [Semiring R]
    {X : Type w} [AddCommMonoid X] [Module R X]
    {P : Type w} [AddCommMonoid P] [Module R P]
    {M : Type w} [AddCommMonoid M] [Module R M]
    {π : P →ₗ[R] M} (hπ : π.IsEssential)
    {σ : X →ₗ[R] P} (hcomp_surj : Function.Surjective (π.comp σ)) :
    Function.Surjective σ := by
  have hmap : (LinearMap.range σ).map π = ⊤ := by
    -- The image of `range σ` under `π` is the range of `π ∘ σ`, which is all of `M`.
    rw [← LinearMap.range_comp]
    exact LinearMap.range_eq_top.2 hcomp_surj
  -- Essentiality upgrades surjectivity on the image to surjectivity on the whole source.
  exact LinearMap.range_eq_top.1 (hπ.eq_top_of_map_eq_top _ hmap)

/-- Helper for Corollary 14-14.4-3: the transported reduced lift `σbar` of the actual quotient
map is surjective because the transported projective envelope is essential and the reduced actual
quotient map is surjective. -/
theorem transported_projective_cover_lift_surjective_local
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (Pbar : ModuleCat k[G])
    (πCbar : Pbar →ₗ[k[G]] (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)))
    (hπCbar : πCbar.IsProjectiveEnvelope)
    (σbar : ModuleCat.of k[G] (k ⊗[A] X.V) ⟶ Pbar)
    (hσCbar :
      πCbar.comp σbar.hom =
        baseChange_groupAlgebraLinear (A := A) (G := G)
          ((LinearMap.range e.hom.hom.hom).mkQ)) :
    Function.Surjective σbar.hom := by
  have hqAred_surj :
      Function.Surjective
        (baseChange_groupAlgebraLinear (A := A) (G := G)
          ((LinearMap.range e.hom.hom.hom).mkQ)) := by
    obtain ⟨cmp, hcmp⟩ :=
      actual_cokernel_reduction_linearEquiv_local (A := A) (G := G) e
    intro y
    obtain ⟨z, rfl⟩ := cmp.surjective y
    obtain ⟨x, rfl⟩ :=
      Submodule.mkQ_surjective
        (LinearMap.range
          (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)) z
    -- Rewrite the reduced actual quotient map through the comparison equivalence.
    refine ⟨x, ?_⟩
    have hx :=
      congrArg
        (fun f :
          (k ⊗[A] X.V) →ₗ[k[G]] (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)) =>
            f x)
        hcmp
    simpa [LinearMap.comp_apply]
      using hx.symm
  have hcomp_surj : Function.Surjective (πCbar.comp σbar.hom) := by
    -- Replace the composite by the reduced actual quotient map and use its surjectivity.
    simpa [hσCbar] using hqAred_surj
  exact
    surjective_of_comp_surjective_of_isEssential_local
      (hπ := hπCbar.toIsEssential) hcomp_surj

/-- Helper for Corollary 14-14.4-3: an endomorphism of a projective envelope fixing the quotient
map is automatically bijective. -/
theorem projective_envelope_endomorphism_bijective_local
    {Mbar : Type w} [AddCommGroup Mbar] [Module k[G] Mbar]
    {Pbar : Type w} [AddCommGroup Pbar] [Module k[G] Pbar]
    {π : Pbar →ₗ[k[G]] Mbar} (hπ : π.IsProjectiveEnvelope)
    {u : Pbar →ₗ[k[G]] Pbar} (hu : π.comp u = π) :
    Function.Bijective u := by
  -- This is the self-envelope specialization of the uniqueness theorem for lifts between
  -- projective envelopes.
  exact LinearMap.lift_between_projective_envelopes_bijective hπ hπ hu

/-- Helper for Corollary 14-14.4-3: once the reduced precomposition-kernel factorization
`η : Q̄ → k[G]` is transported across the actual-cokernel comparison equivalence, the reduced
probe factors through the actual reduced quotient `k ⊗ (X.V ⧸ range(e))`. -/
theorem reduced_probe_factor_through_actual_cokernel_local
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (η :
      ((k ⊗[A] X.V) ⧸
        LinearMap.range (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)) →ₗ[k[G]]
        k[G]) :
    ∃ ηC : (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)) →ₗ[k[G]] k[G],
      ηC.comp
          (baseChange_groupAlgebraLinear (A := A) (G := G)
            ((LinearMap.range e.hom.hom.hom).mkQ)) =
        η.comp
          (LinearMap.range
            (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ := by
  obtain ⟨cmp, hcmp⟩ :=
    actual_cokernel_reduction_linearEquiv_local (A := A) (G := G) e
  let ηC : (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)) →ₗ[k[G]] k[G] :=
    η.comp cmp.symm.toLinearMap
  refine ⟨ηC, ?_⟩
  -- Move the quotient factorization through the comparison equivalence and simplify `cmp⁻¹ ∘ cmp`.
  have hcmp_symm :
      cmp.symm.toLinearMap.comp
          (baseChange_groupAlgebraLinear (A := A) (G := G)
            ((LinearMap.range e.hom.hom.hom).mkQ)) =
        (LinearMap.range
          (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ := by
    calc
      cmp.symm.toLinearMap.comp
          (baseChange_groupAlgebraLinear (A := A) (G := G)
            ((LinearMap.range e.hom.hom.hom).mkQ)) =
          cmp.symm.toLinearMap.comp
            (cmp.toLinearMap.comp
              (LinearMap.range
                (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ) := by
              rw [hcmp]
      _ =
          (cmp.symm.toLinearMap.comp cmp.toLinearMap).comp
            (LinearMap.range
              (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ := by
                rw [LinearMap.comp_assoc]
      _ =
          (LinearMap.range
            (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ := by
              simp
  calc
    ηC.comp
        (baseChange_groupAlgebraLinear (A := A) (G := G)
          ((LinearMap.range e.hom.hom.hom).mkQ)) =
      η.comp
        (cmp.symm.toLinearMap.comp
          (baseChange_groupAlgebraLinear (A := A) (G := G)
            ((LinearMap.range e.hom.hom.hom).mkQ))) := by
              simp [ηC, LinearMap.comp_assoc]
    _ = η.comp
        (LinearMap.range
          (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ := by
            rw [hcmp_symm]


/-- Helper for Corollary 14-14.4-3: after replacing the reduced cokernel by a projective cover,
the remaining source-faithful step is to lift that cover map upstairs and correct it into the
actual precomposition kernel. -/
theorem lift_projective_cover_map_in_precompose_kernel_local
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (Pbar : ModuleCat k[G])
    (πbar :
      Pbar ⟶
        ModuleCat.of k[G]
          ((k ⊗[A] X.V) ⧸
            LinearMap.range (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)))
    (hπbar : πbar.hom.IsProjectiveEnvelope)
    (σbar : ModuleCat.of k[G] (k ⊗[A] X.V) ⟶ Pbar)
    (hσbar :
      πbar.hom.comp σbar.hom =
        (LinearMap.range
          (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ) :
    ∃ (P : FiniteProjectiveGroupAlgebraModule A G)
      (eP : (k ⊗[A] P.V) ≃ₗ[k[G]] Pbar)
      (πCbar : Pbar →ₗ[k[G]] (k ⊗[A] (X.V ⧸ LinearMap.range e.hom.hom.hom)))
      (σ : X.V →ₗ[A[G]] P.V),
      πCbar.IsProjectiveEnvelope ∧
        πCbar.comp σbar.hom =
          baseChange_groupAlgebraLinear (A := A) (G := G)
            ((LinearMap.range e.hom.hom.hom).mkQ) ∧
        (∀ x,
          πCbar (eP ((TensorProduct.mk A k P.V 1) (σ x))) =
            (baseChange_groupAlgebraLinear (A := A) (G := G)
              ((LinearMap.range e.hom.hom.hom).mkQ))
              ((TensorProduct.mk A k X.V 1) x)) ∧
        σ.comp e.hom.hom.hom = 0 := by
  admit
end ProjectiveGrothendieckGroup

end Representation
