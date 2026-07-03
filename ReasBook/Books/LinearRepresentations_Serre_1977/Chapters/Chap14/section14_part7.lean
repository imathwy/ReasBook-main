import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_14_14_4_3 (from Chap14) -/
noncomputable section

open Module
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra Representation TensorProduct

universe u w

namespace Representation

section ProjectiveGrothendieckGroup

local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

variable {A : Type u} [CommRing A]
variable {G : Type u} [Group G]

open scoped Representation
open scoped ZeroObject

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Corollary 14-14.4-3: a nontrivial finite `K[G]`-module over a field admits a
nonzero map to the regular module `K[G]`. -/
private theorem exists_nonzero_map_to_regular_of_nontrivial_field
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    {M : Type w} [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M]
    [Module.Finite K M] [Nontrivial M] :
    ∃ φ : M →ₗ[K[G]] K[G], φ ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis K M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hrepr_ne : b.repr m ≠ 0 := by
    intro hrepr
    exact hm ((LinearEquiv.map_eq_zero_iff b.repr).1 hrepr)
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.1 hrepr_ne
  let L : M →ₗ[K] K := (Finsupp.lapply t).comp b.repr.toLinearMap
  let φ : M →ₗ[K[G]] K[G] := by
    letI : Fintype G := Fintype.ofFinite G
    refine
      { toFun := fun m' =>
          Finsupp.equivFunOnFinite.symm fun s => L ((MonoidAlgebra.of K G s⁻¹) • m')
        map_add' := by
          intro x y
          apply Finsupp.equivFunOnFinite.injective
          funext s
          simp [smul_add, map_add]
        map_smul' := ?_ }
    intro a m'
    let h : K[G] := Finsupp.equivFunOnFinite.symm fun s => L ((MonoidAlgebra.of K G s⁻¹) • m')
    apply Finsupp.equivFunOnFinite.injective
    funext s
    let P : K[G] → Prop := fun b =>
      L ((MonoidAlgebra.of K G s⁻¹) • (b • m')) = (b * h) s
    have hPa : P a := by
      refine MonoidAlgebra.induction_on a ?_ ?_ ?_
      · intro g
        have hsmul :
            MonoidAlgebra.single s⁻¹ (1 : K) • MonoidAlgebra.single g (1 : K) • m' =
              (MonoidAlgebra.single (s⁻¹ * g) (1 : K) : K[G]) • m' := by
          simpa using
            (smul_assoc (MonoidAlgebra.single s⁻¹ (1 : K))
              (MonoidAlgebra.single g (1 : K)) m').symm
        calc
          L ((MonoidAlgebra.of K G s⁻¹) • ((MonoidAlgebra.of K G g) • m')) =
              L (MonoidAlgebra.single s⁻¹ (1 : K) • MonoidAlgebra.single g (1 : K) • m') := by
                simp [MonoidAlgebra.of_apply]
          _ = L ((MonoidAlgebra.single (s⁻¹ * g) (1 : K) : K[G]) • m') := by
                exact congrArg L hsmul
          _ = (((MonoidAlgebra.of K G g) * h : K[G]) s) := by
                simp [h, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply]
      · intro b c hb hc
        calc
          L ((MonoidAlgebra.of K G s⁻¹) • ((b + c) • m')) =
              L ((MonoidAlgebra.of K G s⁻¹) • (b • m')) +
                L ((MonoidAlgebra.of K G s⁻¹) • (c • m')) := by
                  simp [add_smul, map_add]
          _ = (b * h) s + (c * h) s := by rw [hb, hc]
          _ = ((b + c) * h) s := by simp [add_mul]
      · intro r b hb
        calc
          L ((MonoidAlgebra.of K G s⁻¹) • ((r • b) • m')) =
              r * L ((MonoidAlgebra.of K G s⁻¹) • (b • m')) := by
                have hs :
                    (MonoidAlgebra.of K G s⁻¹) • ((r • b) • m') =
                      r • ((MonoidAlgebra.of K G s⁻¹) • (b • m')) := by
                  calc
                    (MonoidAlgebra.of K G s⁻¹) • ((r • b) • m') =
                        (((MonoidAlgebra.of K G s⁻¹) * (r • b)) : K[G]) • m' := by
                          simpa using
                            (smul_assoc (MonoidAlgebra.of K G s⁻¹) (r • b) m').symm
                    _ = (r • (((MonoidAlgebra.of K G s⁻¹) * b : K[G]))) • m' := by
                          rw [mul_smul_comm]
                    _ = r • ((((MonoidAlgebra.of K G s⁻¹) * b : K[G])) • m') := by
                          rw [smul_assoc]
                    _ = r • ((MonoidAlgebra.of K G s⁻¹) • (b • m')) := by
                          simpa [smul_eq_mul] using
                            congrArg (fun x : M => r • x)
                              (smul_assoc (MonoidAlgebra.of K G s⁻¹) b m')
                calc
                  L ((MonoidAlgebra.of K G s⁻¹) • ((r • b) • m')) =
                      L (r • ((MonoidAlgebra.of K G s⁻¹) • (b • m'))) := by
                        exact congrArg L hs
                  _ = r * L ((MonoidAlgebra.of K G s⁻¹) • (b • m')) := by simp
          _ = r * (b * h) s := by rw [hb]
          _ = ((r • b) * h) s := by simp
    exact hPa
  refine ⟨φ, ?_⟩
  intro hφ
  have hφm : φ m = 0 := by
    simp [hφ]
  have hLm' : L ((MonoidAlgebra.of K G (1 : G)⁻¹) • m) = 0 := by
    simpa [φ] using
      congrArg (fun z : K[G] => z 1) hφm
  have hsingle_one_smul : (MonoidAlgebra.single 1 (1 : K) : K[G]) • m = m := by
    simpa [MonoidAlgebra.one_def] using (one_smul K[G] m)
  have hLm : L m = 0 := by
    have hLm_single : L ((MonoidAlgebra.single 1 (1 : K) : K[G]) • m) = 0 := by
      simpa [MonoidAlgebra.of_apply] using hLm'
    simpa [hsingle_one_smul] using hLm_single
  have hrepr_t_zero : b.repr m t = 0 := by simpa [L] using hLm
  exact ht hrepr_t_zero

/-- Helper for Corollary 14-14.4-3: over a field, an epimorphism in the finite-projective owner
category is already surjective on the underlying `K[G]`-linear map. -/
private theorem finiteProjective_underlying_surjective_of_epi_field
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    {E X : FiniteProjectiveGroupAlgebraModule K G} (e : E ⟶ X) [Epi e] :
    Function.Surjective e.hom.hom.hom := by
  let eLin : E.V →ₗ[K[G]] X.V := e.hom.hom.hom
  by_contra hnsurj
  let Q : Type u := X.V ⧸ LinearMap.range eLin
  let q : X.V →ₗ[K[G]] Q := (LinearMap.range eLin).mkQ
  have hQ_nontrivial : Nontrivial Q := by
    -- Route correction: the field case should still be discharged by probing the nonzero quotient
    -- `X / range(e)` with a map to the regular module.
    apply not_subsingleton_iff_nontrivial.mp
    intro hQ_sub
    apply hnsurj
    exact LinearMap.range_eq_top.mp ((Submodule.Quotient.subsingleton_iff).mp hQ_sub)
  letI : Nontrivial Q := hQ_nontrivial
  letI : Module K Q := Module.compHom Q (algebraMap K K[G])
  letI : IsScalarTower K K[G] Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Finite K Q := by
    let _ : Module.Finite K K[G] := MonoidAlgebra.moduleFinite
    exact Module.Finite.trans K[G] Q
  obtain ⟨η, hη_nonzero⟩ :=
    exists_nonzero_map_to_regular_of_nontrivial_field (K := K) (G := G) (M := Q)
  let gLin : X.V →ₗ[K[G]] K[G] := η.comp q
  have hq_comp : q.comp eLin = 0 := by
    -- The quotient map kills the range of `e`.
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hgLin_comp : gLin.comp eLin = 0 := by
    -- Therefore the induced map to the regular module annihilates `e`.
    ext x t
    have hηx : η (q (eLin x)) = 0 := by
      rw [show q (eLin x) = 0 by exact LinearMap.congr_fun hq_comp x, LinearMap.map_zero]
    simpa [gLin, LinearMap.comp_apply] using congrArg (fun z : K[G] => z t) hηx
  have hgLin_nonzero : gLin ≠ 0 := by
    -- If the composite probe vanished, surjectivity of the quotient map would force `η = 0`.
    intro hgLin_zero
    apply hη_nonzero
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range eLin) y
    have hx : gLin x = 0 := by simp [hgLin_zero]
    simpa [gLin] using hx
  let gMor : X ⟶ finiteProjective_regular_owner (A := K) (G := G) :=
    ObjectProperty.homMk (FGModuleCat.ofHom gLin)
  have hcomp_zero : e ≫ gMor = 0 := by
      -- Repackage the vanished composite as an equality in the owner category.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x t
    have hx := congrArg (fun z : K[G] => z t) (LinearMap.congr_fun hgLin_comp x)
    simpa [gMor, gLin, FGModuleCat.ofHom, LinearMap.comp_apply] using hx
  have hgMor_zero : gMor = 0 := by
    exact (cancel_epi e).1 (by simpa using hcomp_zero)
  have hgLin_zero : gLin = 0 := by
    apply LinearMap.ext
    intro x
    have hx :=
      congrArg (fun f : X.obj ⟶ (finiteProjective_regular_owner (A := K) (G := G)).obj ↦ f.hom.hom x)
        (congrArg (fun φ : X ⟶ finiteProjective_regular_owner (A := K) (G := G) ↦ φ.hom) hgMor_zero)
    simpa [gMor, gLin, FGModuleCat.ofHom] using hx
  exact hgLin_nonzero hgLin_zero

/-- Helper for Corollary 14-14.4-3: over a local coefficient ring, an epimorphism in the
finite-projective owner category should already be surjective on the underlying `A[G]`-linear
map. -/
private theorem regular_probe_precompose_reduction_on_lift
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X)
    (gbar : (k ⊗[A] X.V) →ₗ[k[G]] k[G]) (g : X.V →ₗ[A[G]] A[G])
    (hred : ∀ x,
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
          A[G] →ₗ[A] k[G]) (g x)) =
        gbar ((TensorProduct.mk A k X.V 1) x)) :
    ∀ x,
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
          A[G] →ₗ[A] k[G]) ((g.comp e.hom.hom.hom) x)) =
        (gbar.comp (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e))
          ((TensorProduct.mk A k E.V 1) x) := by
  intro x
  -- Push the reduction identity through precomposition, then rewrite the reduced map on `1 ⊗ x`.
  calc
    (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
        A[G] →ₗ[A] k[G]) ((g.comp e.hom.hom.hom) x))
        = gbar ((TensorProduct.mk A k X.V 1) (e.hom.hom.hom x)) := by
            simpa [LinearMap.comp_apply] using hred (e.hom.hom.hom x)
    _ =
        (gbar.comp (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e))
          ((TensorProduct.mk A k E.V 1) x) := by
            simp [LinearMap.comp_apply, reduction_precompose_groupAlgebraLinear,
              LinearMap.baseChange_tmul]

/-- Helper for Corollary 14-14.4-3: if an owner regular probe were zero, then its reduction would
also vanish on every reduced pure tensor, hence the reduced probe itself is zero. -/
private theorem owner_regular_probe_nonzero_of_nonzero_reduction
    {X : FiniteProjectiveGroupAlgebraModule A G}
    (gbar : (k ⊗[A] X.V) →ₗ[k[G]] k[G]) (g : X.V →ₗ[A[G]] A[G])
    (hred : ∀ x,
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
          A[G] →ₗ[A] k[G]) (g x)) =
        gbar ((TensorProduct.mk A k X.V 1) x))
    (hgbar_nonzero : gbar ≠ 0) :
    g ≠ 0 := by
  intro hg_zero
  apply hgbar_nonzero
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro c x
    have hx :
        gbar ((TensorProduct.mk A k X.V 1) x) = 0 := by
      simpa [hg_zero] using (hred x).symm
    have hcx : (c ⊗ₜ[A] x : k ⊗[A] X.V) = c • ((1 : k) ⊗ₜ[A] x) := by
      calc
        (c ⊗ₜ[A] x : k ⊗[A] X.V) = ((c • (1 : k)) ⊗ₜ[A] x : k ⊗[A] X.V) := by
          simp
        _ = c • ((1 : k) ⊗ₜ[A] x) := by
              rw [TensorProduct.smul_tmul']
    calc
      gbar (c ⊗ₜ[A] x) = gbar (c • ((1 : k) ⊗ₜ[A] x)) := by
        rw [hcx]
      _ = c • gbar ((TensorProduct.mk A k X.V 1) x) := by
        simp
      _ = 0 := by
        rw [hx, smul_zero]
  · intro z w hz hw
    simp [hz, hw]

/-- Helper for Corollary 14-14.4-3: a reduced regular probe in the reduced precomposition kernel
factors through the actual reduced cokernel of `e`. -/
private theorem reduced_regular_probe_factor_through_precompose_cokernel_local
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
  simpa [η, ebar] using
    (Submodule.liftQ_apply (p := LinearMap.range ebar) (f := gbar) (x := x))

/-- Helper for Corollary 14-14.4-3: the reduced cokernel of `e` admits a projective envelope, and
the reduced quotient map from `k ⊗ X` lifts to that projective cover. -/
private theorem reduced_precompose_cokernel_projective_cover_data_local
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

/-- Helper for Corollary 14-14.4-3: if two reduced lifts factor the same quotient map through the
same projective envelope and one of them is surjective, then the reduced cover source carries a
comparison automorphism fixing the quotient map. -/
private theorem projective_cover_comparison_endomorphism_local
    {Xbar Mbar Pbar : Type w}
    [AddCommGroup Xbar] [Module k[G] Xbar]
    [AddCommGroup Mbar] [Module k[G] Mbar]
    [AddCommGroup Pbar] [Module k[G] Pbar]
    (πCbar : Pbar →ₗ[k[G]] Mbar)
    (hπCbar : πCbar.IsProjectiveEnvelope)
    (σbar σred : Xbar →ₗ[k[G]] Pbar)
    (hσbar_surj : Function.Surjective σbar)
    (hfactor : πCbar.comp σred = πCbar.comp σbar) :
    ∃ u : Pbar →ₗ[k[G]] Pbar,
      πCbar.comp u = πCbar ∧ Function.Bijective u := by
  -- Split the surjective reference lift on the projective envelope source.
  obtain ⟨t, ht⟩ :=
    Module.projective_lifting_property σbar (LinearMap.id : Pbar →ₗ[k[G]] Pbar) hσbar_surj
  let u : Pbar →ₗ[k[G]] Pbar := σred.comp t
  have hu : πCbar.comp u = πCbar := by
    -- Evaluate the two factorizations after the chosen section of `σbar`.
    ext p
    calc
      (πCbar.comp u) p = (πCbar.comp σred) (t p) := by
        rfl
      _ = (πCbar.comp σbar) (t p) := by
            exact congrArg (fun f : Xbar →ₗ[k[G]] Mbar => f (t p)) hfactor
      _ = πCbar p := by
            have htp : σbar (t p) = p := by
              exact congrArg (fun f : Pbar →ₗ[k[G]] Pbar => f p) ht
            exact congrArg πCbar htp
  refine ⟨u, hu, ?_⟩
  · -- Any endomorphism preserving the quotient map of a projective envelope is bijective.
    exact projective_envelope_endomorphism_bijective_local hπCbar hu

private theorem finiteProjective_underlying_surjective_of_epi_local
    {E X : FiniteProjectiveGroupAlgebraModule A G} (e : E ⟶ X) [Epi e] :
    Function.Surjective e.hom.hom.hom := by
  -- Route correction: the source proof splits the actual short exact sequence upstairs, so the
  -- only remaining missing ingredient is the kernel correction on the lifted projective cover of
  -- the reduced cokernel.
  let eLin : E.V →ₗ[A[G]] X.V := e.hom.hom.hom
  let ebar : (k ⊗[A] E.V) →ₗ[k[G]] (k ⊗[A] X.V) :=
    reduction_precompose_groupAlgebraLinear (A := A) (G := G) e
  by_contra hnsurj
  have hred_nsurj : ¬ Function.Surjective ((e.hom.hom.hom.restrictScalars A).baseChange k) := by
    intro hred
    exact hnsurj
      (finiteProjective_underlying_surjective_of_reduction_surjective
        (A := A) (G := G) e hred)
  let Q : Type u := (k ⊗[A] X.V) ⧸ LinearMap.range ebar
  let q : (k ⊗[A] X.V) →ₗ[k[G]] Q := (LinearMap.range ebar).mkQ
  have hQ_nontrivial : Nontrivial Q := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hQ_sub
    apply hred_nsurj
    simpa [ebar, reduction_precompose_groupAlgebraLinear] using
      (LinearMap.range_eq_top.1
        ((Submodule.Quotient.subsingleton_iff).1 hQ_sub))
  letI : Nontrivial Q := hQ_nontrivial
  have hXred_finite : Module.Finite k[G] (k ⊗[A] X.V) := by
    let _ : Module.Finite A X.V := X.finite
    let _ : Module.Free A X.V := FiniteProjectiveGroupAlgebraModule.free (A := A) (G := G) X
    let b := Module.Free.chooseBasis A X.V
    letI : Finite (Module.Free.ChooseBasisIndex A X.V) := Module.Finite.finite_basis b
    letI : Module.Finite k (k ⊗[A] X.V) :=
      Module.Finite.of_basis (Algebra.TensorProduct.basis k b)
    exact Module.Finite.of_restrictScalars_finite k k[G] (k ⊗[A] X.V)
  letI : Module.Finite k[G] Q :=
    Module.Finite.of_surjective q (Submodule.mkQ_surjective (LinearMap.range ebar))
  letI : Module.Finite k Q := by
    let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
    exact Module.Finite.trans k[G] Q
  obtain ⟨η, hη_nonzero⟩ : ∃ φ : Q →ₗ[k[G]] k[G], φ ≠ 0 := by
    exact exists_nonzero_map_to_regular_of_nontrivial (A := A) (G := G) (M := Q)
  let gbar : (k ⊗[A] X.V) →ₗ[k[G]] k[G] := η.comp q
  have hq_comp : q.comp ebar = 0 := by
    -- The quotient map kills the range of the reduced precomposition map.
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hgbar_comp : gbar.comp ebar = 0 := by
    -- Therefore the reduced regular probe lies in the reduced precomposition kernel.
    ext x
    have hx : q (ebar x) = 0 := LinearMap.congr_fun hq_comp x
    simp [gbar, LinearMap.comp_apply, hx]
  obtain ⟨η, hηfac⟩ :=
    reduced_regular_probe_factor_through_precompose_cokernel_local
      (A := A) (G := G) e gbar hgbar_comp
  obtain ⟨ηC, hηCfac⟩ :=
    reduced_probe_factor_through_actual_cokernel_local (A := A) (G := G) e η
  obtain ⟨Pbar, πbar, σbar, hπbar, hσbar⟩ :=
    reduced_precompose_cokernel_projective_cover_data_local (A := A) (G := G) e
  -- Route correction: the reduced cover is now transported through the actual cokernel
  -- `X.V ⧸ range(e)` before the missing owner-level lift is requested from
  -- `lift_projective_cover_map_in_precompose_kernel_local`.
  obtain ⟨P, eP, πCbar, σ, hπCbar, hσCbar, hσq, hσker⟩ :=
    lift_projective_cover_map_in_precompose_kernel_local
      (A := A) (G := G) e Pbar πbar hπbar σbar hσbar
  let τbar : (k ⊗[A] P.V) →ₗ[k[G]] k[G] :=
    (ηC.comp πCbar).comp eP.toLinearMap
  obtain ⟨τ, hτred⟩ :=
    lift_regular_probe_to_regular_owner (A := A) (G := G) (X := P) τbar
  let g : X.V →ₗ[A[G]] A[G] := τ.comp σ
  have hg_red :
      ∀ x,
        (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
            A[G] →ₗ[A] k[G]) (g x)) =
          gbar ((TensorProduct.mk A k X.V 1) x) := by
    intro x
    -- Reduce the lifted projective-cover composite and rewrite it back through the reduced
    -- quotient factorization of `gbar` through the actual cokernel.
    calc
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
          A[G] →ₗ[A] k[G]) (g x))
          = τbar ((TensorProduct.mk A k P.V 1) (σ x)) := by
              simpa [g, τbar] using hτred (σ x)
      _ = (ηC.comp πCbar)
            (eP ((TensorProduct.mk A k P.V 1) (σ x))) := by
              simp [τbar, LinearMap.comp_apply]
      _ = ηC
            ((baseChange_groupAlgebraLinear (A := A) (G := G)
              ((LinearMap.range e.hom.hom.hom).mkQ))
              ((TensorProduct.mk A k X.V 1) x)) := by
                simpa [LinearMap.comp_apply] using congrArg ηC (hσq x)
      _ = gbar ((TensorProduct.mk A k X.V 1) x) := by
            have hx :=
              congrArg
                (fun f : (k ⊗[A] X.V) →ₗ[k[G]] k[G] =>
                  f ((TensorProduct.mk A k X.V 1) x)) hηCfac
            calc
              ηC
                  ((baseChange_groupAlgebraLinear (A := A) (G := G)
                    ((LinearMap.range e.hom.hom.hom).mkQ))
                    ((TensorProduct.mk A k X.V 1) x))
                  = (η.comp
                      (LinearMap.range
                        (reduction_precompose_groupAlgebraLinear (A := A) (G := G) e)).mkQ)
                      ((TensorProduct.mk A k X.V 1) x) := by
                        simpa [LinearMap.comp_apply] using hx
              _ = gbar ((TensorProduct.mk A k X.V 1) x) := by
                    simpa [q, LinearMap.comp_apply] using
                      congrArg
                        (fun f : (k ⊗[A] X.V) →ₗ[k[G]] k[G] =>
                          f ((TensorProduct.mk A k X.V 1) x)) hηfac.symm
  have hpre_zero :
      regular_probe_precompose_linear (A := A) (G := G) e g = 0 := by
    -- The lifted projective-cover map was corrected into the actual precomposition kernel.
    simpa [g, regular_probe_precompose_linear_apply, LinearMap.comp_assoc] using
      congrArg (fun f => τ.comp f) hσker
  have hg_zero : g = 0 := by
    have hinj :
        Function.Injective (regular_probe_precompose_linear (A := A) (G := G) e) :=
      LinearMap.ker_eq_bot.1
        (regular_probe_precompose_linear_ker_eq_bot (A := A) (G := G) e)
    exact hinj (by simpa using hpre_zero)
  have hgbar_zero : gbar = 0 := by
    by_contra hgbar_nonzero
    exact
      (owner_regular_probe_nonzero_of_nonzero_reduction
        (A := A) (G := G) gbar g hg_red hgbar_nonzero) hg_zero
  apply hη_nonzero
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ebar) y
  have hx : gbar x = 0 := by simpa [hgbar_zero]
  simpa [gbar] using hx

/-- Helper for Corollary 14-14.4-3: over a field, the regular owner is projective in the
finite-projective owner category because owner epimorphisms are surjective on the forgotten
`K[G]`-linear maps. -/
private theorem regular_owner_projective_field
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G] :
    Projective (finiteProjective_regular_owner (A := K) (G := G)) := by
  refine ⟨?_⟩
  intro E X f e hepi
  letI : Epi e := hepi
  let eLin : E.V →ₗ[K[G]] X.V := e.hom.hom.hom
  let fLin : K[G] →ₗ[K[G]] X.V := f.hom.hom.hom
  have hsurj : Function.Surjective eLin := by
    -- In the field case, categorical epis are already surjective on the underlying module.
    simpa [eLin] using finiteProjective_underlying_surjective_of_epi_field (G := G) e
  obtain ⟨l, hl⟩ := Module.projective_lifting_property eLin fLin hsurj
  refine ⟨ObjectProperty.homMk (FGModuleCat.ofHom l), ?_⟩
  -- Repackage the linear lift as a morphism in the owner category.
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  simpa [eLin, fLin] using hl

/-- Helper for Corollary 14-14.4-3: over a local coefficient ring, the regular owner is
projective because owner epimorphisms are surjective on the forgotten `A[G]`-linear maps. -/
private theorem regular_owner_projective_local :
    Projective (finiteProjective_regular_owner (A := A) (G := G)) := by
  refine ⟨?_⟩
  intro E X f e hepi
  letI : Epi e := hepi
  let eLin : E.V →ₗ[A[G]] X.V := e.hom.hom.hom
  let fLin : A[G] →ₗ[A[G]] X.V := f.hom.hom.hom
  have hsurj : Function.Surjective eLin := by
    -- The local split-exact route only needs surjectivity on the forgotten module map.
    simpa [eLin] using finiteProjective_underlying_surjective_of_epi_local (A := A) (G := G) e
  obtain ⟨l, hl⟩ := Module.projective_lifting_property eLin fLin hsurj
  refine ⟨ObjectProperty.homMk (FGModuleCat.ofHom l), ?_⟩
  -- Repackage the linear lift as a morphism in the owner category.
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  simpa [eLin, fLin] using hl

/-- Helper for Corollary 14-14.4-3: over a field, a kernel element of the forgotten right map
comes from the forgotten left map by lifting the regular cyclic map through the source exactness
witness. -/
private theorem finiteProjective_regular_owner_lift_of_kernel_element_field
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule K G)) (hS : S.ShortExact)
    (x₂ : S.X₂.V) (hx₂ : S.g.hom.hom x₂ = 0) :
    ∃ x₁ : S.X₁.V, S.f.hom.hom x₁ = x₂ := by
  haveI : Projective (finiteProjective_regular_owner (A := K) (G := G)) :=
    regular_owner_projective_field (K := K) (G := G)
  haveI : S.HasHomology := hS.exact.hasHomology
  let hLeft := S.leftHomologyData
  let ψ₂ : finiteProjective_regular_owner (A := K) (G := G) ⟶ S.X₂ :=
    ObjectProperty.homMk (FGModuleCat.ofHom ((LinearMap.id : K[G] →ₗ[K[G]] K[G]).smulRight x₂))
  have hψ₂_zero_lin :
      S.g.hom.hom.hom.comp ((LinearMap.id : K[G] →ₗ[K[G]] K[G]).smulRight x₂) = 0 := by
    -- The cyclic map lands in cycles because `x₂` is a kernel element for `g`.
    exact regular_module_generated_map_comp_zero (A := K) (G := G) S.g.hom.hom.hom x₂ hx₂
  have hψ₂_zero : ψ₂ ≫ S.g = 0 := by
    -- Repackage the vanished composite in the owner category.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    simpa [ψ₂, FGModuleCat.ofHom] using hψ₂_zero_lin
  let ψK : finiteProjective_regular_owner (A := K) (G := G) ⟶ hLeft.K :=
    hLeft.liftK ψ₂ hψ₂_zero
  haveI : Epi hLeft.f' := hS.exact.epi_f' hLeft
  let ψ₁ : finiteProjective_regular_owner (A := K) (G := G) ⟶ S.X₁ :=
    Projective.factorThru ψK hLeft.f'
  have hψ₁_factor : ψ₁ ≫ hLeft.f' = ψK := by
    simpa [ψ₁] using (Projective.factorThru_comp ψK hLeft.f')
  have hψ₁f : ψ₁ ≫ S.f = ψ₂ := by
    -- Compare both morphisms after factoring through the cycles object `K`.
    calc
      ψ₁ ≫ S.f = ψ₁ ≫ hLeft.f' ≫ hLeft.i := by
        simp [hLeft.f'_i]
      _ = ψK ≫ hLeft.i := by
        simpa [Category.assoc] using congrArg (fun φ => φ ≫ hLeft.i) hψ₁_factor
      _ = ψ₂ := by
        simpa [ψK] using hLeft.liftK_i ψ₂ hψ₂_zero
  refine ⟨ψ₁.hom.hom.hom 1, ?_⟩
  -- Evaluating the lifted equality at `1` recovers the desired preimage of `x₂`.
  have hEval := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.hom) hψ₁f) 1
  have hEval' :
      S.f.hom.hom.hom (ψ₁.hom.hom.hom 1) =
        ((LinearMap.id : K[G] →ₗ[K[G]] K[G]).smulRight x₂) 1 := by
    have hψ₂_eval :
        (ConcreteCategory.hom
            (FGModuleCat.ofHom ((LinearMap.id : K[G] →ₗ[K[G]] K[G]).smulRight x₂)).hom) 1 =
          ((LinearMap.id : K[G] →ₗ[K[G]] K[G]).smulRight x₂) 1 := rfl
    exact hEval.trans hψ₂_eval
  simpa [regular_module_generated_map_apply_one (A := K) (G := G) (x := x₂)] using hEval'

/-- Helper for Corollary 14-14.4-3: over a local coefficient ring, a kernel element of the
forgotten right map comes from the forgotten left map by lifting the regular cyclic map through
the source exactness witness. -/
private theorem finiteProjective_regular_owner_lift_of_kernel_element_local
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G)) (hS : S.ShortExact)
    (x₂ : S.X₂.V) (hx₂ : S.g.hom.hom x₂ = 0) :
    ∃ x₁ : S.X₁.V, S.f.hom.hom x₁ = x₂ := by
  haveI : Projective (finiteProjective_regular_owner (A := A) (G := G)) :=
    regular_owner_projective_local (A := A) (G := G)
  haveI : S.HasHomology := hS.exact.hasHomology
  let hLeft := S.leftHomologyData
  let ψ₂ : finiteProjective_regular_owner (A := A) (G := G) ⟶ S.X₂ :=
    ObjectProperty.homMk (FGModuleCat.ofHom ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight x₂))
  have hψ₂_zero_lin :
      S.g.hom.hom.hom.comp ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight x₂) = 0 := by
    -- The cyclic map lands in cycles because `x₂` is a kernel element for `g`.
    exact regular_module_generated_map_comp_zero (A := A) (G := G) S.g.hom.hom.hom x₂ hx₂
  have hψ₂_zero : ψ₂ ≫ S.g = 0 := by
    -- Repackage the vanished composite in the owner category.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    simpa [ψ₂, FGModuleCat.ofHom] using hψ₂_zero_lin
  let ψK : finiteProjective_regular_owner (A := A) (G := G) ⟶ hLeft.K :=
    hLeft.liftK ψ₂ hψ₂_zero
  haveI : Epi hLeft.f' := hS.exact.epi_f' hLeft
  let ψ₁ : finiteProjective_regular_owner (A := A) (G := G) ⟶ S.X₁ :=
    Projective.factorThru ψK hLeft.f'
  have hψ₁_factor : ψ₁ ≫ hLeft.f' = ψK := by
    simpa [ψ₁] using (Projective.factorThru_comp ψK hLeft.f')
  have hψ₁f : ψ₁ ≫ S.f = ψ₂ := by
    -- Compare both morphisms after factoring through the cycles object `K`.
    calc
      ψ₁ ≫ S.f = ψ₁ ≫ hLeft.f' ≫ hLeft.i := by
        simp [hLeft.f'_i]
      _ = ψK ≫ hLeft.i := by
        simpa [Category.assoc] using congrArg (fun φ => φ ≫ hLeft.i) hψ₁_factor
      _ = ψ₂ := by
        simpa [ψK] using hLeft.liftK_i ψ₂ hψ₂_zero
  refine ⟨ψ₁.hom.hom.hom 1, ?_⟩
  -- Evaluating the lifted equality at `1` recovers the desired preimage of `x₂`.
  have hEval := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.hom) hψ₁f) 1
  have hEval' :
      S.f.hom.hom.hom (ψ₁.hom.hom.hom 1) =
        ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight x₂) 1 := by
    have hψ₂_eval :
        (ConcreteCategory.hom
            (FGModuleCat.ofHom ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight x₂)).hom) 1 =
          ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight x₂) 1 := rfl
    exact hEval.trans hψ₂_eval
  simpa [regular_module_generated_map_apply_one (A := A) (G := G) (x := x₂)] using hEval'

/-- Helper for Corollary 14-14.4-3: in the field case, owner exactness is already exactness of the
underlying `K[G]`-linear maps. -/
private theorem finiteProjective_underlying_function_exact_field
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule K G)) (hS : S.ShortExact) :
    Function.Exact S.f.hom.hom S.g.hom.hom := by
  intro x₂
  constructor
  · intro hx₂
    -- Route correction: keep the regular-cyclic-map proof, but restrict it to the field case
    -- where the epi-to-surjective step is mathematically valid.
    exact
      finiteProjective_regular_owner_lift_of_kernel_element_field
        (K := K) (G := G) S hS x₂ hx₂
  · intro hx₂
    -- The easy direction is still just `g ∘ f = 0` on the underlying elements.
    rcases hx₂ with ⟨x₁, hx₁⟩
    have hzero : S.g.hom.hom (S.f.hom.hom x₁) = 0 := by
      simpa using
        ConcreteCategory.congr_hom
          (finiteProjective_underlying_moduleCat_zero (A := K) (G := G) S) x₁
    simpa [hx₁] using hzero

/-- Helper for Corollary 14-14.4-3: over a local coefficient ring, owner exactness is already
exactness of the underlying `A[G]`-linear maps. -/
private theorem finiteProjective_underlying_function_exact_local
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G)) (hS : S.ShortExact) :
    Function.Exact S.f.hom.hom S.g.hom.hom := by
  intro x₂
  constructor
  · intro hx₂
    -- The local split-exact route again lifts a kernel element through the regular owner.
    exact
      finiteProjective_regular_owner_lift_of_kernel_element_local
        (A := A) (G := G) S hS x₂ hx₂
  · intro hx₂
    -- The easy direction is still just `g ∘ f = 0` on the underlying elements.
    rcases hx₂ with ⟨x₁, hx₁⟩
    have hzero : S.g.hom.hom (S.f.hom.hom x₁) = 0 := by
      simpa using
        ConcreteCategory.congr_hom
          (finiteProjective_underlying_moduleCat_zero (A := A) (G := G) S) x₁
    simpa [hx₁] using hzero

/-- Helper for Corollary 14-14.4-3: over a field, the underlying `ModuleCat K[G]` short complex
of a short exact sequence of finite projective `K[G]`-modules is itself short exact. -/
private theorem finiteProjective_shortExact_underlying_moduleCat_shortExact_field
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule K G)) (hS : S.ShortExact) :
    (ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (A := K) (G := G) S)).ShortExact := by
  have hf : Function.Injective S.f.hom.hom :=
    finiteProjective_underlying_injective_of_mono (A := K) (G := G) S hS
  have hg : Function.Surjective S.g.hom.hom := by
    letI : Epi S.g := hS.epi_g
    -- In the field case, the right map is already surjective on the underlying module.
    simpa using finiteProjective_underlying_surjective_of_epi_field (G := G) S.g
  -- Rebuild ambient short exactness from the field-valid epi/surjective bridge and the regular
  -- cyclic-map exactness argument.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact finiteProjective_underlying_function_exact_field (K := K) (G := G) S hS
  · rw [ModuleCat.mono_iff_injective]
    exact hf
  · rw [ModuleCat.epi_iff_surjective]
    exact hg

/-- Helper for Corollary 14-14.4-3: over a local coefficient ring, the underlying
`ModuleCat A[G]` short complex of a short exact sequence of finite projective `A[G]`-modules is
itself short exact. -/
theorem finiteProjective_shortExact_underlying_moduleCat_shortExact_local
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G)) (hS : S.ShortExact) :
    (ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (A := A) (G := G) S)).ShortExact := by
  have hf : Function.Injective S.f.hom.hom :=
    finiteProjective_underlying_injective_of_mono (A := A) (G := G) S hS
  have hg : Function.Surjective S.g.hom.hom := by
    letI : Epi S.g := hS.epi_g
    -- The local structural step is exactly the owner-epi to surjective bridge.
    simpa using finiteProjective_underlying_surjective_of_epi_local (A := A) (G := G) S.g
  -- Rebuild ambient short exactness from the local exactness and the forgotten mono/epi data.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact finiteProjective_underlying_function_exact_local (A := A) (G := G) S hS
  · rw [ModuleCat.mono_iff_injective]
    exact hf
  · rw [ModuleCat.epi_iff_surjective]
    exact hg

/-- Helper for Corollary 14-14.4-3: the forgotten `ModuleCat A[G]` object of a finite projective
module is categorically projective. -/
private theorem finiteProjective_projective_moduleCat
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    Projective ((ModuleCat.isFG A[G]).ι.obj P.obj) := by
  -- The module-theoretic projectivity assumption on `P` matches the categorical projectivity
  -- statement in `ModuleCat A[G]`.
  letI : Module.Projective A[G] ((ModuleCat.isFG A[G]).ι.obj P.obj) := by
    simpa using P.property
  infer_instance

/-- Helper for Corollary 14-14.4-3: a short exact sequence of finite projective `A[G]`-modules
splits after forgetting to `ModuleCat A[G]`, so the middle term is linearly equivalent to the
product of the two outer terms. -/
private theorem shortExact_middle_nonempty_linearEquiv_prod_local
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G)) (hS : S.ShortExact) :
    Nonempty (S.X₂.V ≃ₗ[A[G]] S.X₁.V × S.X₃.V) := by
  let Smod : ShortComplex (ModuleCat A[G]) :=
    ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (A := A) (G := G) S)
  have hSmod : Smod.ShortExact :=
    finiteProjective_shortExact_underlying_moduleCat_shortExact_local
      (A := A) (G := G) S hS
  let _ : Projective Smod.X₃ := finiteProjective_projective_moduleCat (A := A) (G := G) S.X₃
  obtain ⟨e⟩ := moduleCat_shortExact_middle_nonempty_linearEquiv_prod Smod hSmod
  -- The source route splits the short exact sequence upstairs, then flips the product equivalence.
  exact ⟨e.symm⟩

omit [Finite G] in
/-- Helper for Corollary 14-14.4-3: the free-abelian lift sending a projective class to the class
of its residue-field reduction. -/
private abbrev projectiveGrothendieckReductionLift :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule A G) →+
      P₀[k](G) :=
  FreeAbelianGroup.lift fun P ↦ [P.residueFieldReduction]ₚ₀

omit [Finite G] in
/-- Helper for Corollary 14-14.4-3: every pure tensor in the reduced product model is a scalar
multiple of one whose left tensor factor is `1`. -/
private theorem reduction_prod_tmul_eq_smul_unit_tmul
    {P Q : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (c : k) (p : P) (q : Q) :
    (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)) = c • ((1 : k) ⊗ₜ[A] (p, q)) := by
  -- Normalize a pure tensor so future equivariance checks can focus on the `1 ⊗ x` case.
  calc
    (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q))
        = ((c • (1 : k)) ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)) := by simp
    _ = c • ((1 : k) ⊗ₜ[A] (p, q)) := by
          rw [TensorProduct.smul_tmul']

omit [Finite G] in
/-- Helper for Corollary 14-14.4-3: `TensorProduct.prodRight` sends a pure tensor in the reduced
product model to the corresponding pair of reduced pure tensors. -/
private theorem reduction_prodRight_tmul_eq_smul
    {P Q : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (c : k) (p : P) (q : Q) :
    TensorProduct.prodRight A k k P Q (c ⊗ₜ[A] (p, q)) =
      c • (((1 : k) ⊗ₜ[A] p), ((1 : k) ⊗ₜ[A] q)) := by
  -- First normalize the source tensor, then evaluate `TensorProduct.prodRight` on `1 ⊗ (p, q)`.
  rw [reduction_prod_tmul_eq_smul_unit_tmul (A := A) (G := G) (P := P) (Q := Q) c p q, map_smul]
  simp [TensorProduct.prodRight_tmul]

omit [Finite G] in
/-- Helper for Corollary 14-14.4-3: `TensorProduct.prodRight` commutes with the action of
`MonoidAlgebra.of k G g` on reduced pure tensors. -/
private theorem reduction_prodRight_map_monoidAlgebra_of
    {P Q : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (g : G) (c : k) (p : P) (q : Q) :
    TensorProduct.prodRight A k k P Q
        (MonoidAlgebra.of k G g • (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q))) =
      MonoidAlgebra.of k G g •
        TensorProduct.prodRight A k k P Q (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)) := by
  have hp :
      MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] p) : k ⊗[A] P) =
        (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : k ⊗[A] P) := by
    simpa using
      (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
        (Λ := A) (G := G) (P := P) g p).symm
  have hq :
      MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] q) : k ⊗[A] Q) =
        (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : k ⊗[A] Q) := by
    simpa using
      (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
        (Λ := A) (G := G) (P := Q) g q).symm
  have hpair :
      MonoidAlgebra.of k G g •
          ((((1 : k) ⊗ₜ[A] p) : k ⊗[A] P), (((1 : k) ⊗ₜ[A] q) : k ⊗[A] Q)) =
        ((((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : k ⊗[A] P),
          (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : k ⊗[A] Q)) := by
    ext <;> assumption
  -- Route correction: prove equivariance first on normalized pure tensors `c • (1 ⊗ (p, q))`,
  -- then transport the normalization through `TensorProduct.prodRight`.
  calc
    TensorProduct.prodRight A k k P Q
        (MonoidAlgebra.of k G g • (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q))) =
      TensorProduct.prodRight A k k P Q
        (c • (MonoidAlgebra.of k G g • ((1 : k) ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)))) := by
          rw [reduction_prod_tmul_eq_smul_unit_tmul (A := A) (G := G) (P := P) (Q := Q) c p q]
          rw [smul_comm]
    _ = c • TensorProduct.prodRight A k k P Q
        (MonoidAlgebra.of k G g • ((1 : k) ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q))) := by
          rw [map_smul]
    _ = c • TensorProduct.prodRight A k k P Q
        (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • (p, q)) : k ⊗[A] (P × Q))) := by
          refine congrArg (fun t ↦ c • TensorProduct.prodRight A k k P Q t) ?_
          simpa using
            (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
              (Λ := A) (G := G) (P := P × Q) g (p, q)).symm
    _ = c •
        ((((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : k ⊗[A] P),
          (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : k ⊗[A] Q)) := by
          simp [TensorProduct.prodRight_tmul]
    _ = c •
        (MonoidAlgebra.of k G g •
          ((((1 : k) ⊗ₜ[A] p) : k ⊗[A] P), (((1 : k) ⊗ₜ[A] q) : k ⊗[A] Q))) := by
          rw [hpair]
    _ = MonoidAlgebra.of k G g •
        (c • ((((1 : k) ⊗ₜ[A] p) : k ⊗[A] P), (((1 : k) ⊗ₜ[A] q) : k ⊗[A] Q))) := by
          rw [smul_comm]
    _ = MonoidAlgebra.of k G g •
        TensorProduct.prodRight A k k P Q (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)) := by
          rw [reduction_prodRight_tmul_eq_smul (A := A) (G := G) (P := P) (Q := Q) c p q]

omit [Finite G] in
/-- Helper for Corollary 14-14.4-3: residue-field reduction commutes with binary products of
projective `A[G]`-modules. -/
private theorem reduction_prod_nonempty_linearEquiv
    {P Q : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q] :
    Nonempty (((k ⊗[A] (P × Q)) ≃ₗ[k[G]] (k ⊗[A] P) × (k ⊗[A] Q))) := by
  let e₀ : (k ⊗[A] (P × Q)) ≃ₗ[k] (k ⊗[A] P) × (k ⊗[A] Q) :=
    TensorProduct.prodRight A k k P Q
  refine ⟨
    { toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv
      map_add' := e₀.map_add
      map_smul' := ?_ }⟩
  intro a x
  -- Extend the `MonoidAlgebra.of` computation from pure tensors to all scalars in `k[G]`.
  refine MonoidAlgebra.induction_on
    (p := fun b : k[G] => e₀ (b • x) = b • e₀ x) a ?_ ?_ ?_
  · intro g
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [e₀]
    | tmul c y =>
        rcases y with ⟨p, q⟩
        simpa [e₀] using
          reduction_prodRight_map_monoidAlgebra_of
            (A := A) (G := G) (P := P) (Q := Q) g c p q
    | add y z hy hz =>
        simpa [MonoidAlgebra.of_apply, map_add, smul_add, e₀] using
          calc
            e₀ (MonoidAlgebra.of k G g • (y + z))
                = e₀ (MonoidAlgebra.of k G g • y) + e₀ (MonoidAlgebra.of k G g • z) := by
                    simp [map_add, smul_add, e₀]
            _ = MonoidAlgebra.of k G g • e₀ y + MonoidAlgebra.of k G g • e₀ z := by
                  rw [hy, hz]
            _ = MonoidAlgebra.of k G g • e₀ (y + z) := by
                  simp [smul_add, e₀]
  · intro b c hb hc
    simp [add_smul, map_add, hb, hc]
  · intro c b hb
    calc
      e₀ ((c • b) • x) = e₀ (c • (b • x)) := by rw [smul_assoc]
      _ = c • e₀ (b • x) := by
            exact e₀.toLinearMap.map_smul c (b • x)
      _ = c • (b • e₀ x) := by rw [hb]
      _ = (c • b) • e₀ x := by rw [smul_assoc]

/-- Helper for Corollary 14-14.4-3: after splitting a short exact sequence of projective
`A[G]`-modules, residue-field reduction converts the middle term into the sum of the reduced outer
classes. -/
private theorem product_owner_reduction_class_eq_add
    {P Q W : FiniteProjectiveGroupAlgebraModule A G}
    (hWlin : Nonempty (W.V ≃ₗ[A[G]] P.V × Q.V)) :
    [W.residueFieldReduction]ₚ₀ =
      [P.residueFieldReduction]ₚ₀ + [Q.residueFieldReduction]ₚ₀ := by
  obtain ⟨eW⟩ := hWlin
  obtain ⟨eprod⟩ :=
    reduction_prod_nonempty_linearEquiv (A := A) (G := G) (P := P.V) (Q := Q.V)
  have hWred_lin :
      Nonempty
        (W.residueFieldReduction.V ≃ₗ[k[G]]
          P.residueFieldReduction.V × Q.residueFieldReduction.V) := by
    -- Reduce the upstairs product equivalence, then identify the reduced product model.
    have hred :
        Nonempty (((k ⊗[A] W.V) ≃ₗ[k[G]] (k ⊗[A] (P.V × Q.V)))) :=
      (projective_monoidAlgebra_nonempty_linearEquiv_iff_reduction_nonempty_linearEquiv
        (Λ := A) (G := G) (P := W.V) (P' := P.V × Q.V)
        (by infer_instance) (by infer_instance)).1 ⟨eW⟩
    obtain ⟨ered⟩ := hred
    exact ⟨by
      simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
        FiniteProjectiveGroupAlgebraModule.V] using ered.trans eprod⟩
  obtain ⟨Wk, hWk_lin, hWk_class⟩ :=
    finiteProjectiveGroupAlgebraGrothendieckClass_prod_eq_add
      (A := k) (G := G) P.residueFieldReduction Q.residueFieldReduction
  have hWred_class : [W.residueFieldReduction]ₚ₀ = [Wk]ₚ₀ := by
    -- Compare `W.residueFieldReduction` with the canonical reduced product owner through the
    -- common product module.
    apply finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
    apply
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
        W.residueFieldReduction Wk).2
    obtain ⟨eWred⟩ := hWred_lin
    obtain ⟨eWk⟩ := hWk_lin
    exact ⟨eWred.trans eWk.symm⟩
  -- Rewrite through the canonical reduced product owner.
  calc
    [W.residueFieldReduction]ₚ₀ = [Wk]ₚ₀ := hWred_class
    _ = [P.residueFieldReduction]ₚ₀ + [Q.residueFieldReduction]ₚ₀ := hWk_class

/-- Helper for Corollary 14-14.4-3: after splitting a short exact sequence of projective
`A[G]`-modules, residue-field reduction converts the middle term into the sum of the reduced outer
classes. -/
private theorem residueFieldReduction_class_middle_eq_left_add_right
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G)) (hS : S.ShortExact) :
    [S.X₂.residueFieldReduction]ₚ₀ =
      [S.X₁.residueFieldReduction]ₚ₀ + [S.X₃.residueFieldReduction]ₚ₀ := by
  have hSplit :
      Nonempty (S.X₂.V ≃ₗ[A[G]] S.X₁.V × S.X₃.V) :=
    shortExact_middle_nonempty_linearEquiv_prod_local (A := A) (G := G) S hS
  -- Route correction: abandon the old `hmidW` class-comparison detour. The source proof splits
  -- the actual short exact sequence upstairs and then reduces that concrete product equivalence.
  exact product_owner_reduction_class_eq_add (A := A) (G := G) (P := S.X₁) (Q := S.X₃)
    (W := S.X₂) hSplit

/-- Helper for Corollary 14-14.4-3: the defining Grothendieck relations are annihilated by
residue-field reduction. -/
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_reductionLift_ker :
    finiteProjectiveGroupAlgebraGrothendieckRelations A G ≤
      (projectiveGrothendieckReductionLift (A := A) (G := G)).ker := by
  -- The quotient lift kills each defining short-exact-sequence generator after reduction.
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  -- Evaluate the free lift on a defining generator and rewrite the result by the reduced class
  -- relation proved just above.
  change
    projectiveGrothendieckReductionLift (A := A) (G := G)
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [projectiveGrothendieckReductionLift, map_sub]
  rw [sub_eq_zero]
  rw [sub_eq_iff_eq_add]
  rw [add_comm]
  exact residueFieldReduction_class_middle_eq_left_add_right (A := A) (G := G) S hS

/-- Helper for Corollary 14-14.4-3: residue-field reduction induces the canonical additive map
`P₀[A](G) →+ P₀[k](G)`. -/
def projectiveGrothendieckReductionHom :
    P₀[A](G) →+ P₀[k](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations A G)
    (projectiveGrothendieckReductionLift (A := A) (G := G))
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_reductionLift_ker (A := A) (G := G))

/-- Helper for Corollary 14-14.4-3: on a generator class, reduction sends `[P]ₚ₀` to the class of
`P.residueFieldReduction`. -/
@[simp] theorem projectiveGrothendieckReductionHom_projectiveClass_eq
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    projectiveGrothendieckReductionHom (A := A) (G := G) [P]ₚ₀ = [P.residueFieldReduction]ₚ₀ := by
  rfl

/-- Helper for Corollary 14-14.4-3: over a field, an isomorphism between the largest semisimple
quotients of two projective `k[G]`-modules lifts to an isomorphism of the projective modules. -/
private theorem projective_linearEquiv_of_largestSemisimpleQuotient_linearEquiv
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P Q : FiniteProjectiveGroupAlgebraModule K G)
    (hPQ : Nonempty ((P.V ⧸ Module.jacobson K[G] P.V) ≃ₗ[K[G]]
      (Q.V ⧸ Module.jacobson K[G] Q.V))) :
    Nonempty (P.V ≃ₗ[K[G]] Q.V) := by
  rcases hPQ with ⟨e⟩
  let fP :
      P.V →ₗ[K[G]] P.V ⧸ Module.jacobson K[G] P.V :=
    (Module.jacobson K[G] P.V).mkQ
  let fQ :
      Q.V →ₗ[K[G]] Q.V ⧸ Module.jacobson K[G] Q.V :=
    (Module.jacobson K[G] Q.V).mkQ
  let g :
      Q.V →ₗ[K[G]] P.V ⧸ Module.jacobson K[G] P.V :=
    e.symm.toLinearMap.comp fQ
  let _ : Module.Finite K K[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing K[G] := IsArtinianRing.of_finite K K[G]
  let _ : IsArtinian K[G] P.V := by infer_instance
  let _ : IsArtinian K[G] Q.V := by infer_instance
  have hfP : fP.IsProjectiveEnvelope := by
    -- The canonical Jacobson-quotient map of a projective module is its projective envelope.
    simpa [fP] using
      (LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope
        (R := K[G]) (P := P.V))
  have hfQ : fQ.IsProjectiveEnvelope := by
    -- Apply the same projective-envelope theorem to `Q`.
    simpa [fQ] using
      (LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope
        (R := K[G]) (P := Q.V))
  have hg : g.IsProjectiveEnvelope := by
    -- Route correction: move `Q`'s quotient map to the common target
    -- `P.V ⧸ Module.jacobson K[G] P.V` before invoking uniqueness.
    simpa [g, fQ] using
      (LinearMap.isProjectiveEnvelope_iff_conj
        (R := K[G])
        (eP := LinearEquiv.refl K[G] Q.V)
        (eM := e.symm)
        (f := fQ)).2 hfQ
  obtain ⟨u, hu⟩ := Module.projective_lifting_property g fP hg.surjective
  have hu_bij : Function.Bijective u :=
    LinearMap.lift_between_projective_envelopes_bijective hfP hg hu
  exact ⟨LinearEquiv.ofBijective u hu_bij⟩

/-- Helper for Corollary 14-14.4-3: an isomorphism in `FDRep K G` induces a `K[G]`-linear
equivalence of the underlying modules. -/
private theorem moduleLinearEquiv_of_fdRep_iso
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (V W : FDRep K G) (i : V ≅ W) :
    Nonempty ((asModule V.ρ) ≃ₗ[K[G]] (asModule W.ρ)) := by
  let F : FDRep K G ⥤ ModuleCat K[G] :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ Rep.toModuleMonoidAlgebra
  let hIso : F.obj V ≅ F.obj W := F.mapIso i
  refine ⟨
    { toFun := hIso.hom.hom
      invFun := hIso.inv.hom
      left_inv := by
        intro x
        have hcomp := congrArg (fun f => f.hom) hIso.hom_inv_id
        exact LinearMap.congr_fun hcomp x
      right_inv := by
        intro x
        have hcomp := congrArg (fun f => f.hom) hIso.inv_hom_id
        exact LinearMap.congr_fun hcomp x
      map_add' := hIso.hom.hom.map_add
      map_smul' := hIso.hom.hom.map_smul }⟩

/-- Helper for Corollary 14-14.4-3: the module underlying
`Rep.ofModuleMonoidAlgebra.obj (ModuleCat.of K[G] M)` is canonically linearly equivalent to `M`. -/
private theorem nonempty_ofModuleMonoidAlgebra_asModuleLinearEquiv
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M] :
    Nonempty ((Rep.ofModuleMonoidAlgebra.obj (ModuleCat.of K[G] M)).ρ.asModule ≃ₗ[K[G]] M) := by
  change Nonempty ((Representation.ofModule (ModuleCat.of K[G] M)).asModule ≃ₗ[K[G]] M)
  let Mmod : ModuleCat K[G] := ModuleCat.of K[G] M
  let toFun : (Representation.ofModule Mmod).asModule → M := fun x ↦
    (RestrictScalars.addEquiv K K[G] M) ((Representation.ofModule Mmod).asModuleEquiv x)
  let invFun : M → (Representation.ofModule Mmod).asModule := fun x ↦
    (Representation.ofModule Mmod).asModuleEquiv.symm ((RestrictScalars.addEquiv K K[G] M).symm x)
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro x
        simp [toFun, invFun, Mmod]
      right_inv := by
        intro x
        simp [toFun, invFun, Mmod]
      map_add' := by
        intro x y
        simp [toFun, Mmod]
      map_smul' := by
        intro r x
        exact Representation.smul_ofModule_asModule (M := Mmod) r x }⟩

/-- Helper for Corollary 14-14.4-3: the largest semisimple quotient of a finite projective
`K[G]`-module is finite-dimensional over `K`. -/
private theorem largestSemisimpleQuotient_moduleFinite
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P : FiniteProjectiveGroupAlgebraModule K G) :
    Module.Finite K (P.V ⧸ Module.jacobson K[G] P.V) := by
  -- The quotient map is surjective, so finite generation descends from `P.V`.
  let _ : Module.Finite K P.V := P.finite
  exact
    Module.Finite.of_surjective
      ((Module.jacobson K[G] P.V).mkQ.restrictScalars K)
      (by
        intro x
        rcases Submodule.mkQ_surjective (Module.jacobson K[G] P.V) x with ⟨y, rfl⟩
        exact ⟨y, rfl⟩)

/-- Helper for Corollary 14-14.4-3: the `Rep K G` owner attached to the largest semisimple
quotient is finite over `K`. -/
private theorem largestSemisimpleQuotient_toRep_moduleFinite
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P : FiniteProjectiveGroupAlgebraModule K G) :
    Module.Finite K
      (Rep.ofModuleMonoidAlgebra.obj
        (ModuleCat.of K[G] (P.V ⧸ Module.jacobson K[G] P.V))) := by
  -- The underlying `K`-vector space is exactly the Jacobson quotient module.
  simpa using largestSemisimpleQuotient_moduleFinite (K := K) (G := G) P

/-- Helper for Corollary 14-14.4-3: attach to a projective `K[G]`-module the finite-dimensional
representation carried by its largest semisimple quotient. -/
private abbrev largestSemisimpleQuotient_fdRep
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P : FiniteProjectiveGroupAlgebraModule K G) : FDRep K G :=
  let _ : Module.Finite K
      (Rep.ofModuleMonoidAlgebra.obj
        (ModuleCat.of K[G] (P.V ⧸ Module.jacobson K[G] P.V))) :=
    largestSemisimpleQuotient_toRep_moduleFinite (K := K) (G := G) P
  FDRep.of
    (Rep.ofModuleMonoidAlgebra.obj
      (ModuleCat.of K[G] (P.V ⧸ Module.jacobson K[G] P.V))).ρ

/-- Helper for Corollary 14-14.4-3: before rebundling into `FDRep`, the representation carried by
the largest semisimple quotient is already semisimple as a `Rep K G`. -/
private theorem largestSemisimpleQuotient_toRep_isSemisimpleRepresentation
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P : FiniteProjectiveGroupAlgebraModule K G) [IsArtinian K[G] P.V] :
    IsSemisimpleRepresentation
      (Rep.ofModuleMonoidAlgebra.obj
        (ModuleCat.of K[G] (P.V ⧸ Module.jacobson K[G] P.V))).ρ := by
  let M := P.V ⧸ Module.jacobson K[G] P.V
  -- The Jacobson quotient is semisimple as a `K[G]`-module, and `Rep.ofModuleMonoidAlgebra`
  -- packages exactly that module action.
  have hsem : IsSemisimpleModule K[G] M := by
    simpa [M] using largestSemisimpleQuotient_isSemisimple (R := K[G]) (M := P.V)
  rw [Rep.ofModuleMonoidAlgebra_obj_ρ]
  simpa [M] using
    ((Representation.isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule M).1 hsem)

/-- Helper for Corollary 14-14.4-3: every finite-dimensional representation is canonically
isomorphic to the object rebuilt from its bundled representation. -/
private noncomputable def fdRepIsoOfRho
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    -- The rebundling keeps the same carrier and action; only the owner wrapper changes.
    ext x
    rfl

/-- Helper for Corollary 14-14.4-3: any `FDRep` class agrees with the class of the
canonically rebuilt `FDRep.of` owner attached to its bundled representation. -/
private theorem finiteRepGrothendieckClass_eq_wrapped_of_fdRep
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (τ : FDRep K G) :
    [τ]₀ = [FDRep.of τ.ρ]₀ := by
  -- Replace `τ` by the canonical `FDRep.of` owner built from its bundled representation.
  exact
    finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G)
      ⟨fdRepIsoOfRho (K := K) (G := G) τ⟩

/-- Helper for Corollary 14-14.4-3: the representation carried by the product of the two largest
semisimple quotients is finite-dimensional over `K`. -/
private theorem largestSemisimpleQuotient_prod_toRep_moduleFinite
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P Q : FiniteProjectiveGroupAlgebraModule K G) :
    Module.Finite K
      (Rep.ofModuleMonoidAlgebra.obj
        (ModuleCat.of K[G]
          (((P.V ⧸ Module.jacobson K[G] P.V : Type u) ×
            (Q.V ⧸ Module.jacobson K[G] Q.V : Type u) : Type u)))) := by
  -- Finite-dimensionality is preserved under binary products of the two quotient modules.
  let _ : Module.Finite K (P.V ⧸ Module.jacobson K[G] P.V) :=
    largestSemisimpleQuotient_moduleFinite (K := K) (G := G) P
  let _ : Module.Finite K (Q.V ⧸ Module.jacobson K[G] Q.V) :=
    largestSemisimpleQuotient_moduleFinite (K := K) (G := G) Q
  simpa using
    (inferInstance :
      Module.Finite K
        ((P.V ⧸ Module.jacobson K[G] P.V) × (Q.V ⧸ Module.jacobson K[G] Q.V)))

/-- Helper for Corollary 14-14.4-3: package the product of the two largest semisimple quotient
modules as a concrete finite-dimensional representation. -/
private abbrev largestSemisimpleQuotient_prod_fdRep
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P Q : FiniteProjectiveGroupAlgebraModule K G) : FDRep K G :=
  let _ : Module.Finite K
      (Rep.ofModuleMonoidAlgebra.obj
        (ModuleCat.of K[G]
          (((P.V ⧸ Module.jacobson K[G] P.V : Type u) ×
            (Q.V ⧸ Module.jacobson K[G] Q.V : Type u) : Type u)))) :=
    largestSemisimpleQuotient_prod_toRep_moduleFinite (K := K) (G := G) P Q
  FDRep.of
    (Rep.ofModuleMonoidAlgebra.obj
      (ModuleCat.of K[G]
        (((P.V ⧸ Module.jacobson K[G] P.V : Type u) ×
          (Q.V ⧸ Module.jacobson K[G] Q.V : Type u) : Type u)))).ρ

/-- Helper for Corollary 14-14.4-3: the class of the concrete product owner on the two largest
semisimple quotients is the sum of the two outer classes in `R₀[K](G)`. -/
private theorem largestSemisimpleQuotient_prod_fdRep_class_eq_add
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P Q : FiniteProjectiveGroupAlgebraModule K G) :
    [largestSemisimpleQuotient_prod_fdRep (K := K) (G := G) P Q]₀ =
      [largestSemisimpleQuotient_fdRep (K := K) (G := G) P]₀ +
        [largestSemisimpleQuotient_fdRep (K := K) (G := G) Q]₀ := by
  let X₁ : FDRep K G := largestSemisimpleQuotient_fdRep (K := K) (G := G) P
  let X₂ : FDRep K G := largestSemisimpleQuotient_prod_fdRep (K := K) (G := G) P Q
  let X₃ : FDRep K G := largestSemisimpleQuotient_fdRep (K := K) (G := G) Q
  let Pquot : ModuleCat K[G] :=
    ModuleCat.of K[G] (P.V ⧸ Module.jacobson K[G] P.V : Type u)
  let Qquot : ModuleCat K[G] :=
    ModuleCat.of K[G] (Q.V ⧸ Module.jacobson K[G] Q.V : Type u)
  let Yquot : ModuleCat K[G] :=
    ModuleCat.of K[G]
      (((P.V ⧸ Module.jacobson K[G] P.V : Type u) ×
        (Q.V ⧸ Module.jacobson K[G] Q.V : Type u) : Type u))
  let FRep : ModuleCat K[G] ⥤ Rep K G := Rep.ofModuleMonoidAlgebra
  let fRep :
      (forget₂ (FDRep K G) (Rep K G)).obj X₁ ⟶
        (forget₂ (FDRep K G) (Rep K G)).obj X₂ :=
    FRep.map (ModuleCat.ofHom (LinearMap.inl K[G] Pquot Qquot))
  let gRep :
      (forget₂ (FDRep K G) (Rep K G)).obj X₂ ⟶
        (forget₂ (FDRep K G) (Rep K G)).obj X₃ :=
    FRep.map (ModuleCat.ofHom (LinearMap.snd K[G] Pquot Qquot))
  let f : X₁ ⟶ X₂ := (FDRep.forget₂HomLinearEquiv X₁ X₂) fRep
  let g : X₂ ⟶ X₃ := (FDRep.forget₂HomLinearEquiv X₂ X₃) gRep
  have hf : (forget₂ (FDRep K G) (Rep K G)).map f = fRep := by
    change (FDRep.forget₂HomLinearEquiv X₁ X₂).symm
        ((FDRep.forget₂HomLinearEquiv X₁ X₂) fRep) = fRep
    exact (FDRep.forget₂HomLinearEquiv X₁ X₂).left_inv fRep
  have hg : (forget₂ (FDRep K G) (Rep K G)).map g = gRep := by
    change (FDRep.forget₂HomLinearEquiv X₂ X₃).symm
        ((FDRep.forget₂HomLinearEquiv X₂ X₃) gRep) = gRep
    exact (FDRep.forget₂HomLinearEquiv X₂ X₃).left_inv gRep
  let S : ShortComplex (FDRep K G) := ShortComplex.mk f g (by
    apply (forget₂ (FDRep K G) (Rep K G)).map_injective
    rw [Functor.map_comp, hf, hg]
    ext x
    rfl)
  let SRep : ShortComplex (Rep K G) := ShortComplex.mk fRep gRep (by
    ext x
    rfl)
  have hMod : (SRep.map (forget₂ (Rep K G) (ModuleCat K))).ShortExact := by
    -- Forget to `ModuleCat K`, where the product sequence is the standard split exact sequence.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.moduleCat_exact_iff]
      intro y hy
      rcases y with ⟨y₁, y₂⟩
      change y₂ = 0 at hy
      refine ⟨y₁, ?_⟩
      cases hy
      rfl
    · rw [ModuleCat.mono_iff_injective]
      intro x y hxy
      simpa using congrArg Prod.fst hxy
    · rw [ModuleCat.epi_iff_surjective]
      intro y
      exact ⟨(0, y), rfl⟩
  have hRep' : SRep.ShortExact := by
    -- Reflect short exactness from `ModuleCat K` back to `Rep K G`.
    apply (CategoryTheory.ShortExact.shortExact_map_iff
      (S := SRep) (F := forget₂ (Rep K G) (ModuleCat K))).1
    simpa using hMod
  have hRep : (S.map (forget₂ (FDRep K G) (Rep K G))).ShortExact := by
    -- The `Rep`-image of the `FDRep` short complex is definitionally the same sequence.
    simpa [S, SRep, hf, hg] using hRep'
  have hS : S.ShortExact := by
    -- Reflect exactness and mono/epi back to `FDRep`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        ((S.exact_map_iff_of_faithful (forget₂ (FDRep K G) (Rep K G))).1 hRep.exact)
    · exact (forget₂ (FDRep K G) (Rep K G)).mono_of_mono_map hRep.mono_f
    · exact (forget₂ (FDRep K G) (Rep K G)).epi_of_epi_map hRep.epi_g
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := K) (G := G) S hS
  simpa [X₁, X₂, X₃, S] using hrelation

/-- Helper for Corollary 14-14.4-3: once the underlying `ModuleCat K[G]` short exact sequence is
known, the largest semisimple quotient of the middle term is linearly equivalent to the product of
the two outer largest semisimple quotients. -/
private theorem largestSemisimpleQuotient_middle_nonempty_linearEquiv_prod
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule K G))
    (hUnderlying :
      (ShortComplex.mk S.f.hom.hom S.g.hom.hom
        (finiteProjective_underlying_moduleCat_zero (A := K) (G := G) S)).ShortExact) :
    Nonempty
      ((S.X₂.V ⧸ Module.jacobson K[G] S.X₂.V) ≃ₗ[K[G]]
        (S.X₁.V ⧸ Module.jacobson K[G] S.X₁.V) ×
          (S.X₃.V ⧸ Module.jacobson K[G] S.X₃.V)) := by
  let Smod : ShortComplex (ModuleCat K[G]) :=
    ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (A := K) (G := G) S)
  -- Split the middle term in `ModuleCat K[G]`, then descend that splitting to Jacobson quotients.
  let _ : Module.Finite K K[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing K[G] := IsArtinianRing.of_finite K K[G]
  let _ : IsArtinian K[G] S.X₁.V := by infer_instance
  let _ : IsArtinian K[G] S.X₃.V := by infer_instance
  obtain ⟨e⟩ :=
    moduleCat_shortExact_middle_nonempty_linearEquiv_prod (R := K[G]) (S := Smod) hUnderlying
  let q :
      S.X₁.V × S.X₃.V →ₗ[K[G]]
        S.X₂.V ⧸ Module.jacobson K[G] S.X₂.V :=
    (Module.jacobson K[G] S.X₂.V).mkQ.comp e.toLinearMap
  have hq_surj : Function.Surjective q := by
    intro y
    obtain ⟨x₂, rfl⟩ := Submodule.mkQ_surjective (Module.jacobson K[G] S.X₂.V) y
    obtain ⟨x, rfl⟩ := e.surjective x₂
    exact ⟨x, rfl⟩
  have hker :
      q.ker = Module.jacobson K[G] (S.X₁.V × S.X₃.V) := by
    -- The split equivalence identifies the kernel of the quotient map with the Jacobson radical
    -- of the product module.
    calc
      q.ker = Submodule.comap e.toLinearMap (Module.jacobson K[G] S.X₂.V) := by
        simpa [q] using
          (LinearMap.ker_comp e.toLinearMap (Module.jacobson K[G] S.X₂.V).mkQ)
      _ = Module.jacobson K[G] (S.X₁.V × S.X₃.V) := by
        simpa using
          (Module.comap_jacobson_of_bijective
            (R := K[G]) (R₂ := K[G]) (τ₁₂ := RingHom.id K[G]) (f := e.toLinearMap)
            e.bijective)
  have hquot :
      ((S.X₁.V × S.X₃.V) ⧸ Module.jacobson K[G] (S.X₁.V × S.X₃.V)) ≃ₗ[K[G]]
        (S.X₂.V ⧸ Module.jacobson K[G] S.X₂.V) := by
    -- Replace the quotient by the Jacobson radical with the quotient by `ker q`.
    exact
      (Submodule.quotEquivOfEq
        (Module.jacobson K[G] (S.X₁.V × S.X₃.V)) q.ker hker.symm).trans
        (LinearMap.quotKerEquivOfSurjective q hq_surj)
  obtain ⟨eprod⟩ := largestSemisimpleQuotient_prod_linearEquiv
    (R := K[G]) (P := S.X₁.V) (Q := S.X₃.V)
  exact ⟨hquot.symm.trans eprod⟩

/-- Helper for Corollary 14-14.4-3: in the field case, the largest semisimple quotient turns a
short exact sequence of projective `K[G]`-modules into the corresponding additive relation in
`R₀[K](G)`. -/
private theorem largestSemisimpleQuotient_class_middle_eq_left_add_right
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule K G)) (hS : S.ShortExact) :
    [largestSemisimpleQuotient_fdRep S.X₂]₀ =
      [largestSemisimpleQuotient_fdRep S.X₁]₀ + [largestSemisimpleQuotient_fdRep S.X₃]₀ := by
  let Smod : ShortComplex (ModuleCat K[G]) :=
    ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (A := K) (G := G) S)
  have hUnderlying : Smod.ShortExact :=
    finiteProjective_shortExact_underlying_moduleCat_shortExact_field
      (K := K) (G := G) S hS
  obtain ⟨equot⟩ :=
    largestSemisimpleQuotient_middle_nonempty_linearEquiv_prod (K := K) (G := G) S hUnderlying
  have hprod_iso :
      Nonempty
        (largestSemisimpleQuotient_fdRep S.X₂ ≅
          largestSemisimpleQuotient_prod_fdRep (K := K) (G := G) S.X₁ S.X₃) := by
    -- Convert the quotient-module linear equivalence into an isomorphism of the corresponding
    -- finite-dimensional representations.
    let FRep : ModuleCat K[G] ⥤ Rep K G := Rep.ofModuleMonoidAlgebra
    let _ :
        Module.Finite K
          (FRep.obj (ModuleCat.of K[G] (S.X₂.V ⧸ Module.jacobson K[G] S.X₂.V))) :=
      largestSemisimpleQuotient_toRep_moduleFinite (K := K) (G := G) S.X₂
    let _ :
        Module.Finite K
          (FRep.obj
            (ModuleCat.of K[G]
              ((S.X₁.V ⧸ Module.jacobson K[G] S.X₁.V) ×
                (S.X₃.V ⧸ Module.jacobson K[G] S.X₃.V)))) :=
      largestSemisimpleQuotient_prod_toRep_moduleFinite (K := K) (G := G) S.X₁ S.X₃
    let iRep :
        FRep.obj (ModuleCat.of K[G] (S.X₂.V ⧸ Module.jacobson K[G] S.X₂.V)) ≅
          FRep.obj
            (ModuleCat.of K[G]
              ((S.X₁.V ⧸ Module.jacobson K[G] S.X₁.V) ×
                (S.X₃.V ⧸ Module.jacobson K[G] S.X₃.V))) :=
      FRep.mapIso equot.toModuleIso
    exact
      ⟨by
        simpa [largestSemisimpleQuotient_fdRep, largestSemisimpleQuotient_prod_fdRep] using
          (Representation.Equiv.toFDRepIso (Representation.equivOfIso iRep))⟩
  have hmid :
      [largestSemisimpleQuotient_fdRep S.X₂]₀ =
        [largestSemisimpleQuotient_prod_fdRep (K := K) (G := G) S.X₁ S.X₃]₀ := by
    exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) hprod_iso
  calc
    [largestSemisimpleQuotient_fdRep S.X₂]₀ =
        [largestSemisimpleQuotient_prod_fdRep (K := K) (G := G) S.X₁ S.X₃]₀ := hmid
    _ = [largestSemisimpleQuotient_fdRep S.X₁]₀ +
          [largestSemisimpleQuotient_fdRep S.X₃]₀ :=
        largestSemisimpleQuotient_prod_fdRep_class_eq_add (K := K) (G := G) S.X₁ S.X₃

/-- Helper for Corollary 14-14.4-3: the free-abelian lift from projective classes to the classes
of their largest semisimple quotients. -/
private abbrev largestSemisimpleQuotientLift
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G] :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule K G) →+ R₀[K](G) :=
  FreeAbelianGroup.lift fun P ↦ [largestSemisimpleQuotient_fdRep P]₀

/-- Helper for Corollary 14-14.4-3: the defining projective Grothendieck relations are annihilated
after passing to largest semisimple quotients in the field case. -/
private theorem
    finiteProjectiveGroupAlgebraGrothendieckRelations_le_largestSemisimpleQuotientLift_ker
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G] :
    finiteProjectiveGroupAlgebraGrothendieckRelations (A := K) (G := G) ≤
      (largestSemisimpleQuotientLift (K := K) (G := G)).ker := by
  -- Evaluate the free lift on each generator relation and rewrite it with the largest-semisimple
  -- quotient class identity.
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    largestSemisimpleQuotientLift (K := K) (G := G)
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [largestSemisimpleQuotientLift, map_sub]
  rw [sub_eq_zero]
  rw [sub_eq_iff_eq_add]
  rw [add_comm]
  exact largestSemisimpleQuotient_class_middle_eq_left_add_right (K := K) (G := G) S hS

/-- Helper for Corollary 14-14.4-3: in the field case, passage to the largest semisimple quotient
descends to a homomorphism `P₀[K](G) →+ R₀[K](G)`. -/
private def largestSemisimpleQuotientHom
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G] :
    finiteProjectiveGroupAlgebraGrothendieckGroup (A := K) (G := G) →+ R₀[K](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations (A := K) (G := G))
    (largestSemisimpleQuotientLift (K := K) (G := G))
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_largestSemisimpleQuotientLift_ker
      (K := K) (G := G))

/-- Helper for Corollary 14-14.4-3: the field-side largest-semisimple-quotient homomorphism sends
a projective generator class to the class of its largest semisimple quotient. -/
@[simp] private theorem largestSemisimpleQuotientHom_projectiveClass_eq
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P : FiniteProjectiveGroupAlgebraModule K G) :
    largestSemisimpleQuotientHom [P]ₚ₀ =
      [largestSemisimpleQuotient_fdRep P]₀ := by
  -- The descended homomorphism is the quotient lift of the free-abelian generator map.
  rfl

/-- Helper for Corollary 14-14.4-3: over a field, equality in `P₀[k](G)` should be converted to a
linear equivalence by passing through largest semisimple quotients. -/
private theorem field_case_projective_class_eq_iff_nonempty_linearEquiv
    {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (P Q : FiniteProjectiveGroupAlgebraModule K G) :
    [P]ₚ₀ = [Q]ₚ₀ ↔
        Nonempty (P.V ≃ₗ[K[G]] Q.V) := by
  constructor
  · intro hclass
    let _ : Module.Finite K K[G] := MonoidAlgebra.moduleFinite
    let _ : IsArtinianRing K[G] := IsArtinianRing.of_finite K K[G]
    let _ : IsArtinian K[G] P.V := by infer_instance
    let _ : IsArtinian K[G] Q.V := by infer_instance
    have hquotClass :
        [largestSemisimpleQuotient_fdRep (K := K) (G := G) P]₀ =
          [largestSemisimpleQuotient_fdRep (K := K) (G := G) Q]₀ := by
      -- Push the projective class equality through the largest-semisimple-quotient homomorphism.
      simpa using congrArg (largestSemisimpleQuotientHom (K := K) (G := G)) hclass
    have hPsemi :
        IsSemisimpleRepresentation (largestSemisimpleQuotient_fdRep (K := K) (G := G) P).ρ := by
      -- The quotient representation attached to `P` is semisimple before and after rebundling.
      simpa [largestSemisimpleQuotient_fdRep] using
        largestSemisimpleQuotient_toRep_isSemisimpleRepresentation (K := K) (G := G) P
    have hQsemi :
        IsSemisimpleRepresentation (largestSemisimpleQuotient_fdRep (K := K) (G := G) Q).ρ := by
      -- Apply the same semisimplicity bridge to `Q`.
      simpa [largestSemisimpleQuotient_fdRep] using
        largestSemisimpleQuotient_toRep_isSemisimpleRepresentation (K := K) (G := G) Q
    obtain ⟨i⟩ :=
      (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple hPsemi hQsemi).mp
        hquotClass
    have hquotLin :
        Nonempty ((P.V ⧸ Module.jacobson K[G] P.V) ≃ₗ[K[G]]
          (Q.V ⧸ Module.jacobson K[G] Q.V)) := by
      -- Convert the `FDRep` isomorphism back to a linear equivalence of the quotient modules.
      obtain ⟨eAs⟩ :=
        moduleLinearEquiv_of_fdRep_iso (K := K) (G := G)
          (largestSemisimpleQuotient_fdRep (K := K) (G := G) P)
          (largestSemisimpleQuotient_fdRep (K := K) (G := G) Q) i
      obtain ⟨eP⟩ :=
        nonempty_ofModuleMonoidAlgebra_asModuleLinearEquiv
          (K := K) (G := G) (P.V ⧸ Module.jacobson K[G] P.V)
      obtain ⟨eQ⟩ :=
        nonempty_ofModuleMonoidAlgebra_asModuleLinearEquiv
          (K := K) (G := G) (Q.V ⧸ Module.jacobson K[G] Q.V)
      exact ⟨(eP.symm.trans eAs).trans eQ⟩
    -- Lift the quotient equivalence to the original projective modules through projective
    -- envelopes.
    exact projective_linearEquiv_of_largestSemisimpleQuotient_linearEquiv P Q hquotLin
  · intro hPQ
    -- The reverse implication is still just Grothendieck-class invariance under isomorphism.
    exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso <|
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv P Q).2 hPQ

/-- Corollary 14-14.4-3 in module-theoretic bridge form: equality in `P_A(G)` is equivalent to
the existence of an `A[G]`-linear equivalence between the underlying modules. -/
theorem finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv
    (P Q : FiniteProjectiveGroupAlgebraModule A G) :
    [P]ₚ₀ = [Q]ₚ₀ ↔
        Nonempty (P.V ≃ₗ[A[G]] Q.V) := by
  constructor
  · intro hclass
    have hred :
        [P.residueFieldReduction]ₚ₀ = [Q.residueFieldReduction]ₚ₀ := by
      -- Apply the reduction homomorphism to move the problem to the residue field.
      simpa using congrArg (projectiveGrothendieckReductionHom (A := A) (G := G)) hclass
    let Pk : FiniteProjectiveGroupAlgebraModule k G := P.residueFieldReduction
    let Qk : FiniteProjectiveGroupAlgebraModule k G := Q.residueFieldReduction
    have hred_lin :
        Nonempty (((k ⊗[A] P.V) ≃ₗ[k[G]] (k ⊗[A] Q.V))) := by
      -- Over the residue field, the field-case classifier supplies the reduced equivalence.
      have hfield' :
          Nonempty
            (P.residueFieldReduction.V ≃ₗ[k[G]] Q.residueFieldReduction.V) :=
        (@field_case_projective_class_eq_iff_nonempty_linearEquiv
          k inferInstance G inferInstance inferInstance
          P.residueFieldReduction Q.residueFieldReduction).1 hred
      have hfield :
          Nonempty (Pk.V ≃ₗ[k[G]] Qk.V) := by
        simpa [Pk, Qk] using hfield'
      simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
        FiniteProjectiveGroupAlgebraModule.V, Pk, Qk] using hfield
    exact
      (projective_monoidAlgebra_nonempty_linearEquiv_iff_reduction_nonempty_linearEquiv
        (Λ := A) (G := G) (P := P.V) (P' := Q.V)
        (by infer_instance) (by infer_instance)).2 hred_lin
  · intro hPQ
    -- The reverse direction is class invariance under an isomorphism in the owner category.
    exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso <|
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv P Q).2 hPQ

-- Proof sketch: once the module-theoretic bridge is available, translate an owner isomorphism to
-- a linear equivalence and apply the class-equality criterion from the bridge theorem.
/-- Corollary 14-14.4-3: two finite projective `A[G]`-modules determine the same class in
`P_A(G)` if and only if they are isomorphic in the canonical owner category of finite projective
`A[G]`-modules. -/
theorem finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso
    (P Q : FiniteProjectiveGroupAlgebraModule A G) :
    [P]ₚ₀ = [Q]ₚ₀ ↔
        Nonempty (P ≅ Q) := by
  -- Translate the owner-level isomorphism statement to the already proved module-level bridge.
  rw [finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv]
  exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv P Q

end ProjectiveGrothendieckGroup

scoped[Representation] notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

end Representation
