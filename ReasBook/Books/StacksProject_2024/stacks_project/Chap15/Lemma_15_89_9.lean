import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Quotient
import StacksProject_2024.stacks_project.Chap10.Lemma_10_8_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_89_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (I : Ideal R)

/- Domain-style sampling for the tensor base-change statement:
- primary domain: commutative algebra of ideal-power torsion modules under scalar extension and
  tensor products;
- sampled owners: `Module.IsIdealPowerTorsion`, `Ideal.quotientMap`, `TensorProduct.mk`;
- best owner abstraction: the canonical tensor-base-change unit `TensorProduct.mk R R' M 1 :
  M →ₗ[R] R' ⊗[R] M`; the symmetric map `M → M ⊗[R] R'` is only its tensor-symmetry view;
- primitive data: the ideal `I`, the algebra map `R → R'`, the module `M`, the torsion
  hypothesis, and the quotient-map bijectivity family;
- derived API: bijectivity of the base-change unit on `I`-power torsion modules.

Layer triage:
- `source-facing`: the tensor-base-change bijectivity statement below;
- `core/canonical`: `Ideal.quotientMap` and `TensorProduct.mk`;
- `bridge/view`: the tensor-symmetry reinterpretation `M → M ⊗[R] R'`.
-/

variable {M : Type u} [AddCommMonoid M] [Module R M]

open scoped IdealPowerTorsion TensorProduct
open CategoryTheory CategoryTheory.Limits ModuleCat MonoidalCategory

variable {N : Type u} [AddCommMonoid N] [Module R N]

/-- Helper for Lemma 15.89.9: the finite `I^n`-torsion stages exhaust any `I`-power torsion
module. -/
theorem idealPowerTorsion_iSup_powerTorsion_eq_top
    (hM : Module.IsIdealPowerTorsion I M) :
    (⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) = ⊤ := by
  -- Unpack the elementwise torsion witnesses and place each element into one finite stage.
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  rw [Module.isIdealPowerTorsion_iff] at hM
  obtain ⟨n, hn⟩ := hM x
  refine Submodule.mem_iSup_of_mem n ?_
  rw [show Ideal.powerTorsion I M (n : ℕ) = M[I^(n : ℕ)] by rfl]
  rw [Submodule.mem_torsionBySet_iff]
  exact hn

/-- Helper for Lemma 15.89.9: every finite `I^n`-torsion stage is annihilated by `I^n`. -/
theorem powerTorsion_le_annihilator
    (n : ℕ) :
    I ^ n ≤ Module.annihilator R (Ideal.powerTorsion I N n) := by
  -- The stage is defined by the property that every coefficient from `I^n` acts trivially.
  intro a ha
  rw [Submodule.mem_annihilator]
  intro x hx
  rw [show Ideal.powerTorsion I N n = N[I^n] by rfl] at hx
  rw [Submodule.mem_torsionBySet_iff] at hx
  exact hx ⟨a, ha⟩

/-- Helper for Lemma 15.89.9: the finite `I^n`-torsion stages form an increasing system with
respect to the positive-power index. -/
theorem powerTorsion_mono
    {n m : ℕ+}
    (hnm : n ≤ m) :
    Ideal.powerTorsion I M (n : ℕ) ≤ Ideal.powerTorsion I M (m : ℕ) := by
  -- Move an element from stage `n` to stage `m` by restricting the annihilating coefficients from
  -- `I ^ m` to `I ^ n`.
  intro x hx
  rw [show Ideal.powerTorsion I M (n : ℕ) = M[I^(n : ℕ)] by rfl] at hx
  rw [show Ideal.powerTorsion I M (m : ℕ) = M[I^(m : ℕ)] by rfl]
  rw [Submodule.mem_torsionBySet_iff] at hx
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  exact hx ⟨a, Ideal.pow_le_pow_right (show (n : ℕ) ≤ (m : ℕ) from hnm) a.2⟩

/-- Helper for Lemma 15.89.9: each finite power-torsion stage is an additive commutative group
because it is an `R`-module over a commutative ring. -/
local instance powerTorsionStageAddCommGroup (n : ℕ) :
    AddCommGroup (Ideal.powerTorsion I M n) :=
  Module.addCommMonoidToAddCommGroup R

/-- Helper for Lemma 15.89.9: the union of the finite power-torsion stages is an additive
commutative group for the same reason. -/
local instance powerTorsionStageISupAddCommGroup :
    AddCommGroup ((⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) : Submodule R M) :=
  Module.addCommMonoidToAddCommGroup R

/-- Helper for Lemma 15.89.9: the source proof uses the filtered system of finite power-torsion
stages indexed by positive integers. -/
noncomputable def powerTorsionStageDiagram : ℕ+ ⥤ ModuleCat R where
  obj n := ModuleCat.of R (Ideal.powerTorsion I M (n : ℕ))
  map f := ModuleCat.ofHom <|
    Submodule.inclusion
      (powerTorsion_mono (I := I) (M := M) (leOfHom f))
  map_id n := by
    -- The identity transition is the identity inclusion on the same torsion stage.
    ext x
    rfl
  map_comp f g := by
    -- Successive stage transitions are literally the composite of the two subtype inclusions.
    ext x
    rfl

/-- Helper for Lemma 15.89.9: every structure map in the stage diagram is literally the subtype
inclusion into the later torsion stage. -/
@[simp] theorem powerTorsionStageDiagram_map_coe
    {n m : ℕ+}
    (f : n ⟶ m)
    (x : Ideal.powerTorsion I M (n : ℕ)) :
    Subtype.val (((powerTorsionStageDiagram I (M := M)).map f).hom x) = x := by
  -- The diagram map is defined using `Submodule.inclusion`, so its underlying value is unchanged.
  rfl

/-- Helper for Lemma 15.89.9: the concrete direct limit of the stage diagram maps to the union of
the finite power-torsion stages by sending each stage generator to the corresponding subtype
element. -/
noncomputable def powerTorsionStageDirectLimitToiSup :
    Module.DirectLimit
        (fun n : ℕ+ ↦ Ideal.powerTorsion I M (n : ℕ))
        (fun _ _ hij ↦
          Submodule.inclusion (powerTorsion_mono (I := I) (M := M) hij)) →ₗ[R]
      ((⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) : Submodule R M) := by
  let G : ℕ+ → Type u := fun n ↦ Ideal.powerTorsion I M (n : ℕ)
  let μ : ∀ i j, i ≤ j → G i →ₗ[R] G j := fun i j hij ↦
    Submodule.inclusion (powerTorsion_mono (I := I) (M := M) hij)
  let ν : ∀ n : ℕ+, G n →ₗ[R] ((⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) : Submodule R M) :=
    fun n ↦
      Submodule.inclusion <|
        show Ideal.powerTorsion I M (n : ℕ) ≤
            ((⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) : Submodule R M) from
          le_iSup (fun n : ℕ+ ↦ Ideal.powerTorsion I M (n : ℕ)) n
  refine Module.DirectLimit.lift R ℕ+ G μ ν ?_
  intro _ _ hij x
  -- Both routes to the union stage are the same subtype inclusion into `M`.
  ext
  rfl

/-- Helper for Lemma 15.89.9: on a stage generator of the direct limit, the comparison map to the
union of the finite power-torsion stages is the literal subtype inclusion. -/
@[simp] theorem powerTorsionStageDirectLimitToiSup_of
    (n : ℕ+)
    (x : Ideal.powerTorsion I M (n : ℕ)) :
    powerTorsionStageDirectLimitToiSup (I := I) (M := M)
        (Module.DirectLimit.of R ℕ+
          (fun n : ℕ+ ↦ Ideal.powerTorsion I M (n : ℕ))
          (fun _ _ hij ↦
            Submodule.inclusion (powerTorsion_mono (I := I) (M := M) hij))
          n x) =
      ⟨x, Submodule.mem_iSup_of_mem n x.2⟩ := by
  -- Evaluate `Module.DirectLimit.lift` on `of`, then compare the two subtype inclusions by value.
  simpa only [powerTorsionStageDirectLimitToiSup, Module.DirectLimit.lift_of] using
    (show
        (Submodule.inclusion
            (show Ideal.powerTorsion I M (n : ℕ) ≤
                ((⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) : Submodule R M) from
              le_iSup (fun n : ℕ+ ↦ Ideal.powerTorsion I M (n : ℕ)) n)
            x) =
          ⟨x, Submodule.mem_iSup_of_mem n x.2⟩ from
      Subtype.ext rfl)

/-- Helper for Lemma 15.89.9: the explicit direct limit of the positive power-torsion stages is
canonically the directed union of those stages. -/
noncomputable def power_torsion_stage_directLimit_linearEquiv_iSup :
    Module.DirectLimit
        (fun n : ℕ+ ↦ Ideal.powerTorsion I M (n : ℕ))
        (fun _ _ hij ↦
          Submodule.inclusion (powerTorsion_mono (I := I) (M := M) hij)) ≃ₗ[R]
      ((⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) : Submodule R M) := by
  -- Prove bijectivity of the explicit forward map by working with direct-limit representatives.
  refine LinearEquiv.ofBijective (powerTorsionStageDirectLimitToiSup (I := I) (M := M)) ?_
  constructor
  · intro z₁ z₂ hz
    have hz0 :
        powerTorsionStageDirectLimitToiSup (I := I) (M := M) (z₁ - z₂) = 0 := by
      rw [map_sub, hz, sub_self]
    -- It is enough to check the kernel on a single direct-limit representative.
    have hkernel : z₁ - z₂ = 0 := by
      obtain ⟨n, x, hxrep⟩ := Module.DirectLimit.exists_of (z₁ - z₂)
      rw [← hxrep] at hz0 ⊢
      have hx :
          (⟨x, Submodule.mem_iSup_of_mem n x.2⟩ :
            ((⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) : Submodule R M)) = 0 := by
        simpa using hz0
      have hxval : (x : M) = 0 := by
        exact congrArg Subtype.val hx
      have hx0 : x = 0 := by
        apply Subtype.ext
        simpa using hxval
      simpa [hx0]
    exact sub_eq_zero.mp hkernel
  · intro y
    have hdir :
        Directed (· ≤ ·) (fun n : ℕ+ ↦ Ideal.powerTorsion I M (n : ℕ)) := by
      intro i j
      refine ⟨max i j, ?_, ?_⟩
      · exact powerTorsion_mono (I := I) (M := M) (le_max_left _ _)
      · exact powerTorsion_mono (I := I) (M := M) (le_max_right _ _)
    obtain ⟨n, hn⟩ :=
      (Submodule.mem_iSup_of_directed
        (fun n : ℕ+ ↦ Ideal.powerTorsion I M (n : ℕ)) hdir).mp y.2
    refine ⟨Module.DirectLimit.of R ℕ+
        (fun n : ℕ+ ↦ Ideal.powerTorsion I M (n : ℕ))
        (fun _ _ hij ↦
          Submodule.inclusion (powerTorsion_mono (I := I) (M := M) hij))
        n ⟨(y : M), hn⟩, ?_⟩
    -- The chosen stage witness maps back to the original element of the directed union.
    rw [powerTorsionStageDirectLimitToiSup_of]

/-- Helper for Lemma 15.89.9: if an ideal lies in the annihilator of a module, then its action on
the whole module is zero. -/
theorem smul_top_eq_bot_of_le_annihilator
    {T : Type u} [AddCommMonoid T] [Module R T]
    (J : Ideal R)
    (hJann : J ≤ Module.annihilator R T) :
    J • (⊤ : Submodule R T) = ⊥ := by
  -- Translate annihilator containment into the vanishing of the ideal action on the whole module.
  have htop : J ≤ (⊤ : Submodule R T).annihilator := by
    simpa [Submodule.annihilator_top] using hJann
  exact
    (Submodule.le_annihilator_iff : J ≤ (⊤ : Submodule R T).annihilator ↔
      J • (⊤ : Submodule R T) = ⊥).mp htop

/-- Helper for Lemma 15.89.9: the algebra-valued quotient map has the same underlying function as
the ring-valued quotient map. -/
theorem quotientMapₐ_bijective_of_quotientMap_bijective
    (J : Ideal R)
    (hquotJ : Function.Bijective
      (Ideal.quotientMap
        (J.map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    Function.Bijective
      (Ideal.quotientMapₐ
        (R₁ := R)
        (I := J)
        (J := J.map (algebraMap R R'))
        (f := Algebra.ofId R R')
        Ideal.le_comap_map) := by
  simpa using hquotJ

/-- Helper for Lemma 15.89.9: if `I ^ n` annihilates `T`, then the quotient-ring bijection on
`R / I ^ n` produces the finite-stage tensor base-change linear equivalence. -/
noncomputable def tensor_base_change_stage_linearEquiv_of_quotient
    (n : ℕ+)
    {T : Type u} [AddCommMonoid T] [Module R T]
    (hJann : I ^ (n : ℕ) ≤ Module.annihilator R T)
    (hquotn : Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    T ≃ₗ[R] R' ⊗[R] T :=
  let J : Ideal R := I ^ (n : ℕ)
  let _ : AddCommGroup T := Module.addCommMonoidToAddCommGroup R
  let eStage : ((R ⧸ J) ⊗[R] T) ≃ₗ[R] T :=
    (TensorProduct.quotTensorEquivQuotSMul T J).trans
      ((J • (⊤ : Submodule R T)).quotEquivOfEqBot
        (smul_top_eq_bot_of_le_annihilator (J := J) hJann))
  let eQuot : (R ⧸ J) ≃ₐ[R] (R' ⧸ J.map (algebraMap R R')) :=
    AlgEquiv.ofBijective
      (Ideal.quotientMapₐ
        (R₁ := R)
        (I := J)
        (J := J.map (algebraMap R R'))
        (f := Algebra.ofId R R')
        Ideal.le_comap_map)
      (quotientMapₐ_bijective_of_quotientMap_bijective (R' := R') J hquotn)
  eStage.symm.trans <|
    (LinearEquiv.rTensor T eQuot.toLinearEquiv).trans <|
      (LinearEquiv.rTensor T
        (LinearEquiv.restrictScalars R
          ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R' J).toLinearEquiv))).trans <|
        (TensorProduct.assoc R R' (R ⧸ J) T).trans <|
          LinearEquiv.lTensor R' eStage

/-- Helper for Lemma 15.89.9: on a generator `x : T`, the finite-stage linear equivalence agrees
with the canonical tensor base-change unit. -/
theorem tensor_base_change_stage_linearEquiv_of_quotient_apply
    (n : ℕ+)
    {T : Type u} [AddCommMonoid T] [Module R T]
    (hJann : I ^ (n : ℕ) ≤ Module.annihilator R T)
    (hquotn : Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map))
    (x : T) :
    tensor_base_change_stage_linearEquiv_of_quotient (I := I) (R' := R') n hJann hquotn x =
      TensorProduct.mk R R' T 1 x := by
  let J : Ideal R := I ^ (n : ℕ)
  let _ : AddCommGroup T := Module.addCommMonoidToAddCommGroup R
  let hsmul : J • (⊤ : Submodule R T) = ⊥ :=
    smul_top_eq_bot_of_le_annihilator (J := J) hJann
  let eStage : ((R ⧸ J) ⊗[R] T) ≃ₗ[R] T :=
    (TensorProduct.quotTensorEquivQuotSMul T J).trans
      ((J • (⊤ : Submodule R T)).quotEquivOfEqBot hsmul)
  let eQuot : (R ⧸ J) ≃ₐ[R] (R' ⧸ J.map (algebraMap R R')) :=
    AlgEquiv.ofBijective
      (Ideal.quotientMapₐ
        (R₁ := R)
        (I := J)
        (J := J.map (algebraMap R R'))
        (f := Algebra.ofId R R')
        Ideal.le_comap_map)
      (quotientMapₐ_bijective_of_quotientMap_bijective (R' := R') J hquotn)
  -- Evaluate the composite on a pure tensor; each bridge has a canonical generator formula.
  change
    (LinearEquiv.lTensor R' eStage)
        ((TensorProduct.assoc R R' (R ⧸ J) T)
          ((LinearEquiv.rTensor T
              (LinearEquiv.restrictScalars R
                ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R' J).toLinearEquiv)))
            ((LinearEquiv.rTensor T eQuot.toLinearEquiv) (eStage.symm x)))) =
      1 ⊗ₜ[R] x
  have hStage : eStage.symm x = 1 ⊗ₜ[R] x := by
    simp [eStage]
  have hQuot :
      (LinearEquiv.rTensor T eQuot.toLinearEquiv) (eStage.symm x) =
        (1 : R' ⧸ J.map (algebraMap R R')) ⊗ₜ[R] x := by
    rw [hStage]
    simp [eQuot]
  have hTensorQuot :
      (LinearEquiv.rTensor T
          (LinearEquiv.restrictScalars R
            ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R' J).toLinearEquiv)))
        ((LinearEquiv.rTensor T eQuot.toLinearEquiv) (eStage.symm x)) =
      (1 ⊗ₜ[R] (1 : R ⧸ J)) ⊗ₜ[R] x := by
    rw [hQuot]
    simp [Algebra.TensorProduct.one_def]
  rw [hTensorQuot, TensorProduct.assoc_tmul]
  simp [eStage]

/-- Helper for Lemma 15.89.9: the canonical tensor base-change unit is bijective on every module
annihilated by a positive power `I ^ n`. -/
theorem tensorBaseChange_bijective_of_annihilator_pow_le_of_quotientMapBijective
    (n : ℕ+)
    {T : Type u} [AddCommMonoid T] [Module R T]
    (hJann : I ^ (n : ℕ) ≤ Module.annihilator R T)
    (hquotn : Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    Function.Bijective (TensorProduct.mk R R' T 1) := by
  let e :=
    tensor_base_change_stage_linearEquiv_of_quotient
      (I := I) (R' := R') n hJann hquotn
  have he :
      ∀ x : T, e x = TensorProduct.mk R R' T 1 x := by
    intro x
    exact tensor_base_change_stage_linearEquiv_of_quotient_apply
      (I := I) (R' := R') n hJann hquotn x
  constructor
  · -- Compare the linear equivalence with the canonical map pointwise to get injectivity.
    intro x y hxy
    apply e.injective
    simpa [he x, he y] using hxy
  · -- Use the inverse linear equivalence to write every tensor as the image of some element.
    intro z
    refine ⟨e.symm z, ?_⟩
    simpa [he (e.symm z)] using e.apply_symm_apply z

section PowerTorsionStageColimit

variable {T : Type u} [AddCommGroup T] [Module R T]

/-- Helper for Lemma 15.89.9: the positive-power torsion diagram admits the explicit direct-limit
cocone whose point is the textbook quotient-model direct limit. -/
noncomputable def power_torsion_stage_directLimit_cocone :
    Cocone (powerTorsionStageDiagram (R := R) I (M := T)) where
  pt := ModuleCat.of R <|
    Module.DirectLimit
      (fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
      (fun i j hij ↦
        Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
  ι :=
    { app := fun n ↦
        ModuleCat.ofHom <|
          Module.DirectLimit.of R ℕ+
            (fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
            (fun i j hij ↦
              Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
            n
      naturality := fun n m f => by
        -- The direct-limit structure maps identify stage transition followed by `of` with the
        -- original stage injection into the direct limit.
        ext x
        simpa using
          (Module.DirectLimit.of_f
            (R := R)
            (ι := ℕ+)
            (G := fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
            (f := fun i j hij ↦
              Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
            (i := n)
            (j := m)
            (hij := leOfHom f)
            (x := x)) }

/-- Helper for Lemma 15.89.9: the explicit direct-limit cocone over the positive-power torsion
diagram satisfies the universal property of the colimit. -/
noncomputable def power_torsion_stage_directLimit_isColimit :
    IsColimit (power_torsion_stage_directLimit_cocone (R := R) (I := I) (T := T)) where
  desc s := ModuleCat.ofHom <|
    Module.DirectLimit.lift R ℕ+
      (fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
      (fun i j hij ↦
        Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
      (P := s.pt)
      (fun n ↦ (s.ι.app n).hom) <|
        by
          intro i j hij x
          -- The cocone condition on `s` is exactly the compatibility required by
          -- `Module.DirectLimit.lift`.
          simpa [powerTorsionStageDiagram] using congr(($((s.w (homOfLE hij))) x))
  fac s n := by
    -- On a stage generator, the universal map out of the direct limit recovers the given cocone
    -- leg.
    ext x
    let g : ∀ n : ℕ+, Ideal.powerTorsion I T (n : ℕ) →ₗ[R] s.pt :=
      fun n ↦ (s.ι.app n).hom
    have hg :
        ∀ i j hij x, g j ((Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij)) x) =
          g i x := by
      intro i j hij x
      simpa [g, powerTorsionStageDiagram] using congr(($((s.w (homOfLE hij))) x))
    exact
      (Module.DirectLimit.lift_of
        (R := R)
        (ι := ℕ+)
        (G := fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
        (f := fun i j hij ↦
          Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
        (P := s.pt)
        (g := g)
        (Hg := hg)
        x)
  uniq s m hm := by
    -- Compare maps out of the direct limit on the canonical stage generators.
    ext x
    let g : ∀ n : ℕ+, Ideal.powerTorsion I T (n : ℕ) →ₗ[R] s.pt :=
      fun n ↦ (s.ι.app n).hom
    have hg :
        ∀ i j hij x, g j ((Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij)) x) =
          g i x := by
      intro i j hij x
      simpa [g, powerTorsionStageDiagram] using congr(($((s.w (homOfLE hij))) x))
    obtain ⟨n, y, rfl⟩ :=
      Module.DirectLimit.exists_of
        (R := R)
        (ι := ℕ+)
        (G := fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
        (f := fun i j hij ↦
          Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
        x
    have hmny :
        m.hom
            (Module.DirectLimit.of R ℕ+
              (fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
              (fun i j hij ↦
                Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
              n y) =
          (s.ι.app n).hom y := by
      simpa [power_torsion_stage_directLimit_cocone] using
        congrArg (fun f => f.hom y) (hm n)
    have hdescy :
        (Module.DirectLimit.lift R ℕ+
            (fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
            (fun i j hij ↦
              Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
            (P := s.pt)
            g
            hg)
          (Module.DirectLimit.of R ℕ+
            (fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
            (fun i j hij ↦
              Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
            n y) =
          (s.ι.app n).hom y :=
      Module.DirectLimit.lift_of
        (R := R)
        (ι := ℕ+)
        (G := fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
        (f := fun i j hij ↦
          Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
        (P := s.pt)
        (g := g)
        (Hg := hg)
        y
    exact hmny.trans hdescy.symm

/-- Helper for Lemma 15.89.9: after the positive-power torsion stages exhaust `T`, the explicit
direct limit identifies with `T` itself. -/
noncomputable def power_torsion_stage_directLimit_to_module_linearEquiv
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤) :
    Module.DirectLimit
        (fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
        (fun _ _ hij ↦
          Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij)) ≃ₗ[R] T :=
  (power_torsion_stage_directLimit_linearEquiv_iSup (I := I) (M := T)).trans <|
    (LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv

/-- Helper for Lemma 15.89.9: after identifying the directed union of the positive power-torsion
stages with `⊤`, the direct-limit generator at stage `n` maps to its underlying element of `T`. -/
@[simp] theorem power_torsion_stage_directLimit_to_module_of
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤)
    (n : ℕ+)
    (x : Ideal.powerTorsion I T (n : ℕ)) :
    power_torsion_stage_directLimit_to_module_linearEquiv (I := I) (T := T) htop
      (Module.DirectLimit.of R ℕ+
        (fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
        (fun _ _ hij ↦
          Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
        n x) = x := by
  -- First evaluate the direct-limit comparison on the chosen generator, then forget the proof
  -- component through the identification of the directed union with `⊤`.
  change
    ((LinearEquiv.ofEq
          ((⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) : Submodule R T)
          ⊤
          htop).trans
        Submodule.topEquiv)
      (powerTorsionStageDirectLimitToiSup (I := I) (M := T)
        (Module.DirectLimit.of R ℕ+
          (fun n : ℕ+ ↦ Ideal.powerTorsion I T (n : ℕ))
          (fun _ _ hij ↦
            Submodule.inclusion (powerTorsion_mono (I := I) (M := T) hij))
          n x)) = x
  rw [powerTorsionStageDirectLimitToiSup_of]
  rfl

/-- Helper for Lemma 15.89.9: once the torsion stages exhaust `T`, the literal inclusion cocone
with point `T` is the colimit cocone for the stage diagram. -/
noncomputable def power_torsion_stage_module_cocone :
    Cocone (powerTorsionStageDiagram (R := R) I (M := T)) where
  pt := ModuleCat.of R T
  ι :=
    { app := fun n ↦
        ModuleCat.ofHom (Submodule.subtype (Ideal.powerTorsion I T (n : ℕ)))
      naturality := fun n m f => by
        -- Both routes are the same subtype inclusion into the ambient module.
        ext x
        rfl }

/-- Helper for Lemma 15.89.9: transport the direct-limit colimit model across the already-proved
direct-limit equivalence to obtain the colimit cocone with point `T`. -/
noncomputable def power_torsion_stage_module_isColimit
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤) :
    IsColimit (power_torsion_stage_module_cocone (R := R) (I := I) (T := T)) := by
  let e :=
    power_torsion_stage_directLimit_to_module_linearEquiv (I := I) (T := T) htop
  let i :
      power_torsion_stage_directLimit_cocone (R := R) (I := I) (T := T) ≅
        power_torsion_stage_module_cocone (R := R) (I := I) (T := T) := by
    refine Cocone.ext e.toModuleIso ?_
    intro n
    -- The direct-limit `of` map becomes the literal stage inclusion into `T`.
    ext x
    exact power_torsion_stage_directLimit_to_module_of (I := I) (T := T) htop n x
  exact
    (power_torsion_stage_directLimit_isColimit (R := R) (I := I) (T := T)).ofIsoColimit i

/-- Helper for Lemma 15.89.9: the colimit of the positive power-torsion stage diagram is the
ambient module once the stages are known to exhaust `M`. -/
noncomputable def power_torsion_stage_colimit_iso
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤) :
    colimit (powerTorsionStageDiagram (R := R) I (M := T)) ≅ ModuleCat.of R T := by
  -- Compare the chosen categorical colimit with the explicit cocone on `T` built from the direct
  -- limit of the source filtration.
  exact
    IsColimit.coconePointUniqueUpToIso
      (colimit.isColimit (powerTorsionStageDiagram (R := R) I (M := T)))
      (power_torsion_stage_module_isColimit (R := R) (I := I) (T := T) htop)

/-- Helper for Lemma 15.89.9: after identifying the colimit of the positive power-torsion stages
with `M`, each colimit leg is the literal inclusion of that stage into `M`. -/
theorem power_torsion_stage_colimit_iso_hom_ι
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤)
    (n : ℕ+) :
    colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
        (power_torsion_stage_colimit_iso (I := I) (T := T) htop).hom =
      ModuleCat.ofHom (Submodule.subtype (Ideal.powerTorsion I T (n : ℕ))) := by
  -- The colimit-point comparison isomorphism identifies each chosen colimit leg with the
  -- corresponding inclusion leg of the explicit cocone on `T`.
  simpa [power_torsion_stage_colimit_iso, power_torsion_stage_module_cocone] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (P := colimit.isColimit (powerTorsionStageDiagram (R := R) I (M := T)))
      (Q := power_torsion_stage_module_isColimit (R := R) (I := I) (T := T) htop)
      n)

end PowerTorsionStageColimit

/-- Helper for Lemma 15.89.9: tensoring the subtype inclusion of a finite power-torsion stage
acts on a pure tensor by applying the subtype inclusion to the second factor. -/
theorem tensorProduct_map_subtype_apply_tmul
    (n : ℕ+)
    (r : R')
    (x : Ideal.powerTorsion I M (n : ℕ)) :
    TensorProduct.map (LinearMap.id) (Submodule.subtype (Ideal.powerTorsion I M (n : ℕ)))
        (r ⊗ₜ[R] x) =
      r ⊗ₜ[R] (x : M) :=
  rfl

/-- Helper for Lemma 15.89.9: the finite-stage tensor base-change maps commute with the transition
morphisms in the positive power-torsion filtration. -/
theorem power_torsion_stage_tensorLeft_naturality
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    ∀ {n m : ℕ+} (f : n ⟶ m),
      (powerTorsionStageDiagram (R := R) I (M := M)).map f ≫
          (tensor_base_change_stage_linearEquiv_of_quotient
            (I := I)
            (R' := R')
            (T := Ideal.powerTorsion I M (m : ℕ))
            m
            (powerTorsion_le_annihilator (I := I) (N := M) (n := (m : ℕ)))
            (hquot m)).toModuleIso.hom =
        (tensor_base_change_stage_linearEquiv_of_quotient
          (I := I)
          (R' := R')
          (T := Ideal.powerTorsion I M (n : ℕ))
          n
          (powerTorsion_le_annihilator (I := I) (N := M) (n := (n : ℕ)))
          (hquot n)).toModuleIso.hom ≫
        (powerTorsionStageDiagram (R := R) I (M := M) ⋙
          tensorLeft (ModuleCat.of R R')).map f := by
  intro n m f
  -- Naturality reduces both routes to the same pure tensor `1 ⊗ inclusion x`.
  ext x
  change
    (tensor_base_change_stage_linearEquiv_of_quotient
        (I := I)
        (R' := R')
        (T := Ideal.powerTorsion I M (m : ℕ))
        m
        (powerTorsion_le_annihilator (I := I) (N := M) (n := (m : ℕ)))
        (hquot m))
      (((powerTorsionStageDiagram (R := R) I (M := M)).map f).hom x) =
      ((powerTorsionStageDiagram (R := R) I (M := M) ⋙
          tensorLeft (ModuleCat.of R R')).map f).hom
        ((tensor_base_change_stage_linearEquiv_of_quotient
          (I := I)
          (R' := R')
          (T := Ideal.powerTorsion I M (n : ℕ))
          n
          (powerTorsion_le_annihilator (I := I) (N := M) (n := (n : ℕ)))
          (hquot n))
          x)
  rw [tensor_base_change_stage_linearEquiv_of_quotient_apply
    (I := I)
    (R' := R')
    (T := Ideal.powerTorsion I M (m : ℕ))
    m
    (powerTorsion_le_annihilator (I := I) (N := M) (n := (m : ℕ)))
    (hquot m)
    (((powerTorsionStageDiagram (R := R) I (M := M)).map f).hom x)]
  rw [tensor_base_change_stage_linearEquiv_of_quotient_apply
    (I := I)
    (R' := R')
    (T := Ideal.powerTorsion I M (n : ℕ))
    n
    (powerTorsion_le_annihilator (I := I) (N := M) (n := (n : ℕ)))
    (hquot n)
    x]
  rfl

/-- Helper for Lemma 15.89.9: the finite-stage base-change equivalences assemble into a natural
isomorphism from the positive power-torsion diagram to its left tensor by `R'`. -/
noncomputable def power_torsion_stage_tensorLeft_natIso
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    powerTorsionStageDiagram (R := R) I (M := M) ≅
      powerTorsionStageDiagram (R := R) I (M := M) ⋙ tensorLeft (ModuleCat.of R R') :=
  NatIso.ofComponents
    (fun n ↦
      (tensor_base_change_stage_linearEquiv_of_quotient
        (I := I)
        (R' := R')
        (T := Ideal.powerTorsion I M (n : ℕ))
        n
        (powerTorsion_le_annihilator (I := I) (N := M) (n := (n : ℕ)))
        (hquot n)).toModuleIso)
    (fun {_ _} f ↦
      power_torsion_stage_tensorLeft_naturality
        (I := I) (R' := R') (M := M) hquot f)

/-- Helper for Lemma 15.89.9: on each finite torsion stage, the natural isomorphism just sends
`x` to the pure tensor `1 ⊗ x`. -/
@[simp] theorem power_torsion_stage_tensorLeft_natIso_hom_app_apply
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map))
    (n : ℕ+)
    (x : Ideal.powerTorsion I M (n : ℕ)) :
    ((power_torsion_stage_tensorLeft_natIso (I := I) (R' := R') (M := M) hquot).hom.app n) x =
      1 ⊗ₜ[R] x := by
  -- Unfold the chosen finite-stage component and apply the already-proved stage formula.
  simpa [power_torsion_stage_tensorLeft_natIso] using
    (tensor_base_change_stage_linearEquiv_of_quotient_apply
      (I := I)
      (R' := R')
      (T := Ideal.powerTorsion I M (n : ℕ))
      n
      (powerTorsion_le_annihilator (I := I) (N := M) (n := (n : ℕ)))
      (hquot n)
      x)

section PowerTorsionTensorColimit

variable {T : Type u} [AddCommGroup T] [Module R T]

/-- Helper for Lemma 15.89.9: after assembling the stagewise tensor isomorphisms and passing to
the colimit, one gets the canonical comparison morphism from the stage colimit to `R' ⊗ T`. -/
noncomputable abbrev power_torsion_stage_tensor_colimit_hom
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map))
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤) :
    colimit (powerTorsionStageDiagram (R := R) I (M := T)) ⟶
      ModuleCat.of R (R' ⊗[R] T) :=
  (HasColimit.isoOfNatIso
      (power_torsion_stage_tensorLeft_natIso (I := I) (R' := R') (M := T) hquot)).hom ≫
    (CategoryTheory.preservesColimitIso
      (tensorLeft (ModuleCat.of R R'))
      (powerTorsionStageDiagram (R := R) I (M := T))).inv ≫
    (Functor.mapIso
      (tensorLeft (ModuleCat.of R R'))
      (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop)).hom

/-- Helper for Lemma 15.89.9: the induced colimit isomorphism identifies `T` with `R' ⊗ T`. -/
noncomputable abbrev tensor_base_change_colimit_iso
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map))
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤) :
    ModuleCat.of R T ≅ ModuleCat.of R (R' ⊗[R] T) :=
  (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop).symm ≪≫
    HasColimit.isoOfNatIso
      (power_torsion_stage_tensorLeft_natIso (I := I) (R' := R') (M := T) hquot) ≪≫
    (CategoryTheory.preservesColimitIso
      (tensorLeft (ModuleCat.of R R'))
      (powerTorsionStageDiagram (R := R) I (M := T))).symm ≪≫
    Functor.mapIso
      (tensorLeft (ModuleCat.of R R'))
      (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop)

/-- Helper for Lemma 15.89.9: on each stage leg, the colimit comparison agrees with tensoring the
literal stage inclusion by `R'`. -/
theorem power_torsion_stage_tensor_colimit_hom_ι_rewrite
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map))
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤)
    (n : ℕ+) :
    colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
        power_torsion_stage_tensor_colimit_hom (I := I) (R' := R') (T := T) hquot htop =
      ((power_torsion_stage_tensorLeft_natIso
          (I := I) (R' := R') (M := T) hquot).hom.app n) ≫
        (tensorLeft (ModuleCat.of R R')).map
          (ModuleCat.ofHom (Submodule.subtype (Ideal.powerTorsion I T (n : ℕ)))) := by
  -- Normalize the stage leg through the two canonical colimit comparison isomorphisms.
  have hpres :
      colimit.ι
          (powerTorsionStageDiagram (R := R) I (M := T) ⋙
            tensorLeft (ModuleCat.of R R')) n ≫
        (CategoryTheory.preservesColimitIso
          (tensorLeft (ModuleCat.of R R'))
          (powerTorsionStageDiagram (R := R) I (M := T))).inv ≫
        (Functor.mapIso
          (tensorLeft (ModuleCat.of R R'))
          (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop)).hom =
      (tensorLeft (ModuleCat.of R R')).map
        (ModuleCat.ofHom (Submodule.subtype (Ideal.powerTorsion I T (n : ℕ)))) := by
    have hpres₁ :
        colimit.ι
            (powerTorsionStageDiagram (R := R) I (M := T) ⋙
              tensorLeft (ModuleCat.of R R')) n ≫
            (CategoryTheory.preservesColimitIso
              (tensorLeft (ModuleCat.of R R'))
              (powerTorsionStageDiagram (R := R) I (M := T))).inv ≫
            (Functor.mapIso
              (tensorLeft (ModuleCat.of R R'))
              (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop)).hom =
          (tensorLeft (ModuleCat.of R R')).map
            (colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
              (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop).hom) := by
      simpa using
        (ι_preservesColimitIso_inv_assoc
          (F := powerTorsionStageDiagram (R := R) I (M := T))
          (G := tensorLeft (ModuleCat.of R R'))
          (j := n)
          (h := (Functor.mapIso
            (tensorLeft (ModuleCat.of R R'))
            (power_torsion_stage_colimit_iso
              (R := R) (I := I) (T := T) htop)).hom))
    have hpres₂ :
        (tensorLeft (ModuleCat.of R R')).map
            (colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
              (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop).hom) =
          (tensorLeft (ModuleCat.of R R')).map
            (ModuleCat.ofHom (Submodule.subtype (Ideal.powerTorsion I T (n : ℕ)))) := by
      simpa using
        congrArg
          ((tensorLeft (ModuleCat.of R R')).map)
          (power_torsion_stage_colimit_iso_hom_ι (I := I) (T := T) htop n)
    exact hpres₁.trans hpres₂
  rw [power_torsion_stage_tensor_colimit_hom]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        ((power_torsion_stage_tensorLeft_natIso
          (I := I) (R' := R') (M := T) hquot).hom.app n) ≫ k)
      hpres

/-- Helper for Lemma 15.89.9: precomposing the colimit base-change comparison with a stage
inclusion recovers the stagewise tensor comparison morphism. -/
theorem tensor_base_change_colimit_iso_hom_comp_stage
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map))
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤)
    (n : ℕ+) :
    ModuleCat.ofHom (Submodule.subtype (Ideal.powerTorsion I T (n : ℕ))) ≫
        (tensor_base_change_colimit_iso (I := I) (R' := R') (T := T) hquot htop).hom =
      colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
        power_torsion_stage_tensor_colimit_hom (I := I) (R' := R') (T := T) hquot htop := by
  -- Expand the left-hand side only far enough to cancel the first colimit comparison isomorphism.
  rw [tensor_base_change_colimit_iso]
  simp only [Iso.trans_hom]
  rw [← power_torsion_stage_colimit_iso_hom_ι (I := I) (T := T) htop n]
  have hcancel :
      (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop).hom ≫
          (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop).symm.hom ≫
          (HasColimit.isoOfNatIso
            (power_torsion_stage_tensorLeft_natIso
              (I := I) (R' := R') (M := T) hquot)).hom ≫
            (CategoryTheory.preservesColimitIso
              (tensorLeft (ModuleCat.of R R'))
              (powerTorsionStageDiagram (R := R) I (M := T))).symm.hom ≫
              (Functor.mapIso
                (tensorLeft (ModuleCat.of R R'))
                (power_torsion_stage_colimit_iso
                  (R := R) (I := I) (T := T) htop)).hom =
        (HasColimit.isoOfNatIso
          (power_torsion_stage_tensorLeft_natIso
            (I := I) (R' := R') (M := T) hquot)).hom ≫
          (CategoryTheory.preservesColimitIso
            (tensorLeft (ModuleCat.of R R'))
            (powerTorsionStageDiagram (R := R) I (M := T))).symm.hom ≫
            (Functor.mapIso
              (tensorLeft (ModuleCat.of R R'))
              (power_torsion_stage_colimit_iso
                (R := R) (I := I) (T := T) htop)).hom := by
    simp
  calc
    (colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
          (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop).hom) ≫
        (power_torsion_stage_colimit_iso (R := R) (I := I) (T := T) htop).symm.hom ≫
          (HasColimit.isoOfNatIso
            (power_torsion_stage_tensorLeft_natIso
              (I := I) (R' := R') (M := T) hquot)).hom ≫
            (CategoryTheory.preservesColimitIso
              (tensorLeft (ModuleCat.of R R'))
              (powerTorsionStageDiagram (R := R) I (M := T))).symm.hom ≫
              (Functor.mapIso
                (tensorLeft (ModuleCat.of R R'))
                (power_torsion_stage_colimit_iso
                  (R := R) (I := I) (T := T) htop)).hom =
      colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
        (HasColimit.isoOfNatIso
          (power_torsion_stage_tensorLeft_natIso
            (I := I) (R' := R') (M := T) hquot)).hom ≫
          (CategoryTheory.preservesColimitIso
            (tensorLeft (ModuleCat.of R R'))
            (powerTorsionStageDiagram (R := R) I (M := T))).symm.hom ≫
            (Functor.mapIso
              (tensorLeft (ModuleCat.of R R'))
              (power_torsion_stage_colimit_iso
                (R := R) (I := I) (T := T) htop)).hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫ k)
              hcancel
    _ = (power_torsion_stage_tensorLeft_natIso
          (I := I) (R' := R') (M := T) hquot).hom.app n ≫
        colimit.ι
            (powerTorsionStageDiagram (R := R) I (M := T) ⋙
              tensorLeft (ModuleCat.of R R')) n ≫
          (CategoryTheory.preservesColimitIso
            (tensorLeft (ModuleCat.of R R'))
            (powerTorsionStageDiagram (R := R) I (M := T))).symm.hom ≫
            (Functor.mapIso
              (tensorLeft (ModuleCat.of R R'))
              (power_torsion_stage_colimit_iso
                (R := R) (I := I) (T := T) htop)).hom := by
          rw [HasColimit.isoOfNatIso_ι_hom_assoc]
    _ = colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
        power_torsion_stage_tensor_colimit_hom (I := I) (R' := R') (T := T) hquot htop := by
          rw [power_torsion_stage_tensor_colimit_hom]
          rw [HasColimit.isoOfNatIso_ι_hom_assoc]
          rfl

/-- Helper for Lemma 15.89.9: on each stage leg, the colimit comparison agrees with tensoring the
literal stage inclusion by `R'`. -/
theorem power_torsion_stage_colimit_tensor_hom_ι
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map))
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤)
    (n : ℕ+) :
    colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
        power_torsion_stage_tensor_colimit_hom (I := I) (R' := R') (T := T) hquot htop =
      ModuleCat.ofHom ((TensorProduct.mk R R' T 1).comp
        (Submodule.subtype (Ideal.powerTorsion I T (n : ℕ)))) := by
  -- Route correction: isolate the transport through the colimit isomorphisms first, then compare
  -- the resulting module maps on a stage element.
  rw [power_torsion_stage_tensor_colimit_hom_ι_rewrite
    (I := I) (R' := R') (T := T) hquot htop n]
  ext x
  -- Both sides evaluate to the same pure tensor `1 ⊗ (x : T)`.
  change
    (Hom.hom
        ((tensorLeft (ModuleCat.of R R')).map
          (ModuleCat.ofHom (Submodule.subtype (Ideal.powerTorsion I T (n : ℕ))))))
        (((power_torsion_stage_tensorLeft_natIso
          (I := I) (R' := R') (M := T) hquot).hom.app n) x) =
      ((TensorProduct.mk R R' T 1).comp
        (Submodule.subtype (Ideal.powerTorsion I T (n : ℕ)))) x
  rw [power_torsion_stage_tensorLeft_natIso_hom_app_apply
    (I := I) (R' := R') (M := T) hquot n x]
  rfl

/-- Helper for Lemma 15.89.9: the hom of the colimit isomorphism is exactly the canonical tensor
base-change unit `T → R' ⊗ T`. -/
theorem tensor_base_change_iso_hom_eq_canonical
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map))
    (htop : (⨆ n : ℕ+, Ideal.powerTorsion I T (n : ℕ)) = ⊤) :
    (tensor_base_change_colimit_iso (I := I) (R' := R') (T := T) hquot htop).hom =
      ModuleCat.ofHom (TensorProduct.mk R R' T 1) := by
  -- Compare the two maps out of the colimit by checking them on every stage inclusion.
  apply (power_torsion_stage_module_isColimit (R := R) (I := I) (T := T) htop).hom_ext
  intro n
  calc
    (power_torsion_stage_module_cocone (R := R) (I := I) (T := T)).ι.app n ≫
        (tensor_base_change_colimit_iso (I := I) (R' := R') (T := T) hquot htop).hom =
      colimit.ι (powerTorsionStageDiagram (R := R) I (M := T)) n ≫
        power_torsion_stage_tensor_colimit_hom (I := I) (R' := R') (T := T) hquot htop := by
          simpa [power_torsion_stage_module_cocone] using
            tensor_base_change_colimit_iso_hom_comp_stage
              (I := I) (R' := R') (T := T) hquot htop n
    _ =
      (power_torsion_stage_module_cocone (R := R) (I := I) (T := T)).ι.app n ≫
        ModuleCat.ofHom (TensorProduct.mk R R' T 1) := by
          simpa [power_torsion_stage_module_cocone] using
            power_torsion_stage_colimit_tensor_hom_ι
              (I := I) (R' := R') (T := T) hquot htop n

end PowerTorsionTensorColimit

-- Proof sketch: if `I ^ n` annihilates `M`, then `M` is naturally an `R ⧸ I ^ n`-module, so
-- base change along `R → R'` factors through `R ⧸ I ^ n → R' ⧸ I ^ n R'`, which is bijective by
-- hypothesis. For a general `I`-power torsion module, write `M` as the directed union of its
-- `I ^ n`-annihilated submodules and use that tensor products commute with direct limits.
/-- Lemma 15.89.9: if the canonical maps `R ⧸ I^n → R' ⧸ I^n R'` are isomorphisms for all positive
`n`, then for every `I`-power torsion `R`-module `M` the canonical base-change unit
`M → R' ⊗[R] M` is bijective. -/
theorem tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
    (hM : Module.IsIdealPowerTorsion I M)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    Function.Bijective (TensorProduct.mk R R' M 1) := by
  -- Route correction: the finite-stage quotient/tensor comparison is now isolated in the helper
  -- theorem above, so only the filtered-colimit assembly from the finite stages to `M` remains.
  have htop :
      (⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) = ⊤ :=
    idealPowerTorsion_iSup_powerTorsion_eq_top (I := I) hM
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let e :=
    tensor_base_change_colimit_iso (I := I) (R' := R') (T := M) hquot htop
  have he :
      e.hom = ModuleCat.ofHom (TensorProduct.mk R R' M 1) :=
    tensor_base_change_iso_hom_eq_canonical (I := I) (R' := R') (T := M) hquot htop
  constructor
  · -- The canonical map is the hom of an isomorphism, hence injective.
    intro x y hxy
    have hxy' : e.hom.hom x = e.hom.hom y := by
      simpa [he] using hxy
    have hback := congrArg e.inv.hom hxy'
    simpa using hback
  · -- The inverse isomorphism provides a preimage for every tensor.
    intro z
    refine ⟨e.inv.hom z, ?_⟩
    have hz : e.hom.hom (e.inv.hom z) = z := by
      exact congrArg (fun f => f.hom z) e.inv_hom_id
    simpa [he] using hz

end

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type u} [AddCommMonoid M] [Module R M]

/- Domain-style sampling for the adic-completion quotient statement:
- primary domain: `I`-adic completion and quotient comparison for commutative rings;
- sampled owners: `Ideal.quotientMap`, `AdicCompletion.evalₐ`,
  `completionIdeal_pow_eq_ker_evalₐ`;
- best owner abstraction: the canonical completion-side map is
  `AdicCompletion.evalₐ I n : AdicCompletion I R →ₐ[R] R ⧸ I ^ n`; the quotient comparison below is
  its source-facing `Ideal.quotientMap` presentation, with the Chapter 10 bridge
  `completionIdeal_pow_eq_ker_evalₐ` identifying the kernel with the extended ideal
  `((I ^ n).map (algebraMap R (AdicCompletion I R)))`;
- primitive data: the ideal `I`, the ring `R`, the finite-generation hypothesis on `I`, and the
  exponent `n`, together with an `I`-power torsion `R`-module when specializing the tensor
  base-change theorem to completion;
- derived API: bijectivity of the induced quotient map to the completion quotient, and the
  completion-specialized tensor base-change statement for `I`-power torsion modules.

Layer triage:
- `source-facing`: the completion-specialized tensor base-change statement below;
- `core/canonical`: `AdicCompletion.evalₐ` and `completionIdeal_pow_eq_ker_evalₐ`;
- `bridge/view`: the quotient-comparison statement below, and its principal-ideal specialization
  `principalAdicCompletion_quotientMap_bijective` in Lemma `15.91.1`.
-/

-- Proof sketch: `AdicCompletion.evalₐ I n` is surjective, and
-- `completionIdeal_pow_eq_ker_evalₐ` identifies its kernel with the extended ideal
-- `(I^n) (AdicCompletion I R)`. The displayed `Ideal.quotientMap` is therefore the quotient-side
-- presentation of `evalₐ`.
/-- If `I` is finitely generated, then for every `n : ℕ` the canonical quotient map
`R ⧸ I^n → AdicCompletion I R ⧸ I^n AdicCompletion I R` is bijective. -/
theorem adicCompletion_quotientMap_bijective
    (hI : I.FG) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        ((I ^ n).map (algebraMap R (AdicCompletion I R)))
        (algebraMap R (AdicCompletion I R))
        Ideal.le_comap_map) := by
  let σ : R →+* AdicCompletion I R := algebraMap R (AdicCompletion I R)
  let e :
      (AdicCompletion I R ⧸ Ideal.map σ (I ^ n)) ≃ₐ[R] (R ⧸ I ^ n) :=
    (Ideal.quotientEquivAlgOfEq R (completionIdeal_pow_eq_ker_evalₐ I hI n)).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := AdicCompletion.evalₐ I n)
        (AdicCompletion.surjective_evalₐ I n))
  have hq :
      Ideal.quotientMap
        (Ideal.map σ (I ^ n))
        σ
        Ideal.le_comap_map =
        e.symm.toRingHom := by
    -- Identify the quotient map on generators with the inverse quotient equivalence.
    apply Ideal.Quotient.ringHom_ext
    ext r
    dsimp [e, σ]
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n))
          ((algebraMap R (AdicCompletion I R)) r) =
        (Ideal.quotientEquivAlgOfEq R (completionIdeal_pow_eq_ker_evalₐ I hI n).symm)
          ((Ideal.quotientKerAlgEquivOfSurjective
              (f := AdicCompletion.evalₐ I n)
              (AdicCompletion.surjective_evalₐ I n)).symm
            ((Ideal.Quotient.mk (I ^ n)) r))
    rw [← AdicCompletion.evalₐ_of (I := I) n r]
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply
      (hf := AdicCompletion.surjective_evalₐ I n)
      (a := AdicCompletion.of I R r)]
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n))
          (AdicCompletion.of I R r) =
        Ideal.Quotient.mk (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n))
          (AdicCompletion.of I R r)
    rfl
  rw [hq]
  exact e.symm.bijective

-- Proof sketch: specialize the general tensor base-change bijectivity theorem to the algebra
-- map `R → AdicCompletion I R`, and supply its quotient-map hypothesis via
-- `adicCompletion_quotientMap_bijective`.
/-- Lemma 15.89.9: if `I` is finitely generated, then for every `I`-power torsion `R`-module `M`
the canonical base-change unit `M → AdicCompletion I R ⊗[R] M` is bijective. This is the direct
completion specialization of the main base-change statement. -/
theorem tensorAdicCompletion_bijective_of_isIdealPowerTorsion
    (hI : I.FG) (hM : Module.IsIdealPowerTorsion I M) :
    Function.Bijective (TensorProduct.mk R (AdicCompletion I R) M 1) := by
  -- Specialize the general base-change theorem to the completion algebra and discharge the
  -- quotient-map hypothesis by the completion comparison proved just above.
  simpa using
    (tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
      (I := I)
      (R' := AdicCompletion I R)
      hM
      (fun n ↦ adicCompletion_quotientMap_bijective I hI n))

end
