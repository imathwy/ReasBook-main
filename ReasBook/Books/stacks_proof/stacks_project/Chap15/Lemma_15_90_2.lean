import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap15.Lemma_15_89_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ModuleCat
open scoped TensorProduct

universe u w

section

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: change of rings on module categories, especially the base-change unit and
  quotient maps modulo ideals;
- inspected same-domain owners:
  `flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`,
  `idealPowerTorsionRestrictedBaseChange`,
  `Module.IsIdealPowerTorsion`,
  `TensorProduct.mk`,
  `Ideal.quotientMap`;
- best owner abstraction: this file should stay a source-facing bridge theorem, but its ambient
  owner is the chapter theorem
  `flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules` together with the
  module-level tensor base-change map `TensorProduct.mk R S M 1 : M →ₗ[R] S ⊗[R] M`; faithfulness
  on `I`-power torsion modules is carried by the chapter owner
  `idealPowerTorsionRestrictedBaseChange (algebraMap R S) I`, and the quotient comparison
  `R ⧸ I → S ⧸ IS` is identified by the canonical tensor/quotient owner
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`; the textbook map `M → M ⊗[R] S` is only
  the tensor-symmetry view.

Source/core/bridge triage:
- `source-facing`: the bijectivity criterion for the canonical map `M → M ⊗[R] S` on ordinary
  `I`-power torsion `R`-modules;
- `core/canonical`: extension of scalars along `algebraMap R S`;
- `bridge/view`: the induced quotient map `R ⧸ I → S ⧸ IS` and the restricted base-change functor
  `idealPowerTorsionRestrictedBaseChange (algebraMap R S) I`.
-/

/-- Helper for Lemma 15.90.2: extension of scalars sends `I`-power torsion `R`-modules to
`IS`-power torsion `S`-modules. -/
theorem Module.IsIdealPowerTorsion.extendScalars
    (φ : R →+* S) (I : Ideal R) (M : ModuleCat R)
    (hM : Module.IsIdealPowerTorsion I M) :
    Module.IsIdealPowerTorsion (Ideal.map φ I) ((extendScalars φ).obj M) := by
  let _ : Algebra R S := φ.toAlgebra
  -- Proof comment: work in the tensor-product model of extension of scalars and reduce the claim
  -- to pure tensors.
  change Module.IsIdealPowerTorsion (Ideal.map φ I) (S ⊗[R] M)
  rw [Module.isIdealPowerTorsion_iff] at hM ⊢
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · refine ⟨1, fun a ↦ ?_⟩
    simp
  · intro s m
    obtain ⟨n, hn⟩ := hM m
    refine ⟨n, fun b ↦ ?_⟩
    have hb : (b : S) ∈ Ideal.map φ (I ^ (n : ℕ)) := by
      simpa [Ideal.map_pow] using b.property
    have hb' : (b : S) ∈ Ideal.span (φ '' (↑(I ^ (n : ℕ)) : Set R)) := by
      simpa [Ideal.map_span] using hb
    -- Proof comment: every generator `φ a` with `a ∈ I^n` kills the pure tensor because `a`
    -- already kills `m`.
    refine Submodule.span_induction (p := fun z _ ↦ z • (s ⊗ₜ[R] m : S ⊗[R] M) = 0)
      ?_ ?_ ?_ ?_ hb'
    · intro y hy
      rcases hy with ⟨a, ha, rfl⟩
      calc
        (φ a : S) • (s ⊗ₜ[R] m : S ⊗[R] M) = ((a • s) ⊗ₜ[R] m : S ⊗[R] M) := by
          rfl
        _ = s ⊗ₜ[R] (a • m) := by
          rw [TensorProduct.smul_tmul]
        _ = 0 := by
          simp [hn ⟨a, ha⟩]
    · simp
    · intro y z hy hz hy' hz'
      rw [add_smul, hy', hz']
      simp
    · intro c y hy hy'
      simpa [smul_smul] using congrArg (fun t : S ⊗[R] M ↦ c • t) hy'
  · intro x y hx hy
    rcases hx with ⟨m, hm⟩
    rcases hy with ⟨n, hn⟩
    -- Proof comment: pass to a common larger power of `I` that kills both summands.
    refine ⟨⟨(m : ℕ) + n, lt_of_lt_of_le m.2 (Nat.le_add_right (m : ℕ) (n : ℕ))⟩,
      fun a ↦ ?_⟩
    have hmx : (a : S) • x = 0 := by
      exact hm ⟨a, Ideal.pow_le_pow_right (Nat.le_add_right (m : ℕ) (n : ℕ)) a.2⟩
    have hny : (a : S) • y = 0 := by
      exact hn ⟨a, Ideal.pow_le_pow_right (Nat.le_add_left (n : ℕ) (m : ℕ)) a.2⟩
    rw [smul_add, hmx, hny]
    simp

/-- Helper for Lemma 15.90.2: restricted base change on the full subcategories of `I`-power
torsion and `IS`-power torsion modules. -/
noncomputable abbrev idealPowerTorsionRestrictedBaseChange
    (φ : R →+* S) (I : Ideal R) :
    ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{u} R ↦ Module.IsIdealPowerTorsion I M) ⥤
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{u} S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M) :=
  ObjectProperty.lift
    (fun M : ModuleCat.{u} S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)
    (ObjectProperty.ι (fun M : ModuleCat.{u} R ↦ Module.IsIdealPowerTorsion I M) ⋙
      extendScalars φ)
    (fun M ↦ Module.IsIdealPowerTorsion.extendScalars φ I M.obj M.property)

/-- Helper for Lemma 15.90.2: on a quotient module `R ⧸ J`, the canonical tensor base-change unit
identifies with the induced quotient ring map `R ⧸ J → S ⧸ JS`. -/
theorem quotientMap_bijective_of_tensorBaseChange_bijective_on_quotient
    (J : Ideal R)
    (hbijJ : Function.Bijective (TensorProduct.mk R S (R ⧸ J) 1)) :
    Function.Bijective
      (Ideal.quotientMap
        (J.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  let e : S ⊗[R] (R ⧸ J) ≃+* S ⧸ J.map (algebraMap R S) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S J).symm.toRingEquiv
  have hAlg :
      Function.Bijective
        (Algebra.TensorProduct.includeRight : R ⧸ J →ₐ[R] S ⊗[R] (R ⧸ J)) := by
    -- Proof comment: `includeRight` is the ring-hom avatar of the tensor-unit map `x ↦ 1 ⊗ x`.
    simpa [Algebra.TensorProduct.includeRight_apply] using hbijJ
  have hEq :
      e.toRingHom.comp (Algebra.TensorProduct.includeRight : R ⧸ J →ₐ[R] S ⊗[R] (R ⧸ J)).toRingHom =
        Ideal.quotientMap
          (J.map (algebraMap R S))
          (algebraMap R S)
          Ideal.le_comap_map := by
    -- Proof comment: both quotient-side maps agree on classes `x mod J` by the standard
    -- tensor/quotient generator formula.
    apply Ideal.Quotient.ringHom_ext
    rw [Ideal.quotientMap_comp_mk]
    ext x
    change
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S J).symm
          ((1 : S) ⊗ₜ[R] (Ideal.Quotient.mk J x)) =
        (Ideal.Quotient.mk (J.map (algebraMap R S))) ((algebraMap R S) x)
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    have hs : x • (1 : S) = algebraMap R S x := by
      simpa [Algebra.smul_def]
    simpa [hs]
  rw [← hEq]
  exact e.bijective.comp hAlg

/-- Helper for Lemma 15.90.2: if the canonical tensor base-change unit is bijective on a
submodule and on the quotient by that submodule, then flatness makes it bijective on the ambient
module. -/
theorem tensorBaseChange_bijective_of_submodule_and_quotient
    (hflat : (algebraMap R S).Flat)
    {T : Type w} [AddCommGroup T] [Module R T]
    (K : Submodule R T)
    (hK : Function.Bijective (TensorProduct.mk R S K 1))
    (hQ : Function.Bijective (TensorProduct.mk R S (T ⧸ K) 1)) :
    Function.Bijective (TensorProduct.mk R S T 1) := by
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  have hSubtypeTensor_injective :
      Function.Injective (LinearMap.lTensor S K.subtype) := by
    -- Proof comment: flatness keeps the submodule inclusion injective after tensoring.
    simpa using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := S)
        K.subtype (Submodule.injective_subtype K))
  have hExactTensor :
      Function.Exact (LinearMap.lTensor S K.subtype) (LinearMap.lTensor S K.mkQ) := by
    -- Proof comment: tensor product is right exact on the canonical quotient row.
    exact lTensor_exact S (LinearMap.exact_subtype_mkQ K) K.mkQ_surjective
  constructor
  · intro x y hxy
    have hqxy :
        TensorProduct.mk R S (T ⧸ K) 1 (K.mkQ x) =
          TensorProduct.mk R S (T ⧸ K) 1 (K.mkQ y) := by
      -- Proof comment: apply the tensorized quotient map and use the naturality square.
      simpa [TensorProduct.mk] using congrArg (LinearMap.lTensor S K.mkQ) hxy
    have hqeq : K.mkQ x = K.mkQ y := hQ.1 hqxy
    have hsub : K.mkQ (x - y) = 0 := by
      -- Proof comment: equality of quotient classes means the difference comes from `K`.
      change K.mkQ x - K.mkQ y = 0
      exact sub_eq_zero.mpr hqeq
    obtain ⟨k, hk⟩ := (LinearMap.exact_subtype_mkQ K (x - y)).1 hsub
    have hkTensor :
        (LinearMap.lTensor S K.subtype) (TensorProduct.mk R S K 1 k) = 0 := by
      -- Proof comment: the chosen lift `k` maps to the tensor-kernel element `x - y`.
      calc
        (LinearMap.lTensor S K.subtype) (TensorProduct.mk R S K 1 k)
            = TensorProduct.mk R S T 1 (K.subtype k) := by
                simp [TensorProduct.mk]
        _ = TensorProduct.mk R S T 1 (x - y) := by
              simpa using congrArg (TensorProduct.mk R S T 1) hk
        _ = TensorProduct.mk R S T 1 x - TensorProduct.mk R S T 1 y := by
              simpa [TensorProduct.mk] using (TensorProduct.tmul_sub (1 : S) x y)
        _ = 0 := by
              simpa [hxy]
    have hkTensor_zero : TensorProduct.mk R S K 1 k = 0 :=
      hSubtypeTensor_injective hkTensor
    have hk_zero : k = 0 := hK.1 <| by simpa using hkTensor_zero
    have hxy_zero : x - y = 0 := by
      simpa [hk_zero] using hk.symm
    exact sub_eq_zero.mp hxy_zero
  · intro z
    obtain ⟨q, hq⟩ := hQ.2 ((LinearMap.lTensor S K.mkQ) z)
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective K q
    have hker :
        (LinearMap.lTensor S K.mkQ) (z - TensorProduct.mk R S T 1 x) = 0 := by
      -- Proof comment: choose a lift of the quotient tensor class so the remaining difference
      -- lands in the kernel of the tensorized quotient map.
      calc
        (LinearMap.lTensor S K.mkQ) (z - TensorProduct.mk R S T 1 x)
            = (LinearMap.lTensor S K.mkQ) z -
                (LinearMap.lTensor S K.mkQ) (TensorProduct.mk R S T 1 x) := by
                  simp
        _ = (LinearMap.lTensor S K.mkQ) z -
              TensorProduct.mk R S (T ⧸ K) 1 (K.mkQ x) := by
                simp [TensorProduct.mk]
        _ = 0 := by
              rw [hq]
              simp
    obtain ⟨w, hw⟩ :=
      (hExactTensor (z - TensorProduct.mk R S T 1 x)).mp hker
    obtain ⟨k, hk⟩ := hK.2 w
    refine ⟨x + (k : T), ?_⟩
    have hkImage :
        TensorProduct.mk R S T 1 (k : T) =
          z - TensorProduct.mk R S T 1 x := by
      -- Proof comment: rewrite the kernel witness through the bijection on `K`.
      calc
        TensorProduct.mk R S T 1 (k : T)
            = (LinearMap.lTensor S K.subtype) (TensorProduct.mk R S K 1 k) := by
                simp [TensorProduct.mk]
        _ = (LinearMap.lTensor S K.subtype) w := by
              simpa [hk]
        _ = z - TensorProduct.mk R S T 1 x := hw
    calc
      TensorProduct.mk R S T 1 (x + (k : T))
          = TensorProduct.mk R S T 1 x + TensorProduct.mk R S T 1 (k : T) := by
              simpa [TensorProduct.mk] using (TensorProduct.tmul_add (1 : S) x (k : T))
      _ = TensorProduct.mk R S T 1 x + (z - TensorProduct.mk R S T 1 x) := by
            rw [hkImage]
      _ = z := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 15.90.2: the quotient by `J • M` is annihilated by `J`. -/
theorem ideal_le_annihilator_quotient_by_smul_top
    (J : Ideal R)
    {T : Type w} [AddCommGroup T] [Module R T] :
    J ≤ Module.annihilator R (T ⧸ (J • (⊤ : Submodule R T))) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R T)) x
  -- Proof comment: every lift is killed modulo `J • T` because multiplication by an element of
  -- `J` lands back in the defining submodule.
  change (Submodule.Quotient.mk ((a : R) • y) :
      T ⧸ (J • (⊤ : Submodule R T))) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 <|
    Submodule.smul_mem_smul ha (by simp)

/-- Helper for Lemma 15.90.2: in the power-step quotient `R / I^(m+2)`, the submodule
`I^(m+1)` is annihilated by `I`, and the quotient by it is annihilated by `I^(m+1)`. -/
theorem quotient_pow_step_annihilator_bounds
    (I : Ideal R) (m : ℕ) :
    let T : Type u := R ⧸ I ^ (m + 2)
    let K : Submodule R T := I ^ (m + 1) • (⊤ : Submodule R T)
    I ≤ Module.annihilator R K ∧
      I ^ (m + 1) ≤ Module.annihilator R (T ⧸ K) := by
  let T : Type u := R ⧸ I ^ (m + 2)
  let K : Submodule R T := I ^ (m + 1) • (⊤ : Submodule R T)
  have hTann : I ^ (m + 2) ≤ Module.annihilator R T := by
    intro a ha
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    -- Proof comment: coefficients from `I^(m+2)` vanish in the quotient `R / I^(m+2)`.
    change (Ideal.Quotient.mk (I ^ (m + 2))) ((a : R) * y) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
      simpa [mul_comm] using Ideal.mul_mem_left (I ^ (m + 2)) y ha
  have hKann : I ≤ Module.annihilator R K := by
    intro a ha
    rw [Module.mem_annihilator]
    intro x
    ext
    change ((a : R) • (x : T)) = 0
    -- Proof comment: every element of `K = I^(m+1) • T` is a sum of generators `r • y`; after
    -- one more multiplication by `a ∈ I`, the coefficient lies in `I^(m+2)` and hence kills `T`.
    refine Submodule.smul_induction_on x.property ?_ ?_
    · intro r hr y hy
      have har : (a : R) * r ∈ I ^ (m + 2) := by
        simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using
          (Ideal.mul_mem_mul ha hr : (a : R) * r ∈ I * I ^ (m + 1))
      calc
        (a : R) • (r • y) = (((a : R) * r) : R) • y := by
          simp [smul_smul]
        _ = 0 := by
          exact Module.mem_annihilator.mp (hTann har) y
    · intro y z hy hz
      simpa [smul_add, hy, hz]
  have hQann :
      I ^ (m + 1) ≤ Module.annihilator R (T ⧸ K) := by
    -- Proof comment: this is the standard quotient-by-`J • T` annihilator calculation.
    simpa [K] using
      (ideal_le_annihilator_quotient_by_smul_top (R := R) (J := I ^ (m + 1))
        (T := T))
  exact ⟨hKann, hQann⟩

/-- Helper for Lemma 15.90.2: if `R ⧸ I → S ⧸ IS` is bijective, then the same holds for every
positive power quotient `R ⧸ I^n → S ⧸ I^nS`. -/
theorem quotientMap_pow_bijective_of_quotientMap_bijective
    (I : Ideal R)
    (hflat : (algebraMap R S).Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap
        (I.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map)) :
    ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        (((I ^ (n : ℕ)).map (algebraMap R S)))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  have hquot1 :
      Function.Bijective
        (Ideal.quotientMap
          (((I ^ (1 : ℕ)).map (algebraMap R S)))
          (algebraMap R S)
          Ideal.le_comap_map) := by
    have hmap1 :
        ((I ^ (1 : ℕ)).map (algebraMap R S)) = I.map (algebraMap R S) := by
      simp [Ideal.map_pow, pow_one]
    let eR : R ⧸ I ^ (1 : ℕ) ≃+* R ⧸ I :=
      Ideal.quotEquivOfEq (pow_one I)
    let eS : S ⧸ ((I ^ (1 : ℕ)).map (algebraMap R S)) ≃+* S ⧸ I.map (algebraMap R S) :=
      Ideal.quotEquivOfEq hmap1
    have hq1_eq :
        Ideal.quotientMap
            (((I ^ (1 : ℕ)).map (algebraMap R S)))
            (algebraMap R S)
            Ideal.le_comap_map =
          eS.symm.toRingHom.comp
            ((Ideal.quotientMap
                (I.map (algebraMap R S))
                (algebraMap R S)
                Ideal.le_comap_map).comp eR.toRingHom) := by
      apply Ideal.Quotient.ringHom_ext
      rw [Ideal.quotientMap_comp_mk]
      ext x
      change
        Ideal.Quotient.mk ((I ^ (1 : ℕ)).map (algebraMap R S)) ((algebraMap R S) x) =
          (Ideal.quotEquivOfEq hmap1.symm)
            (Ideal.Quotient.mk (I.map (algebraMap R S)) ((algebraMap R S) x))
      rw [Ideal.quotEquivOfEq_mk]
    rw [hq1_eq]
    exact eS.symm.bijective.comp (hquot.comp eR.bijective)
  let hpow :
      ∀ m : ℕ, Function.Bijective
        (Ideal.quotientMap
          (((I ^ (m + 1)).map (algebraMap R S)))
          (algebraMap R S)
          Ideal.le_comap_map) := by
    intro m
    induction m with
    | zero =>
        -- Proof comment: the induction starts from the given quotient map modulo `I`.
        simpa using hquot1
    | succ m hm =>
        let T : Type u := R ⧸ I ^ (m + 2)
        let K : Submodule R T := I ^ (m + 1) • (⊤ : Submodule R T)
        have hbounds :
            I ≤ Module.annihilator R K ∧
              I ^ (m + 1) ≤ Module.annihilator R (T ⧸ K) := by
          simpa [T, K] using quotient_pow_step_annihilator_bounds (R := R) (I := I) m
        have hbounds1 : I ^ (1 : ℕ) ≤ Module.annihilator R K := by
          simpa [pow_one] using hbounds.1
        have hKbij :
            Function.Bijective (TensorProduct.mk R S K 1) := by
          -- Proof comment: the left term is annihilated by `I`, so the base hypothesis already
          -- applies after the finite-stage tensor/quotient comparison from Lemma `15.89.9`.
          simpa using
            (tensorBaseChange_bijective_of_annihilator_pow_le_of_quotientMapBijective
              (I := I) (R' := S) (n := (1 : ℕ+)) hbounds1 hquot1)
        have hQbij :
            Function.Bijective (TensorProduct.mk R S (T ⧸ K) 1) := by
          -- Proof comment: the quotient term is annihilated by `I^(m+1)`, so the induction
          -- hypothesis provides its tensor-base-change bijectivity.
          simpa [T, K] using
            (tensorBaseChange_bijective_of_annihilator_pow_le_of_quotientMapBijective
              (I := I) (R' := S)
              (n := ⟨m + 1, Nat.succ_pos m⟩) hbounds.2 hm)
        have hTbij :
            Function.Bijective (TensorProduct.mk R S T 1) :=
          tensorBaseChange_bijective_of_submodule_and_quotient
            (R := R) (S := S) hflat K hKbij hQbij
        -- Proof comment: once the tensor unit is bijective on `R / I^(m+2)`, the quotient map
        -- modulo `I^(m+2)` is the corresponding quotient-ring avatar.
        simpa [T] using
          (quotientMap_bijective_of_tensorBaseChange_bijective_on_quotient
            (R := R) (S := S) (J := I ^ (m + 2)) hTbij)
  intro n
  rcases n with ⟨n, hn⟩
  cases n with
  | zero =>
      exact (False.elim (Nat.not_lt_zero 0 hn))
  | succ m =>
      -- Proof comment: rewrite every positive index as `m + 1` and invoke the internal
      -- induction on ordinary naturals.
      simpa using hpow m

/-- If the canonical tensor base-change unit is bijective on every `I`-power torsion `R`-module,
then the induced quotient map `R ⧸ I → S ⧸ IS` is bijective. This is the source-facing forward
bridge used in Lemma `15.90.2`. -/
@[stacks 05E9]
theorem quotientMap_bijective_of_tensorBaseChange_bijective_on_idealPowerTorsion
    (I : Ideal R)
    (hbij : ∀ M : ModuleCat.{u} R,
      Module.IsIdealPowerTorsion I M →
        Function.Bijective (TensorProduct.mk R S M 1)) :
    Function.Bijective
      (Ideal.quotientMap
        (I.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  -- Proof comment: specialize the global torsion hypothesis to the quotient module `R ⧸ I`,
  -- which is already `I`-power torsion, and then invoke the quotient/tensor adapter.
  have hq1 :
      Function.Bijective (TensorProduct.mk R S (R ⧸ I) 1) := by
    have htors : Module.IsIdealPowerTorsion I (R ⧸ I) := by
      rw [Module.isIdealPowerTorsion_iff]
      intro x
      refine ⟨1, fun a ↦ ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      have haI : (a : R) ∈ I := by
        simpa [pow_one] using a.2
      change (Ideal.Quotient.mk I) ((a : R) * y) = 0
      exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
        simpa [mul_comm] using I.mul_mem_right y haI
    exact hbij (ModuleCat.of R (R ⧸ I)) htors
  exact
    quotientMap_bijective_of_tensorBaseChange_bijective_on_quotient
      (R := R) (S := S) (J := I) hq1

/-- Lemma 15.90.2: under the flatness and faithful restricted base-change hypothesis supplied by
Lemma `15.90.1`, the following are equivalent: every `I`-power torsion `R`-module `M` is
unchanged by the canonical base-change unit `M → S ⊗[R] M`, and the induced map
`R ⧸ I → S ⧸ IS` is bijective. The forward implication is the atomic quotient-recovery theorem
`quotientMap_bijective_of_tensorBaseChange_bijective_on_idealPowerTorsion`, while the converse
uses the chapter owners `idealPowerTorsionRestrictedBaseChange` and
`tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`. -/
@[stacks 05E9]
theorem tensorBaseChange_bijective_iff_quotientMap_bijective_of_baseChangeFaithfulOnIdealPowerTorsion
    (I : Ideal R)
    (hflat : (algebraMap R S).Flat)
    (hfaithful : (idealPowerTorsionRestrictedBaseChange (algebraMap R S) I).Faithful) :
    (∀ M : ModuleCat.{u} R,
      Module.IsIdealPowerTorsion I M →
        Function.Bijective (TensorProduct.mk R S M 1)) ↔
    Function.Bijective
        (Ideal.quotientMap
        (I.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  constructor
  · exact quotientMap_bijective_of_tensorBaseChange_bijective_on_idealPowerTorsion I
  · intro hquot M hM
    -- Route correction: first upgrade the quotient bijection from `I` to all powers `I^n`, then
    -- invoke the colimit theorem from Lemma `15.89.9` on the given `I`-power torsion module.
    exact
      tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
        (I := I) (R' := S) hM <|
          quotientMap_pow_bijective_of_quotientMap_bijective
            (R := R) (S := S) I hflat hquot

end
