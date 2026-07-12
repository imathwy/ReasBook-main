import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_10
import StacksProject_2024.Chap10.Lemma_10_39_18
import StacksProject_2024.Chap10.Lemma_10_99_9.NilpotentCriterion
import StacksProject_2024.Chap10.Remark_10_75_9

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open CategoryTheory CategoryTheory.Limits
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {I : Ideal R}
variable {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

local notation "IS" => Ideal.map (algebraMap R S) I

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the mapped ideal
`IS` is nilpotent whenever `I` is nilpotent. -/
lemma extended_ideal_isNilpotent (hI : IsNilpotent I) :
    IsNilpotent IS := by
  rcases hI with ⟨n, hn⟩
  -- Mapping powers of `I` along `R → S` preserves the vanishing stage.
  refine ⟨n, ?_⟩
  simpa [Ideal.map_pow] using congrArg (Ideal.map (algebraMap R S)) hn

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): flatness of the
quotient by the zero ideal transports back to flatness of the original module. -/
lemma flat_of_flat_quotient_bot
    (hflat :
      Module.Flat (S ⧸ (⊥ : Ideal S))
        (M ⧸ (((⊥ : Ideal S)) • (⊤ : Submodule S M)))) :
    Module.Flat S M := by
  have hflat_ring_quot : Module.Flat S (S ⧸ (⊥ : Ideal S)) := by
    -- The quotient ring by `0` is canonically the original ring.
    exact Module.Flat.of_linearEquiv (AlgEquiv.quotientBot S S).toLinearEquiv
  have hflat_quot_as_S :
      Module.Flat S (M ⧸ (((⊥ : Ideal S)) • (⊤ : Submodule S M))) := by
    -- Compose flatness along `S → S / 0`.
    letI : Module.Flat S (S ⧸ (⊥ : Ideal S)) := hflat_ring_quot
    letI :
        Module.Flat (S ⧸ (⊥ : Ideal S))
          (M ⧸ (((⊥ : Ideal S)) • (⊤ : Submodule S M))) := hflat
    exact Module.Flat.trans S (S ⧸ (⊥ : Ideal S))
      (M ⧸ (((⊥ : Ideal S)) • (⊤ : Submodule S M)))
  have hsmul_bot : ((⊥ : Ideal S) • (⊤ : Submodule S M)) = ⊥ := by
    -- The zero ideal acts trivially on every module.
    simp
  -- Identify the quotient by `0` with the original module.
  letI : Module.Flat S (M ⧸ (((⊥ : Ideal S)) • (⊤ : Submodule S M))) := hflat_quot_as_S
  exact Module.Flat.of_linearEquiv
    ((((⊥ : Ideal S) • (⊤ : Submodule S M)).quotEquivOfEqBot hsmul_bot).symm)

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): over a local
ring, tensoring with the residue field is equivalent to quotienting by the maximal ideal. -/
theorem nontrivial_tensor_local_residueField_iff_nontrivial_quotSMul
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N : Type*} [AddCommGroup N] [Module A N] :
    Nontrivial (N ⊗[A] IsLocalRing.ResidueField A) ↔
      Nontrivial (N ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))) := by
  have hker :
      RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) =
        IsLocalRing.maximalIdeal A := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq A] using
      (IsLocalRing.ker_residue (R := A))
  let eQuotKer :
      (A ⧸ RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) ≃ₐ[A]
        IsLocalRing.ResidueField A :=
    Ideal.quotientKerAlgEquivOfSurjective
      (R₁ := A) (f := Algebra.ofId A (IsLocalRing.ResidueField A))
      IsLocalRing.residue_surjective
  let eQuot :
      (A ⧸ IsLocalRing.maximalIdeal A) ≃ₗ[A] IsLocalRing.ResidueField A :=
    ((Ideal.quotientEquivAlgOfEq A hker.symm).trans eQuotKer).toLinearEquiv
  let e :
      N ⊗[A] IsLocalRing.ResidueField A ≃ₗ[A]
        N ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)) :=
    (TensorProduct.comm A N (IsLocalRing.ResidueField A)) ≪≫ₗ
      (TensorProduct.congr
        eQuot.symm
        (LinearEquiv.refl A N)) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul N (IsLocalRing.maximalIdeal A)
  -- Transport nontriviality across the canonical quotient/tensor comparison.
  exact e.nontrivial_congr

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the localized
fiber `M_q ⊗[S_q] κ(q)` is canonically nontrivial as soon as the original fiber
`M ⊗[S] κ(q)` is nontrivial. -/
theorem localizedModule_atPrime_tensor_residueField_nontrivial
    (q : PrimeSpectrum S)
    (hq : Nontrivial (M ⊗[S] q.asIdeal.ResidueField)) :
    Nontrivial
      (LocalizedModule.AtPrime q.asIdeal M ⊗[Localization.AtPrime q.asIdeal]
        q.asIdeal.ResidueField) := by
  let Sq := Localization.AtPrime q.asIdeal
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  let K := q.asIdeal.ResidueField
  have hleft : Nontrivial (K ⊗[S] M) := by
    -- Commute the original fiber to the tensor order used by base-change cancellation.
    exact (TensorProduct.comm S K M).nontrivial_congr.mpr hq
  have hcancel : Nontrivial (K ⊗[Sq] (Sq ⊗[S] M)) := by
    -- Cancel the intermediate base change `S → S_q`.
    exact (cancelBaseChange S Sq K K M).nontrivial_congr.mpr hleft
  have hcomm : Nontrivial ((Sq ⊗[S] M) ⊗[Sq] K) := by
    -- Rewrite the localized tensor product back to the standard order.
    exact (TensorProduct.comm Sq (Sq ⊗[S] M) K).nontrivial_congr.mpr hcancel
  let eTensor :
      Mq ⊗[Sq] K ≃ₗ[Sq] (Sq ⊗[S] M) ⊗[Sq] K :=
    TensorProduct.congr
      (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M)
      (LinearEquiv.refl Sq K)
  -- Finally replace `M_q` by its canonical tensor-product model.
  exact eTensor.nontrivial_congr.mpr hcomm

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): if the fiber over
`q` is nontrivial and `M` is flat over `S`, then the localized module `M_q` is faithfully flat
over `S_q`. -/
theorem faithfullyFlat_localizedModule_atPrime_of_nontrivial_fiber
    (q : PrimeSpectrum S) (hflat_S : Module.Flat S M)
    (hq : Nontrivial (M ⊗[S] q.asIdeal.ResidueField)) :
    Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal M) := by
  let Sq := Localization.AtPrime q.asIdeal
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  have hflatSq : Module.Flat Sq Mq := by
    let _ : Module.Flat S M := hflat_S
    -- Flatness localizes along `S → S_q`.
    simpa [Sq, Mq, LocalizedModule.AtPrime] using
      (Module.Flat.localizedModule (M := M) q.asIdeal.primeCompl)
  have htensor :
      Nontrivial (Mq ⊗[Sq] q.asIdeal.ResidueField) :=
    localizedModule_atPrime_tensor_residueField_nontrivial (M := M) q hq
  have hquot :
      Nontrivial (Mq ⧸ (IsLocalRing.maximalIdeal Sq • (⊤ : Submodule Sq Mq))) := by
    -- Over the local ring `S_q`, the residue-field tensor is the quotient by the maximal ideal.
    exact
      (nontrivial_tensor_local_residueField_iff_nontrivial_quotSMul
        (A := Sq) (N := Mq)).mp htensor
  have hmax_ne :
      IsLocalRing.maximalIdeal Sq • (⊤ : Submodule Sq Mq) ≠ ⊤ := by
    exact Submodule.Quotient.nontrivial_iff.mp hquot
  -- Use the proper-ideal criterion for faithful flatness over the local ring `S_q`.
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal Sq Mq).2 ⟨hflatSq, ?_⟩
  intro J hJ hJtop
  have hJmax : J ≤ IsLocalRing.maximalIdeal Sq := IsLocalRing.le_maximalIdeal hJ
  apply hmax_ne
  exact eq_top_iff.2 <| by
    calc
      ⊤ = J • (⊤ : Submodule Sq Mq) := hJtop.symm
      _ ≤ IsLocalRing.maximalIdeal Sq • (⊤ : Submodule Sq Mq) :=
        Submodule.smul_mono hJmax le_rfl

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): once the
localized module `M_q` is faithfully flat over `S_q`, flatness of `M` over `R` descends to
flatness of the local ring map `R_(q ∩ R) → S_q`, and then composes with localization flatness to
give flatness of `R → S_q`. -/
theorem algebraMap_atPrime_flat_of_faithfullyFlat_localizedModule
    (q : PrimeSpectrum S) (hflat_R : Module.Flat R M)
    (hff :
      Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := by
  let Rq := Localization.AtPrime (q.asIdeal.under R)
  let Sq := Localization.AtPrime q.asIdeal
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  let f : Rq →+* Sq :=
    Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl
  let _ : Algebra Rq Sq := f.toAlgebra
  have hflatRq : Module.Flat Rq Mq := by
    -- Flatness over `R` localizes to flatness over `R_(q ∩ R)`.
    simpa [Rq, Mq] using
      flat_localizedModule_atPrime_over_under_of_flat
        (R := R) (A := S) (M := M) hflat_R q
  let _ : Module.Flat Rq Mq := hflatRq
  have hflatRqRestrict : Module.Flat Rq (RestrictScalars Rq Sq Mq) := by
    change Module.Flat Rq Mq
    exact hflatRq
  let _ : Module.Flat Rq (RestrictScalars Rq Sq Mq) := hflatRqRestrict
  let _ :
      Module.FaithfullyFlat Sq Mq := hff
  have hlocal : f.Flat := by
    -- Apply the faithfully-flat descent criterion to the local map `R_(q ∩ R) → S_q`.
    simpa [f, Rq, Sq] using
      (algebraMap_flat_of_flat_of_faithfullyFlat
        (R := Rq) (S := Sq) (M := Mq))
  have hbase : (algebraMap R Rq).Flat := by
    -- Localization of the base ring is flat.
    rw [RingHom.flat_algebraMap_iff]
    simpa [Rq] using
      (IsLocalization.flat (S := Rq) (p := (q.asIdeal.under R).primeCompl))
  have hcomp : (f.comp (algebraMap R Rq)).Flat :=
    RingHom.Flat.comp hbase hlocal
  have hfg : f.comp (algebraMap R Rq) = algebraMap R Sq := by
    ext r
    exact Localization.localRingHom_to_map
      (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl r
  -- The composed map is the canonical algebra map `R → S_q`.
  rw [hfg] at hcomp
  simpa [Sq] using hcomp

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the canonical
`R`-balanced map from `I ⊗[R] M` to `IS ⊗[S] M` sends `a ⊗ m` to the pure tensor of the extended
ideal element with `m`. -/
lemma ideal_to_extended_ideal_map_add (a b : I) :
    (⟨algebraMap R S (a + b), Ideal.mem_map_of_mem (algebraMap R S) (a + b).2⟩ : IS) =
      ⟨algebraMap R S a, Ideal.mem_map_of_mem (algebraMap R S) a.2⟩ +
        ⟨algebraMap R S b, Ideal.mem_map_of_mem (algebraMap R S) b.2⟩ := by
  -- Proof comment: equality in the mapped ideal is checked on the ambient ring element.
  ext
  simp

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the canonical
map `I → IS` is compatible with the `R`-module structure. -/
lemma ideal_to_extended_ideal_map_smul (r : R) (a : I) :
    (⟨algebraMap R S (r • a), Ideal.mem_map_of_mem (algebraMap R S) (r • a).2⟩ : IS) =
      r • ⟨algebraMap R S a, Ideal.mem_map_of_mem (algebraMap R S) a.2⟩ := by
  -- Proof comment: the restricted `R`-action on `IS` is transported through `algebraMap`.
  ext
  simp [Algebra.smul_def]

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the base ideal
maps canonically into the extended ideal. -/
noncomputable def ideal_to_extended_ideal :
    I →ₗ[R] IS :=
  { toFun := fun a ↦
      ⟨algebraMap R S a, Ideal.mem_map_of_mem (algebraMap R S) a.2⟩
    map_add' := ideal_to_extended_ideal_map_add (R := R) (S := S) (I := I)
    map_smul' := ideal_to_extended_ideal_map_smul (R := R) (S := S) (I := I) }

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the tensor map
is additive in the left ideal factor before passing to the tensor-product lift. -/
lemma extended_ideal_tensor_left_map_add (a b : I) :
    (TensorProduct.mk S IS M (ideal_to_extended_ideal (R := R) (S := S) (I := I) (a + b))).restrictScalars R =
      (TensorProduct.mk S IS M (ideal_to_extended_ideal (R := R) (S := S) (I := I) a)).restrictScalars R +
        (TensorProduct.mk S IS M (ideal_to_extended_ideal (R := R) (S := S) (I := I) b)).restrictScalars R := by
  -- Proof comment: after identifying the left factor in `IS`, `TensorProduct.mk` turns sums into
  -- sums of pure tensors.
  ext m
  simpa [ideal_to_extended_ideal] using
    (TensorProduct.add_tmul
      (ideal_to_extended_ideal (R := R) (S := S) (I := I) a)
      (ideal_to_extended_ideal (R := R) (S := S) (I := I) b) m)

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the tensor map
is `R`-linear in the left ideal factor before passing to the tensor-product lift. -/
lemma extended_ideal_tensor_left_map_smul (r : R) (a : I) :
    (TensorProduct.mk S IS M (ideal_to_extended_ideal (R := R) (S := S) (I := I) (r • a))).restrictScalars R =
      r • (TensorProduct.mk S IS M (ideal_to_extended_ideal (R := R) (S := S) (I := I) a)).restrictScalars R := by
  -- Proof comment: move the base scalar across the mapped ideal element and then across the pure
  -- tensor in the codomain.
  ext m
  simpa [ideal_to_extended_ideal] using
    (TensorProduct.smul_tmul'
      (R := S) (r := r)
      (m := ideal_to_extended_ideal (R := R) (S := S) (I := I) a) (n := m)).symm

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the canonical
`R`-balanced map from `I ⊗[R] M` to `IS ⊗[S] M` sends `a ⊗ m` to the pure tensor of the extended
ideal element with `m`. -/
noncomputable def extended_ideal_tensor_map :
    I ⊗[R] M →ₗ[R] IS ⊗[S] M :=
  TensorProduct.lift
    { toFun := fun a ↦
        (TensorProduct.mk S IS M (ideal_to_extended_ideal (R := R) (S := S) (I := I) a)).restrictScalars R
      map_add' := extended_ideal_tensor_left_map_add (R := R) (S := S) (I := I) (M := M)
      map_smul' := extended_ideal_tensor_left_map_smul (R := R) (S := S) (I := I) (M := M) }

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the canonical
tensor bridge has the expected value on pure tensors. -/
@[simp] lemma extended_ideal_tensor_map_tmul (a : I) (m : M) :
    extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M) (a ⊗ₜ[R] m) =
      (ideal_to_extended_ideal (R := R) (S := S) (I := I) a) ⊗ₜ[S] m := by
  -- Proof comment: this is the defining computation rule of `TensorProduct.lift`.
  rfl

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): every pure tensor
in `IS ⊗[S] M` comes from the canonical map `I ⊗[R] M → IS ⊗[S] M`. -/
lemma extended_ideal_tensor_map_surjective :
    Function.Surjective (extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M)) := by
  have hIS_span :
      IS = Ideal.span (Set.range fun a : I ↦ algebraMap R S (a : R)) := by
    -- Proof comment: normalize the extended ideal as the span of the image of the original ideal.
    calc
      IS = Ideal.map (algebraMap R S) (Ideal.span (I : Set R)) := by
        rw [Ideal.span_eq]
      _ = Ideal.span ((algebraMap R S) '' (I : Set R)) := by
        rw [Ideal.map_span]
      _ = Ideal.span (Set.range fun a : I ↦ algebraMap R S (a : R)) := by
        congr 1
        ext x
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨a, rfl⟩
          exact ⟨a, a.2, rfl⟩
  intro z
  -- Proof comment: tensor induction reduces surjectivity to pure tensors `y ⊗ m`.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro y m
    have hy_span :
        (y : S) ∈ Ideal.span (Set.range fun a : I ↦ algebraMap R S (a : R)) := by
      simpa [hIS_span] using y.2
    rcases Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hy_span with ⟨c, hc⟩
    let xPre :=
      Finset.sum c.support fun a ↦ (a ⊗ₜ[R] ((c a) • m) : I ⊗[R] M)
    let yTerms : I → IS := fun a ↦
      ⟨c a * algebraMap R S (a : R),
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R S) a.2)⟩
    refine ⟨xPre, ?_⟩
    -- Proof comment: expand the chosen preimage and collapse the resulting finite sum back to
    -- the target tensor using the coefficient presentation of `y`.
    calc
      extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M)
          xPre =
          Finset.sum c.support fun a ↦
            extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M)
              (a ⊗ₜ[R] ((c a) • m)) := by
            simp [xPre]
      _ = Finset.sum c.support fun a ↦ yTerms a ⊗ₜ[S] m := by
            refine Finset.sum_congr rfl fun a ha ↦ ?_
            change
              (ideal_to_extended_ideal (R := R) (S := S) (I := I) a) ⊗ₜ[S] ((c a) • m) =
                yTerms a ⊗ₜ[S] m
            calc
              (ideal_to_extended_ideal (R := R) (S := S) (I := I) a) ⊗ₜ[S] ((c a) • m) =
                  (c a • ideal_to_extended_ideal (R := R) (S := S) (I := I) a) ⊗ₜ[S] m := by
                    simpa using
                      (TensorProduct.smul_tmul'
                        (R := S) (r := c a)
                        (m := ideal_to_extended_ideal (R := R) (S := S) (I := I) a)
                        (n := m)).symm
              _ = yTerms a ⊗ₜ[S] m := by
                    apply congrArg (fun t : IS ↦ t ⊗ₜ[S] m)
                    ext
                    simp [yTerms, ideal_to_extended_ideal, mul_comm]
      _ = (Finset.sum c.support yTerms) ⊗ₜ[S] m := by
            simpa using (TensorProduct.sum_tmul (R := S) c.support yTerms m).symm
      _ = y ⊗ₜ[S] m := by
            apply congrArg (fun t : IS ↦ t ⊗ₜ[S] m)
            ext
            simpa [yTerms, Finsupp.sum] using hc
  · intro x y hx hy
    rcases hx with ⟨x', rfl⟩
    rcases hy with ⟨y', rfl⟩
    refine ⟨x' + y', ?_⟩
    simp

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): flatness over
`R` makes the multiplication map `IS ⊗[S] M → M` injective. -/
lemma extended_ideal_tensor_to_module_injective_of_flat_over_base
    (hflat_R : Module.Flat R M) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul S M).comp (Ideal.map (algebraMap R S) I).subtype)) := by
  let μR : I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let μS : IS ⊗[S] M →ₗ[S] M :=
    TensorProduct.lift
      ((LinearMap.lsmul S M).comp (Ideal.map (algebraMap R S) I).subtype)
  have hμR_inj : Function.Injective μR := by
    have hrt_inj : Function.Injective (I.subtype.rTensor M) :=
      (Module.Flat.iff_rTensor_injective'.mp hflat_R) I
    -- Proof comment: flatness over `R` makes the basic multiplication map `I ⊗[R] M → M`
    -- injective by comparing it with `I.subtype.rTensor M`.
    have hμR :
        μR = (TensorProduct.lid R M).toLinearMap.comp (I.subtype.rTensor M) := by
      ext a m
      rfl
    rw [hμR]
    exact (TensorProduct.lid R M).injective.comp hrt_inj
  have hcompare :
      (μS.restrictScalars R).comp
          (extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M)) =
        μR := by
    -- Proof comment: both tensor-to-module maps agree on pure tensors from `I`.
    ext a m
    simp [μR, μS, ideal_to_extended_ideal]
  -- Proof comment: descend injectivity from `μR` through the surjective bridge
  -- `I ⊗[R] M → IS ⊗[S] M`.
  intro x y hxy
  rcases extended_ideal_tensor_map_surjective (R := R) (S := S) (I := I) (M := M) x with
    ⟨x', rfl⟩
  rcases extended_ideal_tensor_map_surjective (R := R) (S := S) (I := I) (M := M) y with
    ⟨y', rfl⟩
  have hxyR : μR x' = μR y' := by
    calc
      μR x' =
          (μS.restrictScalars R)
            (extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M) x') := by
              simpa [LinearMap.comp_apply] using
                (congrArg (fun f ↦ f x') hcompare).symm
      _ =
          (μS.restrictScalars R)
            (extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M) y') := by
              simpa [μS] using hxy
      _ = μR y' := by
            simpa [LinearMap.comp_apply] using congrArg (fun f ↦ f y') hcompare
  exact congrArg
    (extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M))
    (hμR_inj hxyR)

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): Remark `10.75.9`
turns vanishing of the kernel of `J ⊗[A] N → N` into vanishing of the module-first public
`Tor₁` owner. -/
lemma module_first_tor_quotient_vanishes_of_ker_eq_bot
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type u} [AddCommGroup N] [Module A N]
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype)) = ⊥) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
      (ModuleCat.of A (A ⧸ J)))) := by
  let μ : J ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype)
  have hker_subsingleton : Subsingleton (LinearMap.ker μ) := by
    -- Proof comment: the assumed kernel equality identifies the kernel module with the zero
    -- submodule.
    exact (Submodule.subsingleton_iff_eq_bot).2 (by simpa [μ] using hker)
  let e :
      (((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj (ModuleCat.of A (A ⧸ J))) ≃ₗ[A]
        LinearMap.ker μ :=
    tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := A) (M := N) J
  have hsub :
      Subsingleton ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ J)))) := by
    refine ⟨fun x y ↦ ?_⟩
    apply e.injective
    exact Subsingleton.elim _ _
  -- Proof comment: Remark `10.75.9` identifies the owner with the zero kernel, so the owner
  -- itself is zero.
  exact (ModuleCat.isZero_iff_subsingleton).2 hsub

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): mapping an ideal
into a `ULift` copy of the ring preserves the nilpotence stage. -/
lemma ulift_mapped_ideal_isNilpotent
    {A : Type u} [CommRing A] {J : Ideal A} {N : Type w} [AddCommGroup N] [Module A N]
    (hJ : IsNilpotent J) :
    IsNilpotent (J.map (algebraMap A (ULift.{w} A))) := by
  rcases hJ with ⟨n, hn⟩
  -- Proof comment: apply `Ideal.map` to the vanishing power identity.
  refine ⟨n, ?_⟩
  simpa [Ideal.map_pow] using congrArg (Ideal.map (algebraMap A (ULift.{w} A))) hn

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): quotienting by
the image ideal in a `ULift` ring recovers the original quotient ring. -/
lemma ulift_quotient_ring_equiv_aux
    {A : Type u} [CommRing A] (J : Ideal A) {N : Type w} [AddCommGroup N] [Module A N] :
    J =
      (J.map (algebraMap A (ULift.{w} A))).map
        ((ULift.algEquiv (R := A) (A := A) : ULift.{w} A ≃ₐ[A] A) : ULift.{w} A →+* A) := by
  let eu : ULift.{w} A ≃ₐ[A] A := ULift.algEquiv (R := A) (A := A)
  -- Proof comment: `ULift.algEquiv` is inverse to the canonical lift `A → ULift A`.
  calc
    J = J.map (RingHom.id A) := by simp
    _ = J.map ((eu : ULift.{w} A →+* A).comp (algebraMap A (ULift.{w} A))) := by
          ext a
          rfl
    _ = (J.map (algebraMap A (ULift.{w} A))).map (eu : ULift.{w} A →+* A) := by
          rw [Ideal.map_map]

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): quotienting by
the image of `J` in the lifted ring is canonically the same as quotienting by `J` downstairs. -/
noncomputable def ulift_quotient_ring_equiv
    {A : Type u} [CommRing A] (J : Ideal A) {N : Type w} [AddCommGroup N] [Module A N] :
    ((ULift.{w} A) ⧸ J.map (algebraMap A (ULift.{w} A))) ≃+* (A ⧸ J) :=
  (Ideal.quotientEquivAlg _ _ (ULift.algEquiv (R := A) (A := A))
    (ulift_quotient_ring_equiv_aux (J := J) (N := N))).toRingEquiv

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): quotienting the
module by `J • ⊤` commutes with lifting only the module universe. -/
lemma ulift_module_quotient_equiv_exists
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type w} [AddCommGroup N] [Module A N] :
    Nonempty ((((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))))) := by
  let eA :
      ((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A]
        (N ⧸ (J • (⊤ : Submodule A N))) :=
    Submodule.Quotient.equiv
      (J • (⊤ : Submodule A (ULift.{u} N)))
      (J • (⊤ : Submodule A N))
      (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N)
      (by
        -- Proof comment: `ULift.moduleEquiv` preserves the denominator `J • ⊤`.
        simpa [Submodule.map_smul''])
  -- Proof comment: both quotients carry their canonical `A ⧸ J`-actions.
  exact ⟨eA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): choose the
quotient-module equivalence induced by `ULift.moduleEquiv`. -/
noncomputable def ulift_module_quotient_equiv
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type w} [AddCommGroup N] [Module A N] :
    ((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))) :=
  Classical.choice ulift_module_quotient_equiv_exists

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): a commuting
square with linear equivalences transports injectivity across the horizontal maps. -/
lemma injective_of_ladder_linearEquiv
    {A : Type u} [CommRing A]
    {P : Type v} [AddCommGroup P] [Module A P]
    {Q : Type w} [AddCommGroup Q] [Module A Q]
    {P' : Type v} [AddCommGroup P'] [Module A P']
    {Q' : Type w} [AddCommGroup Q'] [Module A Q']
    {f : P →ₗ[A] Q} {g : P' →ₗ[A] Q'}
    {eP : P ≃ₗ[A] P'} {eQ : Q ≃ₗ[A] Q'}
    (h : g ∘ₗ eP = eQ ∘ₗ f)
    (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply eP.symm.injective
  apply hf
  apply eQ.injective
  calc
    eQ (f (eP.symm x)) = g x := by
      simpa using (LinearMap.congr_fun h (eP.symm x)).symm
    _ = g y := hxy
    _ = eQ (f (eP.symm y)) := by
      simpa using LinearMap.congr_fun h (eP.symm y)

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): injectivity of
`J ⊗[A] N → N` persists after lifting only the module universe to `ULift N`. -/
lemma ulift_injective_tensor_transport
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type w} [AddCommGroup N] [Module A N]
    (hinj : Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype))) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul A (ULift.{u} N)).comp J.subtype)) := by
  let μ : J ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype)
  let μu : J ⊗[A] ULift.{u} N →ₗ[A] ULift.{u} N :=
    TensorProduct.lift ((LinearMap.lsmul A (ULift.{u} N)).comp J.subtype)
  let eTensor :
      J ⊗[A] ULift.{u} N ≃ₗ[A] J ⊗[A] N :=
    TensorProduct.congr (LinearEquiv.refl A J) (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N)
  have hSquare :
      μ.comp eTensor.toLinearMap =
        (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N).toLinearMap.comp μu := by
    -- Proof comment: after identifying `ULift N` with `N`, both multiplication maps act by the
    -- same scalar multiplication formula on pure tensors.
    ext j n
    rfl
  intro x y hxy
  apply eTensor.injective
  apply hinj
  calc
    μ (eTensor x) =
        (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N) (μu x) := by
          simpa [LinearMap.comp_apply] using congrArg (fun f ↦ f x) hSquare
    _ =
        (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N) (μu y) := by
          simpa using congrArg (fun z ↦ (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N) z) hxy
    _ = μ (eTensor y) := by
          simpa [LinearMap.comp_apply] using (congrArg (fun f ↦ f y) hSquare).symm

/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): injectivity of
the source multiplication map `I ⊗[R] M → M` descends through the canonical surjection
`I ⊗[R] M → IS ⊗[S] M`. -/
lemma extended_ideal_tensor_to_module_injective_of_source_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {I : Ideal R}
    {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (hinj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype))) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul S M).comp (Ideal.map (algebraMap R S) I).subtype)) := by
  let μR : I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let μS : Ideal.map (algebraMap R S) I ⊗[S] M →ₗ[S] M :=
    TensorProduct.lift
      ((LinearMap.lsmul S M).comp (Ideal.map (algebraMap R S) I).subtype)
  have hcompare :
      (μS.restrictScalars R).comp
          (extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M)) =
        μR := by
    -- Proof comment: both tensor-to-module maps agree on pure tensors from `I`.
    ext a m
    simp [μR, μS, ideal_to_extended_ideal]
  -- Proof comment: the source map is surjective, so injectivity on `I ⊗[R] M` descends to the
  -- mapped-ideal tensor source over `S`.
  intro x y hxy
  rcases extended_ideal_tensor_map_surjective (R := R) (S := S) (I := I) (M := M) x with
    ⟨x', rfl⟩
  rcases extended_ideal_tensor_map_surjective (R := R) (S := S) (I := I) (M := M) y with
    ⟨y', rfl⟩
  have hxyR : μR x' = μR y' := by
    calc
      μR x' =
          (μS.restrictScalars R)
            (extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M) x') := by
              simpa [LinearMap.comp_apply] using
                (congrArg (fun f ↦ f x') hcompare).symm
      _ =
          (μS.restrictScalars R)
            (extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M) y') := by
              simpa [μS] using hxy
      _ = μR y' := by
            simpa [LinearMap.comp_apply] using congrArg (fun f ↦ f y') hcompare
  exact congrArg
    (extended_ideal_tensor_map (R := R) (S := S) (I := I) (M := M))
    (hinj hxyR)

-- Proof sketch: lift the ring/module data to a common universe, transport the closed-fiber
-- flatness and injective tensor map there, apply the nilpotent-thickening criterion once
-- upstairs, and finally descend flatness back along the `ULift` equivalences.
/-- Helper for Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): the theorem-local
nilpotent-thickening criterion reducing the target flatness claim to the lifted same-universe
criterion. -/
theorem flat_of_nilpotent_ideal_of_flat_mod_ideal_and_injective_tensor
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type w} [AddCommGroup N] [Module A N]
    (hJ : IsNilpotent J)
    (hflat : Module.Flat (A ⧸ J) (N ⧸ (J • (⊤ : Submodule A N))))
    (hinj : Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype))) :
    Module.Flat A N := by
  let Su : Type max u w := ULift.{w} A
  let Nu : Type max u w := ULift.{u} N
  let Ju : Ideal Su := J.map (algebraMap A Su)
  let T : Type max u w := Su ⧸ Ju
  let B : Type u := A ⧸ J
  let eRing : T ≃+* B := ulift_quotient_ring_equiv (A := A) (J := J) (N := N)
  letI : Algebra T B := eRing.toRingHom.toAlgebra
  letI : Module T (N ⧸ (J • (⊤ : Submodule A N))) :=
    Module.compHom (N ⧸ (J • (⊤ : Submodule A N))) (algebraMap T B)
  letI : IsScalarTower A T (N ⧸ (J • (⊤ : Submodule A N))) :=
    IsScalarTower.of_compHom A T (N ⧸ (J • (⊤ : Submodule A N)))
  letI : IsScalarTower T B (N ⧸ (J • (⊤ : Submodule A N))) :=
    IsScalarTower.of_compHom T B (N ⧸ (J • (⊤ : Submodule A N)))
  have hJu : IsNilpotent Ju := by
    -- Proof comment: the nilpotence stage survives the `ULift` ring presentation unchanged.
    simpa [Ju] using ulift_mapped_ideal_isNilpotent (A := A) (J := J) (N := N) hJ
  have hinj_u :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul A Nu).comp J.subtype)) := by
    -- Proof comment: first lift only the module universe on the source injective tensor map.
    simpa [Nu] using ulift_injective_tensor_transport (A := A) (J := J) (N := N) hinj
  have hflatTB : Module.Flat T B := by
    -- Proof comment: `T` is ring-equivalent to the original closed-fiber owner `A ⧸ J`.
    let eAlg : B ≃ₐ[T] T :=
      AlgEquiv.ofRingEquiv (R := T) (f := eRing.symm) (by
        intro x
        change eRing.symm (eRing x) = x
        simp)
    exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv
  have hflatTarget : Module.Flat T (N ⧸ (J • (⊤ : Submodule A N))) := by
    -- Proof comment: transport the given closed-fiber flatness across the quotient-ring
    -- equivalence `T ≃ A ⧸ J`.
    letI : Module.Flat T B := hflatTB
    letI : Module.Flat B (N ⧸ (J • (⊤ : Submodule A N))) := hflat
    exact Module.Flat.trans T B (N ⧸ (J • (⊤ : Submodule A N)))
  have hJu_restrict :
      ((Ju • (⊤ : Submodule Su Nu)).restrictScalars A) =
        (J • (⊤ : Submodule A Nu)) := by
    -- Proof comment: restricting the lifted denominator from `Su` to `A` recovers the original
    -- denominator `J • ⊤`.
    simpa [Ju] using
      (Ideal.smul_restrictScalars
        (R := A) (S := Su) (M := Nu) (I := J) (N := (⊤ : Submodule Su Nu)))
  have hsurjAT : Function.Surjective (algebraMap A T) := by
    -- Proof comment: every class in the iterated quotient `T` has a representative from `A`
    -- because `ULift A` is itself represented by elements of `A`.
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rcases x with ⟨a⟩
    exact ⟨a, rfl⟩
  have eOwnerA :
      (Nu ⧸ (Ju • (⊤ : Submodule Su Nu))) ≃ₗ[A]
        N ⧸ (J • (⊤ : Submodule A N)) := by
    let eRestrict :
        (Nu ⧸ ((Ju • (⊤ : Submodule Su Nu)).restrictScalars A)) ≃ₗ[A]
          Nu ⧸ (Ju • (⊤ : Submodule Su Nu)) :=
      Submodule.Quotient.restrictScalarsEquiv A (Ju • (⊤ : Submodule Su Nu))
    let eDenom :
        (Nu ⧸ ((Ju • (⊤ : Submodule Su Nu)).restrictScalars A)) ≃ₗ[A]
          Nu ⧸ (J • (⊤ : Submodule A Nu)) :=
      Submodule.quotEquivOfEq
        ((Ju • (⊤ : Submodule Su Nu)).restrictScalars A)
        (J • (⊤ : Submodule A Nu))
        hJu_restrict
    let eULift :
        (Nu ⧸ (J • (⊤ : Submodule A Nu))) ≃ₗ[A]
          N ⧸ (J • (⊤ : Submodule A N)) :=
      (ulift_module_quotient_equiv (A := A) (J := J) (N := N)).restrictScalars A
    -- Proof comment: compare the lifted closed fiber to the original one by first restricting
    -- scalars on the quotient, then normalizing the denominator, and finally removing the module
    -- universe lift.
    exact eRestrict.symm.trans (eDenom.trans eULift)
  have eOwner :
      (Nu ⧸ (Ju • (⊤ : Submodule Su Nu))) ≃ₗ[T]
        N ⧸ (J • (⊤ : Submodule A N)) :=
    -- Proof comment: the previous `A`-linear comparison upgrades to the true owner ring `T`
    -- because `A → T` is surjective.
    eOwnerA.extendScalarsOfSurjective hsurjAT
  have hflatClosed :
      Module.Flat T (Nu ⧸ (Ju • (⊤ : Submodule Su Nu))) := by
    -- Proof comment: the lifted closed fiber is flat because it is linearly equivalent to the
    -- already transported flat target module.
    letI : Module.Flat T (N ⧸ (J • (⊤ : Submodule A N))) := hflatTarget
    exact Module.Flat.of_linearEquiv eOwner
  have hmul_inj :
      Function.Injective
        (TensorProduct.lift
          ((LinearMap.lsmul Su Nu).comp (Ideal.map (algebraMap A Su) J).subtype)) := by
    -- Route correction: reuse the canonical mapped-ideal tensor bridge already proved in this
    -- file instead of introducing a second bespoke tensor-source equivalence.
    simpa [Ju] using
      extended_ideal_tensor_to_module_injective_of_source_injective
        (R := A) (S := Su) (I := J) (M := Nu) hinj_u
  have hflatSuNu : Module.Flat Su Nu := by
    -- Proof comment: all lifted hypotheses now match the exact owner expected by the imported
    -- nilpotent-thickening criterion.
    simpa [T] using
      flat_of_nilpotent_ideal_from_flat_closed_fiber_and_injective_tensor
        (S := Su) (J := Ju) (N := Nu) hJu hflatClosed hmul_inj
  have hflatANu : Module.Flat A Nu := by
    have hflatASu : Module.Flat A Su := by
      -- Proof comment: `ULift A` is flat over `A` because it is linearly equivalent to `A`.
      exact Module.Flat.of_linearEquiv
        (ULift.algEquiv (R := A) (A := A)).toLinearEquiv
    -- Proof comment: flatness over `Su` descends to flatness over `A` by transitivity.
    letI : Module.Flat A Su := hflatASu
    letI : Module.Flat Su Nu := hflatSuNu
    exact Module.Flat.trans A Su Nu
  letI : Module.Flat A (ULift.{u} N) := by
    simpa [Nu] using hflatANu
  -- Proof comment: after descending the scalar ring, remove the remaining module universe lift.
  exact Module.Flat.of_linearEquiv
    (ULift.moduleEquiv (R := A) (M := N)).symm

-- Proof sketch: the imported nilpotent-thickening criterion from Lemma `10.99.8` already
-- packages the source-facing flatness conclusion over the target ring `S`.
/-- Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): if `I` is nilpotent,
`M / ISM` is flat over `S / IS`, and `M` is flat over `R`, then `M` is flat over `S`. -/
@[stacks 06A5]
theorem flat_over_target_of_nilpotent_of_flat_over_base_and_flat_mod_extended_ideal
    (hI : IsNilpotent I)
    (hflat_mod : Module.Flat (S ⧸ IS) (M ⧸ (IS • ⊤ : Submodule S M)))
    (hflat_R : Module.Flat R M) :
    Module.Flat S M := by
  have hIS : IsNilpotent IS :=
    extended_ideal_isNilpotent (R := R) (S := S) (I := I) hI
  have hμIS_inj :
      Function.Injective
        (TensorProduct.lift
          ((LinearMap.lsmul S M).comp (Ideal.map (algebraMap R S) I).subtype)) :=
    extended_ideal_tensor_to_module_injective_of_flat_over_base
      (R := R) (S := S) (I := I) (M := M) hflat_R
  -- Route correction: the source-side injectivity bridge stays in this file, while the remaining
  -- common-universe nilpotent-closing step is delegated to the theorem-local helper owner.
  exact flat_of_nilpotent_ideal_of_flat_mod_ideal_and_injective_tensor
    (A := S) (J := IS) (N := M) hIS hflat_mod hμIS_inj

-- Proof sketch: localize at `q`, use the nontrivial fiber to show `M_q` is faithfully flat over
-- `S_q`, localize the `R`-flatness hypothesis, and then descend flatness of the local ring map.
/-- If `M` is flat over both `R` and `S`, then every prime `q` with nontrivial fiber
`M ⊗[S] κ(q)` has `S_q` flat over `R`. -/
theorem atPrime_flat_of_flat_module_and_nontrivial_fiber
    (q : PrimeSpectrum S) (hflat_R : Module.Flat R M) (hflat_S : Module.Flat S M)
    (hq : Nontrivial (M ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := by
  have hff :
      Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M) :=
    faithfullyFlat_localizedModule_atPrime_of_nontrivial_fiber
      (M := M) q hflat_S hq
  -- Combine localized flatness over `R_(q ∩ R)` with faithful flatness over `S_q`.
  exact algebraMap_atPrime_flat_of_faithfullyFlat_localizedModule
    (R := R) (S := S) (M := M) q hflat_R hff

end
