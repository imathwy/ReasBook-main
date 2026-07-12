import Mathlib
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Lemma_10_96_3
import StacksProject_2024.Chap10.Lemma_10_97_3
import StacksProject_2024.Chap10.Lemma_10_97_6
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap15.Definition_15_37_3
import StacksProject_2024.Chap15.Lemma_15_37_2
import StacksProject_2024.Chap15.Lemma_15_37_4
import StacksProject_2024.Chap15.Lemma_15_38_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped Topology

noncomputable section

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsRegularLocalRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

/-- Helper for Lemma 15.38.5: the maximal ideal of `A` stays maximal after passing to the
maximal-ideal-adic completion. -/
lemma completion_map_maximalIdeal_isMaximal :
    Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := by
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  letI : Field (A ⧸ (maximalIdeal A) ^ 1) := by
    let e : A ⧸ (maximalIdeal A) ^ 1 ≃+* A ⧸ maximalIdeal A :=
      Ideal.quotEquivOfEq (pow_one (maximalIdeal A))
    exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
  -- Compare the extended maximal ideal with the kernel of the first completion-evaluation map.
  have hker :
      Ideal.map (algebraMap A ACompletion) (maximalIdeal A) =
        RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1) := by
    simpa [pow_one] using
      completionIdeal_pow_eq_ker_evalₐ (maximalIdeal A)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) 1
  -- The target quotient is the residue field, so that kernel is maximal.
  simpa [hker] using
    (RingHom.ker_isMaximal_of_surjective
      (AdicCompletion.evalₐ (maximalIdeal A) 1)
      (AdicCompletion.surjective_evalₐ (maximalIdeal A) 1) :
        Ideal.IsMaximal (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1)))

/-- Helper for Lemma 15.38.5: the maximal-ideal completion of a regular local ring is again a
local ring. -/
lemma completion_isLocalRing :
    IsLocalRing ACompletion := by
  let hmax :
      Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
    completion_map_maximalIdeal_isMaximal (A := A)
  letI : Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := hmax
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  let hcomplete :
      IsAdicComplete (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion :=
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2
  letI : IsAdicComplete (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion :=
    hcomplete
  -- A complete ring for a maximal ideal of definition is local.
  exact @isLocalRing_of_isAdicComplete_maximal ACompletion _
    (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) hmax hcomplete

local instance : IsLocalRing ACompletion := completion_isLocalRing (A := A)

/-- Helper for Lemma 15.38.5: in the maximal-ideal completion, the extended maximal ideal agrees
with the actual maximal ideal. -/
lemma completion_map_maximalIdeal_eq_maximalIdeal :
    Ideal.map (algebraMap A ACompletion) (maximalIdeal A) = maximalIdeal ACompletion := by
  letI :
      Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
    completion_map_maximalIdeal_isMaximal (A := A)
  -- In a local ring, every maximal ideal is the distinguished maximal ideal.
  exact IsLocalRing.eq_maximalIdeal inferInstance

/-- Helper for Lemma 15.38.5: the completion map is a local homomorphism. -/
instance completion_isLocalHom :
    IsLocalHom (algebraMap A ACompletion) := by
  let φ : ACompletion →+* A ⧸ maximalIdeal A :=
    (AdicCompletion.evalOneₐ (maximalIdeal A)).toRingHom
  have hcomp : φ.comp (algebraMap A ACompletion) = Ideal.Quotient.mk (maximalIdeal A) := by
    ext x
    simp [φ]
  -- The quotient map to the residue field is local, so the completion map is local by
  -- cancellation through the surjective evaluation map.
  haveI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A)) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (φ.comp (algebraMap A ACompletion)) := by
    simpa [hcomp]
  exact isLocalHom_of_comp (algebraMap A ACompletion) φ

/-- Helper for Lemma 15.38.5: the maximal-ideal completion is complete for its own maximal-ideal
adic topology. -/
lemma completion_isAdicComplete_maximalIdeal :
    IsAdicComplete (maximalIdeal ACompletion) ACompletion := by
  -- Rewrite the defining ideal on the completion into its actual maximal ideal.
  simpa [completion_map_maximalIdeal_eq_maximalIdeal (A := A)] using
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2

/-- Helper for Lemma 15.38.5: the maximal-ideal completion is a complete local ring. -/
instance completion_isCompleteLocalRing :
    IsCompleteLocalRing ACompletion := by
  -- Bundle the local and adic-complete facts just established.
  exact
    { toIsLocalRing := completion_isLocalRing (A := A)
      toIsAdicComplete := completion_isAdicComplete_maximalIdeal (A := A) }

/-- Helper for Lemma 15.38.5: completion preserves regularity for a regular local ring. -/
lemma completion_isRegularLocalRing :
    IsRegularLocalRing ACompletion := by
  let _ : RingHom.FaithfullyFlat (algebraMap A ACompletion) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  have hquotient :
      IsRegularLocalRing
        (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := by
    letI : Field (ACompletion ⧸ maximalIdeal ACompletion) :=
      Ideal.Quotient.field (maximalIdeal ACompletion)
    -- The quotient by the maximal ideal is a field, hence regular local.
    let hmap := completion_map_maximalIdeal_eq_maximalIdeal (A := A)
    exact hmap ▸ (inferInstance : IsRegularLocalRing (ACompletion ⧸ maximalIdeal ACompletion))
  have hclosedFiber : IsRegularLocalRing ((maximalIdeal A).Fiber ACompletion) := by
    letI :
        IsRegularLocalRing
          (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
      hquotient
    -- The closed fiber is the quotient by the image of the maximal ideal.
    exact isRegularLocalRing_closedFiber_of_quotient
  -- Apply the flat local transfer criterion to the faithfully flat completion map.
  exact isRegularLocalRing_of_flat_localHom_of_regular_closedFiber hclosedFiber

/-- Helper for Lemma 15.38.5: the first evaluation map on the completion has kernel the maximal
ideal of the completion. -/
lemma completion_evalOne_ker_eq_maximalIdeal :
    RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1) = maximalIdeal ACompletion := by
  -- Compare the evaluation kernel with the extended maximal ideal and then identify that ideal
  -- with the maximal ideal of the local completion.
  calc
    RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1) =
        Ideal.map (algebraMap A ACompletion) (maximalIdeal A) := by
          symm
          simpa [pow_one] using
            completionIdeal_pow_eq_ker_evalₐ (maximalIdeal A)
              (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) 1
    _ = maximalIdeal ACompletion := completion_map_maximalIdeal_eq_maximalIdeal (A := A)

/-- Helper for Lemma 15.38.5: the residue field of the maximal-ideal completion is canonically
identified with the original residue field. -/
noncomputable abbrev completion_residueField_algEquiv :
    ResidueField ACompletion ≃ₐ[k] ResidueField A := by
  -- Quotient by that kernel and use surjectivity of `evalOneₐ`.
  exact
    (Ideal.quotientEquivAlgOfEq k (completion_evalOne_ker_eq_maximalIdeal (A := A)).symm).trans <|
      ((Ideal.quotientKerAlgEquivOfSurjective
        (f := AdicCompletion.evalₐ (maximalIdeal A) 1)
        (AdicCompletion.surjective_evalₐ (maximalIdeal A) 1)).restrictScalars k).trans <|
        Ideal.quotientEquivAlgOfEq k (pow_one (maximalIdeal A))

/-- Helper for Lemma 15.38.5: codomain ring equivalences preserving the defining ideal preserve
adic formal smoothness. -/
lemma formally_smooth_for_adic_of_codomain_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (e : S ≃+* T) {J : Ideal S} {K : Ideal T}
    (hK : Ideal.map e.toRingHom J = K)
    (hf : f.formally_smooth_for_adic J) :
    (e.toRingHom.comp f).formally_smooth_for_adic K := by
  rw [RingHom.formally_smooth_for_adic_iff] at hf ⊢
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : TopologicalSpace S := Ideal.adicTopology J
  letI : TopologicalSpace T := Ideal.adicTopology K
  -- Transport the adic topology across the codomain equivalence in both directions.
  have he_cont : Continuous e.toRingHom := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    simpa [pow_one] using hK.le
  have hsymm_map : Ideal.map e.symm.toRingHom K = J := by
    calc
      Ideal.map e.symm.toRingHom K =
          Ideal.map e.symm.toRingHom (Ideal.map e.toRingHom J) := by
            rw [hK]
      _ = Ideal.map (e.symm.toRingHom.comp e.toRingHom) J := by
            rw [Ideal.map_map]
      _ = J := by
            rw [show e.symm.toRingHom.comp e.toRingHom = RingHom.id S by
              ext x
              simpa using e.left_inv x]
            simp
  have he_symm_cont : Continuous e.symm.toRingHom := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    simpa [pow_one] using hsymm_map.le
  refine
    { toContinuous := he_cont.comp hf.toContinuous
      lift_condition := ?_ }
  intro B _ _ _ L _ hL g hg g0 hg0 hcomm
  let gS : S →+* B ⧸ L := g.comp e.toRingHom
  have hgS : Continuous gS := hg.comp he_cont
  have hcommS : (Ideal.Quotient.mk L).comp g0 = gS.comp f := by
    simpa [gS, RingHom.comp_assoc] using hcomm
  -- Solve the lifted problem on `S`, then conjugate the resulting lift back along `e.symm`.
  obtain ⟨φS, hφScont, hφSquot, hφSbase⟩ :=
    RingHom.FormallySmoothTopologically.exists_lift hf L hL gS hgS g0 hg0 hcommS
  let φ : T →+* B := φS.comp e.symm.toRingHom
  have hφcont : Continuous φ := hφScont.comp he_symm_cont
  refine ⟨φ, hφcont, ?_, ?_⟩
  · ext t
    simpa [φ, gS] using DFunLike.congr_fun hφSquot (e.symm t)
  · ext r
    simpa [φ, RingHom.comp_assoc] using DFunLike.congr_fun hφSbase r

/-- Helper for Lemma 15.38.5: the polynomial algebra on finitely many variables over a separable
field extension is formally smooth for the `idealOfVars`-adic topology over the base field. -/
lemma mvPolynomial_over_separable_field_formally_smooth_for_idealOfVars_adic
    {K : Type*} [Field K] [Algebra k K] (d : ℕ) [Algebra.IsSeparableOver k K] :
    (algebraMap k (MvPolynomial (Fin d) K)).formally_smooth_for_adic
      (MvPolynomial.idealOfVars (Fin d) K) := by
  let f : k →+* MvPolynomial (Fin d) K := algebraMap k (MvPolynomial (Fin d) K)
  let J : Ideal (MvPolynomial (Fin d) K) := MvPolynomial.idealOfVars (Fin d) K
  rw [RingHom.formally_smooth_for_adic_iff]
  letI : TopologicalSpace k := ⊥
  letI : DiscreteTopology k := ⟨rfl⟩
  letI : TopologicalSpace (MvPolynomial (Fin d) K) := Ideal.adicTopology J
  letI : TopologicalRing.IsPreadicRing (MvPolynomial (Fin d) K) :=
    { toIsTopologicalRing := inferInstance
      exists_ideal_isAdic := ⟨J, rfl⟩ }
  -- First upgrade algebraic formal smoothness of the coefficient map to the required adic
  -- topological formal smoothness.
  change f.FormallySmoothTopologically
  have hfs : f.FormallySmooth := by
    have hfsAlg : Algebra.FormallySmooth k (MvPolynomial (Fin d) K) := by
      letI : Algebra.FormallySmooth k K := Algebra.formallySmooth_of_isSeparableOver
      letI : Algebra.FormallySmooth K (MvPolynomial (Fin d) K) :=
        Algebra.mvPolynomial (σ := Fin d)
      exact Algebra.FormallySmooth.comp k K (MvPolynomial (Fin d) K)
    rw [RingHom.formallySmooth_algebraMap]
    exact hfsAlg
  simpa [f] using RingHom.FormallySmooth.toTopologically hfs continuous_of_discreteTopology

/-- Helper for Lemma 15.38.5: the inverse completion equivalence collapses the polynomial-to-
completion map to the canonical polynomial-to-power-series map. -/
lemma completion_equiv_symm_comp_polynomial_map
    {K : Type*} [Field K] (d : ℕ) :
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) K).symm.toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (Fin d) K)
          (AdicCompletion (MvPolynomial.idealOfVars (Fin d) K) (MvPolynomial (Fin d) K))) =
      algebraMap (MvPolynomial (Fin d) K) (MvPowerSeries (Fin d) K) := by
  -- The completion equivalence is `MvPolynomial`-linear, so it commutes with the polynomial
  -- structure map on every polynomial.
  exact RingHom.ext fun p ↦ by
    exact (MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) K).symm.commutes p

/-- Helper for Lemma 15.38.5: each formal variable lies in the maximal ideal of the finite
variable power series ring over a field. -/
lemma powerSeries_variable_mem_maximalIdeal
    {K : Type*} [Field K] (d : ℕ) (i : Fin d) :
    MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin d) K) := by
  -- A unit power series has unit constant coefficient, but `X i` has constant coefficient `0`.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have hcoeff : IsUnit (MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin d) K)) :=
    MvPowerSeries.isUnit_constantCoeff _ hunit
  simpa [MvPowerSeries.constantCoeff_X] using hcoeff

/-- Helper for Lemma 15.38.5: the canonical polynomial-to-power-series map sends each polynomial
variable to the matching formal power-series variable. -/
lemma polynomial_variable_maps_to_powerSeries_variable
    {K : Type*} [Field K] (d : ℕ) (i : Fin d) :
    (algebraMap (MvPolynomial (Fin d) K) (MvPowerSeries (Fin d) K)) (MvPolynomial.X i) =
      MvPowerSeries.X i := by
  -- The polynomial variable embeds as the matching power-series variable.
  rw [MvPowerSeries.algebraMap_apply']
  simpa using (MvPolynomial.coe_X (σ := Fin d) (R := K) i)

/-- Helper for Lemma 15.38.5: after transporting the completed variable ideal from the
`idealOfVars`-adic completion to the power series ring, it is contained in the maximal ideal. -/
lemma mapped_idealOfVars_completion_le_mvPowerSeries_maximalIdeal
    {K : Type*} [Field K] (d : ℕ) :
    Ideal.map
        ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) K).symm.toRingEquiv.toRingHom)
        (Ideal.map
          (algebraMap (MvPolynomial (Fin d) K)
            (AdicCompletion (MvPolynomial.idealOfVars (Fin d) K) (MvPolynomial (Fin d) K)))
          (MvPolynomial.idealOfVars (Fin d) K)) ≤
      maximalIdeal (MvPowerSeries (Fin d) K) := by
  -- First collapse the transported ideal to the direct image of `idealOfVars`.
  rw [Ideal.map_map]
  rw [completion_equiv_symm_comp_polynomial_map (K := K) d]
  -- Then check the generators of `idealOfVars` land in the maximal ideal upstairs.
  refine Ideal.map_le_iff_le_comap.mpr ?_
  rw [MvPolynomial.idealOfVars]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  simpa [Ideal.mem_comap, polynomial_variable_maps_to_powerSeries_variable (K := K) d i] using
    powerSeries_variable_mem_maximalIdeal (K := K) d i

/-- Helper for Lemma 15.38.5: a finite-variable power series ring over a separable field
extension is formally smooth for the maximal-ideal-adic topology over the base field. -/
lemma mvPowerSeries_over_separable_field_formally_smooth_for_maximalIdeal_adic
    {K : Type*} [Field K] [Algebra k K] (d : ℕ) [Algebra.IsSeparableOver k K] :
    (algebraMap k (MvPowerSeries (Fin d) K)).formally_smooth_for_adic
      (maximalIdeal (MvPowerSeries (Fin d) K)) := by
  let J : Ideal (MvPolynomial (Fin d) K) := MvPolynomial.idealOfVars (Fin d) K
  let C := AdicCompletion J (MvPolynomial (Fin d) K)
  let _ : CommRing C := inferInstance
  have hpoly :
      (algebraMap k (MvPolynomial (Fin d) K)).formally_smooth_for_adic J :=
    mvPolynomial_over_separable_field_formally_smooth_for_idealOfVars_adic
      (k := k) (K := K) d
  have hcont :
      letI : TopologicalSpace k := Ideal.adicTopology (⊥ : Ideal k)
      letI : TopologicalSpace (MvPolynomial (Fin d) K) := Ideal.adicTopology J
      Continuous (algebraMap k (MvPolynomial (Fin d) K)) := by
    -- The source carries the discrete adic topology, so continuity is immediate.
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    simpa [J] using
      (bot_le : Ideal.map (algebraMap k (MvPolynomial (Fin d) K)) ((⊥ : Ideal k) ^ 1) ≤ J)
  have hTFAE :
      List.TFAE [
        RingHom.formally_smooth_for_adic (algebraMap k (MvPolynomial (Fin d) K)) J,
        RingHom.formally_smooth_for_adic
          ((algebraMap (MvPolynomial (Fin d) K) C).comp (algebraMap k (MvPolynomial (Fin d) K)))
          (Ideal.map (algebraMap (MvPolynomial (Fin d) K) C) J),
        RingHom.formally_smooth_for_adic
          ((algebraMap k (MvPolynomial (Fin d) K)).adicCompletionMap (⊥ : Ideal k) J hcont)
          (Ideal.map (algebraMap (MvPolynomial (Fin d) K) C) J)
      ] := by
    simpa [J, C] using
      RingHom.formally_smooth_for_adic_tfae_completion_invariance
        (⊥ : Ideal k) (Ideal.fg_of_isNoetherianRing (⊥ : Ideal k))
        J (Ideal.fg_of_isNoetherianRing J)
        (algebraMap k (MvPolynomial (Fin d) K)) hcont
  have hcompletion :
      RingHom.formally_smooth_for_adic
        ((algebraMap (MvPolynomial (Fin d) K) C).comp (algebraMap k (MvPolynomial (Fin d) K)))
        (Ideal.map (algebraMap (MvPolynomial (Fin d) K) C) J) :=
    (hTFAE.out 0 1).mp hpoly
  have htransport :
      RingHom.formally_smooth_for_adic
        (((MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) K).symm.toRingEquiv.toRingHom).comp
          ((algebraMap (MvPolynomial (Fin d) K) C).comp (algebraMap k (MvPolynomial (Fin d) K))))
        (Ideal.map
          ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) K).symm.toRingEquiv.toRingHom)
          (Ideal.map (algebraMap (MvPolynomial (Fin d) K) C) J)) := by
    exact formally_smooth_for_adic_of_codomain_ringEquiv
      (f := ((algebraMap (MvPolynomial (Fin d) K) C).comp
        (algebraMap k (MvPolynomial (Fin d) K))))
      (e := (MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) K).symm.toRingEquiv)
      rfl hcompletion
  have hcomp :
      ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) K).symm.toRingEquiv.toRingHom).comp
          ((algebraMap (MvPolynomial (Fin d) K) C).comp (algebraMap k (MvPolynomial (Fin d) K))) =
        algebraMap k (MvPowerSeries (Fin d) K) := by
    -- Rewrite the completion-side polynomial map to the canonical polynomial-to-power-series map.
    calc
      ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) K).symm.toRingEquiv.toRingHom).comp
          ((algebraMap (MvPolynomial (Fin d) K) C).comp (algebraMap k (MvPolynomial (Fin d) K))) =
          (((MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) K).symm.toRingEquiv.toRingHom).comp
            (algebraMap (MvPolynomial (Fin d) K) C)).comp
              (algebraMap k (MvPolynomial (Fin d) K)) := by
                rw [RingHom.comp_assoc]
      _ = (algebraMap (MvPolynomial (Fin d) K) (MvPowerSeries (Fin d) K)).comp
            (algebraMap k (MvPolynomial (Fin d) K)) := by
              rw [completion_equiv_symm_comp_polynomial_map (K := K) d]
      _ = algebraMap k (MvPowerSeries (Fin d) K) := by
            -- Install the coefficient tower and then read off scalar compatibility of the maps.
            let _ : IsScalarTower k K (MvPowerSeries (Fin d) K) :=
              IsScalarTower.of_algebraMap_eq fun x ↦ by
                simpa [MvPowerSeries.c_eq_algebraMap] using
                  (rfl : MvPowerSeries.C ((algebraMap k K) x) = MvPowerSeries.C ((algebraMap k K) x))
            refine RingHom.ext ?_
            intro x
            rw [RingHom.comp_apply, MvPowerSeries.algebraMap_apply']
            simpa [MvPowerSeries.c_eq_algebraMap] using
              DFunLike.congr_fun
                (IsScalarTower.algebraMap_eq k K (MvPowerSeries (Fin d) K)).symm x
  rw [hcomp] at htransport
  -- Enlarge the transported defining ideal to the maximal ideal of the power series ring.
  exact
    RingHom.formally_smooth_for_adic_of_le
      (f := algebraMap k (MvPowerSeries (Fin d) K))
      (mapped_idealOfVars_completion_le_mvPowerSeries_maximalIdeal (K := K) d)
      htransport

/- Domain-style sampling for Lemma 15.38.5:
- primary domain: local commutative algebra of regular local `k`-algebras and maximal-ideal-adic
  formal smoothness.
- sampled owner declarations:
  `RingHom.formally_smooth_for_adic`,
  `RingHom.formally_smooth_for_adic_tfae_completion_invariance`,
  `exists_algEquiv_mvPowerSeries_residueField_of_isSeparableOver_of_isRegularLocalRing`,
  `Algebra.IsSeparableOver`.
- best owner abstraction: the public conclusion should be stated directly with the chapter owner
  `(algebraMap k A).formally_smooth_for_adic (maximalIdeal A)`. Completion invariance and the
  finite-variable power-series presentation are proof bridges, not extra public data.
- primitive data: the field `k`, the regular local `k`-algebra `A`, and the Stacks-separability
  hypothesis on `ResidueField A / k`.
- derived API: formal smoothness of the structural map for the `maximalIdeal A`-adic topology.

Source/core/bridge triage:
- `source-facing`: the textbook implication from regularity plus separable residue field to adic
  formal smoothness.
- `core/canonical`: `RingHom.formally_smooth_for_adic`.
- `bridge/view`: completion invariance and the complete-regular-local power-series presentation.
-/

-- Proof sketch: pass from `A` to its maximal-ideal completion using completion invariance for
-- `RingHom.formally_smooth_for_adic`. The completion is complete regular local and has the same
-- residue field as `A`, so Lemma `15.38.4` identifies it with a finite-variable power series ring
-- over that residue field. The remaining source-faithful blocker is the generic statement that a
-- finite-variable power series ring over a separable field extension is adically formally smooth
-- over the base field.
/-- Lemma 15.38.5: if `(A, maximalIdeal A, ResidueField A)` is a regular local `k`-algebra and the
residue field extension `ResidueField A / k` is separable in the Stacks Project sense, then the
structure map `k → A`, formalized by `algebraMap k A`, is formally smooth for the
`maximalIdeal A`-adic topology. -/
theorem formallySmooth_for_maximalIdeal_adic_of_isRegularLocalRing_of_isSeparableOver
    [Algebra.IsSeparableOver k (ResidueField A)] :
    (algebraMap k A).formally_smooth_for_adic (maximalIdeal A) := by
  letI : IsCompleteLocalRing ACompletion := completion_isCompleteLocalRing (A := A)
  letI : IsRegularLocalRing ACompletion := completion_isRegularLocalRing (A := A)
  let eκ : ResidueField A ≃ₐ[k] ResidueField ACompletion :=
    (completion_residueField_algEquiv (k := k) (A := A)).symm
  letI : Algebra.IsSeparableOver k (ResidueField ACompletion) :=
    Algebra.IsSeparableOver.of_algEquiv
      (F := k) (E := ResidueField A) (L := ResidueField ACompletion) inferInstance eκ
  obtain ⟨d, hd⟩ :=
    exists_algEquiv_mvPowerSeries_residueField_of_isSeparableOver_of_isRegularLocalRing
      (k := k) (A := ACompletion)
  rcases hd with ⟨e⟩
  have hpower :
      (algebraMap k (MvPowerSeries (Fin d) (ResidueField ACompletion))).formally_smooth_for_adic
        (maximalIdeal (MvPowerSeries (Fin d) (ResidueField ACompletion))) :=
    mvPowerSeries_over_separable_field_formally_smooth_for_maximalIdeal_adic
      (k := k) (K := ResidueField ACompletion) d
  have hcompletion :
      (algebraMap k ACompletion).formally_smooth_for_adic (maximalIdeal ACompletion) := by
    have hmap :
        Ideal.map e.toRingHom
          (maximalIdeal (MvPowerSeries (Fin d) (ResidueField ACompletion))) =
          maximalIdeal ACompletion := by
      haveI : IsLocalHom e.toRingHom := Function.Surjective.isLocalHom _ e.surjective
      -- A ring equivalence carries the distinguished maximal ideal of a local ring to the
      -- distinguished maximal ideal of the target local ring.
      calc
        Ideal.map e.toRingHom
            (maximalIdeal (MvPowerSeries (Fin d) (ResidueField ACompletion))) =
              Ideal.map e.toRingHom (Ideal.comap e.toRingHom (maximalIdeal ACompletion)) := by
                congr 1
                exact (IsLocalRing.maximalIdeal_comap e.toRingHom).symm
        _ = maximalIdeal ACompletion := by
              simpa using
                Ideal.map_comap_of_surjective e.toRingHom e.surjective (maximalIdeal ACompletion)
    have htransport :
        (e.toRingHom.comp
          (algebraMap k (MvPowerSeries (Fin d) (ResidueField ACompletion)))).formally_smooth_for_adic
          (maximalIdeal ACompletion) := by
      exact formally_smooth_for_adic_of_codomain_ringEquiv
        (f := algebraMap k (MvPowerSeries (Fin d) (ResidueField ACompletion)))
        (e := e.toRingEquiv)
        (K := maximalIdeal ACompletion)
        hmap hpower
    have hcomp :
        e.toRingHom.comp (algebraMap k (MvPowerSeries (Fin d) (ResidueField ACompletion))) =
          algebraMap k ACompletion := by
      ext x
      simpa using e.commutes x
    -- Rewrite the composite coefficient map through the chosen `k`-algebra equivalence.
    rw [hcomp] at htransport
    exact htransport
  have hcont :
      letI : TopologicalSpace k := Ideal.adicTopology (⊥ : Ideal k)
      letI : TopologicalSpace A := Ideal.adicTopology (maximalIdeal A)
      Continuous (algebraMap k A) := by
    -- The source carries the discrete adic topology, so continuity is immediate.
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    simpa using
      (bot_le : Ideal.map (algebraMap k A) ((⊥ : Ideal k) ^ 1) ≤ maximalIdeal A)
  have hTFAE :
      List.TFAE [
        (algebraMap k A).formally_smooth_for_adic (maximalIdeal A),
        ((algebraMap A ACompletion).comp (algebraMap k A)).formally_smooth_for_adic
          (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)),
        RingHom.formally_smooth_for_adic
          ((algebraMap k A).adicCompletionMap (⊥ : Ideal k) (maximalIdeal A) hcont)
          (Ideal.map (algebraMap A ACompletion) (maximalIdeal A))
      ] := by
    simpa using
      RingHom.formally_smooth_for_adic_tfae_completion_invariance
        (⊥ : Ideal k) (Ideal.fg_of_isNoetherianRing (⊥ : Ideal k))
        (maximalIdeal A) (Ideal.fg_of_isNoetherianRing (maximalIdeal A))
        (algebraMap k A) hcont
  have hcompletion_map :
      ((algebraMap A ACompletion).comp (algebraMap k A)).formally_smooth_for_adic
        (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := by
    -- Rewrite the completion-side structure map into the canonical map `k → ACompletion`.
    simpa [completion_map_maximalIdeal_eq_maximalIdeal (A := A),
      show ((algebraMap A ACompletion).comp (algebraMap k A)) = algebraMap k ACompletion by
        ext x
        rfl] using hcompletion
  exact (hTFAE.out 1 0).mp hcompletion_map

end
