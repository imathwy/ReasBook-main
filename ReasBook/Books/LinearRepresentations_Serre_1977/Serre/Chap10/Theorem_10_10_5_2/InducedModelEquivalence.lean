import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap03.Definition_3_3_3_1
import LinearRepresentations_Serre_1977.Serre.Chap03.Exercise_3_3_3_6
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Serre.Chap08.Definition_8_8_3_2
import LinearRepresentations_Serre_1977.Serre.Chap08.Exercise_8_8_3_9
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap10.MonomialCharacter

import LinearRepresentations_Serre_1977.Serre.Chap10.Theorem_10_10_5_2.MonomialLinearCharacter

noncomputable section

namespace Representation

open CategoryTheory Rep
open scoped Representation SubgroupInduction
open scoped BigOperators Pointwise

section

variable {G : Type} [Group G] [Finite G]

/-- Helper for isMonomialCharacter_of_isMonomial: restricting a representation equivalence along a
subgroup keeps the same underlying linear equivalence. -/
theorem comp_subtype_equiv_isIntertwining_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) :
    ∀ s, e.toLinearEquiv ∘ₗ (ρ.comp S.subtype) s = (σ.comp S.subtype) s ∘ₗ e.toLinearEquiv := by
  intro s
  -- Restricting the source group does not change the intertwining identity.
  simpa using e.isIntertwining' (s : K)

/-- Helper for isMonomialCharacter_of_isMonomial: restricting a representation equivalence along a
subgroup keeps the same underlying linear equivalence. -/
noncomputable def comp_subtype_equiv_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) :
    Representation.Equiv (ρ.comp S.subtype) (σ.comp S.subtype) :=
  Representation.Equiv.mk e.toLinearEquiv (comp_subtype_equiv_isIntertwining_local e S)

/-- Helper for isMonomialCharacter_of_isMonomial: transporting a subrepresentation across an
ambient equivalence just maps its carrier by the underlying linear equivalence. -/
theorem transported_subrepresentation_of_equiv_stable_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    ∀ g ⦃x : W'⦄, x ∈ U.toSubmodule.map e.toLinearMap → σ g x ∈ U.toSubmodule.map e.toLinearMap := by
  intro g x hx
  rcases hx with ⟨y, hy, rfl⟩
  -- Mapping a stable carrier through an intertwiner preserves stability.
  refine ⟨ρ g y, U.apply_mem_toSubmodule g hy, ?_⟩
  simp [e.isIntertwining]

/-- Helper for isMonomialCharacter_of_isMonomial: transporting a subrepresentation across an
ambient equivalence just maps its carrier by the underlying linear equivalence. -/
noncomputable def transported_subrepresentation_of_equiv_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    Subrepresentation σ where
  toSubmodule := U.toSubmodule.map e.toLinearMap
  apply_mem_toSubmodule := transported_subrepresentation_of_equiv_stable_local e U

/-- Helper for isMonomialCharacter_of_isMonomial: the transported subrepresentation has the
expected mapped carrier. -/
@[simp] theorem transported_subrepresentation_of_equiv_toSubmodule_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    (transported_subrepresentation_of_equiv_local e U).toSubmodule =
      U.toSubmodule.map e.toLinearMap :=
  rfl

/-- Helper for isMonomialCharacter_of_isMonomial: transporting the inducing carrier along an
ambient equivalence transports each quotient summand by the same linear equivalence. -/
theorem leftQuotientSubmodule_eq_map_of_equiv_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype)) (q : K ⧸ S) :
    σ.leftQuotientSubmodule S
        (transported_subrepresentation_of_equiv_local (comp_subtype_equiv_local e S) U) q =
      (ρ.leftQuotientSubmodule S U q).map e.toLinearMap := by
  refine Quotient.inductionOn' q ?_
  intro g
  -- Both quotient summands are the image of `U` under the same translated action.
  rw [Representation.leftQuotientSubmodule_mk, Representation.leftQuotientSubmodule_mk]
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨ρ g u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simpa [comp_subtype_equiv_local] using LinearMap.congr_fun (e.isIntertwining' g) u
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨e u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simp [e.isIntertwining]

/-- Helper for isMonomialCharacter_of_isMonomial: inducedness is preserved when the ambient
representation is replaced by an equivalent one. -/
theorem isInducedFromSubrepresentation_of_equiv_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U) :
    σ.IsInducedFromSubrepresentation S
      (transported_subrepresentation_of_equiv_local (comp_subtype_equiv_local e S) U) := by
  classical
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  let U' := transported_subrepresentation_of_equiv_local (comp_subtype_equiv_local e S) U
  have hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule S U) := by
    -- Unpack the Chapter `3` owner into the quotient-indexed internal direct sum.
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  have hleft_fun :
      σ.leftQuotientSubmodule S U' = fun q ↦ (ρ.leftQuotientSubmodule S U q).map e.toLinearMap := by
    funext q
    simpa [U'] using leftQuotientSubmodule_eq_map_of_equiv_local e S U q
  have hIndep : iSupIndep (σ.leftQuotientSubmodule S U') := by
    -- Independence transports along the injective linear equivalence `e`.
    rw [hleft_fun]
    exact LinearMap.iSupIndep_map e.toLinearMap e.injective hInternal.submodule_iSupIndep
  have hspan : iSup (σ.leftQuotientSubmodule S U') = ⊤ := by
    -- Surjectivity of `e` carries the spanning statement to the transported family.
    calc
      iSup (σ.leftQuotientSubmodule S U') =
          iSup (fun q ↦ (ρ.leftQuotientSubmodule S U q).map e.toLinearMap) := by
            rw [hleft_fun]
      _ = (iSup (ρ.leftQuotientSubmodule S U)).map e.toLinearMap := by
            rw [Submodule.map_iSup]
      _ = ⊤ := by
            rw [hInternal.submodule_iSup_eq_top, Submodule.map_top]
            exact LinearMap.range_eq_top.mpr e.surjective
  -- Package the transported independence and spanning statements back into the Chapter `3` owner.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndep hspan

/-- Helper for isMonomialCharacter_of_isMonomial: the unit-coset projection on an induced model
recovers the original vector. -/
noncomputable def induced_identity_copy_projection_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    Representation.IndV S.subtype σ →ₗ[ℂ] W :=
  Representation.Coinvariants.lift _
    (TensorProduct.lift <|
      Finsupp.lift _ _ _ fun g ↦
        @dite _ (g ∈ S) ((Classical.decPred fun x : K ↦ x ∈ S) g)
          (fun hg ↦ σ ⟨g, hg⟩⁻¹)
          (fun _ ↦ 0))
    (fun s ↦ by
      -- Check the coinvariant relation on generators `δ_g ⊗ w`.
      ext g w
      by_cases hg : g ∈ S
      · have hsg : ((s : K) * g) ∈ S := S.mul_mem s.property hg
        have hmul : σ ⟨(s : K) * g, hsg⟩⁻¹ (σ s w) = σ ⟨g, hg⟩⁻¹ w := by
          have hsub : ((⟨(s : K) * g, hsg⟩⁻¹ : S) * s) = ⟨g, hg⟩⁻¹ := by
            ext
            simp [mul_assoc]
          calc
            σ ⟨(s : K) * g, hsg⟩⁻¹ (σ s w)
                = σ (((⟨(s : K) * g, hsg⟩⁻¹ : S) * s)) w := by
                    simp [Module.End.mul_apply, map_mul]
            _ = σ ⟨g, hg⟩⁻¹ w := by
                    rw [hsub]
        simpa [TensorProduct.lift.tmul, hg, hsg] using hmul
      · have hsng : ((s : K) * g) ∉ S := by
          intro hmem
          have htmp : ((s : K)⁻¹ * ((s : K) * g)) ∈ S :=
            S.mul_mem (S.inv_mem s.property) hmem
          have hg' : g ∈ S := by
            simpa [mul_assoc] using htmp
          exact hg hg'
        simp [TensorProduct.lift.tmul, hg, hsng])

/-- Helper for isMonomialCharacter_of_isMonomial: the unit-coset projection recovers the source
vector on the unit generator. -/
theorem induced_identity_copy_projection_apply_mk_one_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) (w : W) :
    induced_identity_copy_projection_local S σ (Representation.IndV.mk S.subtype σ 1 w) = w := by
  classical
  have hone : (1 : K) ∈ S := S.one_mem
  have hbase : σ ⟨1, hone⟩⁻¹ w = w := by
    have hsub : ((⟨1, hone⟩ : S)⁻¹) = 1 := by
      ext
      simp
    rw [hsub]
    exact LinearMap.congr_fun σ.map_one w
  -- Evaluating the quotient lift at the unit basis vector reduces to the identity on `W`.
  simpa [induced_identity_copy_projection_local, TensorProduct.lift.tmul, hone] using hbase

/-- Helper for isMonomialCharacter_of_isMonomial: the unit-coset embedding in an induced model is
injective. -/
theorem induced_identity_copy_mk_one_injective_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    Function.Injective (Representation.IndV.mk S.subtype σ 1) := by
  intro x y hxy
  have hproj := congrArg (induced_identity_copy_projection_local S σ) hxy
  calc
    x = induced_identity_copy_projection_local S σ (Representation.IndV.mk S.subtype σ 1 x) := by
          symm
          exact induced_identity_copy_projection_apply_mk_one_local S σ x
    _ = induced_identity_copy_projection_local S σ (Representation.IndV.mk S.subtype σ 1 y) := hproj
    _ = y := induced_identity_copy_projection_apply_mk_one_local S σ y

/-- Helper for isMonomialCharacter_of_isMonomial: the unit-coset copy is stable under the
restricted subgroup action. -/
theorem induced_identity_copy_apply_mem_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) (s : S)
    {x : Representation.IndV S.subtype σ}
    (hx : x ∈ LinearMap.range (Representation.IndV.mk S.subtype σ 1)) :
    ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) s x ∈
      LinearMap.range (Representation.IndV.mk S.subtype σ 1) := by
  rcases hx with ⟨w, rfl⟩
  -- Acting on the unit-coset copy just applies `σ s` to the source vector.
  refine ⟨σ s w, ?_⟩
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for isMonomialCharacter_of_isMonomial: the unit-coset copy of the source representation
inside the restricted induced model. -/
noncomputable def induced_identity_copy_subrepresentation_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    Subrepresentation ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) :=
  { toSubmodule := LinearMap.range (Representation.IndV.mk S.subtype σ 1)
    apply_mem_toSubmodule := induced_identity_copy_apply_mem_local S σ }

/-- Helper for isMonomialCharacter_of_isMonomial: the source representation is equivariantly
equivalent to its unit-coset copy in the induced model. -/
noncomputable def induced_identity_copy_equiv_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    σ.Equiv (induced_identity_copy_subrepresentation_local S σ).toRepresentation := by
  let e :
      W ≃ₗ[ℂ] (induced_identity_copy_subrepresentation_local S σ).toSubmodule :=
    LinearEquiv.ofInjective
      (Representation.IndV.mk S.subtype σ 1)
      (induced_identity_copy_mk_one_injective_local S σ)
  refine Representation.Equiv.mk e ?_
  intro s
  -- Both sides are the same vector in the induced model after transport by the unit-coset copy.
  ext w
  change Representation.IndV.mk S.subtype σ 1 (σ s w) =
    ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) s
      (Representation.IndV.mk S.subtype σ 1 w)
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for isMonomialCharacter_of_isMonomial: every vector in the unit-coset copy is the unit
generator attached to its preimage under the explicit equivalence. -/
theorem induced_identity_copy_eq_mk_one_symm_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W)
    (u : (induced_identity_copy_subrepresentation_local S σ).toSubmodule) :
    (u : Representation.IndV S.subtype σ) =
      Representation.IndV.mk S.subtype σ 1 ((induced_identity_copy_equiv_local S σ).symm u) := by
  -- The explicit copy equivalence is defined by the unit-coset embedding `IndV.mk ... 1`.
  have hmk (w : W) :
      (((induced_identity_copy_equiv_local S σ).toLinearEquiv w :
          (induced_identity_copy_subrepresentation_local S σ).toSubmodule) :
        Representation.IndV S.subtype σ) =
        Representation.IndV.mk S.subtype σ 1 w := by
    rfl
  have hEq :
      (induced_identity_copy_equiv_local S σ).toLinearEquiv
          ((induced_identity_copy_equiv_local S σ).symm u) = u := by
    exact (induced_identity_copy_equiv_local S σ).toLinearEquiv.apply_symm_apply u
  have hEq_coe :
      (u : Representation.IndV S.subtype σ) =
        ((((induced_identity_copy_equiv_local S σ).toLinearEquiv
              ((induced_identity_copy_equiv_local S σ).symm u)) :
            (induced_identity_copy_subrepresentation_local S σ).toSubmodule) :
          Representation.IndV S.subtype σ) := by
    simpa using
      congrArg
        (fun z : (induced_identity_copy_subrepresentation_local S σ).toSubmodule ↦
          (z : Representation.IndV S.subtype σ))
        hEq.symm
  calc
    (u : Representation.IndV S.subtype σ) =
        ((((induced_identity_copy_equiv_local S σ).toLinearEquiv
              ((induced_identity_copy_equiv_local S σ).symm u)) :
            (induced_identity_copy_subrepresentation_local S σ).toSubmodule) :
          Representation.IndV S.subtype σ) :=
      hEq_coe
    _ = Representation.IndV.mk S.subtype σ 1 ((induced_identity_copy_equiv_local S σ).symm u) :=
      hmk _

/-- Helper for isMonomialCharacter_of_isMonomial: the standard induced representation is induced
from its unit-coset copy. -/
theorem induced_identity_copy_is_induced_local
    {K : Type} [Group K] [Finite K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    ((Rep.ind S.subtype (Rep.of σ)).ρ).IsInducedFromSubrepresentation
      S (induced_identity_copy_subrepresentation_local S σ) := by
  classical
  let C : Rep ℂ K := Rep.coind S.subtype (Rep.of σ)
  let e :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).Equiv C.ρ :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of σ))
  let W₀ :
      Subrepresentation (C.ρ.comp S.subtype) :=
    Representation.supportedOnSubgroupSubrepresentation S σ
  have hW₀ :
      C.ρ.IsInducedFromSubrepresentation S W₀ := by
    -- The coinduced model already carries the Chapter `3` witness.
    simpa [C, W₀] using
      (Representation.isInducedFrom_supportedOnSubgroupSubrepresentation (H := S) (θ := σ))
  have htransport :
      transported_subrepresentation_of_equiv_local (comp_subtype_equiv_local e.symm S) W₀ =
        induced_identity_copy_subrepresentation_local S σ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      let fy : K → W := (y : C)
      have hySupportSubgroup :
          Function.support fy ⊆ (S : Set K) := by
        simpa [C, W₀] using
          (Representation.mem_supportedOnSubgroupSubrepresentation_iff S σ y).mp hy
      have hySupportOrbit :
          Function.support fy ⊆ MulAction.orbit S (1 : K) := by
        intro u hu
        refine ⟨⟨u, hySupportSubgroup hu⟩, ?_⟩
        simp
      have hyImage :
          e.symm y =
            Representation.IndV.mk S.subtype σ 1 (fy 1) := by
        change (Rep.of σ).coindToInd y =
          Representation.IndV.mk S.subtype σ 1 (fy 1)
        simpa using
          (Rep.coindToInd_of_support_subset_orbit (A := Rep.of σ) (g := (1 : K))
            y hySupportOrbit)
      exact LinearMap.mem_range.mpr ⟨fy 1, hyImage.symm⟩
    · intro hx
      rcases LinearMap.mem_range.mp hx with ⟨w, rfl⟩
      let fw : W₀.toSubmodule :=
        ⟨Representation.subgroupSupportedFunction S σ w,
          Representation.subgroupSupportedFunction_mem_supportedOnSubgroupSubrepresentation S σ w⟩
      let ffw : K → W := (((fw : W₀.toSubmodule) : C) : K → W)
      have hfwSupportSubgroup :
          Function.support ffw ⊆ (S : Set K) := by
        simpa [C, W₀] using
          (Representation.mem_supportedOnSubgroupSubrepresentation_iff S σ
            ((fw : W₀.toSubmodule) : C)).mp fw.property
      have hfwSupportOrbit :
          Function.support ffw ⊆ MulAction.orbit S (1 : K) := by
        intro u hu
        refine ⟨⟨u, hfwSupportSubgroup hu⟩, ?_⟩
        simp
      have hfwImage :
          e.symm fw = Representation.IndV.mk S.subtype σ 1 w := by
        have hcoind :
            e.symm fw =
              Representation.IndV.mk S.subtype σ 1 (ffw 1) := by
          change (Rep.of σ).coindToInd ((fw : W₀.toSubmodule) : C) =
            Representation.IndV.mk S.subtype σ 1 (ffw 1)
          simpa using
            (Rep.coindToInd_of_support_subset_orbit (A := Rep.of σ) (g := (1 : K))
              (((fw : W₀.toSubmodule) : C)) hfwSupportOrbit)
        have hEval :
            ffw 1 = w := by
          calc
            ffw 1 = σ ⟨1, S.one_mem⟩ w := by
              simpa [fw] using
                (Representation.subgroupSupportedFunction_of_mem
                  (H := S) (θ := σ) w S.one_mem)
            _ = w := by
              have hone : σ ⟨1, S.one_mem⟩ = 1 := by
                change σ 1 = 1
                simpa using σ.map_one
              rw [hone]
              rfl
        rw [hEval] at hcoind
        exact hcoind
      exact Submodule.mem_map.mpr ⟨fw, fw.property, hfwImage⟩
  -- Transport the coinduced witness back across the finite-index comparison `Ind ≃ Coind`.
  simpa [htransport] using
    isInducedFromSubrepresentation_of_equiv_local e.symm S W₀ hW₀

/-- Helper for isMonomialCharacter_of_isMonomial: the canonical map from the standard induced
model to the ambient representation. -/
noncomputable abbrev inducedFromSubrepresentationHom_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype)) :
    Rep.ind S.subtype (Rep.of U.toRepresentation) ⟶ Rep.of ρ :=
  (Rep.indResHomEquiv S.subtype (Rep.of U.toRepresentation) (Rep.of ρ)).symm
    ((Rep.res S.subtype (Rep.of ρ)).subtype U.toSubmodule U.apply_mem_toSubmodule)

/-- Helper for isMonomialCharacter_of_isMonomial: evaluating the canonical induced map on
`⟦g ⊗ u⟧` recovers the ambient action `ρ g⁻¹ u`. -/
@[simp] theorem inducedFromSubrepresentationHom_mk_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (g : K) (u : U.toSubmodule) :
    (inducedFromSubrepresentationHom_local ρ S U).hom
        (Representation.IndV.mk S.subtype U.toRepresentation g u) =
      ρ g⁻¹ u := by
  simpa [inducedFromSubrepresentationHom_local] using
    congrArg (ρ g⁻¹)
      (show ((Rep.res S.subtype (Rep.of ρ)).subtype U.toSubmodule
          U.apply_mem_toSubmodule).hom u = (u : W) from rfl)

/-- Helper for isMonomialCharacter_of_isMonomial: each quotient summand in an induced
decomposition is canonically identified with the source by translation. -/
@[simp] theorem left_quotient_submodule_out_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (q : K ⧸ S) :
    ρ.leftQuotientSubmodule S U q = U.toSubmodule.map (ρ q.out) := by
  simpa using (ρ.leftQuotientSubmodule_mk S U q.out)

/-- Helper for isMonomialCharacter_of_isMonomial: each quotient summand in an induced
decomposition is canonically identified with the source by translation. -/
noncomputable def left_quotient_submodule_equiv_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (q : K ⧸ S) :
    U.toSubmodule ≃ₗ[ℂ] ρ.leftQuotientSubmodule S U q :=
  let e : W ≃ₗ[ℂ] W := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
  (e.submoduleMap U.toSubmodule).trans
    (LinearEquiv.ofEq _ _ (left_quotient_submodule_out_local ρ S U q).symm)

/-- Helper for isMonomialCharacter_of_isMonomial: the forward quotient-translation equivalence
acts by the chosen representative action `ρ q.out`. -/
@[simp] theorem left_quotient_submodule_equiv_local_apply
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (q : K ⧸ S) (u : U.toSubmodule) :
    ((left_quotient_submodule_equiv_local ρ S U q u :
        ρ.leftQuotientSubmodule S U q) : W) =
      ρ q.out u := by
  simp [left_quotient_submodule_equiv_local]

/-- Helper for isMonomialCharacter_of_isMonomial: the inverse local quotient-translation
equivalence acts by `ρ q.out⁻¹`. -/
@[simp] theorem left_quotient_submodule_equiv_local_symm_apply
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (q : K ⧸ S) (x : ρ.leftQuotientSubmodule S U q) :
    (((left_quotient_submodule_equiv_local ρ S U q).symm x : U.toSubmodule) : W) =
      ρ q.out⁻¹ x := by
  let e : W ≃ₗ[ℂ] W := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
  change (((e.submoduleMap U.toSubmodule).symm
      ((LinearEquiv.ofEq _ _ (left_quotient_submodule_out_local ρ S U q).symm).symm x) :
        U.toSubmodule) :
        W) = ρ q.out⁻¹ x
  apply (ρ.apply_bijective q.out).injective
  simp [e]

/-- Helper for isMonomialCharacter_of_isMonomial: extend an equivariant map on the inducing
subrepresentation to a single quotient summand. -/
noncomputable def left_quotient_submodule_extension_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype))
    (q : K ⧸ S) :
    ρ.leftQuotientSubmodule S U q →ₗ[ℂ] W' :=
  (ρ' q.out).comp
    (f.toLinearMap.comp (left_quotient_submodule_equiv_local ρ S U q).symm.toLinearMap)

/-- Helper for isMonomialCharacter_of_isMonomial: the quotient-indexed internal sum yields a
global linear extension of an equivariant map on the inducing subrepresentation. -/
noncomputable def extensionLinearMapLocal
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype)) :
    W →ₗ[ℂ] W' :=
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  let hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule S U) := by
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule S U) hInternal
  (DirectSum.toModule ℂ (K ⧸ S) W'
      (left_quotient_submodule_extension_local ρ S U ρ' f)).comp
    (DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule S U)).toLinearMap

/-- Helper for isMonomialCharacter_of_isMonomial: on a single quotient summand the global
extension agrees with the corresponding component extension. -/
theorem extensionLinearMapLocal_apply_of_mem
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype))
    {x : W} {q : K ⧸ S} (hx : x ∈ ρ.leftQuotientSubmodule S U q) :
    extensionLinearMapLocal ρ S U hU ρ' f x =
      left_quotient_submodule_extension_local ρ S U ρ' f q ⟨x, hx⟩ := by
  classical
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  have hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule S U) := by
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule S U) hInternal
  have hxdecomp :
      DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule S U) x =
        DirectSum.lof ℂ (K ⧸ S) (fun i ↦ ρ.leftQuotientSubmodule S U i) q ⟨x, hx⟩ := by
    simpa using
      (DirectSum.decomposeLinearEquiv_apply_coe
        (R := ℂ) (ι := K ⧸ S) (ℳ := ρ.leftQuotientSubmodule S U) q ⟨x, hx⟩)
  rw [extensionLinearMapLocal]
  simpa [LinearMap.comp_apply, DirectSum.toModule_lof] using
    congrArg (DirectSum.toModule ℂ (K ⧸ S) W'
      (left_quotient_submodule_extension_local ρ S U ρ' f)) hxdecomp

/-- Helper for isMonomialCharacter_of_isMonomial: the global extension agrees with the original
equivariant map on the inducing subrepresentation. -/
theorem extensionLinearMapLocal_extends
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype))
    (u : U.toSubmodule) :
    extensionLinearMapLocal ρ S U hU ρ' f u = f u := by
  classical
  let q : K ⧸ S := QuotientGroup.mk 1
  have hq_rel : QuotientGroup.leftRel S q.out 1 := by
    exact Quotient.exact' (by simp [q])
  rw [QuotientGroup.leftRel_apply] at hq_rel
  have hq_mem : q.out ∈ S := by
    simpa using S.inv_mem hq_rel
  let h : S := ⟨q.out, hq_mem⟩
  let uinv : U.toSubmodule := ⟨ρ q.out⁻¹ u, U.apply_mem_toSubmodule h⁻¹ u.property⟩
  have huq : (u : W) ∈ ρ.leftQuotientSubmodule S U q := by
    rw [left_quotient_submodule_out_local ρ S U q]
    exact Submodule.mem_map.mpr ⟨uinv, uinv.property, by
      change ρ q.out (ρ q.out⁻¹ u) = u
      simp⟩
  have hsymm :
      (left_quotient_submodule_equiv_local ρ S U q).symm ⟨u, huq⟩ = uinv := by
    ext
    simp [uinv]
  rw [extensionLinearMapLocal_apply_of_mem ρ S U hU ρ' f huq]
  change ρ' q.out (f ((left_quotient_submodule_equiv_local ρ S U q).symm ⟨u, huq⟩)) = f u
  rw [hsymm]
  have huint : f uinv = ρ' q.out⁻¹ (f u) := by
    simpa [h, uinv] using
      (Representation.IntertwiningMap.isIntertwining (f := f) (g := h⁻¹) (v := u))
  rw [huint]
  simp

/-- Helper for isMonomialCharacter_of_isMonomial: the extension built from the internal sum is
equivariant for the ambient group action. -/
theorem extensionLinearMapLocal_isIntertwining
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype)) :
    ∀ s : K, ∀ x : W,
      extensionLinearMapLocal ρ S U hU ρ' f (ρ s x) =
        ρ' s (extensionLinearMapLocal ρ S U hU ρ' f x) := by
  classical
  let ℳ : K ⧸ S → Submodule ℂ W := ρ.leftQuotientSubmodule S U
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  have hInternal : DirectSum.IsInternal ℳ := by
    simpa [ℳ, Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition ℳ hInternal
  intro s x
  refine DirectSum.Decomposition.inductionOn (ℳ := ℳ)
      (motive := fun x : W ↦
        extensionLinearMapLocal ρ S U hU ρ' f (ρ s x) =
          ρ' s (extensionLinearMapLocal ρ S U hU ρ' f x))
      ?_ ?_ ?_ x
  · simp [extensionLinearMapLocal]
  · intro q x
    let u : U.toSubmodule := (left_quotient_submodule_equiv_local ρ S U q).symm x
    have hx : (x : W) = ρ q.out u := by
      calc
        (x : W) =
            ((left_quotient_submodule_equiv_local ρ S U q u :
                ρ.leftQuotientSubmodule S U q) : W) := by
              exact congrArg
                (fun y : ρ.leftQuotientSubmodule S U q ↦ (y : W))
                ((left_quotient_submodule_equiv_local ρ S U q).apply_symm_apply x).symm
        _ = ρ q.out u := by simp
    have hq : QuotientGroup.leftRel S ((s • q).out) (s * q.out) := by
      apply Quotient.exact'
      calc
        ((s • q).out : K ⧸ S) = s • q := Quotient.out_eq' (s • q)
        _ = s • (q.out : K ⧸ S) := by
          exact congrArg (fun z : K ⧸ S ↦ s • z) (Quotient.out_eq' q).symm
        _ = (s * q.out : K ⧸ S) := rfl
    rw [QuotientGroup.leftRel_apply] at hq
    let t : S := ⟨((s • q).out)⁻¹ * (s * q.out), hq⟩
    let ut : U.toSubmodule := ⟨ρ t u, U.apply_mem_toSubmodule t u.property⟩
    have hsx : (ρ s x : W) = ρ (s • q).out ut := by
      calc
        ρ s x = ρ s (ρ q.out u) := by rw [hx]
        _ = ρ (s * q.out) u := by
          simp [Module.End.mul_apply, map_mul]
        _ = ρ ((s • q).out * t) u := by
          congr 1
          simp [t]
        _ = ρ (s • q).out (ρ t u) := by
          simp [Module.End.mul_apply, map_mul]
        _ = ρ (s • q).out ut := rfl
    have hsx_mem : ρ s x ∈ ρ.leftQuotientSubmodule S U (s • q) := by
      rw [left_quotient_submodule_out_local ρ S U (s • q)]
      exact Submodule.mem_map.mpr ⟨ut, ut.property, hsx.symm⟩
    have hsymm_smul :
        (left_quotient_submodule_equiv_local ρ S U (s • q)).symm ⟨ρ s x, hsx_mem⟩ = ut := by
      ext
      simp [ut, hsx]
    calc
      extensionLinearMapLocal ρ S U hU ρ' f (ρ s x) =
          left_quotient_submodule_extension_local ρ S U ρ' f (s • q) ⟨ρ s x, hsx_mem⟩ := by
            exact extensionLinearMapLocal_apply_of_mem ρ S U hU ρ' f hsx_mem
      _ = ρ' (s • q).out (f ut) := by
            simp [left_quotient_submodule_extension_local, hsymm_smul, ut]
      _ = ρ' (s * q.out) (f u) := by
            have hut_def : ut = U.toRepresentation t u := by
              ext
              rfl
            have hut : f ut = ρ' t (f u) := by
              rw [hut_def]
              exact Representation.IntertwiningMap.isIntertwining (f := f) (g := t) (v := u)
            rw [hut]
            calc
              ρ' (s • q).out (ρ' t (f u)) = ρ' (((s • q).out : K) * t) (f u) := by
                simp [Module.End.mul_apply, map_mul]
              _ = ρ' (s * q.out) (f u) := by
                congr 1
                simp [t]
      _ = ρ' s (ρ' q.out (f u)) := by
            calc
              ρ' (s * q.out) (f u) = ((ρ' s * ρ' q.out)) (f u) := by
                exact LinearMap.congr_fun (ρ'.map_mul s q.out) (f u)
              _ = ρ' s (ρ' q.out (f u)) := by
                simp [Module.End.mul_apply]
      _ = ρ' s (extensionLinearMapLocal ρ S U hU ρ' f x) := by
            congr 1
            simpa [left_quotient_submodule_extension_local, u] using
              (extensionLinearMapLocal_apply_of_mem ρ S U hU ρ' f (x := x) (q := q) x.property).symm
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for isMonomialCharacter_of_isMonomial: bundle the linear extension as an ambient
equivariant intertwiner. -/
noncomputable abbrev extensionIntertwiningMapLocal
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype)) :
    ρ.IntertwiningMap ρ' :=
  (extensionLinearMapLocal ρ S U hU ρ' f).intertwiningMap_of_isIntertwiningMap
    ρ ρ' (extensionLinearMapLocal_isIntertwining ρ S U hU ρ' f)

/-- Helper for isMonomialCharacter_of_isMonomial: an ambient intertwiner is determined by its
values on the inducing subrepresentation. -/
theorem extensionIntertwiningMapLocal_unique
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype))
    (F : ρ.IntertwiningMap ρ') (hF : ∀ u : U.toSubmodule, F u = f u) :
    F = extensionIntertwiningMapLocal ρ S U hU ρ' f := by
  classical
  apply IntertwiningMap.ext
  ext v
  let ℳ : K ⧸ S → Submodule ℂ W := ρ.leftQuotientSubmodule S U
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  have hInternal : DirectSum.IsInternal ℳ := by
    simpa [ℳ, Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition ℳ hInternal
  refine DirectSum.Decomposition.inductionOn (ℳ := ℳ)
      (motive := fun x : W ↦ F x = extensionIntertwiningMapLocal ρ S U hU ρ' f x)
      ?_ ?_ ?_ v
  · simp [extensionIntertwiningMapLocal, extensionLinearMapLocal]
  · intro q x
    let u : U.toSubmodule := (left_quotient_submodule_equiv_local ρ S U q).symm x
    have hx : (x : W) = ρ q.out u := by
      calc
        (x : W) =
            ((left_quotient_submodule_equiv_local ρ S U q u :
                ρ.leftQuotientSubmodule S U q) : W) := by
              exact congrArg
                (fun y : ρ.leftQuotientSubmodule S U q ↦ (y : W))
                ((left_quotient_submodule_equiv_local ρ S U q).apply_symm_apply x).symm
        _ = ρ q.out u := by simp
    calc
      F x = F (ρ q.out u) := by rw [hx]
      _ = ρ' q.out (F u) := by
            simpa using
              (Representation.IntertwiningMap.isIntertwining (f := F) (g := q.out) (v := u))
      _ = ρ' q.out (f u) := by rw [hF u]
      _ = left_quotient_submodule_extension_local ρ S U ρ' f q x := by
            simp [left_quotient_submodule_extension_local, u]
      _ = extensionIntertwiningMapLocal ρ S U hU ρ' f x := by
            symm
            simpa [extensionIntertwiningMapLocal] using
              extensionLinearMapLocal_apply_of_mem ρ S U hU ρ' f (x := x) (q := q) x.property
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for isMonomialCharacter_of_isMonomial: every subgroup-equivariant map out of the
inducing subrepresentation extends uniquely to the ambient representation. -/
theorem existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype)) :
    ∃! F : ρ.IntertwiningMap ρ', ∀ u : U.toSubmodule, F u = f u := by
  refine ⟨extensionIntertwiningMapLocal ρ S U hU ρ' f, ?_, ?_⟩
  · intro u
    exact extensionLinearMapLocal_extends ρ S U hU ρ' f u
  · intro F hF
    exact extensionIntertwiningMapLocal_unique ρ S U hU ρ' f F hF

/-- Helper for isMonomialCharacter_of_isMonomial: the tautological inclusion of a stable
subrepresentation into the restricted ambient representation. -/
def subrepresentation_inclusion_hom_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype)) :
    U.toRepresentation.IntertwiningMap (ρ.comp S.subtype) :=
  U.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap
    U.toRepresentation (ρ.comp S.subtype) fun _ _ ↦ rfl

/-- Helper for isMonomialCharacter_of_isMonomial: the unit-coset embedding as an intertwiner from
the source representation into the restricted induced representation. -/
noncomputable def induced_identity_copy_hom_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    σ.IntertwiningMap (((Rep.ind S.subtype (Rep.of σ)).ρ).comp S.subtype) :=
  (Representation.IndV.mk S.subtype σ 1).intertwiningMap_of_isIntertwiningMap
    σ (((Rep.ind S.subtype (Rep.of σ)).ρ).comp S.subtype) fun s w ↦ by
      -- The unit-coset generator transforms exactly by the source action.
      change Representation.IndV.mk S.subtype σ 1 (σ s w) =
        ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) s
          (Representation.IndV.mk S.subtype σ 1 w)
      simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for isMonomialCharacter_of_isMonomial: a Chapter `3` inducedness witness identifies a
representation with the standard induced model built from the witnessing subrepresentation. -/
noncomputable def equiv_induced_of_isInducedFromSubrepresentation_local
    {K : Type} [Group K] [Finite K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U) :
    ρ.Equiv ((Rep.ind S.subtype (Rep.of U.toRepresentation)).ρ) := by
  let σind : Representation ℂ K (Representation.IndV S.subtype U.toRepresentation) :=
    (Rep.ind S.subtype (Rep.of U.toRepresentation)).ρ
  let φ : σind.IntertwiningMap ρ := (inducedFromSubrepresentationHom_local ρ S U).hom
  let iotaρ : U.toRepresentation.IntertwiningMap (ρ.comp S.subtype) :=
    subrepresentation_inclusion_hom_local ρ S U
  let iotaind : U.toRepresentation.IntertwiningMap (σind.comp S.subtype) :=
    induced_identity_copy_hom_local S U.toRepresentation
  classical
  let hψexists :=
    (existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation ρ S U hU σind iotaind).exists
  let ψ : ρ.IntertwiningMap σind := Classical.choose hψexists
  have hψ : ∀ u : U.toSubmodule, ψ u = iotaind u := Classical.choose_spec hψexists
  have hright :
      φ.comp ψ = (1 : ρ.IntertwiningMap ρ) := by
    apply (existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation
      ρ S U hU ρ iotaρ).unique
    · intro u
      calc
        (φ.comp ψ) u = φ (ψ u) := rfl
        _ = φ (iotaind u) := by rw [hψ u]
        _ = ρ 1⁻¹ u := by
              simpa [φ, iotaind, induced_identity_copy_hom_local] using
                inducedFromSubrepresentationHom_mk_local ρ S U 1 u
        _ = u := by simp
    · intro u
      rfl
  let Uind : Subrepresentation (σind.comp S.subtype) :=
    induced_identity_copy_subrepresentation_local S U.toRepresentation
  let iotaUind : Uind.toRepresentation.IntertwiningMap (σind.comp S.subtype) :=
    subrepresentation_inclusion_hom_local σind S Uind
  have hUinduced : σind.IsInducedFromSubrepresentation S Uind :=
    induced_identity_copy_is_induced_local S U.toRepresentation
  have hleft :
      ψ.comp φ = (1 : σind.IntertwiningMap σind) := by
    apply (existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation
      σind S Uind hUinduced σind iotaUind).unique
    · intro u
      calc
        (ψ.comp φ) u = ψ (φ u) := rfl
        _ = ψ (ρ 1⁻¹ ((induced_identity_copy_equiv_local S U.toRepresentation).symm u)) := by
              rw [induced_identity_copy_eq_mk_one_symm_local S U.toRepresentation u]
              congr 1
              simpa [φ] using
                inducedFromSubrepresentationHom_mk_local ρ S U 1
                  ((induced_identity_copy_equiv_local S U.toRepresentation).symm u)
        _ = ψ ((induced_identity_copy_equiv_local S U.toRepresentation).symm u) := by simp
        _ = iotaind ((induced_identity_copy_equiv_local S U.toRepresentation).symm u) := by
              rw [hψ ((induced_identity_copy_equiv_local S U.toRepresentation).symm u)]
        _ = u := by
              change Representation.IndV.mk S.subtype U.toRepresentation 1
                    ((induced_identity_copy_equiv_local S U.toRepresentation).symm u) = u
              simpa using
                (induced_identity_copy_eq_mk_one_symm_local S U.toRepresentation u).symm
    · intro u
      rfl
  have hleft_linear : ψ.toLinearMap ∘ₗ φ.toLinearMap = LinearMap.id := by
    simpa using congrArg IntertwiningMap.toLinearMap hleft
  have hright_linear : φ.toLinearMap ∘ₗ ψ.toLinearMap = LinearMap.id := by
    simpa using congrArg IntertwiningMap.toLinearMap hright
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear ψ.toLinearMap φ.toLinearMap hleft_linear hright_linear)
    ψ.isIntertwining'

/-- The character of a monomial finite-dimensional complex representation is a monomial
character. -/
theorem isMonomialCharacter_of_isMonomial
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V} (hρ : Representation.IsMonomial ρ) :
    IsMonomialCharacter ρ.character := by
  rcases hρ with ⟨H, W, hWfinrank, hWinduced⟩
  -- Route correction: the direct Chapter `7` import path conflicts with the local Chapter `3`
  -- owner file, so we rebuild the needed induced-model equivalence locally using the source-faithful
  -- Chapter `3` uniqueness argument.
  let eInd : ρ.Equiv ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ) :=
    equiv_induced_of_isInducedFromSubrepresentation_local ρ H W hWinduced
  -- Once the ambient representation is identified with the standard induced model, the character
  -- argument reduces to the already proved one-dimensional induced case.
  exact isMonomialCharacter_of_equiv_induced_finrank_one H W hWfinrank eInd
end

end Representation
