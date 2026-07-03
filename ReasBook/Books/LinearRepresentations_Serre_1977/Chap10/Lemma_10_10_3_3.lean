import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_4
import LinearRepresentations_Serre_1977.Chap10.Lemma_10_10_3_3.Index
import LinearRepresentations_Serre_1977.Chap10.Lemma_10_10_3_1
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension

-- Declarations for this item will be appended below by the statement pipeline.

open Representation
open scoped Representation SubgroupInduction TensorProduct

noncomputable section

universe u v

section

variable {G : Type u} [Group G]

attribute [local instance] Classical.propDecidable

local notation "C(" x ")" => Subgroup.centralizer ({x} : Set G)

section

variable [Finite G]
variable {p : ℕ} [Fact p.Prime]

variable (x : G) (P : Sylow p C(x))

local notation "H" => associatedPElementarySubgroup p x P

/-- Helper for Lemma 10-10.3-3: the associated subgroup has order `orderOf x * |P|`. -/
lemma associatedPElementarySubgroup_card_eq_orderOf_mul_card_sylow
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x) :
    Nat.card (associatedPElementarySubgroup p x P) = orderOf x * Nat.card P := by
  let H' := associatedPElementarySubgroup p x P
  let C₀ : Subgroup H' := (Subgroup.zpowers x).subgroupOf H'
  let Pimg : Subgroup G := Subgroup.map C(x).subtype (P : Subgroup C(x))
  let P₀ : Subgroup H' := Pimg.subgroupOf H'
  let hdecomp := associatedPElementarySubgroup_decomposition x hx P
  -- The imported decomposition identifies `H` with the product of its cyclic and `p`-group
  -- factors, so the cardinal splits multiplicatively.
  have hcard_prod : Nat.card H' = Nat.card C₀ * Nat.card P₀ := by
    simpa [C₀, P₀, Nat.card_prod] using
      (Nat.card_congr (hdecomp.isComplement.prodMulEquiv hdecomp.commute).toEquiv).symm
  have hcard_cyclic : Nat.card C₀ = orderOf x := by
    have hz : Subgroup.zpowers x ≤ H' := zpowers_le_associatedPElementarySubgroup p x P
    simpa [C₀] using
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz).toEquiv).trans (Nat.card_zpowers x)
  have hcard_image : Nat.card Pimg = Nat.card P := by
    simpa [Pimg] using
      (Subgroup.card_map_of_injective C(x).subtype_injective)
  have hcard_pgroup : Nat.card P₀ = Nat.card P := by
    have hPimg_le : Pimg ≤ H' := le_sup_right
    simpa [P₀] using
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPimg_le).toEquiv).trans hcard_image
  calc
    Nat.card H' = Nat.card C₀ * Nat.card P₀ := hcard_prod
    _ = orderOf x * Nat.card P := by rw [hcard_cyclic, hcard_pgroup]

/-- Helper for Lemma 10-10.3-3: on `p`-regular elements of the associated subgroup, the explicit
auxiliary function is supported only at `x`. -/
lemma brauer_auxiliary_nonzero_on_pregular_iff_eq_x
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x)
    (h : associatedPElementarySubgroup p x P) (hh : IsPRegular p h.1) :
    brauerAssociatedAuxiliaryFunction p x P h ≠ 0 ↔ h.1 = x := by
  constructor
  · intro hne
    -- A nonzero value provides the explicit factorization `h = x * y` with `y ∈ P`.
    rw [brauerAssociatedAuxiliaryFunction] at hne
    split_ifs at hne with hxy
    · rcases hxy with ⟨y, hy⟩
      have hyP : IsPElement p ((C(x)).subtype y : G) := by
        rw [isPElement_iff_exists_pow_eq_one]
        rcases P.isPGroup' y with ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg (fun z : P ↦ ((z : P) : G)) hn⟩
      have hyComm : Commute ((C(x)).subtype y : G) x :=
        Subgroup.mem_centralizer_singleton_iff.mp ((y : C(x)).2)
      have hdecomp : IsPComponentDecomposition p h.1 ((C(x)).subtype y : G) x := by
        refine ⟨hyP, hx, hyComm, ?_⟩
        calc
          ((C(x)).subtype y : G) * x = x * (C(x)).subtype y := hyComm.eq
          _ = h.1 := hy.symm
      -- A `p`-regular element has trivial `p`-unipotent component, so the `P`-factor is `1`.
      have hy_one : ((C(x)).subtype y : G) = 1 := by
        calc
          ((C(x)).subtype y : G) = pUnipotentComponent p h.1 := hdecomp.eq_pUnipotentComponent
          _ = 1 := by
            symm
            have htriv : IsPComponentDecomposition p h.1 1 h.1 := by
              refine ⟨?_, hh, Commute.one_left _, by simp⟩
              exact ⟨0, by simp⟩
            exact htriv.eq_pUnipotentComponent
      calc
        h.1 = x * (C(x)).subtype y := hy
        _ = x := by simp [hy_one]
    · exact False.elim (hne rfl)
  · intro hxh
    -- At the point `x`, the defining witness is the trivial element of the Sylow subgroup.
    have hx_witness : ∃ y : P, x = x * (C(x)).subtype y := by
      refine ⟨1, ?_⟩
      simp
    have horder_ne : (orderOf x : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (orderOf_pos x).ne'
    unfold brauerAssociatedAuxiliaryFunction
    simp [hxh, horder_ne]

/-- Helper for Lemma 10-10.3-3: inducing the explicit auxiliary function back to `G` takes the
value `|C_G(x)| / |P|` at `x`. -/
lemma induced_brauer_auxiliary_value_at_x_eq_centralizer_quotient
    (x : G) (P : Sylow p C(x)) (_hx : IsPRegular p x) :
    Ind[H](brauerAssociatedAuxiliaryFunction p x P) x =
      (Nat.card C(x) / Nat.card P : ℂ) := by
  classical
  have hxH : x ∈ H := by
    exact le_sup_left <| Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have horder_ne : (orderOf x : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (orderOf_pos x).ne'
  have hsummand :
      ∀ s : G,
        (if hsx : s⁻¹ * x * s ∈ H then
          brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩
        else
          0) =
        if s ∈ C(x) then (orderOf x : ℂ) else 0 := by
    intro s
    by_cases hs : s ∈ C(x)
    · have hs_comm : s * x = x * s :=
        Subgroup.mem_centralizer_singleton_iff.mp hs
      have hconj : s⁻¹ * x * s = x := by
        calc
          s⁻¹ * x * s = s⁻¹ * (x * s) := by simp [mul_assoc]
          _ = s⁻¹ * (s * x) := by rw [hs_comm.eq.symm]
          _ = x := by simp [mul_assoc]
      have hsx : s⁻¹ * x * s ∈ H := by
        simpa [hconj] using hxH
      have hsub : (⟨s⁻¹ * x * s, hsx⟩ : H) = ⟨x, hxH⟩ := by
        apply Subtype.ext
        exact hconj
      have hx_witness : ∃ y : P, x = x * (C(x)).subtype y := by
        refine ⟨1, ?_⟩
        simp
      rw [dif_pos hsx, dif_pos hs]
      rw [hsub]
      simp [brauerAssociatedAuxiliaryFunction, hx_witness, horder_ne]
    · by_cases hsx : s⁻¹ * x * s ∈ H
      · have hsx_reg : IsPRegular p (s⁻¹ * x * s) :=
          isPRegular_conj p x s⁻¹ _hx
        have hneq : s⁻¹ * x * s ≠ x := by
          intro hs_eq
          apply hs
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          calc
            s * x = s * (s⁻¹ * x * s) := by rw [hs_eq]
            _ = x * s := by group
        have hzero :
            brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩ = 0 := by
          by_contra hne
          exact hneq <|
            (brauer_auxiliary_nonzero_on_pregular_iff_eq_x x P _hx ⟨s⁻¹ * x * s, hsx⟩ hsx_reg).1 hne
        simp [dif_pos hsx, dif_neg hs, hzero]
      · simp [dif_neg hsx, dif_neg hs]
  have hsum :
      ∑ s : G,
          (if hsx : s⁻¹ * x * s ∈ H then
            brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩
          else
            0) =
        (Nat.card C(x) : ℂ) * (orderOf x : ℂ) := by
    calc
      ∑ s : G,
          (if hsx : s⁻¹ * x * s ∈ H then
            brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩
          else
            0) =
          ∑ s : G, if s ∈ C(x) then (orderOf x : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            exact hsummand s
      _ = (Nat.card C(x) : ℂ) * (orderOf x : ℂ) := by
        simp [Nat.card_eq_fintype_card, mul_comm, mul_left_comm, mul_assoc]
  have hcardH :
      (Nat.card H : ℂ) = (orderOf x : ℂ) * (Nat.card P : ℂ) := by
    norm_num [associatedPElementarySubgroup_card_eq_orderOf_mul_card_sylow x P _hx]
  have hcardH_ne : (Nat.card H : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcardP_ne : (Nat.card P : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  calc
    Ind[H](brauerAssociatedAuxiliaryFunction p x P) x =
        ((Nat.card H : ℂ)⁻¹) *
          ∑ s : G,
            if hsx : s⁻¹ * x * s ∈ H then
              brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩
            else
              0 := by
              simp [Subgroup.inducedClassFunction]
    _ = ((Nat.card H : ℂ)⁻¹) * ((Nat.card C(x) : ℂ) * (orderOf x : ℂ)) := by rw [hsum]
    _ = (Nat.card C(x) / Nat.card P : ℂ) := by
      rw [hcardH]
      field_simp [horder_ne, hcardP_ne]
      ring

-- Proof sketch: use the left-coset induction formula for `Ind_H^G` on the explicit witness. The
-- only nonzero summands at `x` come from elements of the centralizer of `x`, so the induced value
-- is the `p'`-part of `|Z_G(x)|`, which is nonzero modulo `p`.
-- Route correction: once the induction value is rewritten as the centralizer quotient, the
-- nondivisibility statement is pure Sylow-cardinality arithmetic.
/-- For a `p'`-element `x`, the induced value of Brauer's auxiliary function at `x` is nonzero
modulo `p`. -/
theorem brauerAssociatedAuxiliaryFunction_induced_value_at_x_nonzero_mod_p
    (x : G) (P : Sylow p C(x)) (_hx : IsPRegular p x) :
    ∃ n : ℤ,
      Ind[H](brauerAssociatedAuxiliaryFunction p x P) x = (n : ℂ) ∧
        ¬ (p : ℤ) ∣ n := by
  -- Freeze the Sylow-cardinality quotient first, then package the two final clauses with the
  -- standard `ordCompl` witness.
  refine ⟨ordCompl[p] (Nat.card C(x)), ?_, ?_⟩
  · calc
      Ind[H](brauerAssociatedAuxiliaryFunction p x P) x
          = (Nat.card C(x) / Nat.card P : ℂ) :=
        induced_brauer_auxiliary_value_at_x_eq_centralizer_quotient x P _hx
      _ = ((ordCompl[p] (Nat.card C(x)) : ℤ) : ℂ) := by
        rw [Int.cast_natCast, P.card_eq_multiplicity]
  · simpa using
      (Nat.not_dvd_ordCompl (p := p) Fact.out (n := Nat.card C(x)) Nat.card_pos.ne')

/-- Helper for Lemma 10-10.3-3: restate the Brauer induced-value formula at `x` in the explicit
associated-subgroup spelling used by the realization lemmas. -/
lemma induced_brauer_auxiliary_value_at_x_eq_centralizer_quotient_on_associated_subgroup
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x) :
    Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) x =
      (Nat.card C(x) / Nat.card P : ℂ) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hxH : x ∈ associatedPElementarySubgroup p x P := by
    exact zpowers_le_associatedPElementarySubgroup p x P <|
      Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have horder_ne : (orderOf x : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (orderOf_pos x).ne'
  have hsummand :
      ∀ s : G,
        (if hsx : s⁻¹ * x * s ∈ associatedPElementarySubgroup p x P then
          brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩
        else
          0) =
        if s ∈ C(x) then (orderOf x : ℂ) else 0 := by
    intro s
    by_cases hs : s ∈ C(x)
    · have hs_comm : s * x = x * s :=
        Subgroup.mem_centralizer_singleton_iff.mp hs
      have hconj : s⁻¹ * x * s = x := by
        calc
          s⁻¹ * x * s = s⁻¹ * (x * s) := by simp [mul_assoc]
          _ = s⁻¹ * (s * x) := by rw [hs_comm.symm]
          _ = x := by simp
      have hsx : s⁻¹ * x * s ∈ associatedPElementarySubgroup p x P := by
        simpa [hconj] using hxH
      have hsub :
          (⟨s⁻¹ * x * s, hsx⟩ : associatedPElementarySubgroup p x P) = ⟨x, hxH⟩ := by
        apply Subtype.ext
        exact hconj
      have hx_witness : ∃ y : P, x = x * (C(x)).subtype y := by
        refine ⟨1, ?_⟩
        simp
      rw [dif_pos hsx, if_pos hs]
      rw [hsub]
      simp [brauerAssociatedAuxiliaryFunction]
    · by_cases hsx : s⁻¹ * x * s ∈ associatedPElementarySubgroup p x P
      · have hsx_reg : IsPRegular p (s⁻¹ * x * s) := by
          simpa using isPRegular_conj p x s⁻¹ hx
        have hneq : s⁻¹ * x * s ≠ x := by
          intro hs_eq
          apply hs
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          calc
            s * x = s * (s⁻¹ * x * s) := by rw [hs_eq]
            _ = x * s := by group
        have hzero :
            brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩ = 0 := by
          by_contra hne
          exact hneq <|
            (brauer_auxiliary_nonzero_on_pregular_iff_eq_x x P hx ⟨s⁻¹ * x * s, hsx⟩ hsx_reg).1
              hne
        rw [dif_pos hsx, if_neg hs, hzero]
      · rw [dif_neg hsx, if_neg hs]
  have hsum :
      ∑ s : G,
          (if hsx : s⁻¹ * x * s ∈ associatedPElementarySubgroup p x P then
            brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩
          else
            0) =
        (Nat.card C(x) : ℂ) * (orderOf x : ℂ) := by
    have hsum_centralizer :
        ∑ s : G, (if s ∈ C(x) then (orderOf x : ℂ) else 0) =
          (Nat.card C(x) : ℂ) * (orderOf x : ℂ) := by
      have hsum_filtered :
          ∑ s : G, (if s ∈ C(x) then (orderOf x : ℂ) else 0) =
            ((Finset.univ.filter (fun s : G ↦ s ∈ C(x))).card : ℂ) * (orderOf x : ℂ) := by
        simpa [Finset.mem_filter, Finset.sum_const, nsmul_eq_mul] using
          (Fintype.sum_ite_mem
            (s := Finset.univ.filter (fun s : G ↦ s ∈ C(x)))
            (f := fun _ : G ↦ (orderOf x : ℂ)))
      have hcard_filter :
          (Finset.univ.filter (fun s : G ↦ s ∈ C(x))).card = Nat.card C(x) := by
        rw [Nat.card_eq_fintype_card]
        symm
        exact
          Fintype.card_ofFinset
            (s := Finset.univ.filter (fun s : G ↦ s ∈ C(x)))
            (by
              intro s
              simp [Finset.mem_filter])
      calc
        ∑ s : G, (if s ∈ C(x) then (orderOf x : ℂ) else 0) =
            ((Finset.univ.filter (fun s : G ↦ s ∈ C(x))).card : ℂ) * (orderOf x : ℂ) :=
              hsum_filtered
        _ = (Nat.card C(x) : ℂ) * (orderOf x : ℂ) := by
          rw [hcard_filter]
    calc
      ∑ s : G,
          (if hsx : s⁻¹ * x * s ∈ associatedPElementarySubgroup p x P then
            brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩
          else
            0) =
          ∑ s : G, if s ∈ C(x) then (orderOf x : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            exact hsummand s
      _ = (Nat.card C(x) : ℂ) * (orderOf x : ℂ) := hsum_centralizer
  have hcardH :
      (Nat.card (associatedPElementarySubgroup p x P) : ℂ) =
        (orderOf x : ℂ) * (Nat.card P : ℂ) := by
    exact_mod_cast
      associatedPElementarySubgroup_card_eq_orderOf_mul_card_sylow (p := p) x P hx
  have hcardP_ne : (Nat.card P : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  calc
    Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) x =
        ((Nat.card (associatedPElementarySubgroup p x P) : ℂ)⁻¹) *
          ∑ s : G,
            if hsx : s⁻¹ * x * s ∈ associatedPElementarySubgroup p x P then
              brauerAssociatedAuxiliaryFunction p x P ⟨s⁻¹ * x * s, hsx⟩
            else
              0 := by
              simp [Subgroup.inducedClassFunction]
    _ = ((Nat.card (associatedPElementarySubgroup p x P) : ℂ)⁻¹) *
          ((Nat.card C(x) : ℂ) * (orderOf x : ℂ)) := by
            rw [hsum]
    _ = (Nat.card C(x) / Nat.card P : ℂ) := by
      rw [hcardH]
      field_simp [horder_ne, hcardP_ne]

-- Proof sketch: if `s` is `p`-regular and not conjugate to `x`, then every conjugate of `s`
-- landing in the associated subgroup lies in the cyclic factor `⟨x⟩` but is different from `x`,
-- so the explicit witness vanishes on every summand of the induction formula.
-- Route correction: after the support lemma is available, every nonzero summand in the induction
-- formula would force a conjugate of `s` to equal `x`, contradicting `¬ IsConj s x`.
/-- For a `p'`-element `x`, the induced auxiliary function vanishes on `p'`-elements not
conjugate to `x`. -/
theorem brauerAssociatedAuxiliaryFunction_induced_value_eq_zero_of_isPRegular_of_not_isConj
    (x : G) (P : Sylow p C(x)) (_hx : IsPRegular p x) (s : G) (_hs : IsPRegular p s)
    (_hsx : ¬ IsConj s x) :
    Ind[H](brauerAssociatedAuxiliaryFunction p x P) s = (0 : ℂ) := by
  classical
  have hsummand :
      ∀ y : G,
        (if hys : y⁻¹ * s * y ∈ H then
          brauerAssociatedAuxiliaryFunction p x P ⟨y⁻¹ * s * y, hys⟩
        else
          0) = 0 := by
    intro y
    by_cases hys : y⁻¹ * s * y ∈ H
    · have hys_reg : IsPRegular p (y⁻¹ * s * y) := by
        simpa using isPRegular_conj p s y⁻¹ _hs
      have hzero :
          brauerAssociatedAuxiliaryFunction p x P ⟨y⁻¹ * s * y, hys⟩ = 0 := by
        by_contra hne
        have hyx :
            y⁻¹ * s * y = x :=
          (brauer_auxiliary_nonzero_on_pregular_iff_eq_x x P _hx ⟨y⁻¹ * s * y, hys⟩ hys_reg).1 hne
        apply _hsx
        refine isConj_iff.2 ?_
        refine ⟨y⁻¹, ?_⟩
        simpa using hyx
      simp [dif_pos hys, hzero]
    · rw [dif_neg hys]
  simp [Subgroup.inducedClassFunction, hsummand]

/-- Helper for Lemma 10-10.3-3: the auxiliary tensor character exists with the required
induction support when the associated subgroup is written explicitly. -/
lemma exists_tensor_character_realizing_brauerAssociatedAuxiliaryFunction
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x) :
    ∃ ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P),
      (ψ : associatedPElementarySubgroup p x P → ℂ) = brauerAssociatedAuxiliaryFunction p x P := by
  -- Freeze the scalar-extension witness as an actual tensor character before packaging its three
  -- properties.
  exact
    tensorCharacter_exists_of_mem_characterRingScalarExtension_local
      (K := associatedPElementarySubgroup p x P)
      (f := brauerAssociatedAuxiliaryFunction p x P)
      (brauerAssociatedAuxiliaryFunction_mem_characterRingScalarExtension (p := p) x P hx)

/-- Helper for Lemma 10-10.3-3: any realized tensor character inherits the integer-valued clause
from Brauer's explicit auxiliary function. -/
lemma associated_auxiliary_character_integer_clause_of_realization
    (x : G) (P : Sylow p C(x))
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P))
    (hψ : (ψ : associatedPElementarySubgroup p x P → ℂ) =
      brauerAssociatedAuxiliaryFunction p x P) :
    ∀ h : associatedPElementarySubgroup p x P, ∃ n : ℤ, ψ h = (n : ℂ) := by
  intro h
  -- Reuse the integer-valued support lemma for the explicit auxiliary function at this point.
  simpa [hψ] using brauerAssociatedAuxiliaryFunction_integerValued (p := p) (x := x) P h

omit [Fact p.Prime] in
/-- Helper for Lemma 10-10.3-3: any realized tensor character inherits the nonzero induced value
at `x` modulo `p`. -/
lemma associated_auxiliary_character_induced_value_transport
    (x : G) (P : Sylow p C(x))
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P))
    (hψ : (ψ : associatedPElementarySubgroup p x P → ℂ) =
      brauerAssociatedAuxiliaryFunction p x P) :
    Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
        x =
      Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) x := by
  -- Transport the scalar induced value at `x` directly through equality of the underlying class
  -- functions, leaving the induction formula itself opaque.
  simpa using
    congrArg
      (fun φ : associatedPElementarySubgroup p x P → ℂ ↦
        Ind[associatedPElementarySubgroup p x P](φ) x)
      hψ

/-- Helper for Lemma 10-10.3-3: after realizing Brauer's auxiliary function as a tensor
character, the induced value at `x` is still the centralizer quotient. -/
lemma associated_auxiliary_character_induced_value_at_x_eq_centralizer_quotient_of_realization
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x)
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P))
    (hψ : (ψ : associatedPElementarySubgroup p x P → ℂ) =
      brauerAssociatedAuxiliaryFunction p x P) :
    Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
        x =
      (Nat.card C(x) / Nat.card P : ℂ) := by
  -- Route correction: first transport the realized tensor witness back to Brauer's explicit
  -- function, then apply the frozen scalar bridge in the explicit subgroup spelling.
  calc
    Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
        x =
      Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) x := by
        exact associated_auxiliary_character_induced_value_transport (p := p) x P ψ hψ
    _ = (Nat.card C(x) / Nat.card P : ℂ) := by
      exact
        induced_brauer_auxiliary_value_at_x_eq_centralizer_quotient_on_associated_subgroup
          (p := p) x P hx

/-- Helper for Lemma 10-10.3-3: the centralizer quotient at `x` is the prime-to-`p` part of the
centralizer cardinality. -/
lemma associated_auxiliary_character_centralizer_quotient_eq_ord_compl
    (x : G) (P : Sylow p C(x)) :
    Nat.card C(x) / Nat.card P = ordCompl[p] (Nat.card C(x)) := by
  -- This is the standard Sylow-cardinality identity inside the centralizer.
  rw [P.card_eq_multiplicity]

omit [Fact p.Prime] in
/-- Helper for Lemma 10-10.3-3: transporting a verified nonzero-at-`x` witness from Brauer's
explicit auxiliary function to a realized tensor character preserves the same integer witness. -/
lemma associated_auxiliary_character_induced_at_x_clause_transport
    (x : G) (P : Sylow p C(x))
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P))
    (hψ : (ψ : associatedPElementarySubgroup p x P → ℂ) =
      brauerAssociatedAuxiliaryFunction p x P) :
    (∃ n : ℤ,
      Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) x =
        (n : ℂ) ∧
      ¬ (p : ℤ) ∣ n) →
    ∃ n : ℤ,
      Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
          x = (n : ℂ) ∧
        ¬ (p : ℤ) ∣ n := by
  rintro ⟨n, hn, hnp⟩
  -- First transport the induced value along `hψ`, then reuse the same integer witness `n`.
  refine ⟨n, ?_, hnp⟩
  calc
    Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
        x =
      Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) x := by
        exact associated_auxiliary_character_induced_value_transport (p := p) x P ψ hψ
    _ = (n : ℂ) := hn

/-- Helper for Lemma 10-10.3-3: any realized tensor character inherits the nonzero induced value
at `x` modulo `p`. -/
lemma associated_auxiliary_character_induced_at_x_clause_of_realization
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x)
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P))
    (hψ : (ψ : associatedPElementarySubgroup p x P → ℂ) =
      brauerAssociatedAuxiliaryFunction p x P) :
    ∃ n : ℤ,
      Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
          x = (n : ℂ) ∧
        ¬ (p : ℤ) ∣ n := by
  have hexplicit :
      ∃ n : ℤ,
        Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) x =
          (n : ℂ) ∧
        ¬ (p : ℤ) ∣ n := by
    -- Build the explicit witness on Brauer's function from the frozen centralizer quotient, then
    -- let the transport helper move that witness to the realized tensor character.
    refine ⟨Nat.card C(x) / Nat.card P, ?_, ?_⟩
    · -- The scalar induced value has already been computed as the centralizer quotient.
      calc
        Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) x =
          (Nat.card C(x) / Nat.card P : ℂ) := by
            exact
              induced_brauer_auxiliary_value_at_x_eq_centralizer_quotient_on_associated_subgroup
                (p := p) x P hx
        _ = (((Nat.card C(x) / Nat.card P : ℕ) : ℤ) : ℂ) := by
          rw [Int.cast_natCast]
          rw [Nat.cast_div]
          · rw [P.card_eq_multiplicity]
            exact Nat.ordProj_dvd (Nat.card C(x)) p
          · exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    · -- The quotient equals the prime-to-`p` part of `|C_G(x)|`, so it is not divisible by `p`.
      intro hdiv
      have hnat : p ∣ Nat.card C(x) / Nat.card P := Int.natCast_dvd_natCast.mp hdiv
      rw [associated_auxiliary_character_centralizer_quotient_eq_ord_compl (p := p) x P] at hnat
      exact
        (Nat.not_dvd_ordCompl (p := p) Fact.out (n := Nat.card C(x)) Nat.card_pos.ne') hnat
  -- Route correction: once the explicit witness is frozen, move it across the realization
  -- equality instead of redoing the arithmetic inside the tensor-valued proof.
  exact
    associated_auxiliary_character_induced_at_x_clause_transport (p := p) x P ψ hψ hexplicit

omit [Fact p.Prime] in
/-- Helper for Lemma 10-10.3-3: any realized tensor character inherits the vanishing-away-from-
conjugacy clause from Brauer's explicit auxiliary function. -/
lemma associated_auxiliary_character_vanishing_transport
    (x : G) (P : Sylow p C(x))
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P))
    (hψ : (ψ : associatedPElementarySubgroup p x P → ℂ) =
      brauerAssociatedAuxiliaryFunction p x P)
    (s : G) :
    Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
        s =
      Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) s := by
  -- Transport the scalar induced value at the test point `s` through the realization equality.
  simpa using
    congrArg
      (fun φ : associatedPElementarySubgroup p x P → ℂ ↦
        Ind[associatedPElementarySubgroup p x P](φ) s)
      hψ

/-- Helper for Lemma 10-10.3-3: any realized tensor character inherits the vanishing-away-from-
conjugacy clause from Brauer's explicit auxiliary function. -/
lemma associated_auxiliary_character_vanishing_clause_of_realization
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x)
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P))
    (hψ : (ψ : associatedPElementarySubgroup p x P → ℂ) =
      brauerAssociatedAuxiliaryFunction p x P) :
    ∀ s : G, IsPRegular p s → ¬ IsConj s x →
      Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
        s = 0 := by
  intro s hs hsx
  have hzero :
      Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) s = 0 := by
    classical
    have hsummand :
        ∀ y : G,
          (if hys : y⁻¹ * s * y ∈ associatedPElementarySubgroup p x P then
            brauerAssociatedAuxiliaryFunction p x P ⟨y⁻¹ * s * y, hys⟩
          else
            0) = 0 := by
      intro y
      by_cases hys : y⁻¹ * s * y ∈ associatedPElementarySubgroup p x P
      · have hys_reg : IsPRegular p (y⁻¹ * s * y) := by
          simpa using isPRegular_conj p s y⁻¹ hs
        have hvalue_zero :
            brauerAssociatedAuxiliaryFunction p x P ⟨y⁻¹ * s * y, hys⟩ = 0 := by
          by_contra hne
          have hyx :
              y⁻¹ * s * y = x :=
            (brauer_auxiliary_nonzero_on_pregular_iff_eq_x (p := p) x P hx
              ⟨y⁻¹ * s * y, hys⟩ hys_reg).1 hne
          apply hsx
          refine isConj_iff.2 ?_
          refine ⟨y⁻¹, ?_⟩
          simpa using hyx
        simp [dif_pos hys, hvalue_zero]
      · rw [dif_neg hys]
    -- Once every summand of the induction formula vanishes, the induced value is zero.
    simp [Subgroup.inducedClassFunction, hsummand]
  -- Rewrite only the scalar induced value at `s`, then invoke the explicit support-vanishing
  -- computation already frozen in `hzero`.
  calc
    Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
        s =
      Ind[associatedPElementarySubgroup p x P](brauerAssociatedAuxiliaryFunction p x P) s := by
        exact associated_auxiliary_character_vanishing_transport (p := p) x P ψ hψ s
    _ = 0 := hzero

/-- Helper for Lemma 10-10.3-3: once a tensor character realizes Brauer's explicit auxiliary
function, the integer-valued, nonzero-at-`x`, and vanishing-away-from-conjugacy clauses all follow
at once. -/
lemma associated_auxiliary_character_support_clauses_of_realization
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x)
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P))
    (hψ : (ψ : associatedPElementarySubgroup p x P → ℂ) =
      brauerAssociatedAuxiliaryFunction p x P) :
    (∀ h : associatedPElementarySubgroup p x P, ∃ n : ℤ, ψ h = (n : ℂ)) ∧
      (∃ n : ℤ,
        Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
            x = (n : ℂ) ∧
          ¬ (p : ℤ) ∣ n) ∧
      ∀ s : G, IsPRegular p s → ¬ IsConj s x →
        Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
          s = 0 := by
  -- Apply the three clause-specific realization lemmas without reopening the Brauer computations.
  have h_int :
      ∀ h : associatedPElementarySubgroup p x P, ∃ n : ℤ, ψ h = (n : ℂ) :=
    associated_auxiliary_character_integer_clause_of_realization
      (p := p) x P ψ hψ
  have h_at_x :
      ∃ n : ℤ,
        Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
            x = (n : ℂ) ∧
          ¬ (p : ℤ) ∣ n :=
    associated_auxiliary_character_induced_at_x_clause_of_realization
      (p := p) x P hx ψ hψ
  have h_vanish :
      ∀ s : G, IsPRegular p s → ¬ IsConj s x →
        Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
          s = 0 :=
    associated_auxiliary_character_vanishing_clause_of_realization
      (p := p) x P hx ψ hψ
  -- Package the three transported clauses so the existential theorem below only has witness
  -- assembly left to do.
  exact And.intro h_int <| And.intro h_at_x h_vanish

/-- Helper for Lemma 10-10.3-3: the auxiliary tensor character exists with the required
induction support when the associated subgroup is written explicitly. -/
theorem exists_associated_auxiliary_character_with_brauer_induction_support_explicit
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x) :
    ∃ ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P),
      (∀ h : associatedPElementarySubgroup p x P, ∃ n : ℤ, ψ h = (n : ℂ)) ∧
        (∃ n : ℤ,
          Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
              x = (n : ℂ) ∧
            ¬ (p : ℤ) ∣ n) ∧
        ∀ s : G, IsPRegular p s → ¬ IsConj s x →
          Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
            s = 0 := by
  -- Route correction: realize the tensor witness once, then transport each clause separately so
  -- Lean never rewrites the whole nested existential-and-conjunction package in one step.
  obtain ⟨ψ, hψ⟩ :=
    exists_tensor_character_realizing_brauerAssociatedAuxiliaryFunction
      (p := p) x P hx
  -- The new packaging helper leaves only the existential witness assembly in this theorem.
  have h_support :
      (∀ h : associatedPElementarySubgroup p x P, ∃ n : ℤ, ψ h = (n : ℂ)) ∧
        (∃ n : ℤ,
          Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
              x = (n : ℂ) ∧
            ¬ (p : ℤ) ∣ n) ∧
        ∀ s : G, IsPRegular p s → ¬ IsConj s x →
          Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
            s = 0 :=
    associated_auxiliary_character_support_clauses_of_realization
      (p := p) x P hx ψ hψ
  exact ⟨ψ, h_support⟩

/-- The source-faithful public form of Lemma 10-10.3-3 uses the algebraic-integer owner
`A ⊗ R(H)`, not the stronger integral owner `R(H)`. -/
theorem exists_associated_auxiliary_character_with_brauer_induction_support
    (P : Sylow p C(x)) (hx : IsPRegular p x) :
    ∃ ψ : (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P),
      (∀ h : associatedPElementarySubgroup p x P, ∃ n : ℤ, ψ h = (n : ℂ)) ∧
        (∃ n : ℤ,
          Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
              x = (n : ℂ) ∧
            ¬ (p : ℤ) ∣ n) ∧
        ∀ s : G, IsPRegular p s → ¬ IsConj s x →
          Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ))
              s = 0 := by
  -- Route correction: bind `P` explicitly so the public wrapper keeps the intended Sylow
  -- parameter instead of elaborating a hidden unresolved `P`.
  -- The public theorem is then exactly the already-verified explicit subgroup theorem.
  simpa using
    exists_associated_auxiliary_character_with_brauer_induction_support_explicit
      (p := p) x P hx

end

end

end
