import Mathlib
import Mathlib.Data.ZMod.QuotientRing

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_10_3_3 (from Chap10) -/
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

/-! ### Exercise_10_10_5_5 (from Chap10) -/
noncomputable section

universe u

open scoped Representation SubgroupInduction

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Exercise 10-10.5-5: evaluating the pulled-back quotient linear-character sum at
`g` is the same as evaluating the original quotient characters at the quotient class `gH`. -/
private theorem quotient_linearCharacter_sum_apply_eq_sum_values
    (H : Subgroup G) [H.Normal] [CommGroup (G ⧸ H)]
    [Fintype ((G ⧸ H) →* ℂˣ)] (g : G) :
    (((∑ χ : (G ⧸ H) →* ℂˣ, (χ.comp (QuotientGroup.mk' H)).toCharacterRing : R(G)) : G → ℂ) g) =
      ∑ χ : (G ⧸ H) →* ℂˣ, (χ (QuotientGroup.mk' H g) : ℂ) := by
  -- Evaluate the finite sum termwise; each pulled-back quotient character at `g` is just the
  -- original quotient character evaluated at the class `gH`.
  simp [Finset.sum_apply]

/-- Exercise 10-10.5-5: if `H` is normal with abelian quotient, the induced trivial
character is exactly the sum of the quotient degree-`1` characters pulled back to `G`. The
commutativity hypothesis is stated for the canonical quotient multiplication used by
`QuotientGroup.mk' H`. -/
theorem induced_trivial_eq_sum_quotient_linearCharacters
    (H : Subgroup G) [H.Normal]
    (hcomm : ∀ a b : G ⧸ H, a * b = b * a)
    [Fintype ((G ⧸ H) →* ℂˣ)] :
    Subgroup.characterRingInduction H (1 : R(H)) =
      ∑ χ : (G ⧸ H) →* ℂˣ, (χ.comp (QuotientGroup.mk' H)).toCharacterRing := by
  -- Route correction: use the support theorem with the exact canonical quotient-commutativity
  -- witness it consumes, instead of trying to transport a theorem-local `CommGroup` owner.
  exact induced_trivial_eq_sum_quotient_linearCharacters_of_mul_comm (H := H) hcomm

/-- Helper for Exercise 10-10.5-5: the trivial character belongs to the supremum of Brauer's
`p`-elementary induction submodules. -/
private theorem one_mem_iSup_pElementaryInducedCharacterSpan_local :
    (1 : R(G)) ∈ (⨆ p : Nat.Primes, Representation.pElementaryInducedCharacterSpan p G) := by
  -- Route correction: after switching the theorem-local prelude back to the canonical Brauer
  -- owner, Brauer's theorem applies directly to the trivial character.
  simpa using
    (character_mem_iSup_pElementaryInducedCharacterSpan
      (G := G) (χ := (1 : R(G))))

/-- Helper for Exercise 10-10.5-5: subtracting the index copy of the trivial character rewrites
the induced trivial character as a sum of quotient linear-character differences. -/
theorem induced_trivial_sub_index_smul_one_eq_sum_quotient_linearCharacter_differences
    (H : Subgroup G) [H.Normal]
    (hcomm : ∀ a b : G ⧸ H, a * b = b * a)
    [Fintype ((G ⧸ H) →* ℂˣ)] :
    Subgroup.characterRingInduction H (1 : R(H)) - (H.index : ℤ) • (1 : R(G)) =
      ∑ χ : (G ⧸ H) →* ℂˣ, ((χ.comp (QuotientGroup.mk' H)).toCharacterRing - 1) := by
  have hcard :
      H.index = Fintype.card ((G ⧸ H) →* ℂˣ) := by
    have hcard_complex :
        (H.index : ℂ) = Fintype.card ((G ⧸ H) →* ℂˣ) := by
      have hpoint :
          (((Subgroup.characterRingInduction H (1 : R(H)) : R(G)) : G → ℂ) 1) =
            (((∑ χ : (G ⧸ H) →* ℂˣ,
                (χ.comp (QuotientGroup.mk' H)).toCharacterRing : R(G)) : G → ℂ) 1) := by
        exact congrArg (fun ψ : R(G) ↦ ((ψ : G → ℂ) 1))
          (induced_trivial_eq_sum_quotient_linearCharacters H hcomm)
      -- Evaluate the packaged quotient-character identity at the identity to read off the count of
      -- quotient linear characters.
      simpa [Subgroup.characterRingInduction_apply,
        Subgroup.inducedClassFunction_one_eq_index_mul_value, MonoidHom.toCharacterRing_apply]
        using hpoint
    exact_mod_cast hcard_complex
  have hone_sum :
      (H.index : ℤ) • (1 : R(G)) =
        ∑ χ : (G ⧸ H) →* ℂˣ, (1 : R(G)) := by
    -- Rewrite the index multiple of the trivial character as a finite sum of identical summands.
    have hone_card :
        (Fintype.card ((G ⧸ H) →* ℂˣ) : ℤ) • (1 : R(G)) =
          ∑ χ : (G ⧸ H) →* ℂˣ, (1 : R(G)) := by
      simp
    rw [hcard]
    exact hone_card
  -- After expanding `Ind_H^G(1)` as the quotient-character sum, subtract the matching number of
  -- trivial summands and combine the subtraction termwise.
  calc
    Subgroup.characterRingInduction H (1 : R(H)) - (H.index : ℤ) • (1 : R(G)) =
        (∑ χ : (G ⧸ H) →* ℂˣ, (χ.comp (QuotientGroup.mk' H)).toCharacterRing) -
          ∑ χ : (G ⧸ H) →* ℂˣ, (1 : R(G)) := by
            rw [induced_trivial_eq_sum_quotient_linearCharacters H hcomm, hone_sum]
    _ = ∑ χ : (G ⧸ H) →* ℂˣ, ((χ.comp (QuotientGroup.mk' H)).toCharacterRing - 1) := by
      rw [Finset.sum_sub_distrib]

namespace Subgroup

/-- Helper for Exercise 10-10.5-5: if `M` is a coatom of an elementary finite group, then
`Ind_M^G(1_M)` already belongs to LinearRepresentations_Serre_1977's subgroup `R'(G)`. -/
theorem induced_trivial_mem_elementaryLinearCharacterSpan_of_isCoatom_of_isElementary
    (M : Subgroup G) (hM : IsCoatom M) (hG : IsElementary G) :
    Subgroup.characterRingInduction M (1 : R(M)) ∈ R'(G) := by
  -- Route correction: instead of trying to package the whole quotient character sum abstractly,
  -- use the coatom quotient and place each linear-character difference term directly in `R₀'(G)`
  -- via the ambient elementary-group generator `E = ⊤`.
  letI : Group.IsNilpotent G := by
    rcases hG with ⟨p, hp⟩
    exact IsPElementary.isNilpotent hp
  letI : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom
      (G := G) (H := M) (normalizerCondition_of_isNilpotent (G := G)) hM
  letI : IsSimpleGroup (G ⧸ M) :=
    isSimpleGroup_quotient_of_isCoatom (G := G) M hM
  let hcomm : ∀ a b : G ⧸ M, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  letI : CommGroup (G ⧸ M) :=
    { QuotientGroup.Quotient.group M with
      mul_comm := hcomm }
  letI : Fintype ((G ⧸ M) →* ℂˣ) := linearCharacterFintype
  have hdiff :
      Subgroup.characterRingInduction M (1 : R(M)) - (M.index : ℤ) • (1 : R(G)) ∈ R₀'(G) := by
    rw [induced_trivial_sub_index_smul_one_eq_sum_quotient_linearCharacter_differences
      (H := M) hcomm]
    refine Submodule.sum_mem _ ?_
    intro χ hχ
    exact
      linearCharacter_difference_mem_elementaryLinearCharacterAugmentationSpan_of_isElementary
        (G := G) hG (χ.comp (QuotientGroup.mk' M))
  have hone :
      (M.index : ℤ) • (1 : R(G)) ∈ Submodule.span ℤ ({1} : Set (R(G))) := by
    exact Submodule.smul_mem _ (M.index : ℤ) (Submodule.subset_span (by simp))
  have hone' : (M.index : ℤ) • (1 : R(G)) ∈ R'(G) := by
    rw [elementaryLinearCharacterSpan]
    exact
      (le_sup_left :
        Submodule.span ℤ ({1} : Set (R(G))) ≤
          Submodule.span ℤ ({1} : Set (R(G))) ⊔ R₀'(G)) hone
  have hdiff' :
      Subgroup.characterRingInduction M (1 : R(M)) - (M.index : ℤ) • (1 : R(G)) ∈ R'(G) := by
    rw [elementaryLinearCharacterSpan]
    exact
      (le_sup_right :
        R₀'(G) ≤ Submodule.span ℤ ({1} : Set (R(G))) ⊔ R₀'(G)) hdiff
  have hsplit :
      Subgroup.characterRingInduction M (1 : R(M)) =
        (M.index : ℤ) • (1 : R(G)) +
          (Subgroup.characterRingInduction M (1 : R(M)) - (M.index : ℤ) • (1 : R(G))) := by
    abel
  rw [hsplit]
  exact Submodule.add_mem _ hone' hdiff'

/-- Helper for Exercise 10-10.5-5: induction from a coatom of an elementary finite group maps
LinearRepresentations_Serre_1977's subgroup `R'(M)` into the ambient subgroup `R'(G)`. -/
theorem map_elementaryLinearCharacterSpan_of_isCoatom_of_isElementary
    (M : Subgroup G) (hM : IsCoatom M) (hG : IsElementary G) :
    Submodule.map (Subgroup.characterRingInduction M) (R'(M)) ≤ R'(G) := by
  letI : Group.IsNilpotent G := by
    rcases hG with ⟨p, hp⟩
    exact IsPElementary.isNilpotent hp
  letI : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom
      (G := G) (H := M) (normalizerCondition_of_isNilpotent (G := G)) hM
  letI : IsSimpleGroup (G ⧸ M) :=
    isSimpleGroup_quotient_of_isCoatom (G := G) M hM
  let hcomm : ∀ a b : G ⧸ M, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  letI : CommGroup (G ⧸ M) :=
    { QuotientGroup.Quotient.group M with
      mul_comm := hcomm }
  letI : Fintype ((G ⧸ M) →* ℂˣ) := linearCharacterFintype
  -- Split `R'(M)` into the trivial line and the augmentation subgroup. The coatom theorem handles
  -- the trivial generator, and part (a) handles the augmentation summand.
  rw [elementaryLinearCharacterSpan, Submodule.map_sup]
  refine sup_le ?_ ?_
  · rw [Submodule.map_span_le]
    intro χ hχ
    simp only [Set.mem_singleton_iff] at hχ
    subst hχ
    exact induced_trivial_mem_elementaryLinearCharacterSpan_of_isCoatom_of_isElementary M hM hG
  · exact le_trans (map_elementaryLinearCharacterAugmentationSpan M) le_sup_right

end Subgroup

namespace Subgroup

/-- Helper for Exercise 10-10.5-5: in an elementary ambient group, induction of the trivial
character from any subgroup already lies in LinearRepresentations_Serre_1977's subgroup `R'(G)`. -/
theorem induced_trivial_mem_elementaryLinearCharacterSpan_of_subgroup_of_isElementary
    (H : Subgroup G) (hG : IsElementary G) :
    Subgroup.characterRingInduction H (1 : R(H)) ∈ R'(G) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ {A : Type} [Group A] [Finite A], Nat.card A = n →
      ∀ K : Subgroup A, IsElementary A →
        Subgroup.characterRingInduction K (1 : R(K)) ∈ R'(A)
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on (p := P) n ?_
    intro n ih A _ _ hcard K hA
    obtain rfl | ⟨M, hM, hKM⟩ := eq_top_or_exists_le_coatom K
    · -- At the top subgroup, induction of the trivial character is the trivial ambient character.
      have htop :
          Subgroup.characterRingInduction (⊤ : Subgroup A) (1 : R((⊤ : Subgroup A))) =
            (1 : R(A)) := by
        -- Rewrite the source `1` as the trivial degree-`1` character and induce from `⊤`.
        calc
          Subgroup.characterRingInduction (⊤ : Subgroup A) (1 : R((⊤ : Subgroup A))) =
              Subgroup.characterRingInduction (⊤ : Subgroup A)
                (((1 : (⊤ : Subgroup A) →* ℂˣ).toCharacterRing) : R((⊤ : Subgroup A))) := by
                  rw [Subgroup.toCharacterRing_one]
          _ = ((1 : A →* ℂˣ).toCharacterRing : R(A)) := by
                simpa using characterRingInduction_top_toCharacterRing (G := A) (β := (1 : A →* ℂˣ))
          _ = (1 : R(A)) := by
                ext a
                simp
      rw [htop, elementaryLinearCharacterSpan]
      exact
        (le_sup_left :
          Submodule.span ℤ ({1} : Set (R(A))) ≤
            Submodule.span ℤ ({1} : Set (R(A))) ⊔ R₀'(A))
          (Submodule.subset_span (by simp))
    · -- Move to a coatom `M` above `K`, recurse inside `M`, then induce once more to `A`.
      have hM_elem : IsElementary M := Subgroup.isElementary_of_isElementary M hA
      have hsubset : (M : Set A) ⊂ Set.univ := by
        refine ⟨by intro x hx; simp, ?_⟩
        intro htop
        exact hM.1 <| eq_top_iff.2 (by
          intro x hx
          exact htop (show x ∈ (Set.univ : Set A) by simp))
      have hcardM_lt : Nat.card M < n := by
        calc
          Nat.card M < Nat.card A := by
            simpa using (Set.toFinite (Set.univ : Set A)).card_lt_card hsubset
          _ = n := hcard
      have hIH :
          Subgroup.characterRingInduction (K.subgroupOf M) (1 : R(K.subgroupOf M)) ∈ R'(M) :=
        ih (Nat.card M) hcardM_lt rfl (K.subgroupOf M) hM_elem
      have hmap :
          Submodule.map (Subgroup.characterRingInduction M) (R'(M)) ≤ R'(A) :=
        Subgroup.map_elementaryLinearCharacterSpan_of_isCoatom_of_isElementary
          (G := A) M hM hA
      have hmem :
          Subgroup.characterRingInduction M
              (Subgroup.characterRingInduction (K.subgroupOf M) (1 : R(K.subgroupOf M))) ∈
            Submodule.map (Subgroup.characterRingInduction M) (R'(M)) := by
        exact ⟨Subgroup.characterRingInduction (K.subgroupOf M) (1 : R(K.subgroupOf M)), hIH, rfl⟩
      have hmem' :
          Subgroup.characterRingInduction M
              (Subgroup.characterRingInduction (K.subgroupOf M) (1 : R(K.subgroupOf M))) ∈
            R'(A) :=
        hmap hmem
      have hmap_eq : (K.subgroupOf M).map M.subtype = K := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hKM hx⟩, hx, rfl⟩
      have hstages :
          Subgroup.characterRingInduction M
              (Subgroup.characterRingInduction (K.subgroupOf M) (1 : R(K.subgroupOf M))) =
            Subgroup.characterRingInduction K (1 : R(K)) := by
        -- Specialize the subgroup-chain induction theorem to the trivial degree-`1` character.
        calc
          Subgroup.characterRingInduction M
              (Subgroup.characterRingInduction (K.subgroupOf M) (1 : R(K.subgroupOf M))) =
            Subgroup.characterRingInduction M
              (Subgroup.characterRingInduction (K.subgroupOf M)
                ((1 : (K.subgroupOf M) →* ℂˣ).toCharacterRing)) := by
                  rw [Subgroup.toCharacterRing_one]
          _ = Subgroup.characterRingInduction ((K.subgroupOf M).map M.subtype)
                ((mappedLinearCharacter M (K.subgroupOf M)
                  (1 : (K.subgroupOf M) →* ℂˣ)).toCharacterRing) := by
                  simpa using
                    characterRingInduction_induced_linearCharacter_subgroup_chain
                      (G := A) M (K.subgroupOf M) (1 : (K.subgroupOf M) →* ℂˣ)
          _ = Subgroup.characterRingInduction ((K.subgroupOf M).map M.subtype)
                ((1 : ((K.subgroupOf M).map M.subtype) →* ℂˣ).toCharacterRing) := by
                  rw [mappedLinearCharacter_one]
          _ = Subgroup.characterRingInduction ((K.subgroupOf M).map M.subtype)
                (1 : R(((K.subgroupOf M).map M.subtype))) := by
                  rw [Subgroup.toCharacterRing_one]
          _ = Subgroup.characterRingInduction K (1 : R(K)) := by
                  rw [hmap_eq]
      simpa [hstages] using hmem'
  exact hP (Nat.card G) rfl H hG

end Subgroup


/-- Helper for Exercise 10-10.5-5: inducing a degree-`1` subgroup character of an elementary
group lands in LinearRepresentations_Serre_1977's subgroup `R'(G)`. -/
private theorem
    induced_linearCharacter_mem_elementaryLinearCharacterSpan_of_subgroup_of_isElementary
    (H : Subgroup G) (α : H →* ℂˣ) (hG : IsElementary G) :
    Subgroup.characterRingInduction H α.toCharacterRing ∈ R'(G) := by
  have htriv :
      Subgroup.characterRingInduction H (1 : R(H)) ∈ R'(G) :=
    Subgroup.induced_trivial_mem_elementaryLinearCharacterSpan_of_subgroup_of_isElementary H hG
  have hH : IsElementary H := Subgroup.isElementary_of_isElementary H hG
  have haugH :
      (α.toCharacterRing - 1 : R(H)) ∈ R₀'(H) :=
    linearCharacter_difference_mem_elementaryLinearCharacterAugmentationSpan_of_isElementary
      (G := H) hH α
  have haug_map :
      Subgroup.characterRingInduction H (α.toCharacterRing - 1) ∈
        Submodule.map (Subgroup.characterRingInduction H) (R₀'(H)) := by
    -- Package the subgroup augmentation piece as an element of the mapped submodule.
    exact ⟨α.toCharacterRing - 1, haugH, rfl⟩
  have haugG₀ :
      Subgroup.characterRingInduction H (α.toCharacterRing - 1) ∈ R₀'(G) :=
    Subgroup.map_elementaryLinearCharacterAugmentationSpan H haug_map
  have haugG :
      Subgroup.characterRingInduction H (α.toCharacterRing - 1) ∈ R'(G) := by
    -- The augmentation subgroup sits inside `R'(G)` as the right summand.
    rw [elementaryLinearCharacterSpan]
    exact
      (le_sup_right :
        R₀'(G) ≤ Submodule.span ℤ ({1} : Set (R(G))) ⊔ R₀'(G)) haugG₀
  have hsum :
      Subgroup.characterRingInduction H (1 : R(H)) +
          Subgroup.characterRingInduction H (α.toCharacterRing - 1) ∈
        R'(G) :=
    Submodule.add_mem _ htriv haugG
  have hsplit : (1 : R(H)) + (α.toCharacterRing - 1) = α.toCharacterRing := by
    -- Split the subgroup linear character into its trivial and augmentation parts.
    abel
  have hrewrite :
      Subgroup.characterRingInduction H α.toCharacterRing =
        Subgroup.characterRingInduction H (1 : R(H)) +
          Subgroup.characterRingInduction H (α.toCharacterRing - 1) := by
    -- The induction map is additive, so the subgroup splitting transports to `R(G)`.
    calc
      Subgroup.characterRingInduction H α.toCharacterRing =
          Subgroup.characterRingInduction H ((1 : R(H)) + (α.toCharacterRing - 1)) := by
            rw [hsplit]
      _ = Subgroup.characterRingInduction H (1 : R(H)) +
            Subgroup.characterRingInduction H (α.toCharacterRing - 1) := by
            rw [(Subgroup.characterRingInduction H).map_add]
  -- Rewrite the induced class as the sum of the trivial induced character and the induced
  -- augmentation piece.
  exact hrewrite ▸ hsum

/-- Helper for Exercise 10-10.5-5: the character of an irreducible finite-dimensional complex
representation of an elementary group belongs to LinearRepresentations_Serre_1977's subgroup `R'(G)`. -/
lemma irreducible_fdRepCharacterRing_mem_elementaryLinearCharacterSpan_of_isElementary
    (V : FDRep ℂ G) [CategoryTheory.Simple V] (hG : IsElementary G) :
    fdRepCharacterRing V ∈ R'(G) := by
  -- Route correction: follow LinearRepresentations_Serre_1977's source path directly inside this file:
  -- elementary => supersolvable => monomial => induced linear character => `R'(G)`.
  have hsup : IsSupersolvable G := elementary_group_isSupersolvable hG
  letI : IsSupersolvable G := hsup
  letI : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
  have hmono : Representation.IsMonomial V.ρ :=
    Representation.isMonomial_of_irreducible_of_supersolvable V.ρ
  obtain ⟨H, α, hchar⟩ := fdRepCharacterRing_eq_characterRingInduction_of_isMonomial V hmono
  -- Once the irreducible character is written as an induced linear character, the previously
  -- established `R'(G)` decomposition closes the argument.
  rw [hchar]
  exact
    induced_linearCharacter_mem_elementaryLinearCharacterSpan_of_subgroup_of_isElementary
      H α hG

/-- Helper for Exercise 10-10.5-5: every honest finite-dimensional character of an elementary
group belongs to LinearRepresentations_Serre_1977's subgroup `R'(G)`. -/
lemma fdRepCharacterRing_mem_elementaryLinearCharacterSpan_of_isElementary
    (V : FDRep ℂ G) (hG : IsElementary G) :
    fdRepCharacterRing V ∈ R'(G) := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation V.ρ),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i, (σ i).toRepresentation.IsIrreducible :=
    exists_isInternal_irreducible_subrepresentations (ρ := V.ρ)
  let hinternal : DirectSum.IsInternal (fun i : κ ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  have hchar :
      V.character = ∑ i : κ, ((σ i).toRepresentation).character := by
    -- Decompose the trace of `V g` along the internal direct sum of irreducible summands.
    ext g
    simpa [Representation.character] using
      (LinearMap.trace_eq_sum_trace_restrict
        (R := ℂ) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
        (f := V.ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))
  have hring :
      fdRepCharacterRing V = ∑ i : κ, fdRepCharacterRing (FDRep.of (σ i).toRepresentation) := by
    -- Bundle the character decomposition inside LinearRepresentations_Serre_1977's character ring.
    apply Subtype.ext
    ext g
    simpa [fdRepCharacterRing] using congrFun hchar g
  rw [hring]
  refine Submodule.sum_mem _ ?_
  intro i hi
  let τ : FDRep ℂ G := FDRep.of (σ i).toRepresentation
  letI : Representation.IsIrreducible τ.ρ := by
    simpa [τ] using hσ_irr i
  letI : CategoryTheory.Simple τ := FDRep.simple_of_isIrreducible τ
  simpa [τ] using
    irreducible_fdRepCharacterRing_mem_elementaryLinearCharacterSpan_of_isElementary τ hG

/-- Helper for Exercise 10-10.5-5: the span of honest finite-dimensional characters is all of
LinearRepresentations_Serre_1977's character ring `R(G)`. -/
theorem rep_character_span_eq_top_local :
    Submodule.span ℤ {χ : R(G) | ∃ V : FDRep ℂ G, fdRepCharacterRing V = χ} = ⊤ := by
  let S : Set (R(G)) := {χ : R(G) | ∃ V : FDRep ℂ G, fdRepCharacterRing V = χ}
  have hmul_span :
      ∀ {χ ψ : R(G)},
        χ ∈ Submodule.span ℤ S →
        ψ ∈ Submodule.span ℤ S →
        χ * ψ ∈ Submodule.span ℤ S := by
    intro χ ψ hχ hψ
    have hχ_mul : ∀ ψ : R(G), ψ ∈ Submodule.span ℤ S → χ * ψ ∈ Submodule.span ℤ S := by
      induction hχ using Submodule.span_induction with
      | mem η hη =>
          rcases hη with ⟨V, rfl⟩
          intro ψ hψ
          induction hψ using Submodule.span_induction with
          | mem ξ hξ =>
              rcases hξ with ⟨W, rfl⟩
              refine Submodule.subset_span ?_
              refine ⟨CategoryTheory.MonoidalCategoryStruct.tensorObj V W, ?_⟩
              exact fdRepCharacterRing_tensor_eq_mul V W
          | zero =>
              rw [mul_zero]
              exact Submodule.zero_mem (Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using
                Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro ψ hψ
          rw [zero_mul]
          exact Submodule.zero_mem (Submodule.span ℤ S)
      | add χ₁ χ₂ _ _ hχ₁ hχ₂ =>
          intro ψ hψ
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hχ₁ ψ hψ) (hχ₂ ψ hψ)
      | smul n χ' _ hχ' =>
          intro ψ hψ
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hχ' ψ hψ)
    exact hχ_mul ψ hψ
  -- The ring `R(G)` is generated by irreducible characters, and honest characters are stable
  -- under the ring operations through the trivial representation and tensor products.
  refine top_unique ?_
  intro χ _
  have hspan_of_mem :
      ∀ (f : G → ℂ) (hf : f ∈ R(G)),
        (⟨f, hf⟩ : R(G)) ∈ Submodule.span ℤ S := by
    intro f hf
    refine
      Algebra.adjoin_induction
        (p := fun f hf ↦ (⟨f, hf⟩ : R(G)) ∈ Submodule.span ℤ S)
        ?_ ?_ ?_ ?_ hf
    · intro ψ hψ
      rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
      letI : FiniteDimensional ℂ ρ := hρfd
      change fdRepCharacterRing (FDRep.of ρ.ρ) ∈ Submodule.span ℤ S
      exact Submodule.subset_span ⟨FDRep.of ρ.ρ, rfl⟩
    · intro n
      change (algebraMap ℤ (R(G)) n) ∈ Submodule.span ℤ S
      rw [show algebraMap ℤ (R(G)) n =
          n • fdRepCharacterRing (FDRep.of (Representation.trivial ℂ G ℂ)) by
        rw [fdRepCharacterRing_trivial_eq_one]
        simp]
      exact Submodule.smul_mem (Submodule.span ℤ S) n <|
        Submodule.subset_span ⟨FDRep.of (Representation.trivial ℂ G ℂ), rfl⟩
    · intro f g hf hg hfspan hgspan
      change (⟨f, hf⟩ : R(G)) + ⟨g, hg⟩ ∈ Submodule.span ℤ S
      exact Submodule.add_mem (Submodule.span ℤ S) hfspan hgspan
    · intro f g hf hg hfspan hgspan
      change (⟨f, hf⟩ : R(G)) * ⟨g, hg⟩ ∈ Submodule.span ℤ S
      exact hmul_span hfspan hgspan
  exact hspan_of_mem (χ : G → ℂ) χ.2

-- Proof sketch: a finite `p`-elementary group is nilpotent, so every maximal subgroup is normal
-- and has prime index. Induct on `Nat.card G`; Brauer's theorem `10-10.5-1` and the subgroup
-- induction result above show that the contributions induced from maximal subgroups already lie in
-- `R'(G)`, while the remaining degree-one characters generate the quotient.
/-- For an elementary finite group, LinearRepresentations_Serre_1977's subgroup `R'(G)` equals the whole character ring
`R(G)`. -/
theorem elementaryLinearCharacterSpan_eq_top_of_isElementary
    (hG : IsElementary G) :
    R'(G) = ⊤ := by
  refine top_unique ?_
  rw [← rep_character_span_eq_top_local (G := G)]
  rw [Submodule.span_le]
  intro η hη
  rcases hη with ⟨V, rfl⟩
  exact fdRepCharacterRing_mem_elementaryLinearCharacterSpan_of_isElementary V hG

/-- Helper for Exercise 10-10.5-5: on an elementary finite group, every virtual character whose
value at the identity is zero already belongs to `R₀'`. -/
lemma character_mem_elementaryLinearCharacterAugmentationSpan_of_apply_one_eq_zero_of_isElementary
    (hG : IsElementary G) {η : R(G)} (hη : η 1 = 0) :
    η ∈ R₀'(G) := by
  have hη' : η ∈ R'(G) := by
    rw [elementaryLinearCharacterSpan_eq_top_of_isElementary hG]
    simp
  rw [elementaryLinearCharacterSpan] at hη'
  rcases Submodule.mem_sup.mp hη' with ⟨ξ, hξ, ζ, hζ, rfl⟩
  rcases Submodule.mem_span_singleton.mp hξ with ⟨n, rfl⟩
  have hζ_zero : ((ζ : G → ℂ) 1) = 0 :=
    apply_one_eq_zero_of_mem_elementaryLinearCharacterAugmentationSpan hζ
  have hn_complex : (n : ℂ) = 0 := by
    -- Evaluate the decomposition at the identity; the augmentation part vanishes there.
    simpa [hζ_zero] using hη
  have hn : n = 0 := by
    exact_mod_cast hn_complex
  subst n
  rw [zero_zsmul, zero_add]
  exact hζ

-- Proof sketch: use Theorem `10-10.5-1` to decompose `χ` as a sum of characters induced from
-- elementary subgroups. On each elementary subgroup, the restriction factor belongs to `R₀'` by
-- the previous theorem because its value at the identity is `χ 1 = 0`; then part (a) sends each
-- induced summand back into `R₀'(G)`.
/-- Helper for Exercise 10-10.5-5: every virtual character of the finite group `G` whose
value at the identity is zero belongs to the `ℤ`-span of the induced differences
`Ind_E^G(α - 1)`, where `E`
is an elementary subgroup of `G` and `α` is a degree-one complex character of `E`. -/
theorem character_mem_elementaryLinearCharacterAugmentationSpan_of_apply_one_eq_zero
    (χ : R(G)) (hχ : χ 1 = 0) :
    χ ∈ R₀'(G) := by
  classical
  let B : Nat.Primes → Submodule ℤ (R(G)) :=
    fun p ↦ Representation.pElementaryInducedCharacterSpan (p : ℕ) G
  have hone : (1 : R(G)) ∈ ⨆ p : Nat.Primes, B p := by
    simpa [B] using one_mem_iSup_pElementaryInducedCharacterSpan_local (G := G)
  obtain ⟨μ, hμmem, hone_eq⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp B (1 : R(G))).mp hone
  have hpiece : ∀ p : Nat.Primes, μ p * χ ∈ R₀'(G) := by
    intro p
    let X : Finset (Subgroup G) := Finset.univ.filter fun H : Subgroup G ↦ IsPElementary (p : ℕ) H
    have hp_mem : μ p ∈ artinInducedCharacterSubmodule X := by
      simpa [B, X, Representation.pElementaryInducedCharacterSpan] using hμmem p
    obtain ⟨ξ, hξ⟩ :=
      Representation.exists_family_characterRingInduction_eq_of_mem_artinInducedCharacterSubmodule
        hp_mem
    have hmul :
        μ p * χ =
          ∑ H : X,
            H.1.characterRingInduction
              (ξ H *
                (⟨fun h : H.1 ↦ (χ : G → ℂ) h,
                  restrict_mem_characterRing_local (G := G) (H := H.1) χ⟩ : R(H.1))) := by
      -- Multiply Brauer's `p`-piece by `χ`, then push that multiplication inside each subgroup
      -- induction after restricting `χ` to the source subgroup.
      calc
        μ p * χ = (∑ H : X, H.1.characterRingInduction (ξ H)) * χ := by
          rw [hξ]
        _ = ∑ H : X, (H.1.characterRingInduction (ξ H)) * χ := by
          simp [Finset.sum_mul]
        _ = ∑ H : X,
              H.1.characterRingInduction
                (ξ H *
                  (⟨fun h : H.1 ↦ (χ : G → ℂ) h,
                    restrict_mem_characterRing_local (G := G) (H := H.1) χ⟩ : R(H.1))) := by
              refine Finset.sum_congr rfl ?_
              intro H hH
              apply Subtype.ext
              ext g
              simpa [Subgroup.characterRingInduction_apply] using
                congrFun
                  (Subgroup.induced_mul_eq_induced_mul_restriction_local
                    (G := G) H.1 ((ξ H : R(H.1)) : H.1 → ℂ) χ)
                  g
    rw [hmul]
    refine Submodule.sum_mem _ ?_
    intro H hH
    let χH : R(H.1) :=
      ⟨fun h : H.1 ↦ (χ : G → ℂ) h,
        restrict_mem_characterRing_local (G := G) (H := H.1) χ⟩
    have hH_elem : IsElementary H.1 := by
      exact ⟨p, (Finset.mem_filter.mp H.2).2⟩
    have hprod_zero : ((ξ H * χH : R(H.1)) 1) = 0 := by
      simp [χH, hχ]
    have hprod_mem : ξ H * χH ∈ R₀'(H.1) :=
      character_mem_elementaryLinearCharacterAugmentationSpan_of_apply_one_eq_zero_of_isElementary
        (G := H.1) hH_elem hprod_zero
    have hmap :
        H.1.characterRingInduction (ξ H * χH) ∈
          Submodule.map (H.1.characterRingInduction) (R₀'(H.1)) := by
      exact ⟨ξ H * χH, hprod_mem, rfl⟩
    exact Subgroup.map_elementaryLinearCharacterAugmentationSpan (G := G) H.1 hmap
  have hsum_mem : μ.sum (fun _ η ↦ η * χ) ∈ R₀'(G) := by
    refine Submodule.sum_mem _ ?_
    intro p hp
    exact hpiece p
  have hχeq : χ = μ.sum (fun _ η ↦ η * χ) := by
    calc
      χ = (1 : R(G)) * χ := by simp
      _ = (μ.sum fun _ η ↦ η) * χ := by rw [hone_eq]
      _ = μ.sum (fun _ η ↦ η * χ) := by
            simp [Finsupp.sum, Finset.sum_mul]
  -- Decompose `1` by Brauer's theorem, multiply by `χ`, and reduce each elementary-source factor
  -- to the elementary zero-at-identity lemma proved above.
  rw [hχeq]
  exact hsum_mem


-- Proof sketch: every element of `R(G)` differs from its value at the identity times the trivial
-- character by an element of `R₀'(G)` by the previous theorem, so `R'(G)` contains all of
-- `R(G)`.
/-- LinearRepresentations_Serre_1977's subgroup `R'(G)` generated by the trivial character and the induced differences
`Ind_E^G(α - 1)` is all of `R(G)`. -/
theorem elementaryLinearCharacterSpan_eq_top :
    R'(G) = ⊤ := by
  refine top_unique ?_
  intro χ hχ_mem
  rcases virtual_character_eq_character_difference_global (G := G) χ with ⟨Vpos, Vneg, hχdiff⟩
  let n : ℤ := Module.finrank ℂ Vpos - Module.finrank ℂ Vneg
  let η : R(G) := χ - n • (1 : R(G))
  have hχ_one : χ 1 = n := by
    calc
      χ 1 = (Vpos.character - Vneg.character) 1 := by
        simpa using congrFun hχdiff 1
      _ = Module.finrank ℂ Vpos - Module.finrank ℂ Vneg := by
        simp [FDRep.char_one, sub_eq_add_neg]
      _ = n := by
        simp [n]
  have hη_zero : η 1 = 0 := by
    -- Subtract the identity value of `χ` so the augmentation theorem applies to the remainder.
    simp [η, hχ_one]
  have hη_mem : η ∈ R₀'(G) :=
    character_mem_elementaryLinearCharacterAugmentationSpan_of_apply_one_eq_zero (G := G) η hη_zero
  have hscalar :
      n • (1 : R(G)) ∈ Submodule.span ℤ ({1} : Set (R(G))) := by
    exact Submodule.smul_mem _ n (Submodule.subset_span (by simp))
  have hscalar' : n • (1 : R(G)) ∈ R'(G) := by
    rw [elementaryLinearCharacterSpan]
    exact
      (le_sup_left :
        Submodule.span ℤ ({1} : Set (R(G))) ≤
          Submodule.span ℤ ({1} : Set (R(G))) ⊔ R₀'(G)) hscalar
  have hη' : η ∈ R'(G) := by
    rw [elementaryLinearCharacterSpan]
    exact
      (le_sup_right :
        R₀'(G) ≤ Submodule.span ℤ ({1} : Set (R(G))) ⊔ R₀'(G)) hη_mem
  have hsplit :
      χ = n • (1 : R(G)) + η := by
    dsimp [η]
    abel
  rw [hsplit]
  exact Submodule.add_mem _ hscalar' hη'

namespace Subgroup

/-- Helper for Exercise 10-10.5-5: the packaged quotient regular-minus-rank element belongs to
LinearRepresentations_Serre_1977's augmentation subgroup `R₀'(G)`. -/
theorem quotient_linearCharacter_differences_sum_mem_elementaryLinearCharacterAugmentationSpan
    (H : Subgroup G) [H.Normal]
    (hcomm : ∀ a b : G ⧸ H, a * b = b * a)
    [Fintype ((G ⧸ H) →* ℂˣ)] :
    (∑ χ : (G ⧸ H) →* ℂˣ, ((χ.comp (QuotientGroup.mk' H)).toCharacterRing - 1)) ∈ R₀'(G) := by
  have hzero :
      ((∑ χ : (G ⧸ H) →* ℂˣ,
          ((χ.comp (QuotientGroup.mk' H)).toCharacterRing - 1) : R(G)) 1) = 0 := by
    -- Evaluate the packaged difference at `1`; the index term cancels the induced trivial value.
    rw [← induced_trivial_sub_index_smul_one_eq_sum_quotient_linearCharacter_differences
      (G := G) (H := H) hcomm]
    simp [Subgroup.characterRingInduction_apply,
      Subgroup.inducedClassFunction_one_eq_index_mul_value]
  exact
    character_mem_elementaryLinearCharacterAugmentationSpan_of_apply_one_eq_zero
      (G := G)
      (∑ χ : (G ⧸ H) →* ℂˣ, ((χ.comp (QuotientGroup.mk' H)).toCharacterRing - 1))
      hzero

/-- Helper for Exercise 10-10.5-5: if `H` is normal and the canonical quotient multiplication on
`G ⧸ H` is commutative, then `Ind_H^G(1_H)` already lies in LinearRepresentations_Serre_1977's subgroup `R'(G)`. -/
theorem induced_trivial_mem_elementaryLinearCharacterSpan_of_normal_quotient_mul_comm
    (H : Subgroup G) [H.Normal]
    (hcomm : ∀ a b : G ⧸ H, a * b = b * a)
    [Finite ((G ⧸ H) →* ℂˣ)] :
    Subgroup.characterRingInduction H (1 : R(H)) ∈ R'(G) := by
  -- Route correction: the raw quotient-character sum is not the right owner target. Package only
  -- the augmentation piece `Ind_H^G(1) - [G : H] · 1` inside `R₀'(G)`, then add back the trivial
  -- line.
  letI : Fintype ((G ⧸ H) →* ℂˣ) := Fintype.ofFinite ((G ⧸ H) →* ℂˣ)
  have hdiff :
      Subgroup.characterRingInduction H (1 : R(H)) - (H.index : ℤ) • (1 : R(G)) ∈ R₀'(G) := by
    rw [induced_trivial_sub_index_smul_one_eq_sum_quotient_linearCharacter_differences H hcomm]
    exact
      quotient_linearCharacter_differences_sum_mem_elementaryLinearCharacterAugmentationSpan
        H hcomm
  have hone :
      (H.index : ℤ) • (1 : R(G)) ∈ Submodule.span ℤ ({1} : Set (R(G))) := by
    exact Submodule.smul_mem _ (H.index : ℤ) (Submodule.subset_span (by simp))
  have hone' : (H.index : ℤ) • (1 : R(G)) ∈ R'(G) := by
    rw [elementaryLinearCharacterSpan]
    exact
      (le_sup_left :
        Submodule.span ℤ ({1} : Set (R(G))) ≤
          Submodule.span ℤ ({1} : Set (R(G))) ⊔ R₀'(G)) hone
  have hdiff' :
      Subgroup.characterRingInduction H (1 : R(H)) - (H.index : ℤ) • (1 : R(G)) ∈ R'(G) := by
    rw [elementaryLinearCharacterSpan]
    exact
      (le_sup_right :
        R₀'(G) ≤ Submodule.span ℤ ({1} : Set (R(G))) ⊔ R₀'(G)) hdiff
  have hsplit :
      Subgroup.characterRingInduction H (1 : R(H)) =
        (H.index : ℤ) • (1 : R(G)) +
          (Subgroup.characterRingInduction H (1 : R(H)) - (H.index : ℤ) • (1 : R(G))) := by
    abel
  rw [hsplit]
  exact Submodule.add_mem _ hone' hdiff'

-- Proof sketch: by the previous theorem it is enough to check the image of the trivial character
-- of `H`. If `H` is normal and `G ⧸ H` is abelian, then `Ind_H^G(1_H)` is a sum of degree-one
-- characters of `G` with kernel containing `H`, hence lies in `R'(G)`.
/-- If `H` is normal with abelian quotient, induction sends LinearRepresentations_Serre_1977's subgroup `R'(H)` into
`R'(G)`. -/
theorem map_elementaryLinearCharacterSpan_of_normal_quotient_mul_comm
    (H : Subgroup G) [H.Normal]
    (hcomm : ∀ a b : G ⧸ H, a * b = b * a)
    [Finite ((G ⧸ H) →* ℂˣ)] :
    Submodule.map (Subgroup.characterRingInduction H) (R'(H)) ≤ R'(G) := by
  -- Split LinearRepresentations_Serre_1977's subgroup into the trivial line and the augmentation subgroup, then use part (a)
  -- for the augmentation part and the previous theorem for the trivial generator.
  letI : Fintype ((G ⧸ H) →* ℂˣ) := Fintype.ofFinite ((G ⧸ H) →* ℂˣ)
  rw [elementaryLinearCharacterSpan, Submodule.map_sup]
  refine sup_le ?_ ?_
  · rw [Submodule.map_span_le]
    intro χ hχ
    simp only [Set.mem_singleton_iff] at hχ
    subst hχ
    exact induced_trivial_mem_elementaryLinearCharacterSpan_of_normal_quotient_mul_comm H hcomm
  · exact le_trans (map_elementaryLinearCharacterAugmentationSpan H) le_sup_right

end Subgroup

end

end Representation
