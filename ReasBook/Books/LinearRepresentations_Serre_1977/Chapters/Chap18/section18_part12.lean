import Mathlib
import Mathlib.RingTheory.Morita.Matrix

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_18_18_6_5 (from Chap18) -/
noncomputable section

open Representation (IsMonomialCharacter)
open AlternatingGroupFive
open scoped SubgroupInduction
open scoped BigOperators

local notation "A5" => alternatingGroup (Fin 5)

/- Domain-style sampling for this item:
* primary domain: ordinary character theory of the finite group `A₅`, specialized to LinearRepresentations_Serre_1977's
  question about which labeled irreducible ordinary characters are monomial;
* relevant owner declarations inspected in this domain:
  `Representation.IsMonomialCharacter`,
  `Representation.isMonomialCharacter_of_induced`,
  `Representation.character`,
  `OrdinaryIrreducible.character`;
* best owner abstraction: the source-facing objects in Chapter 18 are the ordinary-character
  labels from `Remark_18_18_6_1`, while the canonical chapter owner for monomiality is the
  character-level predicate `Representation.IsMonomialCharacter`;
* source/core/bridge triage:
  - source-facing: the `OrdinaryIrreducible` labels `.chi3_phi_psi`, `.chi3_psi_phi`, `.chi4`,
    `.chi5` from LinearRepresentations_Serre_1977's `A₅` character table;
  - core/canonical: `Representation.IsMonomialCharacter`;
  - bridge/view: the owner-level source-facing character
    `OrdinaryIrreducible.character` from `Remark_18_18_6_1`.

Primitive data versus derived API:
* primitive data: the existing `OrdinaryIrreducible` and `ConjugacyClass` labels together with the
  ordinary-character table from `Remark_18_18_6_1`;
* derived API: the owner-level character bridge `OrdinaryIrreducible.character` from
  `Remark_18_18_6_1` and the monomial/nonmonomial theorems stated on
  `Representation.IsMonomialCharacter` of those labeled characters.
-/

namespace OrdinaryIrreducible

/-- Helper for Exercise 18-18.6-5: the alternating group `A₅` has order `60`. -/
private theorem a5_card_eq_sixty :
    Nat.card A5 = 60 := by
  -- Reduce the cardinality to the computable `Fintype.card` of `A₅`.
  simpa using (show Fintype.card A5 = 60 by native_decide)

/-- Helper for Exercise 18-18.6-5: evaluating an induced class function at the identity scales the
subgroup value at `1` by the subgroup index. -/
private theorem inducedClassFunction_one_eq_index_mul_value
    (H : Subgroup A5) (χ : H → ℂ) :
    Ind[H](χ) 1 = (H.index : ℂ) * χ 1 := by
  -- Route correction: reuse the earlier Chapter 7 identity-value theorem instead of reproving the
  -- same induced-character formula locally.
  simpa using (Subgroup.inducedClassFunction_one_eq_index_mul_value (H := H) (χ := χ))

/-- Helper for Exercise 18-18.6-5: any monomial character of `A₅` has degree equal to a subgroup
index. -/
private theorem monomial_subgroup_index_eq_character_one
    (χ : A5 → ℂ) (hχ : IsMonomialCharacter χ) :
    ∃ H : Subgroup A5, (H.index : ℂ) = χ 1 := by
  rcases hχ with ⟨H, α, hα⟩
  -- Unpack the monomial witness and evaluate the induced linear character at `1`.
  refine ⟨H, ?_⟩
  calc
    (H.index : ℂ) = Ind[H](α.toRepresentation.character) 1 := by
      symm
      rw [inducedClassFunction_one_eq_index_mul_value]
      simp [Representation.char_one]
    _ = χ 1 := by
      simp [hα]

/-- Helper for Exercise 18-18.6-5: the simple group `A₅` has no subgroup of index `3` or `4`. -/
private theorem no_subgroup_of_a5_index_three_or_four
    {n : ℕ} (hn : n = 3 ∨ n = 4) :
    ¬ ∃ H : Subgroup A5, H.index = n := by
  intro hex
  rcases hex with ⟨H, hHindex⟩
  letI : Fintype (A5 ⧸ H) := Fintype.ofFinite (A5 ⧸ H)
  letI : DecidableEq (A5 ⧸ H) := Classical.decEq _
  let φ : A5 →* Equiv.Perm (A5 ⧸ H) := MulAction.toPermHom A5 (A5 ⧸ H)
  have hker_bot : φ.ker = ⊥ := by
    -- The coset action kernel is normal, so simplicity forces it to be `⊥` or `⊤`.
    have hker_cases : φ.ker = ⊥ ∨ φ.ker = ⊤ :=
      Subgroup.Normal.eq_bot_or_eq_top (H := φ.ker) (inferInstance : φ.ker.Normal)
    rcases hker_cases with hbot | htop
    · exact hbot
    · exfalso
      have hcore_top : H.normalCore = ⊤ := by
        simpa [Subgroup.normalCore_eq_ker] using htop
      have htop_le : ⊤ ≤ H := by
        rw [← hcore_top]
        exact H.normalCore_le
      have hH_top : H = ⊤ := top_le_iff.mp htop_le
      have hone : n = 1 := by
        simpa [hHindex] using (Subgroup.index_eq_one).2 hH_top
      rcases hn with rfl | rfl <;> omega
  have hφ_injective : Function.Injective φ :=
    (MonoidHom.ker_eq_bot_iff φ).1 hker_bot
  have hcard_le :
      Fintype.card A5 ≤ Fintype.card (Equiv.Perm (A5 ⧸ H)) :=
    Fintype.card_le_of_injective φ hφ_injective
  have hquot_card : Fintype.card (A5 ⧸ H) = n := by
    simpa [Subgroup.index_eq_card] using hHindex
  have hperm_card : Fintype.card (Equiv.Perm (A5 ⧸ H)) = n.factorial := by
    -- The permutation group on `A₅ / H` has factorial cardinality in the quotient size.
    simpa [hquot_card] using (Fintype.card_perm (α := A5 ⧸ H))
  have hbound : 60 ≤ n.factorial := by
    simpa [a5_card_eq_sixty, hperm_card] using hcard_le
  rcases hn with rfl | rfl <;> norm_num at hbound

/-- Helper for Exercise 18-18.6-5: the explicit even permutation sending `0` to `1`. -/
private def transport_zero_to_one_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

/-- Helper for Exercise 18-18.6-5: the explicit even permutation sending `0` to `2`. -/
private def transport_zero_to_two_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 1 2 * Equiv.swap 0 1

/-- Helper for Exercise 18-18.6-5: the explicit even permutation sending `0` to `3`. -/
private def transport_zero_to_three_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 3 * Equiv.swap 3 1

/-- Helper for Exercise 18-18.6-5: the explicit even permutation sending `0` to `4`. -/
private def transport_zero_to_four_perm : Equiv.Perm (Fin 5) :=
  (finRotate 5)⁻¹

/-- Helper for Exercise 18-18.6-5: the transport to `1` lies in `A₅`. -/
private theorem transport_zero_to_one_perm_mem :
    transport_zero_to_one_perm ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

/-- Helper for Exercise 18-18.6-5: the transport to `2` lies in `A₅`. -/
private theorem transport_zero_to_two_perm_mem :
    transport_zero_to_two_perm ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

/-- Helper for Exercise 18-18.6-5: the transport to `3` lies in `A₅`. -/
private theorem transport_zero_to_three_perm_mem :
    transport_zero_to_three_perm ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

/-- Helper for Exercise 18-18.6-5: the transport to `4` lies in `A₅`. -/
private theorem transport_zero_to_four_perm_mem :
    transport_zero_to_four_perm ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

/-- Helper for Exercise 18-18.6-5: a fixed explicit representative for each point of the natural
five-point action of `A₅`. -/
private def point_stabilizer_zero_transport : Fin 5 → A5
  | 0 => 1
  | 1 => ⟨transport_zero_to_one_perm, transport_zero_to_one_perm_mem⟩
  | 2 => ⟨transport_zero_to_two_perm, transport_zero_to_two_perm_mem⟩
  | 3 => ⟨transport_zero_to_three_perm, transport_zero_to_three_perm_mem⟩
  | 4 => ⟨transport_zero_to_four_perm, transport_zero_to_four_perm_mem⟩

/-- Helper for Exercise 18-18.6-5: the chosen transport sends `0` to its indexed point. -/
private theorem point_stabilizer_zero_transport_apply_zero (x : Fin 5) :
    point_stabilizer_zero_transport x • (0 : Fin 5) = x := by
  -- The explicit representatives were chosen precisely to realize the five left cosets.
  fin_cases x <;> decide

/-- Helper for Exercise 18-18.6-5: the explicit transports are injective because they send `0` to
different points. -/
private theorem point_stabilizer_zero_transport_injective :
    Function.Injective point_stabilizer_zero_transport := by
  intro x y hxy
  have hxy0 := congrArg (fun g : A5 => g • (0 : Fin 5)) hxy
  simpa [point_stabilizer_zero_transport_apply_zero] using hxy0

/-- Helper for Exercise 18-18.6-5: the chosen transport family gives one representative in each
left coset of `Stab_{A₅}(0)`. -/
private theorem point_stabilizer_zero_transport_range_isComplement :
    Subgroup.IsComplement (Set.range point_stabilizer_zero_transport)
      (MulAction.stabilizer A5 (0 : Fin 5) : Set A5) := by
  -- Route correction: certify the transport family as a left transversal via a quotient section.
  let H : Subgroup A5 := MulAction.stabilizer A5 (0 : Fin 5)
  let sigma : A5 ⧸ H → A5 := fun q ↦ point_stabilizer_zero_transport (q.out • (0 : Fin 5))
  have hsigma : ∀ q : A5 ⧸ H, ((sigma q : A5) : A5 ⧸ H) = q := by
    intro q
    have hqout : ((sigma q : A5) : A5 ⧸ H) = ((q.out : A5) : A5 ⧸ H) := by
      rw [QuotientGroup.eq]
      -- `sigma q` and `q.out` lie in the same left coset because they send `0` to the same point.
      rw [MulAction.mem_stabilizer_iff]
      calc
        (((sigma q : A5)⁻¹ * q.out : A5) • (0 : Fin 5))
            = ((sigma q : A5)⁻¹) • (q.out • (0 : Fin 5)) := by
                simp [smul_smul]
        _ = ((sigma q : A5)⁻¹) • ((sigma q : A5) • (0 : Fin 5)) := by
              rw [show (sigma q : A5) • (0 : Fin 5) = q.out • (0 : Fin 5) by
                simp [sigma, point_stabilizer_zero_transport_apply_zero]]
        _ = (0 : Fin 5) := by
              simp [smul_smul]
    exact hqout.trans (Quotient.out_eq q)
  have hsame_coset_apply_zero {a b : A5}
      (hab : ((a : A5) : A5 ⧸ H) = ((b : A5) : A5 ⧸ H)) :
      a • (0 : Fin 5) = b • (0 : Fin 5) := by
    have hmem : a⁻¹ * b ∈ H := (QuotientGroup.eq).mp hab
    have hfix : (((a⁻¹ * b : A5) : A5) • (0 : Fin 5)) = 0 :=
      MulAction.mem_stabilizer_iff.mp hmem
    -- Elements of the same left coset differ by an element fixing `0`, so they move `0` equally.
    calc
      a • (0 : Fin 5) = a • (((a⁻¹ * b : A5) : A5) • (0 : Fin 5)) := by
          rw [hfix]
      _ = b • (0 : Fin 5) := by
          simp [smul_smul, mul_assoc]
  have hrange : Set.range sigma = Set.range point_stabilizer_zero_transport := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.out • (0 : Fin 5), rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨(((point_stabilizer_zero_transport x : A5) : A5 ⧸ H)), ?_⟩
      have hclass :
          (((sigma (((point_stabilizer_zero_transport x : A5) : A5 ⧸ H)) : A5) : A5 ⧸ H)) =
            (((point_stabilizer_zero_transport x : A5) : A5) : A5 ⧸ H) := hsigma _
      have hpoint :
          ((((point_stabilizer_zero_transport x : A5) : A5 ⧸ H)).out • (0 : Fin 5)) = x := by
        have hsame :
            (sigma (((point_stabilizer_zero_transport x : A5) : A5 ⧸ H)) : A5) • (0 : Fin 5) =
              (point_stabilizer_zero_transport x : A5) • (0 : Fin 5) :=
          hsame_coset_apply_zero hclass
        simpa [sigma, point_stabilizer_zero_transport_apply_zero] using hsame
      simpa [sigma, hpoint]
  simpa [hrange] using (Subgroup.isComplement_range_left hsigma)

/-- Helper for Exercise 18-18.6-5: the image finset of the transports is the concrete left
transversal used in the induced-character formula. -/
private def point_stabilizer_zero_transversal : Finset A5 :=
  Finset.univ.image point_stabilizer_zero_transport

/-- Helper for Exercise 18-18.6-5: the concrete transversal from the chosen transports really is a
left complement to `Stab_{A₅}(0)`. -/
private theorem point_stabilizer_zero_transversal_isComplement :
    Subgroup.IsComplement ((point_stabilizer_zero_transversal : Finset A5) : Set A5)
      (MulAction.stabilizer A5 (0 : Fin 5) : Set A5) := by
  -- Transfer the quotient-section complement to the concrete finset of explicit transports.
  have hset :
      ((point_stabilizer_zero_transversal : Finset A5) : Set A5) =
        Set.range point_stabilizer_zero_transport := by
    ext g
    constructor
    · intro hg
      simp [point_stabilizer_zero_transversal] at hg
      rcases hg with ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      simp [point_stabilizer_zero_transversal]
  rw [hset]
  exact point_stabilizer_zero_transport_range_isComplement

/-- Helper for Exercise 18-18.6-5: after transporting the fixed point `x` back to `0`, subgroup
membership is exactly the fixed-point condition `g • x = x`. -/
private theorem point_stabilizer_zero_transport_conj_mem_stabilizer_iff
    (g : A5) (x : Fin 5) :
    (point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x ∈
      MulAction.stabilizer A5 (0 : Fin 5) ↔ g • x = x := by
  constructor
  · intro hx
    -- Conjugating back by the chosen transport turns fixation of `0` into fixation of `x`.
    have hfix :
        (((point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x : A5) •
          (0 : Fin 5)) = 0 :=
      MulAction.mem_stabilizer_iff.mp hx
    calc
      g • x = g • ((point_stabilizer_zero_transport x : A5) • (0 : Fin 5)) := by
          rw [point_stabilizer_zero_transport_apply_zero]
      _ = (point_stabilizer_zero_transport x : A5) •
            (((point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x : A5) •
              (0 : Fin 5)) := by
                simp [smul_smul, mul_assoc]
      _ = (point_stabilizer_zero_transport x : A5) • (0 : Fin 5) := by rw [hfix]
      _ = x := point_stabilizer_zero_transport_apply_zero x
  · intro hfix
    -- Conversely, if `g` fixes `x`, then the conjugate by the transport fixes `0`.
    rw [MulAction.mem_stabilizer_iff]
    have hτ :
        (point_stabilizer_zero_transport x : A5) • (0 : Fin 5) = x :=
      point_stabilizer_zero_transport_apply_zero x
    have hτinv :
        ((point_stabilizer_zero_transport x : A5)⁻¹) • x = (0 : Fin 5) := by
      simpa [smul_smul] using
        (congrArg (fun z : Fin 5 => ((point_stabilizer_zero_transport x : A5)⁻¹) • z) hτ).symm
    calc
      (((point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x : A5) •
          (0 : Fin 5))
          = ((point_stabilizer_zero_transport x : A5)⁻¹) •
              (g • ((point_stabilizer_zero_transport x : A5) • (0 : Fin 5))) := by
                simp [smul_smul, mul_assoc]
      _ = ((point_stabilizer_zero_transport x : A5)⁻¹) • x := by
            rw [hτ, hfix]
      _ = (0 : Fin 5) := hτinv

/-- Helper for Exercise 18-18.6-5: the transported conjugate of `g` at a fixed point is the
corresponding stabilizer element of `Stab_{A₅}(0)`. -/
private def point_stabilizer_zero_transported_element
    (g : A5) (x : Fin 5) (hfix : g • x = x) :
    MulAction.stabilizer A5 (0 : Fin 5) :=
  ⟨(point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x,
    (point_stabilizer_zero_transport_conj_mem_stabilizer_iff g x).2 hfix⟩

/-- Helper for Exercise 18-18.6-5: transport does not change the order of the conjugated element.
-/
private theorem point_stabilizer_zero_transported_element_orderOf
    (g : A5) (x : Fin 5) (hfix : g • x = x) :
    orderOf (point_stabilizer_zero_transported_element g x hfix) = orderOf g := by
  -- View the transported subgroup element in `A₅`, then use conjugacy invariance of `orderOf`.
  have hsemi :
      SemiconjBy ((point_stabilizer_zero_transport x : A5)⁻¹) g
        (((point_stabilizer_zero_transport x : A5)⁻¹) * g *
          point_stabilizer_zero_transport x) := by
    simp [SemiconjBy, mul_assoc]
  calc
    orderOf (point_stabilizer_zero_transported_element g x hfix)
        =
          orderOf
            (((point_stabilizer_zero_transported_element g x hfix :
                MulAction.stabilizer A5 (0 : Fin 5)) : A5)) := by
            symm
            exact orderOf_submonoid _
    _ = orderOf
          (((point_stabilizer_zero_transport x : A5)⁻¹) * g *
            point_stabilizer_zero_transport x) := rfl
    _ = orderOf g := by
          simpa using hsemi.orderOf_eq.symm

/-- Helper for Exercise 18-18.6-5: summing over the explicit transport transversal is the same as
summing over the points of `Fin 5`. -/
private theorem point_stabilizer_zero_transport_sum_reindex
    (F : A5 → ℂ) :
    Finset.sum point_stabilizer_zero_transversal F =
      ∑ x : Fin 5, F (point_stabilizer_zero_transport x) := by
  classical
  -- Rewrite the explicit image finset back to `Finset.univ` using injectivity of the transport.
  rw [point_stabilizer_zero_transversal]
  simpa using
    (Finset.sum_image
      (s := (Finset.univ : Finset (Fin 5)))
      (g := point_stabilizer_zero_transport)
      (f := F)
      (fun x _ y _ hxy ↦ point_stabilizer_zero_transport_injective hxy))

/-- Helper for Exercise 18-18.6-5: the subtype built from any proof of stabilizer membership agrees
with the canonical transported stabilizer element. -/
private theorem point_stabilizer_zero_transported_element_subtype_eq
    (g : A5) (x : Fin 5) (hfix : g • x = x)
    (hr : (point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x ∈
      MulAction.stabilizer A5 (0 : Fin 5)) :
    (⟨(point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x, hr⟩ :
      MulAction.stabilizer A5 (0 : Fin 5)) =
        point_stabilizer_zero_transported_element g x hfix := by
  -- Both subgroup elements have the same underlying conjugate in `A₅`, so proof irrelevance
  -- identifies the subtype witnesses.
  apply Subtype.ext
  rfl

/-- Helper for Exercise 18-18.6-5: the induced class function from the pulled-back `A₄/V₄`
character is LinearRepresentations_Serre_1977's fixed-point sum over the natural five-point action. -/
private theorem point_stabilizer_zero_induced_character_fixed_point_formula
    (g : A5) :
    Ind[MulAction.stabilizer A5 (0 : Fin 5)](
      point_stabilizer_zero_linear_character.toRepresentation.character) g =
      ∑ x : Fin 5,
        if hfix : g • x = x then
          (point_stabilizer_zero_linear_character
            (point_stabilizer_zero_transported_element g x hfix) : ℂ)
        else 0 := by
  let H : Subgroup A5 := MulAction.stabilizer A5 (0 : Fin 5)
  let ψ : H → ℂ := point_stabilizer_zero_linear_character.toRepresentation.character
  letI : NeZero (Nat.card H : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hψ : IsClassFunction ψ := by
    simpa [ψ] using
      (Representation.character_isClassFunction point_stabilizer_zero_linear_character.toRepresentation)
  calc
    Ind[H](ψ) g =
        Finset.sum point_stabilizer_zero_transversal fun r ↦
          if hr : r⁻¹ * g * r ∈ H then
            ψ ⟨r⁻¹ * g * r, hr⟩
          else 0 := by
            -- Apply the Chapter 7 left-transversal formula to the explicit transport family.
            simpa [H, ψ] using
              (Subgroup.induced_class_function_eq_sum_over_left_transversal
                (H := H) (ψ := ψ) hψ
                (R := point_stabilizer_zero_transversal)
                point_stabilizer_zero_transversal_isComplement g)
    _ = ∑ x : Fin 5,
          if hfix : g • x = x then
            (point_stabilizer_zero_linear_character
              (point_stabilizer_zero_transported_element g x hfix) : ℂ)
          else 0 := by
            -- Reindex the explicit transversal by the transported point and simplify each summand
            -- by the fixed-point criterion.
            rw [point_stabilizer_zero_transport_sum_reindex]
            refine Fintype.sum_congr
              (fun x ↦
                if hr : (point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x ∈
                    H then
                  ψ ⟨(point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x,
                    hr⟩
                else 0)
              (fun x ↦
                if hfix : g • x = x then
                  (point_stabilizer_zero_linear_character
                    (point_stabilizer_zero_transported_element g x hfix) : ℂ)
                else 0)
              (fun x ↦ ?_)
            by_cases hfix : g • x = x
            · have hr :
                (point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x ∈
                  H :=
                (point_stabilizer_zero_transport_conj_mem_stabilizer_iff g x).2 hfix
              change
                (if hr' : (point_stabilizer_zero_transport x)⁻¹ * g *
                    point_stabilizer_zero_transport x ∈ H then
                  ψ ⟨(point_stabilizer_zero_transport x)⁻¹ * g *
                      point_stabilizer_zero_transport x, hr'⟩
                else 0) =
                  (if hfix' : g • x = x then
                    (point_stabilizer_zero_linear_character
                      (point_stabilizer_zero_transported_element g x hfix') : ℂ)
                  else 0)
              rw [dif_pos hr, dif_pos hfix]
              -- The positive branch is exactly the transported stabilizer element.
              simpa [H, ψ, MonoidHom.toRepresentation_character_apply] using
                congrArg
                  (fun z : H ↦ (point_stabilizer_zero_linear_character z : ℂ))
                  (point_stabilizer_zero_transported_element_subtype_eq g x hfix hr)
            · have hrnot :
                ¬ (point_stabilizer_zero_transport x)⁻¹ * g * point_stabilizer_zero_transport x ∈
                    H := by
                  intro hr
                  exact hfix ((point_stabilizer_zero_transport_conj_mem_stabilizer_iff g x).1 hr)
              change
                (if hr' : (point_stabilizer_zero_transport x)⁻¹ * g *
                    point_stabilizer_zero_transport x ∈ H then
                  ψ ⟨(point_stabilizer_zero_transport x)⁻¹ * g *
                      point_stabilizer_zero_transport x, hr'⟩
                else 0) =
                  (if hfix' : g • x = x then
                    (point_stabilizer_zero_linear_character
                      (point_stabilizer_zero_transported_element g x hfix') : ℂ)
                  else 0)
              rw [dif_neg hrnot, dif_neg hfix]

/-- Helper for Exercise 18-18.6-5: every element of `A₄` has order `1`, `2`, or `3`. -/
private theorem a4_cycleType_eq_zero_or_three_or_double_two
    (g : alternatingGroup (Fin 4)) :
    (((g : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)).cycleType = 0) ∨
      (((g : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)).cycleType = {3}) ∨
        (((g : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)).cycleType = {2, 2}) := by
  let σ : Equiv.Perm (Fin 4) := ((g : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))
  have hsign : σ.sign = 1 := Equiv.Perm.mem_alternatingGroup.mp g.property
  have hsupp : σ.cycleType.sum ≤ 4 := by
    simpa [σ, Equiv.Perm.sum_cycleType] using σ.support.card_le_univ
  have hcard_le_two : σ.cycleType.card ≤ 2 := by
    have hsum_lower : σ.cycleType.card * 2 ≤ σ.cycleType.sum := by
      simpa using
        (Multiset.card_nsmul_le_sum (s := σ.cycleType) (a := 2)
          (fun n hn ↦ Equiv.Perm.two_le_of_mem_cycleType hn))
    omega
  by_cases hσ : σ = 1
  · left
    simpa [σ] using (Equiv.Perm.cycleType_eq_zero.2 hσ)
  have hcard_pos : 0 < σ.cycleType.card := by
    simpa [σ, hσ] using (Equiv.Perm.card_cycleType_pos.2 hσ)
  have hcard_cases : σ.cycleType.card = 1 ∨ σ.cycleType.card = 2 := by
    omega
  rcases hcard_cases with hcard | hcard
  · obtain ⟨n, hn⟩ := Multiset.card_eq_one.mp hcard
    have htwole : 2 ≤ n := by
      have hn_mem : n ∈ σ.cycleType := by simpa [hn]
      exact Equiv.Perm.two_le_of_mem_cycleType hn_mem
    have hnle : n ≤ 4 := by simpa [hn, σ] using hsupp
    interval_cases n
    · exfalso
      norm_num [Equiv.Perm.sign_of_cycleType, hn, σ] at hsign
    · right
      left
      simpa [σ] using hn
    · exfalso
      norm_num [Equiv.Perm.sign_of_cycleType, hn, σ] at hsign
  · obtain ⟨m, n, hmn⟩ := Multiset.card_eq_two.mp hcard
    have hm_mem : m ∈ σ.cycleType := by simpa [hmn]
    have hn_mem : n ∈ σ.cycleType := by simpa [hmn, add_comm]
    have hm_two : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm_mem
    have hn_two : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn_mem
    have hmn_sum : m + n ≤ 4 := by simpa [hmn, σ] using hsupp
    have hm_eq : m = 2 := by omega
    have hn_eq : n = 2 := by omega
    right
    right
    simpa [σ, hm_eq, hn_eq] using hmn

/-- Helper for Exercise 18-18.6-5: every element of `A₄` has order `1`, `2`, or `3`. -/
private theorem a4_orderOf_eq_one_or_two_or_three
    (g : alternatingGroup (Fin 4)) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 := by
  let σ : Equiv.Perm (Fin 4) := ((g : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))
  rcases a4_cycleType_eq_zero_or_three_or_double_two g with hσ | hσ | hσ
  · left
    -- The identity cycle type gives order `1`.
    exact (orderOf_submonoid g).symm.trans <| by
      simpa [σ, hσ] using (Equiv.Perm.lcm_cycleType σ).symm
  · right
    right
    -- A three-cycle has order `3`.
    exact (orderOf_submonoid g).symm.trans <| by
      simpa [σ, hσ] using (Equiv.Perm.lcm_cycleType σ).symm
  · right
    left
    -- The double-transposition cycle type has order `2`.
    exact (orderOf_submonoid g).symm.trans <| by
      simpa [σ, hσ] using (Equiv.Perm.lcm_cycleType σ).symm

/-- Helper for Exercise 18-18.6-5: a concrete order-`2` element of `A₅` with fixed point `2`. -/
private def double_transposition_rep : A5 :=
  ⟨Equiv.swap 0 4 * Equiv.swap 1 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

/-- Helper for Exercise 18-18.6-5: a concrete `3`-cycle in `A₅` fixing `3` and `4`. -/
private def three_cycle_rep : A5 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 0 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

/-- Helper for Exercise 18-18.6-5: the chosen `3`-cycle representative is indeed a three-cycle. -/
private theorem three_cycle_rep_isThreeCycle :
    Equiv.Perm.IsThreeCycle ((three_cycle_rep : A5) : Equiv.Perm (Fin 5)) := by
  -- The representative is the standard product of swaps giving the `3`-cycle `(0 1 2)`.
  simpa [three_cycle_rep] using
    Equiv.Perm.isThreeCycle_swap_mul_swap_same
      (a := (0 : Fin 5)) (b := (1 : Fin 5)) (c := (2 : Fin 5))
      (by decide) (by decide) (by decide)

/-- Helper for Exercise 18-18.6-5: the second fixed-point transport for `three_cycle_rep` is the
square of the first. -/
private theorem three_cycle_rep_transported_element_four_eq_sq_of_three
    (h3 : three_cycle_rep • (3 : Fin 5) = 3) (h4 : three_cycle_rep • (4 : Fin 5) = 4) :
    point_stabilizer_zero_transported_element three_cycle_rep 4 h4 =
      (point_stabilizer_zero_transported_element three_cycle_rep 3 h3) ^ 2 := by
  -- Route correction: compute the two transported stabilizer elements explicitly and compare
  -- them in the subgroup by finite extensionality.
  have h3eq : h3 = (by decide : three_cycle_rep • (3 : Fin 5) = 3) :=
    Subsingleton.elim _ _
  have h4eq : h4 = (by decide : three_cycle_rep • (4 : Fin 5) = 4) :=
    Subsingleton.elim _ _
  rw [h3eq, h4eq]
  apply Subtype.ext
  decide

/-- Helper for Exercise 18-18.6-5: if an order-`2` element of `A₅` is induced from the chosen
point-stabilizer character, each fixed point contributes the value `1`. -/
private theorem point_stabilizer_zero_induced_character_order_two
    (g : A5) (hg : orderOf g = 2) :
    Ind[MulAction.stabilizer A5 (0 : Fin 5)](
      point_stabilizer_zero_linear_character.toRepresentation.character) g = 1 := by
  let σ : Equiv.Perm (Fin 5) := ((g : A5) : Equiv.Perm (Fin 5))
  have hσord : orderOf σ = 2 := by
    simpa [σ, hg] using (orderOf_submonoid g)
  have hfixed_card : Fintype.card (Function.fixedPoints σ) = 1 := by
    have hprime : Nat.Prime (orderOf σ) := by
      simpa [hσord] using Nat.prime_two
    obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) hprime
    have hsum : 2 + n * 2 ≤ 5 := by
      have hsupp : σ.cycleType.sum ≤ 5 := by
        simpa [Equiv.Perm.sum_cycleType] using σ.support.card_le_univ
      simpa [hn, hσord] using hsupp
    have hn_le : n ≤ 1 := by
      omega
    have hsign : σ.sign = 1 := by
      exact Equiv.Perm.mem_alternatingGroup.mp g.property
    have hn1 : n = 1 := by
      interval_cases n
      · norm_num [Equiv.Perm.sign_of_cycleType, hn, hσord] at hsign
      · rfl
    rw [Equiv.Perm.card_fixedPoints, hn, hσord, hn1]
    norm_num
  rw [point_stabilizer_zero_induced_character_fixed_point_formula]
  have hsummand :
      ∀ x : Fin 5,
        (if hfix : g • x = x then
          (point_stabilizer_zero_linear_character
            (point_stabilizer_zero_transported_element g x hfix) : ℂ)
        else 0) =
          if σ x = x then (1 : ℂ) else 0 := by
    intro x
    by_cases hfix : g • x = x
    · have hord :
          orderOf (point_stabilizer_zero_transported_element g x hfix) = 2 := by
        simpa [hg] using
          point_stabilizer_zero_transported_element_orderOf g x hfix
      have hchar :
          (point_stabilizer_zero_linear_character
            (point_stabilizer_zero_transported_element g x hfix) : ℂ) = 1 := by
        exact congrArg (fun z : ℂˣ => (z : ℂ))
          (point_stabilizer_zero_linear_character_order_two_eq_one
            (point_stabilizer_zero_transported_element g x hfix) hord)
      -- On a fixed point, the transported stabilizer element has order `2`, so the linear
      -- character contributes `1`.
      simpa [σ, hfix, hchar]
    · -- Away from the fixed-point set, both sides of the summand vanish.
      simpa [σ, hfix]
  simp_rw [hsummand]
  rw [Finset.sum_boole]
  have hcard :
      Fintype.card (Function.fixedPoints σ) =
        (Finset.univ.filter fun x : Fin 5 ↦ σ x = x).card := by
    exact Fintype.card_ofFinset
      (Finset.univ.filter fun x : Fin 5 ↦ σ x = x)
      (by
        intro x
        simp [Function.fixedPoints, Function.IsFixedPt])
  exact_mod_cast (hcard.symm.trans hfixed_card)

/-- Helper for Exercise 18-18.6-5: evaluating the induced character on the concrete `3`-cycle
representative yields the table value `-1`. -/
private theorem point_stabilizer_zero_induced_character_three_cycle_rep :
    Ind[MulAction.stabilizer A5 (0 : Fin 5)](
      point_stabilizer_zero_linear_character.toRepresentation.character) three_cycle_rep = -1 := by
  have h3 : three_cycle_rep • (3 : Fin 5) = 3 := by decide
  have h4 : three_cycle_rep • (4 : Fin 5) = 4 := by decide
  let h : MulAction.stabilizer A5 (0 : Fin 5) :=
    point_stabilizer_zero_transported_element three_cycle_rep 3 h3
  have hrep_ord : orderOf three_cycle_rep = 3 := by
    -- The concrete representative is a genuine three-cycle in `A₅`.
    exact (orderOf_submonoid three_cycle_rep).symm.trans three_cycle_rep_isThreeCycle.orderOf
  have hh_ord : orderOf h = 3 := by
    -- Transport preserves the order, so the stabilizer generator still has order `3`.
    calc
      orderOf h = orderOf three_cycle_rep := by
        simpa [h] using point_stabilizer_zero_transported_element_orderOf three_cycle_rep 3 h3
      _ = 3 := hrep_ord
  have h4_transport :
      point_stabilizer_zero_transported_element three_cycle_rep 4 h4 = h ^ 2 := by
    simpa [h] using three_cycle_rep_transported_element_four_eq_sq_of_three h3 h4
  have h0 :
      (if hfix : three_cycle_rep • (0 : Fin 5) = 0 then
        (point_stabilizer_zero_linear_character
          (point_stabilizer_zero_transported_element three_cycle_rep 0 hfix) : ℂ)
      else 0) = 0 := by
    have hfix : ¬ three_cycle_rep • (0 : Fin 5) = 0 := by decide
    simp [hfix]
  have h1 :
      (if hfix : three_cycle_rep • (1 : Fin 5) = 1 then
        (point_stabilizer_zero_linear_character
          (point_stabilizer_zero_transported_element three_cycle_rep 1 hfix) : ℂ)
      else 0) = 0 := by
    have hfix : ¬ three_cycle_rep • (1 : Fin 5) = 1 := by decide
    simp [hfix]
  have h2 :
      (if hfix : three_cycle_rep • (2 : Fin 5) = 2 then
        (point_stabilizer_zero_linear_character
          (point_stabilizer_zero_transported_element three_cycle_rep 2 hfix) : ℂ)
      else 0) = 0 := by
    have hfix : ¬ three_cycle_rep • (2 : Fin 5) = 2 := by decide
    simp [hfix]
  have h3_term :
      (if hfix : three_cycle_rep • (3 : Fin 5) = 3 then
        (point_stabilizer_zero_linear_character
          (point_stabilizer_zero_transported_element three_cycle_rep 3 hfix) : ℂ)
      else 0) =
        (point_stabilizer_zero_linear_character h : ℂ) := by
    rw [dif_pos h3]
  have h4_term :
      (if hfix : three_cycle_rep • (4 : Fin 5) = 4 then
        (point_stabilizer_zero_linear_character
          (point_stabilizer_zero_transported_element three_cycle_rep 4 hfix) : ℂ)
      else 0) =
        (point_stabilizer_zero_linear_character (h ^ 2) : ℂ) := by
    rw [dif_pos h4]
    simpa [h4_transport]
  rw [point_stabilizer_zero_induced_character_fixed_point_formula, Fin.sum_univ_five,
    h0, h1, h2, h3_term, h4_term]
  -- Only the two fixed points `3` and `4` contribute, and their values sum to `-1`.
  simpa [h] using point_stabilizer_zero_linear_character_order_three_sum h hh_ord

/-- Helper for Exercise 18-18.6-5: an order-`3` element of `A₅` is a three-cycle on `Fin 5`. -/
private theorem a5_isThreeCycle_of_order_three
    (g : A5) (hg : orderOf g = 3) :
    Equiv.Perm.IsThreeCycle (((g : A5) : Equiv.Perm (Fin 5))) := by
  let σ : Equiv.Perm (Fin 5) := ((g : A5) : Equiv.Perm (Fin 5))
  have hσord : orderOf σ = 3 := by
    simpa [σ, hg] using (orderOf_submonoid g)
  have hprime : Nat.Prime (orderOf σ) := by
    simpa [hσord] using Nat.prime_three
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) hprime
  have hsum : 3 + n * 3 ≤ 5 := by
    have hsupp : σ.cycleType.sum ≤ 5 := by
      simpa [Equiv.Perm.sum_cycleType] using σ.support.card_le_univ
    simpa [hn, hσord] using hsupp
  have hn0 : n = 0 := by
    omega
  -- A permutation of five letters with prime order `3` cannot split into two disjoint `3`-cycles,
  -- so its cycle type is exactly `{3}`.
  simpa [Equiv.Perm.IsThreeCycle, σ, hn, hσord, hn0]

/-- Helper for Exercise 18-18.6-5: the induced character takes the value `-1` on every order-`3`
element because those form one `A₅`-conjugacy class. -/
private theorem point_stabilizer_zero_induced_character_order_three
    (g : A5) (hg : orderOf g = 3) :
    Ind[MulAction.stabilizer A5 (0 : Fin 5)](
      point_stabilizer_zero_linear_character.toRepresentation.character) g = -1 := by
  have hg_three : Equiv.Perm.IsThreeCycle (((g : A5) : Equiv.Perm (Fin 5))) :=
    a5_isThreeCycle_of_order_three g hg
  have hconj : IsConj g three_cycle_rep := by
    simpa using
      alternatingGroup.isThreeCycle_isConj
        (α := Fin 5) (by decide : 5 ≤ Fintype.card (Fin 5))
        hg_three three_cycle_rep_isThreeCycle
  have hclass :
      IsClassFunction
        Ind[MulAction.stabilizer A5 (0 : Fin 5)](
          point_stabilizer_zero_linear_character.toRepresentation.character) :=
    Subgroup.inducedClassFunction_isClassFunction
      (H := MulAction.stabilizer A5 (0 : Fin 5))
      (f := point_stabilizer_zero_linear_character.toRepresentation.character)
  -- The induced character is a class function, so it suffices to compute one representative.
  calc
    Ind[MulAction.stabilizer A5 (0 : Fin 5)](
        point_stabilizer_zero_linear_character.toRepresentation.character) g
        =
          Ind[MulAction.stabilizer A5 (0 : Fin 5)](
            point_stabilizer_zero_linear_character.toRepresentation.character) three_cycle_rep := by
              exact hclass.eq_of_isConj hconj
    _ = -1 := point_stabilizer_zero_induced_character_three_cycle_rep

/-- Helper for Exercise 18-18.6-5: if an element has order different from `1`, `2`, and `3`, then
the induced character has no fixed-point contributions and hence vanishes on it. -/
private theorem point_stabilizer_zero_induced_character_eq_zero_of_order_ne_one_ne_two_ne_three
    (g : A5) (h1 : orderOf g ≠ 1) (h2 : orderOf g ≠ 2) (h3 : orderOf g ≠ 3) :
    Ind[MulAction.stabilizer A5 (0 : Fin 5)](
      point_stabilizer_zero_linear_character.toRepresentation.character) g = 0 := by
  rw [point_stabilizer_zero_induced_character_fixed_point_formula]
  refine Finset.sum_eq_zero ?_
  intro x hx
  by_cases hfix : g • x = x
  · have hA4_orders :
        orderOf
            (point_stabilizer_zero_mulEquiv_a4
              (point_stabilizer_zero_transported_element g x hfix)) = 1 ∨
          orderOf
              (point_stabilizer_zero_mulEquiv_a4
                (point_stabilizer_zero_transported_element g x hfix)) = 2 ∨
            orderOf
                (point_stabilizer_zero_mulEquiv_a4
                  (point_stabilizer_zero_transported_element g x hfix)) = 3 :=
      a4_orderOf_eq_one_or_two_or_three
        (point_stabilizer_zero_mulEquiv_a4
          (point_stabilizer_zero_transported_element g x hfix))
    have htransport_orders :
        orderOf (point_stabilizer_zero_transported_element g x hfix) = 1 ∨
          orderOf (point_stabilizer_zero_transported_element g x hfix) = 2 ∨
            orderOf (point_stabilizer_zero_transported_element g x hfix) = 3 := by
      rcases hA4_orders with hA4 | hA4 | hA4
      · left
        exact
          (point_stabilizer_zero_mulEquiv_a4.orderOf_eq
            (point_stabilizer_zero_transported_element g x hfix)).symm.trans hA4
      · right
        left
        exact
          (point_stabilizer_zero_mulEquiv_a4.orderOf_eq
            (point_stabilizer_zero_transported_element g x hfix)).symm.trans hA4
      · right
        right
        exact
          (point_stabilizer_zero_mulEquiv_a4.orderOf_eq
            (point_stabilizer_zero_transported_element g x hfix)).symm.trans hA4
    have hg_orders : orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 := by
      simpa [point_stabilizer_zero_transported_element_orderOf g x hfix] using htransport_orders
    rcases hg_orders with hg1 | hg2 | hg3
    · exact (h1 hg1).elim
    · exact (h2 hg2).elim
    · exact (h3 hg3).elim
  · -- If `g` does not fix `x`, the corresponding summand is zero by definition.
    simp [hfix]

/-- Helper for Exercise 18-18.6-5: the induced character from the nontrivial point-stabilizer
linear character is exactly LinearRepresentations_Serre_1977's row `χ₅`. -/
private theorem point_stabilizer_zero_induced_character_eq_chi5 :
    Ind[MulAction.stabilizer A5 (0 : Fin 5)](
      point_stabilizer_zero_linear_character.toRepresentation.character) = character .chi5 := by
  ext g
  by_cases h1 : orderOf g = 1
  · have hg1 : g = 1 := orderOf_eq_one_iff.mp h1
    subst hg1
    rw [point_stabilizer_zero_induced_character_fixed_point_formula, Fin.sum_univ_five]
    have hterm (x : Fin 5) :
        (if hfix : ((1 : A5) • x = x) then
          (point_stabilizer_zero_linear_character
            (point_stabilizer_zero_transported_element (1 : A5) x hfix) : ℂ)
        else 0) = 1 := by
      have hfix : (1 : A5) • x = x := by simp
      rw [dif_pos hfix]
      have hone :
          point_stabilizer_zero_transported_element (1 : A5) x hfix = 1 := by
        -- Conjugating the identity by any transport still gives the identity stabilizer element.
        apply Subtype.ext
        simp [point_stabilizer_zero_transported_element]
      simp [hone]
    rw [hterm 0, hterm 1, hterm 2, hterm 3, hterm 4]
    norm_num [OrdinaryIrreducible.character, conjugacyClass,
      alternating_group_five_ordinary_irreducible_character_table]
  · by_cases h2 : orderOf g = 2
    · rw [point_stabilizer_zero_induced_character_order_two g h2]
      norm_num [OrdinaryIrreducible.character, conjugacyClass, h1, h2,
        alternating_group_five_ordinary_irreducible_character_table]
    · by_cases h3 : orderOf g = 3
      · rw [point_stabilizer_zero_induced_character_order_three g h3]
        norm_num [OrdinaryIrreducible.character, conjugacyClass, h1, h2, h3,
          alternating_group_five_ordinary_irreducible_character_table]
      · rw [point_stabilizer_zero_induced_character_eq_zero_of_order_ne_one_ne_two_ne_three
          g h1 h2 h3]
        simp only [OrdinaryIrreducible.character, conjugacyClass, h1, h2, h3,
          alternating_group_five_ordinary_irreducible_character_table]
        split_ifs <;> simp_all

-- Proof sketch: use the index-`5` subgroup `A₄ ≤ A₅` and a nontrivial linear character on that
-- stabilizer to recover the row `χ₅`.
/-- Exercise 18-18.6-5 (1): LinearRepresentations_Serre_1977's labeled ordinary character `χ₅` of `A₅` is monomial. -/
theorem chi5_isMonomialCharacter :
    IsMonomialCharacter (character .chi5) := by
  let H : Subgroup A5 := MulAction.stabilizer A5 (0 : Fin 5)
  let α : H →* ℂˣ := point_stabilizer_zero_linear_character
  have hχ :
      Ind[H](α.toRepresentation.character) = character .chi5 := by
    -- Route correction: finish LinearRepresentations_Serre_1977's subgroup route by identifying the induced character with
    -- the table row `χ₅` through the explicit five-point transport sum.
    simpa [H, α] using point_stabilizer_zero_induced_character_eq_chi5
  -- The monomial witness is exactly the nontrivial linear character on the point stabilizer.
  simpa [hχ] using Representation.isMonomialCharacter_of_induced H α

-- Proof sketch: inspect the characters induced from degree-`1` subgroup characters and compare
-- them with the degree-`3` row taking values `(φ, ψ)` on the split `5`-cycle classes.
/-- Exercise 18-18.6-5 (2): the degree-`3` labeled ordinary character of `A₅` taking the values
`(φ, ψ)` on the split `5`-cycle classes, one of LinearRepresentations_Serre_1977's rows `χ₂`, `χ₃`, is not monomial. -/
theorem chi3_phi_psi_not_isMonomialCharacter :
    ¬ IsMonomialCharacter (character .chi3_phi_psi) := by
  intro hmono
  rcases monomial_subgroup_index_eq_character_one (character .chi3_phi_psi) hmono with
    ⟨H, hH⟩
  -- Read the degree of `χ₃` from the identity column of LinearRepresentations_Serre_1977's table.
  have hχ : character .chi3_phi_psi 1 = 3 := by
    norm_num [OrdinaryIrreducible.character, conjugacyClass,
      alternating_group_five_ordinary_irreducible_character_table]
  have hindexC : (H.index : ℂ) = 3 := by
    calc
      (H.index : ℂ) = character .chi3_phi_psi 1 := hH
      _ = 3 := hχ
  have hindex : H.index = 3 := by
    exact_mod_cast hindexC
  exact no_subgroup_of_a5_index_three_or_four (n := 3) (Or.inl rfl) ⟨H, hindex⟩

-- Proof sketch: the same induced-character classification excludes the conjugate degree-`3` row
-- taking the values `(ψ, φ)` on the two split `5`-cycle classes.
/-- Exercise 18-18.6-5 (2): the degree-`3` labeled ordinary character of `A₅` taking the values
`(ψ, φ)` on the split `5`-cycle classes, the other of LinearRepresentations_Serre_1977's rows `χ₂`, `χ₃`, is not monomial. -/
theorem chi3_psi_phi_not_isMonomialCharacter :
    ¬ IsMonomialCharacter (character .chi3_psi_phi) := by
  intro hmono
  rcases monomial_subgroup_index_eq_character_one (character .chi3_psi_phi) hmono with
    ⟨H, hH⟩
  -- The conjugate degree-`3` row has the same degree at the identity.
  have hχ : character .chi3_psi_phi 1 = 3 := by
    norm_num [OrdinaryIrreducible.character, conjugacyClass,
      alternating_group_five_ordinary_irreducible_character_table]
  have hindexC : (H.index : ℂ) = 3 := by
    calc
      (H.index : ℂ) = character .chi3_psi_phi 1 := hH
      _ = 3 := hχ
  have hindex : H.index = 3 := by
    exact_mod_cast hindexC
  exact no_subgroup_of_a5_index_three_or_four (n := 3) (Or.inl rfl) ⟨H, hindex⟩

-- Proof sketch: compare the degree-`4` row with the same list of subgroup-induced linear
-- characters and note that no such induced character has those values.
/-- Exercise 18-18.6-5 (3): LinearRepresentations_Serre_1977's labeled ordinary character `χ₄` of `A₅` is not monomial. -/
theorem chi4_not_isMonomialCharacter :
    ¬ IsMonomialCharacter (character .chi4) := by
  intro hmono
  rcases monomial_subgroup_index_eq_character_one (character .chi4) hmono with ⟨H, hH⟩
  -- Read the degree of `χ₄` from the identity column of LinearRepresentations_Serre_1977's table.
  have hχ : character .chi4 1 = 4 := by
    norm_num [OrdinaryIrreducible.character, conjugacyClass,
      alternating_group_five_ordinary_irreducible_character_table]
  have hindexC : (H.index : ℂ) = 4 := by
    calc
      (H.index : ℂ) = character .chi4 1 := hH
      _ = 4 := hχ
  have hindex : H.index = 4 := by
    exact_mod_cast hindexC
  exact no_subgroup_of_a5_index_three_or_four (n := 4) (Or.inr rfl) ⟨H, hindex⟩

end OrdinaryIrreducible

/-! ### Remark_18_18_6_1 (from Chap18) -/
noncomputable section

open Equiv.Perm Matrix
open scoped goldenRatio

namespace AlternatingGroupFive

/-- The ordinary irreducible characters used in LinearRepresentations_Serre_1977's `A₅` example. The two degree-`3`
characters are distinguished by their values `(φ, ψ)` and `(ψ, φ)` on the two `5`-cycle
classes. -/
inductive OrdinaryIrreducible
  | chi1
  | chi3_phi_psi
  | chi3_psi_phi
  | chi4
  | chi5
  deriving DecidableEq, Fintype

/-- The conjugacy-class labels for LinearRepresentations_Serre_1977's ordinary character table of `A₅`. The two `5`-cycle
classes are ordered so that `OrdinaryIrreducible.chi3_phi_psi` takes the values `φ` and `ψ` on
`fiveCycle_phi` and `fiveCycle_psi`, respectively. -/
inductive ConjugacyClass
  | identity
  | doubleTransposition
  | threeCycle
  | fiveCycle_phi
  | fiveCycle_psi
  deriving DecidableEq, Fintype

/-- The common ordered labels for the `p = 2` irreducible Brauer characters of `A₅` and the
corresponding indecomposable projective classes. This is the row index of the `p = 2`
decomposition matrix and, in the chapter's `cartanMatrix` convention, both the row and column
index of the `p = 2` Cartan matrix. The two degree-`2` labels are distinguished by which
degree-`3` ordinary character appears in their decomposition row. -/
inductive BrauerProjectiveModTwo
  | trivial
  | degreeTwo_from_chi3_phi_psi
  | degreeTwo_from_chi3_psi_phi
  | degreeFour
  deriving DecidableEq, Fintype

/-- The common ordered labels for the `p = 3` irreducible Brauer characters of `A₅` and the
corresponding indecomposable projective classes. This is the row index of the `p = 3`
decomposition matrix and, in the chapter's `cartanMatrix` convention, both the row and column
index of the `p = 3` Cartan matrix. The two degree-`3` labels are distinguished by the matching
ordinary degree-`3` character. -/
inductive BrauerProjectiveModThree
  | trivial
  | degreeThree_from_chi3_phi_psi
  | degreeThree_from_chi3_psi_phi
  | degreeFour
  deriving DecidableEq, Fintype

/-- The common ordered labels for the `p = 5` irreducible Brauer characters of `A₅` and the
corresponding indecomposable projective classes. This is the row index of the `p = 5`
decomposition matrix and, in the chapter's `cartanMatrix` convention, both the row and column
index of the `p = 5` Cartan matrix. -/
inductive BrauerProjectiveModFive
  | trivial
  | degreeThree
  | degreeFive
  deriving DecidableEq, Fintype

end AlternatingGroupFive

open AlternatingGroupFive

local notation "A5" => alternatingGroup (Fin 5)

/- Domain-style sampling for this remark:
* primary domain: modular representation theory of finite groups, specialized here to LinearRepresentations_Serre_1977's
  explicit `A₅` ordinary-character, decomposition, and Cartan tables;
* relevant owner declarations inspected upstream in the chapter/project:
  `Representation.decompositionHom`,
  `Representation.cartanHom`,
  `Representation.cartanMatrix`,
  `Representation.decompositionHom_toMatrix_eq_one_of_order_prime_to_p`;
* best owner abstraction for this file: LinearRepresentations_Serre_1977's tables are source-facing matrix data, but their
  indices should be the chapter's ordinary-simple and Brauer/projective basis labels rather than
  anonymous `Fin` coordinates;
* source/core/bridge triage:
  source-facing: these explicit `A₅` tables with LinearRepresentations_Serre_1977's chosen basis orderings;
  core/canonical: the chapter-level decomposition and Cartan owners determining the orientation of
    those basis labels;
  bridge/view: this file stays at the explicit table layer, so the Cartan matrices remain derived
    matrix companions `D * Dᵀ` of the recorded decomposition matrices.

Primitive data vs derived API:
* primitive data: the labeled ordinary irreducible character table and the three labeled
  decomposition matrices;
* derived API: the source-facing bridge from those labels to actual class functions on `A₅`,
  together with the three Cartan matrices and their explicit-value and determinant lemmas.
-/

/-- The ordinary irreducible character table of `A₅` in LinearRepresentations_Serre_1977's example, with rows indexed by the
labeled ordinary irreducible characters and columns indexed by the labeled conjugacy classes. -/
def alternating_group_five_ordinary_irreducible_character_table :
    Matrix OrdinaryIrreducible ConjugacyClass ℝ
  | .chi1, .identity => 1
  | .chi1, .doubleTransposition => 1
  | .chi1, .threeCycle => 1
  | .chi1, .fiveCycle_phi => 1
  | .chi1, .fiveCycle_psi => 1
  | .chi3_phi_psi, .identity => 3
  | .chi3_phi_psi, .doubleTransposition => -1
  | .chi3_phi_psi, .threeCycle => 0
  | .chi3_phi_psi, .fiveCycle_phi => φ
  | .chi3_phi_psi, .fiveCycle_psi => ψ
  | .chi3_psi_phi, .identity => 3
  | .chi3_psi_phi, .doubleTransposition => -1
  | .chi3_psi_phi, .threeCycle => 0
  | .chi3_psi_phi, .fiveCycle_phi => ψ
  | .chi3_psi_phi, .fiveCycle_psi => φ
  | .chi4, .identity => 4
  | .chi4, .doubleTransposition => 0
  | .chi4, .threeCycle => 1
  | .chi4, .fiveCycle_phi => -1
  | .chi4, .fiveCycle_psi => -1
  | .chi5, .identity => 5
  | .chi5, .doubleTransposition => 1
  | .chi5, .threeCycle => -1
  | .chi5, .fiveCycle_phi => 0
  | .chi5, .fiveCycle_psi => 0

/-- A fixed representative of the `fiveCycle_phi` column in LinearRepresentations_Serre_1977's split `5`-cycle ordering for
the ordinary character table of `A₅`. -/
private def fiveCyclePhiRepresentative : A5 :=
  ⟨finRotate 5, by
    have h : finRotate (2 * 2 + 1) ∈ alternatingGroup (Fin (2 * 2 + 1)) :=
      finRotate_bit1_mem_alternatingGroup
    simpa using h⟩

/-- The labeled conjugacy class of an element of `A₅` in LinearRepresentations_Serre_1977's ordinary character table. The
two split `5`-cycle classes are ordered so that `OrdinaryIrreducible.chi3_phi_psi` has values
`(φ, ψ)` on `fiveCycle_phi` and `fiveCycle_psi`. -/
def conjugacyClass (g : A5) : ConjugacyClass :=
  if orderOf g = 1 then .identity
  else if orderOf g = 2 then .doubleTransposition
  else if orderOf g = 3 then .threeCycle
  else if IsConj g fiveCyclePhiRepresentative then .fiveCycle_phi
  else .fiveCycle_psi

namespace OrdinaryIrreducible

/-- The ordinary complex character of `A₅` attached to one of LinearRepresentations_Serre_1977's labeled rows in the
ordinary character table from `Remark 18-18.6-1`. -/
def character (χ : OrdinaryIrreducible) : A5 → ℂ :=
  fun g ↦ (alternating_group_five_ordinary_irreducible_character_table χ (conjugacyClass g) : ℂ)

@[simp] theorem character_apply (χ : OrdinaryIrreducible) (g : A5) :
    character χ g =
      (alternating_group_five_ordinary_irreducible_character_table χ (conjugacyClass g) : ℂ) :=
  rfl

end OrdinaryIrreducible

/-- The `p = 2` decomposition matrix in LinearRepresentations_Serre_1977's modular-character example for `A₅`, with rows
indexed by the ordered `p = 2` Brauer/projective labels and columns indexed by the ordered
ordinary irreducible labels. -/
def alternating_group_five_decomposition_matrix_mod_two :
    Matrix BrauerProjectiveModTwo OrdinaryIrreducible ℤ
  | .trivial, .chi1 => 1
  | .trivial, .chi3_phi_psi => 1
  | .trivial, .chi3_psi_phi => 1
  | .trivial, .chi4 => 0
  | .trivial, .chi5 => 1
  | .degreeTwo_from_chi3_phi_psi, .chi1 => 0
  | .degreeTwo_from_chi3_phi_psi, .chi3_phi_psi => 1
  | .degreeTwo_from_chi3_phi_psi, .chi3_psi_phi => 0
  | .degreeTwo_from_chi3_phi_psi, .chi4 => 0
  | .degreeTwo_from_chi3_phi_psi, .chi5 => 1
  | .degreeTwo_from_chi3_psi_phi, .chi1 => 0
  | .degreeTwo_from_chi3_psi_phi, .chi3_phi_psi => 0
  | .degreeTwo_from_chi3_psi_phi, .chi3_psi_phi => 1
  | .degreeTwo_from_chi3_psi_phi, .chi4 => 0
  | .degreeTwo_from_chi3_psi_phi, .chi5 => 1
  | .degreeFour, .chi1 => 0
  | .degreeFour, .chi3_phi_psi => 0
  | .degreeFour, .chi3_psi_phi => 0
  | .degreeFour, .chi4 => 1
  | .degreeFour, .chi5 => 0

/-- The `p = 2` Cartan matrix in LinearRepresentations_Serre_1977's modular-character example for `A₅`. Its rows are indexed
by the chosen `p = 2` Brauer-character labels, and its columns by the corresponding projective
indecomposable labels in the same order. -/
def alternating_group_five_cartan_matrix_mod_two :
    Matrix BrauerProjectiveModTwo BrauerProjectiveModTwo ℤ :=
  alternating_group_five_decomposition_matrix_mod_two *
    alternating_group_five_decomposition_matrix_mod_twoᵀ

/-- The `p = 2` Cartan matrix for `A₅` is the Gram matrix of the recorded decomposition matrix in
the chosen Brauer/projective basis order. -/
theorem alternating_group_five_cartan_matrix_mod_two_eq :
    alternating_group_five_cartan_matrix_mod_two =
      fun i j ↦
        match i, j with
        | .trivial, .trivial => 4
        | .trivial, .degreeTwo_from_chi3_phi_psi => 2
        | .trivial, .degreeTwo_from_chi3_psi_phi => 2
        | .trivial, .degreeFour => 0
        | .degreeTwo_from_chi3_phi_psi, .trivial => 2
        | .degreeTwo_from_chi3_phi_psi, .degreeTwo_from_chi3_phi_psi => 2
        | .degreeTwo_from_chi3_phi_psi, .degreeTwo_from_chi3_psi_phi => 1
        | .degreeTwo_from_chi3_phi_psi, .degreeFour => 0
        | .degreeTwo_from_chi3_psi_phi, .trivial => 2
        | .degreeTwo_from_chi3_psi_phi, .degreeTwo_from_chi3_phi_psi => 1
        | .degreeTwo_from_chi3_psi_phi, .degreeTwo_from_chi3_psi_phi => 2
        | .degreeTwo_from_chi3_psi_phi, .degreeFour => 0
        | .degreeFour, .trivial => 0
        | .degreeFour, .degreeTwo_from_chi3_phi_psi => 0
        | .degreeFour, .degreeTwo_from_chi3_psi_phi => 0
        | .degreeFour, .degreeFour => 1 := by
  decide

/-- The determinant of LinearRepresentations_Serre_1977's `p = 2` Cartan matrix for `A₅` is `4`. -/
theorem alternating_group_five_cartan_matrix_mod_two_det :
    det alternating_group_five_cartan_matrix_mod_two = 4 := by
  decide

/-- The `p = 3` decomposition matrix in LinearRepresentations_Serre_1977's modular-character example for `A₅`, with rows
indexed by the ordered `p = 3` Brauer/projective labels and columns indexed by the ordered
ordinary irreducible labels. -/
def alternating_group_five_decomposition_matrix_mod_three :
    Matrix BrauerProjectiveModThree OrdinaryIrreducible ℤ
  | .trivial, .chi1 => 1
  | .trivial, .chi3_phi_psi => 0
  | .trivial, .chi3_psi_phi => 0
  | .trivial, .chi4 => 0
  | .trivial, .chi5 => 1
  | .degreeThree_from_chi3_phi_psi, .chi1 => 0
  | .degreeThree_from_chi3_phi_psi, .chi3_phi_psi => 1
  | .degreeThree_from_chi3_phi_psi, .chi3_psi_phi => 0
  | .degreeThree_from_chi3_phi_psi, .chi4 => 0
  | .degreeThree_from_chi3_phi_psi, .chi5 => 0
  | .degreeThree_from_chi3_psi_phi, .chi1 => 0
  | .degreeThree_from_chi3_psi_phi, .chi3_phi_psi => 0
  | .degreeThree_from_chi3_psi_phi, .chi3_psi_phi => 1
  | .degreeThree_from_chi3_psi_phi, .chi4 => 0
  | .degreeThree_from_chi3_psi_phi, .chi5 => 0
  | .degreeFour, .chi1 => 0
  | .degreeFour, .chi3_phi_psi => 0
  | .degreeFour, .chi3_psi_phi => 0
  | .degreeFour, .chi4 => 1
  | .degreeFour, .chi5 => 1

/-- The `p = 3` Cartan matrix in LinearRepresentations_Serre_1977's modular-character example for `A₅`. Its rows are indexed
by the chosen `p = 3` Brauer-character labels, and its columns by the corresponding projective
indecomposable labels in the same order. -/
def alternating_group_five_cartan_matrix_mod_three :
    Matrix BrauerProjectiveModThree BrauerProjectiveModThree ℤ :=
  alternating_group_five_decomposition_matrix_mod_three *
    alternating_group_five_decomposition_matrix_mod_threeᵀ

/-- The `p = 3` Cartan matrix for `A₅` is the Gram matrix of the recorded decomposition matrix in
the chosen Brauer/projective basis order. -/
theorem alternating_group_five_cartan_matrix_mod_three_eq :
    alternating_group_five_cartan_matrix_mod_three =
      fun i j ↦
        match i, j with
        | .trivial, .trivial => 2
        | .trivial, .degreeThree_from_chi3_phi_psi => 0
        | .trivial, .degreeThree_from_chi3_psi_phi => 0
        | .trivial, .degreeFour => 1
        | .degreeThree_from_chi3_phi_psi, .trivial => 0
        | .degreeThree_from_chi3_phi_psi, .degreeThree_from_chi3_phi_psi => 1
        | .degreeThree_from_chi3_phi_psi, .degreeThree_from_chi3_psi_phi => 0
        | .degreeThree_from_chi3_phi_psi, .degreeFour => 0
        | .degreeThree_from_chi3_psi_phi, .trivial => 0
        | .degreeThree_from_chi3_psi_phi, .degreeThree_from_chi3_phi_psi => 0
        | .degreeThree_from_chi3_psi_phi, .degreeThree_from_chi3_psi_phi => 1
        | .degreeThree_from_chi3_psi_phi, .degreeFour => 0
        | .degreeFour, .trivial => 1
        | .degreeFour, .degreeThree_from_chi3_phi_psi => 0
        | .degreeFour, .degreeThree_from_chi3_psi_phi => 0
        | .degreeFour, .degreeFour => 2 := by
  decide

/-- The determinant of LinearRepresentations_Serre_1977's `p = 3` Cartan matrix for `A₅` is `3`. -/
theorem alternating_group_five_cartan_matrix_mod_three_det :
    det alternating_group_five_cartan_matrix_mod_three = 3 := by
  decide

/-- The `p = 5` decomposition matrix in LinearRepresentations_Serre_1977's modular-character example for `A₅`, with rows
indexed by the ordered `p = 5` Brauer/projective labels and columns indexed by the ordered
ordinary irreducible labels. -/
def alternating_group_five_decomposition_matrix_mod_five :
    Matrix BrauerProjectiveModFive OrdinaryIrreducible ℤ
  | .trivial, .chi1 => 1
  | .trivial, .chi3_phi_psi => 0
  | .trivial, .chi3_psi_phi => 0
  | .trivial, .chi4 => 1
  | .trivial, .chi5 => 0
  | .degreeThree, .chi1 => 0
  | .degreeThree, .chi3_phi_psi => 1
  | .degreeThree, .chi3_psi_phi => 1
  | .degreeThree, .chi4 => 1
  | .degreeThree, .chi5 => 0
  | .degreeFive, .chi1 => 0
  | .degreeFive, .chi3_phi_psi => 0
  | .degreeFive, .chi3_psi_phi => 0
  | .degreeFive, .chi4 => 0
  | .degreeFive, .chi5 => 1

/-- The `p = 5` Cartan matrix in LinearRepresentations_Serre_1977's modular-character example for `A₅`. Its rows are indexed
by the chosen `p = 5` Brauer-character labels, and its columns by the corresponding projective
indecomposable labels in the same order. -/
def alternating_group_five_cartan_matrix_mod_five :
    Matrix BrauerProjectiveModFive BrauerProjectiveModFive ℤ :=
  alternating_group_five_decomposition_matrix_mod_five *
    alternating_group_five_decomposition_matrix_mod_fiveᵀ

/-- The `p = 5` Cartan matrix for `A₅` is the Gram matrix of the recorded decomposition matrix in
the chosen Brauer/projective basis order. -/
theorem alternating_group_five_cartan_matrix_mod_five_eq :
    alternating_group_five_cartan_matrix_mod_five =
      fun i j ↦
        match i, j with
        | .trivial, .trivial => 2
        | .trivial, .degreeThree => 1
        | .trivial, .degreeFive => 0
        | .degreeThree, .trivial => 1
        | .degreeThree, .degreeThree => 3
        | .degreeThree, .degreeFive => 0
        | .degreeFive, .trivial => 0
        | .degreeFive, .degreeThree => 0
        | .degreeFive, .degreeFive => 1 := by
  decide

/-- The determinant of LinearRepresentations_Serre_1977's `p = 5` Cartan matrix for `A₅` is `5`. -/
theorem alternating_group_five_cartan_matrix_mod_five_det :
    det alternating_group_five_cartan_matrix_mod_five = 5 := by
  decide

/- Remark 18-18.6-1 records LinearRepresentations_Serre_1977's `A₅` example: the labeled ordinary irreducible character
table and, for `p = 2`, `3`, and `5`, the labeled decomposition matrices together with the
corresponding Cartan matrices, defined canonically as `D * Dᵀ` in the chapter's
Brauer/projective basis conventions. -/
