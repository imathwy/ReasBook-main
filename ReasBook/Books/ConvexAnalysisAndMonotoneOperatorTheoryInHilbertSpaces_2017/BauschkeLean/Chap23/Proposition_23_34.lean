import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap20.Proposition_20_24
import BauschkeLean.Chap23.Corollary_23_11

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

open ContinuousLinearMap
open ContinuousLinearMap.Renormed
open ERealFunction

variable {H : Type u}

/- Source/core/bridge triage:
- `source-facing`: Proposition 23.34 studies the resolvent of the left-composed operator `U A`
  for a self-adjoint strongly monotone linear map `U`.
- `core/canonical`: the Chapter 20/23 owners are the renormed operator
  `(U.toSetValuedOperator.comp A).renormed U hU_self hU_strong`, the resolvent surfaces `J[...]`
  and `resolventMap`, and the Chapter 16 bridge `ContinuousLinearMap.adjointImage`.
- `bridge/view`: the inverse-sum, square-root, and inverse-resolvent formulas are source-facing
  views of that canonical resolvent.

Domain-style sampling:
- `Chap20/Proposition_20_24.lean`: `SetValuedOperator.renormed` and
  `comp_isMaximallyMonotone_of_isSelfAdjoint_of_isStronglyMonotone` give the ambient owner for
  `U A`.
- `Chap23/Corollary_23_11.lean`: `resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq`
  and `resolventMap_toSetValuedOperator_eq` are the canonical resolvent-realizer API.
- `Chap23/Proposition_23_25.lean`:
  `resolvent_adjointImage_eq_id_sub_adjointImage_inverse_comp_adjoint_add_inverse` is the chapter
  owner for adjoint-image resolvent algebra.
- `Chap23/Proposition_23_20.lean`: `resolvent_inverse_eq_id_sub_resolvent` is the canonical
  inverse-resolvent identity used in the same calculus layer.

Primitive data vs derived API:
- primitive data: clause (1) uses `A`, `hA`, `U`, `hU_self`, and `hU_strong`; clauses (2) and
  (4) use only the invertibility of `U`; clause (3) uses the explicit square-root equivalence
  witness `L`, where positivity records that `L` is the source's `U^(1/2)` rather than an
  arbitrary square witness;
- derived API: firm nonexpansiveness of the induced resolvent realizer and the three algebraic
  resolvent identities below. -/

section Operator

variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Proposition 23.34: in the unscaled `γ = 1` case, resolvent membership is exactly
the residual membership condition `x - p ∈ B p`. -/
private theorem mem_resolvent_iff_sub_mem
    {B : SetValuedOperator H H} {x p : H} :
    p ∈ J[B] x ↔ x - p ∈ B p := by
  -- Specialize the scaled resolvent criterion to the scale `γ = 1`.
  simpa using (mem_resolvent_smul_iff_sub_mem_smul B (1 : PosReal) x p)

/-- Helper for Proposition 23.34: membership in `J[(U.toSetValuedOperator.comp A)] x` is
equivalent to a witness `v ∈ A p` with residual equation `x - p = U v`. -/
private theorem mem_resolvent_comp_iff_exists_sub_eq_apply
    {A : SetValuedOperator H H} (U : H →L[ℝ] H) {x p : H} :
    p ∈ J[(U.toSetValuedOperator.comp A)] x ↔ ∃ v ∈ A p, x - p = U v := by
  -- Unfold the resolvent once and read the singleton-valued `U` witness explicitly.
  have hres :
      p ∈ J[(U.toSetValuedOperator.comp A)] x ↔
        x - p ∈ (1 : ℝ) • (U.toSetValuedOperator.comp A) p := by
    simpa using
      (mem_resolvent_smul_iff_sub_mem_smul (U.toSetValuedOperator.comp A) (1 : PosReal) x p)
  rw [hres]
  rw [one_smul, SetValuedOperator.mem_comp]
  constructor
  · rintro ⟨v, hv, hres⟩
    rw [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply,
      Set.mem_singleton_iff] at hres
    exact ⟨v, hv, hres⟩
  · rintro ⟨v, hv, hres⟩
    refine ⟨v, hv, ?_⟩
    rw [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply]
    simp [hres]

/-- Helper for Proposition 23.34: the resolvent of `U A` is equivalent to the inverse residual
condition `ContinuousLinearMap.inverse U (x - p) ∈ A p`. -/
private theorem mem_resolvent_comp_iff_inverse_sub_mem
    {A : SetValuedOperator H H} (U : H →L[ℝ] H) (hU_inv : U.IsInvertible) {x p : H} :
    p ∈ J[(U.toSetValuedOperator.comp A)] x ↔ ContinuousLinearMap.inverse U (x - p) ∈ A p := by
  -- Convert the explicit `U`-witness into the unique inverse image under `U`.
  rw [mem_resolvent_comp_iff_exists_sub_eq_apply (A := A) U]
  constructor
  · rintro ⟨v, hv, hres⟩
    have hvEq : ContinuousLinearMap.inverse U (x - p) = v := by
      simpa using (hU_inv.inverse_apply_eq (x := v) (y := x - p)).2 hres
    simpa [hvEq] using hv
  · intro hp
    refine ⟨ContinuousLinearMap.inverse U (x - p), hp, ?_⟩
    simpa [ContinuousLinearMap.map_sub] using (hU_inv.self_apply_inverse (x - p)).symm

/-- Helper for Proposition 23.34: membership in `((U⁻¹ + A)⁻¹) ∘ U⁻¹` has the same inverse
residual normal form as `J[(U.toSetValuedOperator.comp A)]`. -/
private theorem mem_inverse_add_inverse_comp_iff_inverse_sub_mem
    {A : SetValuedOperator H H} (U : H →L[ℝ] H) {x p : H} :
    p ∈ (((ContinuousLinearMap.inverse U).toSetValuedOperator + A)⁻¹).comp
        (ContinuousLinearMap.inverse U).toSetValuedOperator x ↔
      ContinuousLinearMap.inverse U (x - p) ∈ A p := by
  -- Expand the composition and the inverse-sum once, then isolate the `A p` witness.
  rw [SetValuedOperator.mem_comp]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply,
      Set.mem_singleton_iff] at hy
    subst y
    rw [SetValuedOperator.mem_inverse_iff, Pi.add_apply, Set.mem_add] at hp
    rcases hp with ⟨u, hu, v, hv, huv⟩
    rw [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply,
      Set.mem_singleton_iff] at hu
    subst u
    have hvEq : v = ContinuousLinearMap.inverse U (x - p) := by
      have hsub := congrArg (fun t : H ↦ t - ContinuousLinearMap.inverse U p) huv
      simpa [ContinuousLinearMap.map_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hsub
    simpa [hvEq] using hv
  · intro hp
    refine ⟨ContinuousLinearMap.inverse U x, ?_, ?_⟩
    · simp [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply]
    · rw [SetValuedOperator.mem_inverse_iff, Pi.add_apply, Set.mem_add]
      refine ⟨ContinuousLinearMap.inverse U p, ?_, ContinuousLinearMap.inverse U (x - p), hp, ?_⟩
      · simp [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply]
      · calc
          ContinuousLinearMap.inverse U p + ContinuousLinearMap.inverse U (x - p)
              = ContinuousLinearMap.inverse U (p + (x - p)) := by
                  rw [← ContinuousLinearMap.map_add]
          _ = ContinuousLinearMap.inverse U x := by
                congr 1
                abel_nf

/-- Clause (2) of Proposition 23.34: once `U` is invertible, the algebraic resolvent identity
for the left-composed operator `UA`, realized as `U.toSetValuedOperator.comp A`, is
`(U⁻¹ + A)⁻¹ ∘ U⁻¹`. -/
theorem resolvent_comp_eq_inverse_add_inverse_comp
    {A : SetValuedOperator H H} (U : H →L[ℝ] H) (hU_inv : U.IsInvertible) :
    J[(U.toSetValuedOperator.comp A)] =
      (((ContinuousLinearMap.inverse U).toSetValuedOperator + A)⁻¹).comp
        (ContinuousLinearMap.inverse U).toSetValuedOperator := by
  ext x p
  -- Compare both sides through the same inverse-residual normal form.
  rw [mem_resolvent_comp_iff_inverse_sub_mem (A := A) U hU_inv]
  rw [mem_inverse_add_inverse_comp_iff_inverse_sub_mem (A := A) U]

/-- Helper for Proposition 23.34: membership in
`Id - U ∘ J[((ContinuousLinearMap.inverse U).toSetValuedOperator.comp A⁻¹)] ∘ U⁻¹`
is equivalent to the inverse residual condition `ContinuousLinearMap.inverse U (x - p) ∈ A p`. -/
private theorem mem_id_sub_comp_resolvent_inverse_comp_inverse_iff_inverse_sub_mem
    {A : SetValuedOperator H H} (U : H →L[ℝ] H) (hU_inv : U.IsInvertible) {x p : H} :
    p ∈ ((((id : H → H).toSetValuedOperator -
        (U.toSetValuedOperator.comp
          J[((ContinuousLinearMap.inverse U).toSetValuedOperator.comp A⁻¹)]).comp
          (ContinuousLinearMap.inverse U).toSetValuedOperator : SetValuedOperator H H)) x) ↔
      ContinuousLinearMap.inverse U (x - p) ∈ A p := by
  rw [Pi.sub_apply, Set.mem_sub]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    -- Read the outer subtraction witness as `z = U r` with `r` in the inner resolvent.
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hy
    subst y
    rw [SetValuedOperator.mem_comp] at hz
    rcases hz with ⟨q, hq, hz⟩
    rw [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply,
      Set.mem_singleton_iff] at hq
    subst q
    rw [SetValuedOperator.mem_comp] at hz
    rcases hz with ⟨r, hr, hz⟩
    rw [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply,
      Set.mem_singleton_iff] at hz
    have hzEq : U r = x - p := by
      have hzShift : x - (x - z) = x - p := by
        simpa using congrArg (fun t : H ↦ x - t) hyz
      calc
        U r = z := hz.symm
        _ = x - p := by
              calc
                z = x - (x - z) := by abel_nf
                _ = x - p := hzShift
    have hrEq : ContinuousLinearMap.inverse U (x - p) = r := by
      simpa using (hU_inv.inverse_apply_eq (x := r) (y := x - p)).2 hzEq.symm
    have hr_mem :
        ContinuousLinearMap.inverse U x - r ∈
          ((ContinuousLinearMap.inverse U).toSetValuedOperator.comp A⁻¹) r :=
      (mem_resolvent_iff_sub_mem
        (B := ((ContinuousLinearMap.inverse U).toSetValuedOperator.comp A⁻¹))
        (x := ContinuousLinearMap.inverse U x) (p := r)).1 hr
    rw [SetValuedOperator.mem_comp] at hr_mem
    rcases hr_mem with ⟨v, hv, hvEq⟩
    rw [SetValuedOperator.mem_inverse_iff] at hv
    rw [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply,
      Set.mem_singleton_iff] at hvEq
    have hvA : ContinuousLinearMap.inverse U (x - p) ∈ A v := by
      simpa [hrEq] using hv
    have hvEq' : ContinuousLinearMap.inverse U x -
        ContinuousLinearMap.inverse U (x - p) = ContinuousLinearMap.inverse U v := by
      simpa [hrEq] using hvEq
    have hxp : x - (x - p) = p := by
      abel_nf
    have hdiff : ContinuousLinearMap.inverse U x -
        ContinuousLinearMap.inverse U (x - p) = ContinuousLinearMap.inverse U p := by
      calc
        ContinuousLinearMap.inverse U x - ContinuousLinearMap.inverse U (x - p)
            = ContinuousLinearMap.inverse U (x - (x - p)) := by
                rw [← ContinuousLinearMap.map_sub]
        _ = ContinuousLinearMap.inverse U p := by rw [hxp]
    have hpv : p = v := by
      have happly :=
        congrArg U (hdiff.symm.trans hvEq')
      simpa [hU_inv.self_apply_inverse] using happly
    simpa [hpv] using hvA
  · intro hp
    -- Rebuild the same residual witness by choosing the canonical inverse image of `x - p`.
    refine ⟨x, ?_, x - p, ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · rw [SetValuedOperator.mem_comp]
      refine ⟨ContinuousLinearMap.inverse U x, ?_, ?_⟩
      · simp [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply]
      · rw [SetValuedOperator.mem_comp]
        refine ⟨ContinuousLinearMap.inverse U (x - p), ?_, ?_⟩
        · rw [mem_resolvent_iff_sub_mem]
          rw [SetValuedOperator.mem_comp]
          refine ⟨p, ?_, ?_⟩
          · simpa [SetValuedOperator.mem_inverse_iff] using hp
          · have hxp : x - (x - p) = p := by
              abel_nf
            rw [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply,
              Set.mem_singleton_iff]
            calc
              ContinuousLinearMap.inverse U x - ContinuousLinearMap.inverse U (x - p)
                  = ContinuousLinearMap.inverse U (x - (x - p)) := by
                      rw [← ContinuousLinearMap.map_sub]
              _ = ContinuousLinearMap.inverse U p := by rw [hxp]
        · simpa [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply] using
            (hU_inv.self_apply_inverse (x - p)).symm
    · abel_nf

/-- Proposition 23.34 (4): once `U` is invertible, the resolvent of `UA` also equals
`Id - U J_{U⁻¹ A⁻¹} U⁻¹`. -/
theorem resolvent_comp_eq_id_sub_comp_resolvent_inverse_comp_inverse
    {A : SetValuedOperator H H} (U : H →L[ℝ] H) (hU_inv : U.IsInvertible) :
    J[(U.toSetValuedOperator.comp A)] =
      id.toSetValuedOperator -
        (U.toSetValuedOperator.comp
          J[((ContinuousLinearMap.inverse U).toSetValuedOperator.comp A⁻¹)]).comp
          (ContinuousLinearMap.inverse U).toSetValuedOperator := by
  ext x p
  -- Compare both sides through the same inverse-residual normal form.
  rw [mem_resolvent_comp_iff_inverse_sub_mem (A := A) U hU_inv]
  rw [mem_id_sub_comp_resolvent_inverse_comp_inverse_iff_inverse_sub_mem
    (A := A) U hU_inv]

end Operator

section Hilbert

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 23.34: whole-space firm nonexpansiveness is the standard Hilbert-space
inequality `‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
private abbrev FirmlyNonexpansive (T : H → H) : Prop :=
  ∀ x y : H, ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y)

/-- Clause (1) of Proposition 23.34: if `A : H → 2^H` is maximally monotone and `U : H →L[ℝ] H` is
self-adjoint and strongly monotone, then the resolvent `J_{UA}` on the renormed Hilbert space
attached to `U`, realized as the canonical resolvent map of
`(U.toSetValuedOperator.comp A).renormed U hU_self hU_strong`, is firmly nonexpansive. -/
theorem resolvent_comp_firmlyNonexpansive_renormed
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (U : H →L[ℝ] H)
    (hU_self : IsSelfAdjoint U) {α : ℝ} (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    FirmlyNonexpansive
      (resolventMap ((U.toSetValuedOperator.comp A).renormed U hU_self hU_strong)
        (comp_isMaximallyMonotone_of_isSelfAdjoint_of_isStronglyMonotone
          A U hA hU_self hU_strong)
        (1 : PosReal)) := by
  let B := (U.toSetValuedOperator.comp A).renormed U hU_self hU_strong
  have hB : Maximal IsMonotone B :=
    comp_isMaximallyMonotone_of_isSelfAdjoint_of_isStronglyMonotone
      A U hA hU_self hU_strong
  simpa [B] using
    resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq
      B hB (1 : PosReal) (resolventMap B hB (1 : PosReal))
      (resolventMap_toSetValuedOperator_eq B hB (1 : PosReal))

/-- Helper for Proposition 23.34: membership in
`L ∘ J[(L.toContinuousLinearMap.adjointImage A)] ∘ L.symm`
is equivalent to the witness form `∃ v ∈ A p, x - p = U v`. -/
private theorem
    mem_squareRootWitness_comp_resolvent_adjointImage_comp_inverse_iff_exists_sub_eq_apply
    {A : SetValuedOperator H H} (U : H →L[ℝ] H) (L : H ≃L[ℝ] H)
    (hL_pos : L.toContinuousLinearMap.IsPositive)
    (hL_sq : L.toContinuousLinearMap.comp L.toContinuousLinearMap = U) {x p : H} :
    p ∈ (((Function.toSetValuedOperator L).comp
      J[(L.toContinuousLinearMap.adjointImage A)]).comp
      (Function.toSetValuedOperator L.symm)) x ↔
      ∃ v ∈ A p, x - p = U v := by
  have hAdj : L.toContinuousLinearMap.adjoint = L.toContinuousLinearMap :=
    hL_pos.isSelfAdjoint.adjoint_eq
  constructor
  · intro hp
    -- Unpack the conjugated resolvent and transport the inner witness back through `L`.
    rw [SetValuedOperator.mem_comp] at hp
    rcases hp with ⟨q, hq, hp⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hq
    subst q
    rw [SetValuedOperator.mem_comp] at hp
    rcases hp with ⟨r, hr, hp⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hp
    have hrEq : r = L.symm p := by
      simpa using (congrArg (fun z : H ↦ L.symm z) hp).symm
    have hr_sub :
        L.symm x - L.symm p ∈ L.toContinuousLinearMap.adjointImage A (L.symm p) := by
      have hr_sub_raw :
          L.symm x - r ∈ L.toContinuousLinearMap.adjointImage A r :=
        (mem_resolvent_iff_sub_mem
          (B := L.toContinuousLinearMap.adjointImage A)
          (x := L.symm x) (p := r)).1 hr
      simpa [hrEq] using hr_sub_raw
    rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image] at hr_sub
    rcases hr_sub with ⟨v, hv, hvEq⟩
    have hvA : v ∈ A p := by
      simpa using hv
    have hLv : L (L v) = x - p := by
      have hcore : L v = L.symm x - L.symm p := by
        simpa [hAdj] using hvEq
      have happly : L (L v) = L (L.symm x - L.symm p) := by
        exact congrArg (fun z : H ↦ L z) hcore
      calc
        L (L v) = L (L.symm x - L.symm p) := happly
        _ = L (L.symm x) - L (L.symm p) := by
              exact L.toContinuousLinearMap.map_sub (L.symm x) (L.symm p)
        _ = x - p := by simp
    have hsqv : L (L v) = U v := by
      simpa using congrArg (fun T : H →L[ℝ] H ↦ T v) hL_sq
    exact ⟨v, hvA, hLv.symm.trans hsqv⟩
  · rintro ⟨v, hv, hxp⟩
    -- Build the conjugated resolvent witness from the same vector `v ∈ A p`.
    have hsqv : L (L v) = U v := by
      simpa using congrArg (fun T : H →L[ℝ] H ↦ T v) hL_sq
    rw [SetValuedOperator.mem_comp]
    refine ⟨L.symm x, ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · rw [SetValuedOperator.mem_comp]
      refine ⟨L.symm p, ?_, ?_⟩
      · rw [mem_resolvent_iff_sub_mem]
        rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image]
        refine ⟨v, ?_, ?_⟩
        · simpa using hv
        · have hxp' : x - p = L (L v) := by
            simpa [hsqv] using hxp
          have hsymmEq : L.symm (x - p) = L v := by
            simpa using congrArg (fun z : H ↦ L.symm z) hxp'
          calc
            L.toContinuousLinearMap.adjoint v = L v := by
              rw [hAdj]
              rfl
            _ = L.symm (x - p) := by symm; exact hsymmEq
            _ = L.symm x - L.symm p := by
                  exact L.symm.map_sub x p
      · simp [Function.toSetValuedOperator_apply]

/-- Clause (3) of Proposition 23.34: the `U^(1/2)` identity from the source, recorded with an
explicit positive square-root equivalence witness `L : H ≃L[ℝ] H` satisfying
`L.toContinuousLinearMap.comp L.toContinuousLinearMap = U`, since the current real-operator API
in this workspace does not expose a canonical owner for `U^(1/2)`. -/
theorem resolvent_comp_eq_squareRootWitness_comp_resolvent_adjointImage_comp_inverse
    {A : SetValuedOperator H H} (U : H →L[ℝ] H) (L : H ≃L[ℝ] H)
    (hL_pos : L.toContinuousLinearMap.IsPositive)
    (hL_sq : L.toContinuousLinearMap.comp L.toContinuousLinearMap = U) :
    J[(U.toSetValuedOperator.comp A)] =
      ((Function.toSetValuedOperator L).comp
        J[(L.toContinuousLinearMap.adjointImage A)]).comp
        (Function.toSetValuedOperator L.symm) := by
  ext x p
  -- Route correction: use the source-faithful square-root witness `x - p = U v`,
  -- not the inverse-residual route from clause (4).
  rw [mem_resolvent_comp_iff_exists_sub_eq_apply (A := A) U]
  rw [mem_squareRootWitness_comp_resolvent_adjointImage_comp_inverse_iff_exists_sub_eq_apply
    (A := A) (U := U) (L := L) hL_pos hL_sq]

end Hilbert

end SetValuedOperator
