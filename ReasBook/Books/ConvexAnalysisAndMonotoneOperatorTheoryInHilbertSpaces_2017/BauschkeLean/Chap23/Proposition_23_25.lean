import BauschkeLean.Chap23.Proposition_23_7
import BauschkeLean.Chap21.Corollary_21_20
import BauschkeLean.Chap16.Proposition_16_6

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u v

namespace SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Proposition 23.25 studies the conjugate operator `B = L^* A L` under the
  surjectivity condition that `L.comp L.adjoint` is invertible, together with the induced
  resolvent identities.
- `core/canonical`: the reusable owners are `Maximal IsMonotone` and the Chapter 23 resolvent and
  Yosida surfaces `J[...]` and `{}^[μ]`.
- `bridge/view`: the canonical Chapter 16/25 bridge for `L^* A L` is
  `ContinuousLinearMap.adjointImage`.

Domain-style sampling:
- `Chap16/Proposition_16_6.lean`: `ContinuousLinearMap.adjointImage` is the owner bridge for
  `L^* A L`.
-- `Chap21/Corollary_21_20.lean`: `dom_nonempty_of_maximal` supplies the nonempty-domain witness
  used in the direct Minty argument.
- `Chap23/Proposition_23_7.lean`: `yosidaApproximation_eq_inverse_smul_id_add_inverse` is the
  Chapter 23 owner for the inverse-sum description of `{}^[μ] A`.
-- `Chap20/Definition_20_20.lean`: `maximal_iff_mem_iff` and `Maximal.mem_iff` package the Minty
  criterion used to prove maximality directly. -/

/-- Helper for Proposition 23.25: invertibility of `L ∘L L.adjoint` makes `L` surjective. -/
private theorem surjective_of_isUnit_comp_adjoint
    (L : H →L[ℝ] K) (hLLstar : IsUnit (L.comp L.adjoint)) :
    Function.Surjective L := by
  -- Surjectivity of `L L*` gives a concrete preimage `L.adjoint z` for every target point.
  have hsurj : Function.Surjective (L.comp L.adjoint) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hLLstar).2
  intro y
  rcases hsurj y with ⟨z, hz⟩
  refine ⟨L.adjoint z, ?_⟩
  exact hz

/-- Helper for Proposition 23.25: membership in `L.adjointImage A x` is witnessed by a value of
`A (L x)` whose adjoint image is the given vector. -/
private theorem mem_adjointImage_iff_exists
    (L : H →L[ℝ] K) {A : SetValuedOperator K K} {x : H} {u : H} :
    u ∈ L.adjointImage A x ↔ ∃ v ∈ A (L x), L.adjoint v = u := by
  -- Expand the owner `adjointImage` once and read the image witness explicitly.
  rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image]

/-- Helper for Proposition 23.25: if an affine function `t ↦ c - t * a` is nonnegative on all of
`ℝ`, then its slope vanishes. -/
private theorem eq_zero_of_nonneg_affine_family
    {a c : ℝ} (h : ∀ t : ℝ, 0 ≤ c - t * a) :
    a = 0 := by
  -- Test the affine family at a point where a nonzero slope would force a negative value.
  by_contra ha
  by_cases hpos : 0 < a
  · let t : ℝ := c / a + 1
    have ht : 0 ≤ c - t * a := h t
    have ha0 : a ≠ 0 := ne_of_gt hpos
    have hcalc : c - t * a = -a := by
      dsimp [t]
      field_simp [ha0]
      ring
    linarith
  · have hane : a ≠ 0 := ha
    have hneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hane
    let t : ℝ := c / a - 1
    have ht : 0 ≤ c - t * a := h t
    have ha0 : a ≠ 0 := ne_of_lt hneg
    have hcalc : c - t * a = a := by
      dsimp [t]
      field_simp [ha0]
      ring
    linarith

/-- Helper for Proposition 23.25: a vector orthogonal to `ker L` lies in `range L.adjoint` when
`L ∘L L.adjoint` is invertible. -/
private theorem exists_adjoint_eq_of_orthogonal_ker
    (L : H →L[ℝ] K) (hLLstar : IsUnit (L.comp L.adjoint)) {u : H}
    (hu : ∀ k, k ∈ L.ker → ⟪k, u⟫_ℝ = 0) :
    ∃ q : K, L.adjoint q = u := by
  let q : K := (L.comp L.adjoint).inverse (L u)
  have hker : u - L.adjoint q ∈ L.ker := by
    -- The inverse of `L L*` matches the `L`-image of `u`.
    rw [LinearMap.mem_ker]
    calc
      L (u - L.adjoint q) = L u - (L.comp L.adjoint) q := by
        simp [q]
      _ = L u - (L.comp L.adjoint) ((L.comp L.adjoint).inverse (L u)) := by
        rfl
      _ = L u - L u := by
        rw [show
          (L.comp L.adjoint) ((L.comp L.adjoint).inverse (L u)) = L u by
          simpa [← ContinuousLinearMap.ringInverse_eq_inverse, ContinuousLinearMap.one_def] using
            congrArg (fun A : K →L[ℝ] K ↦ A (L u))
              (Ring.mul_inverse_cancel (L.comp L.adjoint) hLLstar)]
      _ = 0 := by
        simp
  have horth : ∀ k, k ∈ L.ker → ⟪k, u - L.adjoint q⟫_ℝ = 0 := by
    -- The residual stays orthogonal to `ker L` because `L.adjoint q` already is.
    intro k hk
    have hk0 : L k = 0 := (LinearMap.mem_ker.mp hk)
    calc
      ⟪k, u - L.adjoint q⟫_ℝ = ⟪k, u⟫_ℝ - ⟪k, L.adjoint q⟫_ℝ := by
        rw [inner_sub_right]
      _ = 0 - ⟪L k, q⟫_ℝ := by
        rw [hu k hk, (ContinuousLinearMap.adjoint_inner_right L k q).symm]
      _ = 0 := by
        simp [hk0]
  have hself : ⟪u - L.adjoint q, u - L.adjoint q⟫_ℝ = 0 :=
    horth (u - L.adjoint q) hker
  have hzero : u - L.adjoint q = 0 := by
    simpa using inner_self_eq_zero.mp hself
  refine ⟨q, ?_⟩
  simpa [eq_comm] using sub_eq_zero.mp hzero

/-- Helper for Proposition 23.25: a Minty relation against all graph points of `L.adjointImage A`
produces the required adjoint-image witness. -/
private theorem mem_adjointImage_of_mintyRelation
    (L : H →L[ℝ] K) {A : SetValuedOperator K K}
    (hLLstar : IsUnit (L.comp L.adjoint)) (hA : Maximal IsMonotone A)
    {x u : H}
    (hrel : ∀ ⦃p v : H⦄, v ∈ L.adjointImage A p → 0 ≤ ⟪x - p, u - v⟫_ℝ) :
    u ∈ L.adjointImage A x := by
  let hsurj : Function.Surjective L := surjective_of_isUnit_comp_adjoint L hLLstar
  rcases dom_nonempty_of_maximal A hA with ⟨y0, hy0⟩
  rcases (mem_dom_iff A y0).mp hy0 with ⟨v0, hv0⟩
  rcases hsurj y0 with ⟨p0, hp0⟩
  have hu_orth : ∀ k, k ∈ L.ker → ⟪k, u⟫_ℝ = 0 := by
    -- Vary a fixed graph point of `A` along the affine fiber `p0 + t • k`.
    intro k hk
    let c : ℝ := ⟪x - p0, u - L.adjoint v0⟫_ℝ
    have hineq : ∀ t : ℝ, 0 ≤ c - t * ⟪k, u⟫_ℝ := by
      intro t
      have hk0 : L k = 0 := LinearMap.mem_ker.mp hk
      have hfiber : L (p0 + t • k) = y0 := by
        calc
          L (p0 + t • k) = L p0 + t • L k := by
            simp
          _ = y0 := by
            simp [hp0, hk0]
      have hgraph :
          L.adjoint v0 ∈ L.adjointImage A (p0 + t • k) := by
        refine (mem_adjointImage_iff_exists (L := L) (A := A)).mpr ?_
        refine ⟨v0, ?_, rfl⟩
        simpa [hfiber] using hv0
      have htpair : 0 ≤ ⟪x - (p0 + t • k), u - L.adjoint v0⟫_ℝ := hrel hgraph
      have horth : ⟪k, L.adjoint v0⟫_ℝ = 0 := by
        have hinner : ⟪k, L.adjoint v0⟫_ℝ = ⟪L k, v0⟫_ℝ := by
          simpa using ContinuousLinearMap.adjoint_inner_right L k v0
        rw [hinner, hk0]
        simp
      have hsplit : x - (p0 + t • k) = (x - p0) - t • k := by
        abel_nf
      have hcalc :
          ⟪x - (p0 + t • k), u - L.adjoint v0⟫_ℝ = c - t * ⟪k, u⟫_ℝ := by
        calc
          ⟪x - (p0 + t • k), u - L.adjoint v0⟫_ℝ
              = ⟪(x - p0) - t • k, u - L.adjoint v0⟫_ℝ := by
                  rw [hsplit]
          _ = ⟪x - p0, u - L.adjoint v0⟫_ℝ - ⟪t • k, u - L.adjoint v0⟫_ℝ := by
                rw [inner_sub_left]
          _ = c - t * ⟪k, u - L.adjoint v0⟫_ℝ := by
                rw [real_inner_smul_left]
          _ = c - t * ⟪k, u⟫_ℝ := by
                rw [inner_sub_right, horth]
                ring
      rw [hcalc] at htpair
      exact htpair
    exact eq_zero_of_nonneg_affine_family hineq
  rcases exists_adjoint_eq_of_orthogonal_ker L hLLstar hu_orth with ⟨q, hq⟩
  have hq_mem : q ∈ A (L x) := by
    -- Push the Minty relation down from `H` to `K` via a preimage of each graph point.
    refine (SetValuedOperator.Maximal.mem_iff hA (L x) q).mpr ?_
    intro y v hv
    rcases hsurj y with ⟨p, hp⟩
    have hgraph : L.adjoint v ∈ L.adjointImage A p := by
      refine (mem_adjointImage_iff_exists (L := L) (A := A)).mpr ?_
      refine ⟨v, ?_, rfl⟩
      simpa [hp] using hv
    have hpair : 0 ≤ ⟪x - p, u - L.adjoint v⟫_ℝ := hrel hgraph
    have hcalc : ⟪x - p, u - L.adjoint v⟫_ℝ = ⟪L x - y, q - v⟫_ℝ := by
      calc
        ⟪x - p, u - L.adjoint v⟫_ℝ = ⟪x - p, L.adjoint q - L.adjoint v⟫_ℝ := by
              rw [hq]
        _ = ⟪x - p, L.adjoint (q - v)⟫_ℝ := by
              rw [ContinuousLinearMap.map_sub]
        _ = ⟪L (x - p), q - v⟫_ℝ := by
              rw [(ContinuousLinearMap.adjoint_inner_right L (x - p) (q - v)).symm]
        _ = ⟪L x - L p, q - v⟫_ℝ := by
              rw [ContinuousLinearMap.map_sub]
        _ = ⟪L x - y, q - v⟫_ℝ := by
              rw [hp]
    rw [hcalc] at hpair
    exact hpair
  -- Read the `A`-graph witness back as membership in `L.adjointImage A x`.
  exact (mem_adjointImage_iff_exists (L := L) (A := A)).mpr ⟨q, hq_mem, hq⟩

/-- Proposition 23.25 (1): let `L : H →L[ℝ] K` satisfy that `L ∘L L.adjoint` is invertible, let
`A : K → 2^K` be maximally monotone, and set `B = L^* A L`, realized as `L.adjointImage A`; then
`B` is maximally monotone. -/
theorem Maximal.adjointImage_of_isUnit_comp_adjoint
    (L : H →L[ℝ] K) {A : SetValuedOperator K K}
    (hLLstar : IsUnit (L.comp L.adjoint)) (hA : Maximal IsMonotone A) :
    Maximal IsMonotone (L.adjointImage A) := by
  -- Route correction: avoid the broken Chapter 25 import chain and prove maximality directly via
  -- the Minty membership criterion for `L.adjointImage A`.
  rw [SetValuedOperator.maximal_iff_mem_iff]
  intro x u
  constructor
  · intro hu
    rcases (mem_adjointImage_iff_exists (L := L) (A := A)).mp hu with ⟨q, hq, rfl⟩
    -- The forward Minty direction is just monotonicity of `A` transported through `L.adjoint`.
    intro y v hv
    rcases (mem_adjointImage_iff_exists (L := L) (A := A)).mp hv with ⟨w, hw, rfl⟩
    have hmono : 0 ≤ ⟪L x - L y, q - w⟫_ℝ :=
      (SetValuedOperator.Maximal.isMonotone hA) hq hw
    have hcalc :
        ⟪x - y, L.adjoint q - L.adjoint w⟫_ℝ = ⟪L x - L y, q - w⟫_ℝ := by
      calc
        ⟪x - y, L.adjoint q - L.adjoint w⟫_ℝ = ⟪x - y, L.adjoint (q - w)⟫_ℝ := by
              rw [ContinuousLinearMap.map_sub]
        _ = ⟪L (x - y), q - w⟫_ℝ := by
              rw [(ContinuousLinearMap.adjoint_inner_right L (x - y) (q - w)).symm]
        _ = ⟪L x - L y, q - w⟫_ℝ := by
              rw [ContinuousLinearMap.map_sub]
    rw [hcalc]
    exact hmono
  · intro hrel
    -- The reverse direction is the Minty reconstruction lemma specialized to the graph of
    -- `L.adjointImage A`.
    exact mem_adjointImage_of_mintyRelation (L := L) (A := A) hLLstar hA hrel

/-- Helper for Proposition 23.25: membership in the inverse of
`(L.comp L.adjoint).toSetValuedOperator + A⁻¹` is equivalent to the canonical graph condition
`v ∈ A (y - (L.comp L.adjoint) v)`. -/
private theorem mem_inverse_comp_adjoint_add_inverse_iff_mem_sub
    (L : H →L[ℝ] K) {A : SetValuedOperator K K} {y v : K} :
    v ∈ (((L.comp L.adjoint).toSetValuedOperator + A⁻¹)⁻¹) y ↔
      v ∈ A (y - (L.comp L.adjoint) v) := by
  -- Expand the inverse-sum membership once and isolate the singleton contribution from `L L*`.
  rw [SetValuedOperator.mem_inverse_iff]
  rw [Pi.add_apply, Set.mem_add]
  constructor
  · rintro ⟨w, hw, z, hz, hEq⟩
    simp [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply] at hw
    subst w
    rw [SetValuedOperator.mem_inverse_iff] at hz
    have hzEq : z = y - (L.comp L.adjoint) v := by
      have hsub := congrArg (fun t : K ↦ t - (L.comp L.adjoint) v) hEq
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    simpa [hzEq] using hz
  · intro hv
    refine ⟨(L.comp L.adjoint) v, ?_, y - (L.comp L.adjoint) v, ?_, ?_⟩
    · simp [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply]
    · rw [SetValuedOperator.mem_inverse_iff]
      simpa using hv
    · abel_nf

/-- Helper for Proposition 23.25: a point lies in `J[(L.adjointImage A)] x` exactly when it can
be written as `x - L.adjoint v` for some `v ∈ A (L p)`. -/
private theorem mem_resolvent_adjointImage_iff_existsValue
    (L : H →L[ℝ] K) {A : SetValuedOperator K K} {x p : H} :
    p ∈ J[(L.adjointImage A)] x ↔ ∃ v, v ∈ A (L p) ∧ p = x - L.adjoint v := by
  -- Normalize the resolvent at parameter `1`, then unpack the adjoint-image witness.
  constructor
  · intro hp
    have hsub : x - p ∈ L.adjointImage A p := by
      have hiff :=
        mem_resolvent_smul_iff_sub_mem_smul (L.adjointImage A) (1 : PosReal) x p
      have hunit : p ∈ J[((1 : ℝ) • L.adjointImage A)] x := by
        simpa [one_smul] using hp
      simpa [one_smul] using hiff.mp hunit
    rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image] at hsub
    rcases hsub with ⟨v, hv, hEq⟩
    refine ⟨v, hv, ?_⟩
    calc
      p = x - (x - p) := by
            abel_nf
      _ = x - L.adjoint v := by
            rw [← hEq]
  · rintro ⟨v, hv, hpEq⟩
    have hsub : x - p ∈ L.adjointImage A p := by
      rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image]
      refine ⟨v, hv, ?_⟩
      calc
        L.adjoint v = x - (x - L.adjoint v) := by
              abel_nf
        _ = x - p := by
              rw [hpEq]
    have hiff :=
      mem_resolvent_smul_iff_sub_mem_smul (L.adjointImage A) (1 : PosReal) x p
    have hscaled : x - p ∈ (1 : ℝ) • L.adjointImage A p := by
      simpa [one_smul] using hsub
    simpa [one_smul] using hiff.mpr hscaled

/-- Helper for Proposition 23.25: membership in
`id.toSetValuedOperator - L.adjointImage T` is equivalent to the same affine witness
`p = x - L.adjoint v` with `v ∈ T (L x)`. -/
private theorem mem_id_sub_adjointImage_iff_existsValue
    (L : H →L[ℝ] K) (T : SetValuedOperator K K) {x p : H} :
    p ∈ ((((id : H → H).toSetValuedOperator - L.adjointImage T : SetValuedOperator H H)) x) ↔
      ∃ v, v ∈ T (L x) ∧ p = x - L.adjoint v := by
  -- Expand the pointwise subtraction and read the unique `id` witness from the singleton set.
  rw [Pi.sub_apply, Set.mem_sub]
  constructor
  · rintro ⟨y, hy, z, hz, hEq⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hy
    subst y
    rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image] at hz
    rcases hz with ⟨v, hv, rfl⟩
    exact ⟨v, hv, hEq.symm⟩
  · rintro ⟨v, hv, hpEq⟩
    refine ⟨x, ?_, L.adjoint v, ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image]
      exact ⟨v, hv, rfl⟩
    · exact hpEq.symm

/-- Proposition 23.25 (2): for `B = L^* A L`, realized as `L.adjointImage A`, the resolvent
satisfies the algebraic identity
`J_B = Id - L^* ∘ (L L^* + A⁻¹)⁻¹ ∘ L`, formalized as the operator identity below. -/
theorem resolvent_adjointImage_eq_id_sub_adjointImage_inverse_comp_adjoint_add_inverse
    (L : H →L[ℝ] K) {A : SetValuedOperator K K} :
    J[(L.adjointImage A)] =
      id.toSetValuedOperator -
        L.adjointImage (((L.comp L.adjoint).toSetValuedOperator + A⁻¹)⁻¹) := by
  ext x p
  constructor
  · intro hp
    -- Package the resolvent witness and transport `A (L p)` to the inverse-sum normal form.
    rcases (mem_resolvent_adjointImage_iff_existsValue (L := L) (A := A) (x := x) (p := p)).mp hp
      with ⟨v, hv, hpEq⟩
    refine (mem_id_sub_adjointImage_iff_existsValue (L := L)
      (((L.comp L.adjoint).toSetValuedOperator + A⁻¹)⁻¹) (x := x) (p := p)).mpr ?_
    refine ⟨v, ?_, hpEq⟩
    rw [mem_inverse_comp_adjoint_add_inverse_iff_mem_sub]
    simpa [hpEq, ContinuousLinearMap.map_sub] using hv
  · intro hp
    -- Read the same affine witness on the right-hand side and convert the inverse-sum condition
    -- back to `v ∈ A (L p)`.
    rcases (mem_id_sub_adjointImage_iff_existsValue (L := L)
      (((L.comp L.adjoint).toSetValuedOperator + A⁻¹)⁻¹) (x := x) (p := p)).mp hp with
      ⟨v, hv, hpEq⟩
    refine (mem_resolvent_adjointImage_iff_existsValue (L := L) (A := A) (x := x) (p := p)).mpr ?_
    refine ⟨v, ?_, hpEq⟩
    rw [mem_inverse_comp_adjoint_add_inverse_iff_mem_sub] at hv
    simpa [hpEq, ContinuousLinearMap.map_sub] using hv

/-- Helper for Proposition 23.25: the singleton-valued operator induced by the scaled identity
linear map agrees with the pointwise scalar multiple of `id.toSetValuedOperator`. -/
private theorem smulIdentityToSetValuedOperator_eq_smulFunctionId
    (μ : PosReal) :
    (((μ : ℝ) • (1 : K →L[ℝ] K)).toSetValuedOperator : SetValuedOperator K K) =
      ((μ : ℝ) • (id : K → K).toSetValuedOperator) := by
  -- Compare both singleton-valued operators pointwise; each side is exactly `{(μ : ℝ) • x}`.
  ext x y
  constructor
  · intro hy
    simpa [Function.toSetValuedOperator_apply, ContinuousLinearMap.one_apply,
      Set.mem_smul_set] using hy
  · intro hy
    simpa [Function.toSetValuedOperator_apply, ContinuousLinearMap.one_apply,
      Set.mem_smul_set] using hy

/-- Proposition 23.25 (3): if `L ∘L L.adjoint = μ • Id` for some `μ ∈ ℝ_{++}`, then for
`B = L^* A L`, realized as `L.adjointImage A`, one has
`J_B = Id - L^* ∘ {}^[μ] A ∘ L`, where `{}^[μ] A` is the `μ`-Yosida approximation of `A`. -/
theorem resolvent_adjointImage_eq_id_sub_adjointImage_yosidaApproximation_of_comp_adjoint_eq_smul_id
    (L : H →L[ℝ] K) {A : SetValuedOperator K K}
    (μ : PosReal) (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K)) :
    J[(L.adjointImage A)] =
      id.toSetValuedOperator - L.adjointImage ({}^[μ] A) := by
  -- Rewrite part (ii) with the scalar identity and then identify the inverse sum with the
  -- `μ`-Yosida approximation from Proposition 23.7.
  rw [resolvent_adjointImage_eq_id_sub_adjointImage_inverse_comp_adjoint_add_inverse
    (L := L) (A := A)]
  rw [hscalar, smulIdentityToSetValuedOperator_eq_smulFunctionId]
  rw [← yosidaApproximation_eq_inverse_smul_id_add_inverse A μ]

end SetValuedOperator
