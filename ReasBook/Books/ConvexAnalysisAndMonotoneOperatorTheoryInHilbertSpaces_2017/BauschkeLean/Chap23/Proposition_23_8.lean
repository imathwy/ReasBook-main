import BauschkeLean.Chap04.FirmlyNonexpansiveOn
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap21.Theorem_21_1
import BauschkeLean.Chap23.Definition_23_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` only surfaced unrelated generic monotonicity lemmas, so
-- this file uses the verified local owners `ofFunction`, `J[...]`, `IsMonotone`, `Maximal`, and
-- `FirmlyNonexpansiveOn`.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

section Algebraic

variable {H : Type u} [AddCommGroup H]

/-- Helper for Proposition 23.8: membership in `((ofFunction D T)⁻¹ - id.toSetValuedOperator) x`
is equivalent to the source identity `x = T (x + u)`. -/
lemma mem_sub_id_inverse_ofFunction_iff
    (D : Set H) (T : D → H) {x u : H} :
    u ∈ ((((ofFunction D T)⁻¹ - (id : H → H).toSetValuedOperator) : SetValuedOperator H H) x) ↔
      ∃ hxu : x + u ∈ D, T ⟨x + u, hxu⟩ = x := by
  rw [Pi.sub_apply, Set.mem_sub]
  constructor
  · intro hu
    rcases hu with ⟨y, hy, z, hz, hyz⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hz
    subst z
    rw [SetValuedOperator.mem_inverse_iff] at hy
    rcases hy with ⟨hyD, hyT⟩
    have hy_eq : y = x + u := by
      calc
        y = (y - x) + x := by abel_nf
        _ = u + x := by simpa using congrArg (fun t ↦ t + x) hyz
        _ = x + u := by ac_rfl
    -- Rewrite the inverse witness into the canonical point `x + u`.
    refine ⟨hy_eq ▸ hyD, ?_⟩
    have hsub : (⟨y, hyD⟩ : D) = ⟨x + u, hy_eq ▸ hyD⟩ := Subtype.ext hy_eq
    simpa [hsub] using hyT.symm
  · rintro ⟨hxu, hTxu⟩
    -- Package the canonical point `x + u` into the pointwise set subtraction witness.
    refine ⟨x + u, ?_, x, ?_, ?_⟩
    · rw [SetValuedOperator.mem_inverse_iff]
      exact ⟨hxu, hTxu.symm⟩
    · simp [Function.toSetValuedOperator_apply]
    · abel_nf

/-- Part (1) of Proposition 23.8: for a nonempty subset `D ⊆ H` and a map `T : D → H`, the
operator
`A = T⁻¹ - Id`, realized directly as `((ofFunction D T)⁻¹ - id.toSetValuedOperator)`, has
resolvent `J[A] = T`, realized by
`J[((ofFunction D T)⁻¹ - id.toSetValuedOperator)] = ofFunction D T`. -/
theorem resolvent_sub_id_inverse_ofFunction_eq_ofFunction
    (D : Set H) (hD : D.Nonempty) (T : D → H) :
    J[((ofFunction D T)⁻¹ - id.toSetValuedOperator)] = ofFunction D T := by
  let _ := hD
  ext x y
  constructor
  · intro hy
    rw [SetValuedOperator.resolvent_def, SetValuedOperator.mem_inverse_iff] at hy
    rw [Pi.add_apply, Function.toSetValuedOperator_apply, Set.mem_add] at hy
    rcases hy with ⟨z, hz, u, hu, hzu⟩
    rw [Set.mem_singleton_iff] at hz
    subst z
    -- Convert the resolvent witness into the source identity `y = T x`.
    have hu' :
        x - y ∈
          ((((ofFunction D T)⁻¹ - (id : H → H).toSetValuedOperator) :
            SetValuedOperator H H) y) := by
      have hu_eq : u = x - y := by
        calc
          u = (y + u) - y := by abel_nf
          _ = x - y := by simpa using congrArg (fun t ↦ t - y) hzu
      simpa [hu_eq] using hu
    rcases (mem_sub_id_inverse_ofFunction_iff D T).1 hu' with ⟨hxyD, hTxy⟩
    have hxD : x ∈ D := by
      simpa using hxyD
    have hsub : (⟨y + (x - y), hxyD⟩ : D) = ⟨x, hxD⟩ := by
      apply Subtype.ext
      abel_nf
    rw [SetValuedOperator.ofFunction_apply_of_mem D T hxD]
    simpa [hsub] using hTxy.symm
  · intro hy
    by_cases hxD : x ∈ D
    · rw [SetValuedOperator.ofFunction_apply_of_mem D T hxD] at hy
      rw [Set.mem_singleton_iff] at hy
      rw [SetValuedOperator.resolvent_def, SetValuedOperator.mem_inverse_iff]
      rw [Pi.add_apply, Function.toSetValuedOperator_apply, Set.mem_add]
      have hsumD : y + (x - y) ∈ D := by
        simpa using hxD
      have hsub : (⟨y + (x - y), hsumD⟩ : D) = ⟨x, hxD⟩ := by
        apply Subtype.ext
        abel_nf
      refine ⟨y, by simp, x - y, ?_, ?_⟩
      · exact (mem_sub_id_inverse_ofFunction_iff D T).2 ⟨hsumD, by simpa [hsub] using hy.symm⟩
      · abel_nf
    · rw [SetValuedOperator.ofFunction_apply_of_not_mem D T hxD] at hy
      exact False.elim (Set.notMem_empty y hy)

end Algebraic

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 23.8: firm nonexpansiveness is equivalent to nonnegativity of the
residual cross term `⟪T x - T y, ((x : H) - T x) - (y - T y)⟫_ℝ`. -/
lemma firmlyNonexpansiveOn_iff_residualInner_nonneg
    (D : Set H) (T : D → H) :
    FirmlyNonexpansiveOn D T ↔
      ∀ x y : D, 0 ≤ ⟪T x - T y, ((x : H) - T x) - (y - T y)⟫_ℝ := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro hT x y
    have hxy : ‖T x - T y‖ ^ (2 : ℕ) ≤ ⟪((x : H) - y), T x - T y⟫_ℝ := hT x y
    have hres :
        ((x : H) - T x) - (y - T y) = (((x : H) - y) - (T x - T y)) := by
      abel_nf
    have hinner :
        ⟪T x - T y, ((x : H) - T x) - (y - T y)⟫_ℝ =
          ⟪((x : H) - y), T x - T y⟫_ℝ - ‖T x - T y‖ ^ (2 : ℕ) := by
      calc
        ⟪T x - T y, ((x : H) - T x) - (y - T y)⟫_ℝ
            = ⟪T x - T y, (((x : H) - y) - (T x - T y))⟫_ℝ := by rw [hres]
        _ = ⟪T x - T y, ((x : H) - y)⟫_ℝ - ⟪T x - T y, T x - T y⟫_ℝ := by
              rw [inner_sub_right]
        _ = ⟪((x : H) - y), T x - T y⟫_ℝ - ‖T x - T y‖ ^ (2 : ℕ) := by
              rw [real_inner_comm, real_inner_self_eq_norm_sq]
    -- The residual form is exactly the firm inequality after expanding the displacement.
    nlinarith [hxy, hinner]
  · intro hT x y
    have hxy : 0 ≤ ⟪T x - T y, ((x : H) - T x) - (y - T y)⟫_ℝ := hT x y
    have hres :
        ((x : H) - T x) - (y - T y) = (((x : H) - y) - (T x - T y)) := by
      abel_nf
    have hinner :
        ⟪T x - T y, ((x : H) - T x) - (y - T y)⟫_ℝ =
          ⟪((x : H) - y), T x - T y⟫_ℝ - ‖T x - T y‖ ^ (2 : ℕ) := by
      calc
        ⟪T x - T y, ((x : H) - T x) - (y - T y)⟫_ℝ
            = ⟪T x - T y, (((x : H) - y) - (T x - T y))⟫_ℝ := by rw [hres]
        _ = ⟪T x - T y, ((x : H) - y)⟫_ℝ - ⟪T x - T y, T x - T y⟫_ℝ := by
              rw [inner_sub_right]
        _ = ⟪((x : H) - y), T x - T y⟫_ℝ - ‖T x - T y‖ ^ (2 : ℕ) := by
              rw [real_inner_comm, real_inner_self_eq_norm_sq]
    -- The same identity runs backwards to recover the textbook firm inequality.
    nlinarith [hxy, hinner]

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 23.8: every `x : D` yields the canonical graph point
`((x : H) - T x) ∈ ((ofFunction D T)⁻¹ - id.toSetValuedOperator) (T x)`. -/
lemma residual_mem_sub_id_inverse_ofFunction
    (D : Set H) (T : D → H) (x : D) :
    ((x : H) - T x) ∈
      ((((ofFunction D T)⁻¹ - (id : H → H).toSetValuedOperator) :
        SetValuedOperator H H) (T x)) := by
  have hsumD : (T x : H) + ((x : H) - T x) ∈ D := by
    simp
  have hsub : (⟨(T x : H) + ((x : H) - T x), hsumD⟩ : D) = x := by
    apply Subtype.ext
    abel_nf
  have hTx :
      T ⟨(T x : H) + ((x : H) - T x), hsumD⟩ = T x := by
    exact congrArg T hsub
  -- Repackage the canonical residual vector through the graph-membership bridge.
  exact
    (mem_sub_id_inverse_ofFunction_iff D T).2
      ⟨hsumD, hTx⟩

/-- Part (2) of Proposition 23.8: for a nonempty subset `D ⊆ H` and a map `T : D → H`, the map
`T` is firmly nonexpansive on `D` if and only if `A = T⁻¹ - Id`, realized directly as
`((ofFunction D T)⁻¹ - id.toSetValuedOperator)`, is monotone. -/
theorem firmlyNonexpansiveOn_iff_isMonotone_sub_id_inverse_ofFunction
    (D : Set H) (hD : D.Nonempty) (T : D → H) :
    FirmlyNonexpansiveOn D T ↔
      ((ofFunction D T)⁻¹ - id.toSetValuedOperator).IsMonotone := by
  let _ := hD
  rw [SetValuedOperator.isMonotone_iff]
  constructor
  · intro hT x u y v hxu hyv
    rcases (mem_sub_id_inverse_ofFunction_iff D T).1 hxu with ⟨hxuD, hTxu⟩
    rcases (mem_sub_id_inverse_ofFunction_iff D T).1 hyv with ⟨hyvD, hTyv⟩
    have hres :=
      (firmlyNonexpansiveOn_iff_residualInner_nonneg D T).1 hT ⟨x + u, hxuD⟩ ⟨y + v, hyvD⟩
    -- Rewrite the residual inequality along the graph identities
    -- `x = T (x + u)` and `y = T (y + v)`.
    simpa [hTxu, hTyv] using hres
  · intro hA
    refine (firmlyNonexpansiveOn_iff_residualInner_nonneg D T).2 ?_
    intro x y
    have hxA := residual_mem_sub_id_inverse_ofFunction D T x
    have hyA := residual_mem_sub_id_inverse_ofFunction D T y
    -- Apply monotonicity to the canonical graph points of `A`.
    exact (SetValuedOperator.isMonotone_iff _).1 hA hxA hyA

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 23.8: the range of `Id + ((ofFunction D T)⁻¹ - id.toSetValuedOperator)`
is exactly `D`. -/
lemma range_id_add_sub_id_inverse_ofFunction
    (D : Set H) (T : D → H) :
    (((id : H → H).toSetValuedOperator + ((ofFunction D T)⁻¹ - id.toSetValuedOperator)).range) =
      D := by
  ext x
  constructor
  · intro hx
    rcases
        (SetValuedOperator.mem_range_iff
          ((id : H → H).toSetValuedOperator + ((ofFunction D T)⁻¹ - id.toSetValuedOperator)) x).1
          hx with
      ⟨y, hy⟩
    rw [Pi.add_apply, Function.toSetValuedOperator_apply, Set.mem_add] at hy
    rcases hy with ⟨z, hz, u, hu, hzu⟩
    rw [Set.mem_singleton_iff] at hz
    subst z
    rcases (mem_sub_id_inverse_ofFunction_iff D T).1 hu with ⟨hyuD, hyTu⟩
    -- The range witness has the form `x = y + u`, so the bridge gives `x ∈ D`.
    have hyux : y + u = x := by
      simpa using hzu
    simpa [hyux] using hyuD
  · intro hx
    -- Choose the canonical graph point over `T x` to realize `x ∈ range (Id + A)`.
    refine
      (SetValuedOperator.mem_range_iff
        ((id : H → H).toSetValuedOperator + ((ofFunction D T)⁻¹ - id.toSetValuedOperator)) x).2
        ⟨T ⟨x, hx⟩, ?_⟩
    rw [Pi.add_apply, Function.toSetValuedOperator_apply, Set.mem_add]
    refine ⟨T ⟨x, hx⟩, by simp, x - T ⟨x, hx⟩, ?_, ?_⟩
    · exact residual_mem_sub_id_inverse_ofFunction D T ⟨x, hx⟩
    · abel_nf

section Complete

variable [CompleteSpace H]

/-- Proposition 23.8 (3): for a nonempty subset `D ⊆ H` and a map `T : D → H`, the conjunction
that `T` is firmly nonexpansive on `D` and `D = H`, realized as `D = Set.univ`, is equivalent to
maximal monotonicity of `A = T⁻¹ - Id`, realized directly as
`((ofFunction D T)⁻¹ - id.toSetValuedOperator)`. -/
theorem firmlyNonexpansiveOn_and_univ_iff_maximal_sub_id_inverse_ofFunction
    (D : Set H) (hD : D.Nonempty) (T : D → H) :
    FirmlyNonexpansiveOn D T ∧ D = Set.univ ↔
      Maximal IsMonotone ((ofFunction D T)⁻¹ - id.toSetValuedOperator) := by
  constructor
  · rintro ⟨hT, hUniv⟩
    have hMono :
        ((ofFunction D T)⁻¹ - id.toSetValuedOperator).IsMonotone :=
      (firmlyNonexpansiveOn_iff_isMonotone_sub_id_inverse_ofFunction D hD T).1 hT
    have hRange :
        (((id : H → H).toSetValuedOperator + ((ofFunction D T)⁻¹ - id.toSetValuedOperator)).range) =
          Set.univ := by
      rw [range_id_add_sub_id_inverse_ofFunction D T, hUniv]
    -- Minty's range characterization closes the maximality direction once monotonicity is known.
    exact
      (SetValuedOperator.maximal_iff_range_id_add_eq_univ
        ((ofFunction D T)⁻¹ - id.toSetValuedOperator) hMono).2 hRange
  · intro hMax
    have hMono :
        ((ofFunction D T)⁻¹ - id.toSetValuedOperator).IsMonotone :=
      SetValuedOperator.Maximal.isMonotone hMax
    have hRange :
        (((id : H → H).toSetValuedOperator + ((ofFunction D T)⁻¹ - id.toSetValuedOperator)).range) =
          Set.univ :=
      (SetValuedOperator.maximal_iff_range_id_add_eq_univ
        ((ofFunction D T)⁻¹ - id.toSetValuedOperator) hMono).1 hMax
    -- Read Minty's range equality back as `D = Set.univ` through the explicit range formula.
    refine
      ⟨(firmlyNonexpansiveOn_iff_isMonotone_sub_id_inverse_ofFunction D hD T).2 hMono, ?_⟩
    rw [range_id_add_sub_id_inverse_ofFunction D T] at hRange
    exact hRange

end Complete

end Hilbert

end SetValuedOperator
