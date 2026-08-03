import BauschkeLean.Chap23.Definition_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Helper for Proposition 23.19: resolvent membership is equivalent to membership in the
singleton translate `({u} : Set H) + A u`, hence to an explicit graph witness. -/
private theorem mem_resolvent_iff_existsValue
    {A : SetValuedOperator H H} {x u : H} :
    u ∈ J[A] x ↔ ∃ a ∈ A u, x = u + a := by
  -- Unfold the resolvent once and express the value of `Id + A` at `u` as a singleton translate.
  rw [SetValuedOperator.resolvent_def, SetValuedOperator.mem_inverse_iff]
  change x ∈ ((Function.toSetValuedOperator id) u + A u) ↔ ∃ a ∈ A u, x = u + a
  rw [Function.toSetValuedOperator_apply, Set.mem_add]
  constructor
  · rintro ⟨y, hy, a, ha, hEq⟩
    -- The singleton witness forces the graph base point to be `u`.
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨a, ha, hEq.symm⟩
  · rintro ⟨a, ha, rfl⟩
    have hu : u ∈ ({u} : Set H) := by
      simp
    exact ⟨u, hu, a, ha, rfl⟩

/-- Helper for Proposition 23.19: the affine combination on the graph image collapses to
`u + γ • a`. -/
private theorem affineCombo_eq_base_add_smul
    (γ : ℝ) (u a : H) :
    γ • (u + a) + (1 - γ) • u = u + γ • a := by
  -- Expand the affine combination and collapse the two copies of `u`.
  have hu : γ • u + (1 - γ) • u = u := by
    calc
      γ • u + (1 - γ) • u = (γ + (1 - γ)) • u := by
        rw [← add_smul]
      _ = (1 : ℝ) • u := by
        ring_nf
      _ = u := by
        simp
  calc
    γ • (u + a) + (1 - γ) • u
        = (γ • u + γ • a) + (1 - γ) • u := by
            rw [smul_add]
    _ = (γ • u + (1 - γ) • u) + γ • a := by
          abel_nf
    _ = u + γ • a := by
          rw [hu]

/-- Helper for Proposition 23.19: membership in the resolvent of `γ • A` is equivalent to an
explicit witness `a ∈ A u` with source point `u + γ • a`. -/
private theorem mem_resolvent_smul_iff_existsValue
    {A : SetValuedOperator H H} {γ : ℝ} {x u : H} :
    u ∈ J[(γ • A)] x ↔
      ∃ a ∈ A u, x = u + γ • a := by
  constructor
  · intro hx
    -- First view `x` as `u + b` with `b ∈ (γ • A) u`, then unpack the scaled witness.
    rcases (mem_resolvent_iff_existsValue.mp hx) with ⟨b, hb, hEq⟩
    change b ∈ γ • A u at hb
    rcases hb with ⟨a, ha, rfl⟩
    exact ⟨a, ha, hEq⟩
  · rintro ⟨a, ha, rfl⟩
    -- Package `γ • a` as a value of `(γ • A) u` and reuse the unscaled resolvent helper.
    refine mem_resolvent_iff_existsValue.mpr ?_
    refine ⟨γ • a, ?_, rfl⟩
    change γ • a ∈ γ • A u
    exact ⟨a, ha, rfl⟩

/-- Proposition 23.19: for any set-valued operator `A` and scalar `γ : ℝ`, the graph of the
resolvent of `γ • A` is the image of the graph of `J[A]` under the affine map
`(x, u) ↦ (γ • x + (1 - γ) • u, u)`. -/
theorem graph_resolvent_smul_eq_image
    {A : SetValuedOperator H H} (γ : ℝ) :
    gra (J[(γ • A)]) =
      (fun xu ↦ (γ • xu.1 + (1 - γ) • xu.2, xu.2)) '' gra (J[A]) := by
  -- Compare both sides by reducing both graph conditions to the same witness `a ∈ A u`.
  ext xu
  rcases xu with ⟨x, u⟩
  constructor
  · intro hx
    rw [Set.mem_image]
    change u ∈ J[(γ • A)] x at hx
    rcases (mem_resolvent_smul_iff_existsValue.mp hx) with ⟨a, ha, rfl⟩
    refine ⟨(u + a, u), ?_, ?_⟩
    · change u ∈ J[A] (u + a)
      exact mem_resolvent_iff_existsValue.mpr ⟨a, ha, rfl⟩
    · -- The affine image of the witness point is exactly the target graph point.
      refine Prod.ext ?_ rfl
      exact affineCombo_eq_base_add_smul γ u a
  · rw [Set.mem_image]
    rintro ⟨⟨y, v⟩, hy, hEq⟩
    -- Read the same witness from the graph point of `J[A]`, then rewrite the target pair.
    have hyv : v ∈ J[A] y := by
      simpa [SetValuedOperator.mem_graph] using hy
    rcases (mem_resolvent_iff_existsValue.mp hyv) with ⟨a, ha, hyEq⟩
    cases hEq
    change v ∈ J[(γ • A)] (γ • y + (1 - γ) • v)
    refine mem_resolvent_smul_iff_existsValue.mpr ⟨a, ha, ?_⟩
    calc
      γ • y + (1 - γ) • v = γ • (v + a) + (1 - γ) • v := by
            rw [hyEq]
      _ = v + γ • a := affineCombo_eq_base_add_smul γ v a

end SetValuedOperator
