import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap04.Definition_4_1
import BauschkeLean.Chap04.Definition_4_10
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Proposition_20_10
import BauschkeLean.Chap21.Theorem_21_1
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Proposition_23_2
import BauschkeLean.Chap23.Proposition_23_22

/- Source/core/bridge triage:
- `source-facing`: the single-valued resolvent and Yosida realizers for a maximally monotone
  operator.
- `core/canonical`: the set-valued owners `J[((γ : ℝ) • A)]` and `{}^[γ] A`.
- `bridge/view`: singleton-valued realizer maps and the corresponding realization theorems. -/

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

section Basic

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- If a self-map `T : H → H` realizes the resolvent `J[((γ : ℝ) • A)]`, then every resolvent
value is the singleton `{T x}`. -/
theorem resolvent_smul_eq_singleton_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (γ : PosReal) (T : H → H)
    (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) (x : H) :
    J[((γ : ℝ) • A)] x = ({T x} : Set H) := by
  rw [← hT, Function.toSetValuedOperator_apply]

/-- If a self-map `T : H → H` realizes the resolvent `J[((γ : ℝ) • A)]`, then its scaled residual
`x ↦ (γ : ℝ)⁻¹ • (x - T x)` realizes the Yosida approximation `{}^[γ] A`. -/
theorem scaledResidual_toSetValuedOperator_eq_yosidaApproximation
    (A : SetValuedOperator H H) (γ : PosReal) (T : H → H)
    (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    (fun x : H ↦ (γ : ℝ)⁻¹ • (x - T x)).toSetValuedOperator = {}^[γ] A := by
  ext x y
  rw [Function.toSetValuedOperator_apply, yosidaApproximation_apply, ← hT,
    Function.toSetValuedOperator_apply]
  constructor
  · rw [Set.mem_singleton_iff]
    intro hy
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero γ.2.ne'), inv_inv, Set.mem_sub]
    refine ⟨x, by simp, T x, by simp, ?_⟩
    calc
      x - T x = (γ : ℝ) • ((γ : ℝ)⁻¹ • (x - T x)) := by
        simp [smul_smul, mul_inv_cancel₀ γ.2.ne']
      _ = (γ : ℝ) • y := by rw [hy]
  · rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero γ.2.ne'), inv_inv, Set.mem_sub]
    rintro ⟨z, rfl, w, rfl, hzw⟩
    rw [Set.mem_singleton_iff]
    simpa [smul_smul, inv_mul_cancel₀ γ.2.ne'] using
      (congrArg (fun v : H ↦ (γ : ℝ)⁻¹ • v) hzw).symm

/-- If a self-map `T : H → H` realizes the resolvent `J[((γ : ℝ) • A)]`, then every Yosida value
is the singleton containing the scaled residual `(γ : ℝ)⁻¹ • (x - T x)`. -/
theorem yosidaApproximation_eq_singleton_scaledResidual_of_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (γ : PosReal) (T : H → H)
    (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) (x : H) :
    ({}^[γ] A) x = ({(γ : ℝ)⁻¹ • (x - T x)} : Set H) := by
  rw [← scaledResidual_toSetValuedOperator_eq_yosidaApproximation A γ T hT,
    Function.toSetValuedOperator_apply]

/-- If a self-map `T : H → H` realizes the resolvent `J[((γ : ℝ) • A)]`, then the residual map
`x ↦ x - T x` realizes the scaled Yosida approximation `(γ : ℝ) • {}^[γ] A`. -/
theorem residual_toSetValuedOperator_eq_smul_yosidaApproximation
    (A : SetValuedOperator H H) (γ : PosReal) (T : H → H)
    (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    (fun x : H ↦ x - T x).toSetValuedOperator = (γ : ℝ) • {}^[γ] A := by
  ext x y
  rw [Function.toSetValuedOperator_apply, Pi.smul_apply,
    yosidaApproximation_eq_singleton_scaledResidual_of_toSetValuedOperator_eq A γ T hT x]
  simp [smul_smul, γ.2.ne']

end Basic

section SingleValuedBridges

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Positive scalar multiples of a maximally monotone operator remain maximally monotone. -/
theorem maximal_isMonotone_smul
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) :
    Maximal IsMonotone ((γ : ℝ) • A) := by
  rw [maximal_iff_mem_iff]
  intro x u
  rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne']
  constructor
  · intro hxu y v hv
    rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hv
    have hrel := (Maximal.mem_iff hA x ((γ : ℝ)⁻¹ • u)).1 hxu hv
    rw [← smul_sub, real_inner_smul_right] at hrel
    nlinarith [inv_pos.mpr γ.2]
  · intro hrel
    refine (Maximal.mem_iff hA x ((γ : ℝ)⁻¹ • u)).2 ?_
    intro y w hw
    have hw' : (γ : ℝ) • w ∈ ((γ : ℝ) • A) y := by
      simpa [Pi.smul_apply] using Set.smul_mem_smul_set hw
    have hrel' := hrel hw'
    have hrewrite :
        inner ℝ (x - y) (u - (γ : ℝ) • w) =
          (γ : ℝ) * inner ℝ (x - y) (((γ : ℝ)⁻¹ : ℝ) • u - w) := by
      calc
        inner ℝ (x - y) (u - (γ : ℝ) • w)
            = inner ℝ (x - y) ((γ : ℝ) • (((γ : ℝ)⁻¹ : ℝ) • u - w)) := by
                congr 2
                calc
                  u - (γ : ℝ) • w = (γ : ℝ) • (((γ : ℝ)⁻¹ : ℝ) • u) - (γ : ℝ) • w := by
                    rw [smul_inv_smul₀ γ.2.ne' u]
                  _ = (γ : ℝ) • ((((γ : ℝ)⁻¹ : ℝ) • u) - w) := by
                    rw [smul_sub]
        _ = (γ : ℝ) * inner ℝ (x - y) ((((γ : ℝ)⁻¹ : ℝ) • u) - w) := by
              rw [real_inner_smul_right]
    rw [hrewrite] at hrel'
    by_contra hneg
    have hneg' : inner ℝ (x - y) ((((γ : ℝ)⁻¹ : ℝ) • u) - w) < 0 := lt_of_not_ge hneg
    have hlt : (γ : ℝ) * inner ℝ (x - y) ((((γ : ℝ)⁻¹ : ℝ) • u) - w) < 0 := by
      exact mul_neg_of_pos_of_neg γ.2 hneg'
    linarith

/-- For maximally monotone `A`, the scaled resolvent `J[((γ : ℝ) • A)]` is everywhere defined. -/
theorem dom_resolvent_smul_eq_univ_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) :
    (J[((γ : ℝ) • A)]).dom = Set.univ := by
  have hγAmono : (((γ : ℝ) • A) : SetValuedOperator H H).IsMonotone := by
    let γnn : NNReal := ⟨(γ : ℝ), γ.2.le⟩
    simpa [γnn] using IsMonotone.smul hA.1 γnn
  have hγAmax : Maximal IsMonotone (((γ : ℝ) • A) : SetValuedOperator H H) :=
    maximal_isMonotone_smul hA γ
  simpa [resolvent_def] using
    (maximal_iff_range_id_add_eq_univ (((γ : ℝ) • A) : SetValuedOperator H H) hγAmono).1 hγAmax

/-- For maximally monotone `A`, every resolvent value `J[((γ : ℝ) • A)] x` is a singleton. -/
private theorem exists_eq_singleton_resolvent_smul_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) (x : H) :
    ∃ y : H, J[((γ : ℝ) • A)] x = ({y} : Set H) := by
  have hxdom : x ∈ (J[((γ : ℝ) • A)]).dom := by
    rw [dom_resolvent_smul_eq_univ_of_maximal A hA γ]
    simp
  rw [mem_dom_iff] at hxdom
  rcases hxdom with ⟨y, hy⟩
  exact ⟨y, resolvent_smul_eq_singleton_of_mem hA.1 γ hy⟩

/-- The maximally monotone resolvent realizer obtained from the singleton-valued owner
`J[((γ : ℝ) • A)]`. -/
noncomputable def resolventMap
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) : H → H :=
  fun x ↦ Classical.choose (exists_eq_singleton_resolvent_smul_of_maximal A hA γ x)

/-- For maximally monotone `A`, the chosen resolvent map realizes the singleton resolvent value. -/
theorem resolvent_smul_eq_singleton_resolventMap_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) (x : H) :
    J[((γ : ℝ) • A)] x = ({resolventMap A hA γ x} : Set H) :=
  Classical.choose_spec (exists_eq_singleton_resolvent_smul_of_maximal A hA γ x)

/-- For maximally monotone `A`, the chosen resolvent map realizes `J[((γ : ℝ) • A)]` as a
singleton-valued operator. -/
theorem resolventMap_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) :
    (resolventMap A hA γ).toSetValuedOperator = J[((γ : ℝ) • A)] := by
  ext x y
  rw [Function.toSetValuedOperator_apply,
    resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ x]

/-- Every canonical resolvent realizer of a maximally monotone operator is firmly nonexpansive on
`Set.univ` in the Chapter 4 ambient self-map sense. -/
theorem resolventMap_firmlyNonexpansiveOn_univ
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) :
    FirmlyNonexpansiveOn (Set.univ : Set H) (resolventMap A hA γ) := by
  rw [firmlyNonexpansiveOn_iff]
  intro x _ y _
  let tx := resolventMap A hA γ x
  let ty := resolventMap A hA γ y
  have htx : tx ∈ J[((γ : ℝ) • A)] x := by
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ x]
    simp [tx]
  have hty : ty ∈ J[((γ : ℝ) • A)] y := by
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ y]
    simp [ty]
  have htx_graph : (tx, (γ : ℝ)⁻¹ • (x - tx)) ∈ gra A := by
    simpa [mem_graph, smul_sub] using (mem_resolvent_smul_iff_mem_graph A γ x tx).1 htx
  have hty_graph : (ty, (γ : ℝ)⁻¹ • (y - ty)) ∈ gra A := by
    simpa [mem_graph, smul_sub] using (mem_resolvent_smul_iff_mem_graph A γ y ty).1 hty
  rw [mem_graph] at htx_graph hty_graph
  have hcross :
      0 ≤
        ⟪tx - ty, ((γ : ℝ)⁻¹ • (x - tx)) - ((γ : ℝ)⁻¹ • (y - ty))⟫_ℝ :=
    (isMonotone_iff A).1 hA.1 htx_graph hty_graph
  have hscaled_cross : 0 ≤ ⟪tx - ty, (x - tx) - (y - ty)⟫_ℝ := by
    have hγinv_pos : 0 < (γ : ℝ)⁻¹ := inv_pos.mpr γ.2
    rw [← smul_sub, real_inner_smul_right] at hcross
    exact nonneg_of_mul_nonneg_right hcross hγinv_pos
  have hdecomp : x - y = (tx - ty) + ((x - tx) - (y - ty)) := by
    abel
  have hnorm :
      ‖x - y‖ ^ 2 =
        ‖tx - ty‖ ^ 2 +
          2 * ⟪tx - ty, (x - tx) - (y - ty)⟫_ℝ +
            ‖(x - tx) - (y - ty)‖ ^ 2 := by
    simpa [hdecomp] using norm_add_sq_real (tx - ty) ((x - tx) - (y - ty))
  nlinarith

/-- The maximally monotone Yosida realizer, defined as the scaled residual of the canonical
resolvent realizer. -/
noncomputable def yosidaApproximationMap
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) : H → H :=
  fun x ↦ (γ : ℝ)⁻¹ • (x - resolventMap A hA γ x)

@[simp] theorem yosidaApproximationMap_apply
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) (x : H) :
    yosidaApproximationMap A hA γ x = (γ : ℝ)⁻¹ • (x - resolventMap A hA γ x) :=
  rfl

/-- For maximally monotone `A`, the chosen Yosida map realizes the singleton Yosida value. -/
theorem yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) (x : H) :
    ({}^[γ] A) x = ({yosidaApproximationMap A hA γ x} : Set H) := by
  simpa [yosidaApproximationMap] using
    yosidaApproximation_eq_singleton_scaledResidual_of_toSetValuedOperator_eq
      A γ (resolventMap A hA γ) (resolventMap_toSetValuedOperator_eq A hA γ) x

/-- For maximally monotone `A`, the chosen Yosida map realizes `{}^[γ] A` as a singleton-valued
operator. -/
theorem yosidaApproximationMap_toSetValuedOperator_eq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) :
    (yosidaApproximationMap A hA γ).toSetValuedOperator = {}^[γ] A := by
  simpa [yosidaApproximationMap] using
    scaledResidual_toSetValuedOperator_eq_yosidaApproximation
      A γ (resolventMap A hA γ) (resolventMap_toSetValuedOperator_eq A hA γ)

end SingleValuedBridges

end SetValuedOperator
