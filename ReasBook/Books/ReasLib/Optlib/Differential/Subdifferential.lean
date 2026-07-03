import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.EReal.Basic
import ReasLib.Optlib.Differential.Calculation
import ReasLib.Optlib.Function.Proximal

noncomputable section

open Filter BigOperators Set Topology

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f g : E → ℝ} {x y u v : E} {c : ℝ}

/- the general differential function used in the definition -/
def differential_fun (x : E) (f : E → ℝ) (u : E) :=
  fun y ↦ Real.toEReal ((f y - f x - inner (ℝ) u (y - x)) / ‖y - x‖)

/- the definition of the Frechet subdifferential-/
def f_subdifferential (f : E → ℝ) (x : E) : Set E :=
  {v : E | liminf (differential_fun x f v) (𝓝[≠] x) ≥ 0}

/- the definition of the limit subdifferential-/
def subdifferential (f : E → ℝ) (x : E) : Set E :=
  {v₀ : E | ∃ u : ℕ → E, Tendsto u atTop (𝓝 x) ∧ Tendsto (fun n ↦ f (u n)) atTop (𝓝 (f x))
    ∧ (∃ v : ℕ → E, ∀ n, v n ∈ f_subdifferential f (u n) ∧ Tendsto v atTop (𝓝 v₀))}

/- the domain of the function is the points whose subifferential are non empty -/
def active_domain (f : E → ℝ) : Set E :=
  {x | subdifferential f x ≠ ∅}

/- the critial point of a function -/
def critial_point (f : E → ℝ) : Set E :=
  {x | 0 ∈ subdifferential f x}

/-- equivalence of Frechet subdifferential -/
theorem has_f_subdiff_iff : u ∈ f_subdifferential f x ↔
    ∀ ε > 0, ∀ᶠ y in 𝓝 x, f y - f x - inner (ℝ) u (y - x) ≥ -ε * ‖y - x‖ := by
  have h0 : (∀ ε > 0, ∀ᶠ y in 𝓝[≠] x, f y - f x - inner (ℝ) u (y - x) > -ε * ‖y - x‖)
      ↔ ∀ ε > 0, ∀ᶠ y in 𝓝 x, f y - f x - inner (ℝ) u (y - x) ≥ -ε * ‖y - x‖ := by
    constructor
    · intro h ε εpos
      specialize h ε εpos
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with y hy
      by_cases heq : y = x; rw [heq]; simp
      exact le_of_lt (hy heq)
    · intro h ε εpos
      specialize h (ε / 2) (by positivity)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [h] with y h hy
      have : 0 < ε * ‖y - x‖ := mul_pos εpos (norm_sub_pos_iff.2 hy)
      linarith
  rw [← h0]
  simp only [f_subdifferential, mem_setOf_eq, liminf, limsInf, eventually_map]
  let sa := {a | ∀ᶠ (y : E) in 𝓝[≠] x, a ≤ differential_fun x f u y}
  constructor
  · intro (h : 0 ≤ sSup sa) ε εpos
    have hn : sa.Nonempty := by
      by_contra hn
      have : sa = ∅ := not_nonempty_iff_eq_empty.mp hn
      rw [this, sSup_empty] at h
      absurd h; exact of_decide_eq_false rfl
    have hsa : Real.toEReal (-ε) < sSup sa := by
      apply lt_of_lt_of_le _ h
      rw [EReal.coe_neg']
      exact neg_neg_iff_pos.mpr εpos
    obtain ⟨a, as, ha⟩ := exists_lt_of_lt_csSup hn hsa
    rw [mem_setOf_eq] at as
    apply Eventually.mp as
    apply eventually_nhdsWithin_of_forall
    rintro y hy h
    have := (lt_div_iff₀ (norm_sub_pos_iff.2 hy)).1 (EReal.coe_lt_coe_iff.1 (lt_of_lt_of_le ha h))
    linarith
  · intro h
    suffices 0 ≤ sSup sa by exact this
    rw [le_sSup_iff]
    intro b hb
    rw [mem_upperBounds] at hb
    contrapose! hb
    have h' : ∀ ε > 0, ∀ᶠ (y : E) in 𝓝[≠] x, differential_fun x f u y > -ε := by
      intro ε εpos
      by_cases hε : ε = ⊤
      · filter_upwards with a
        rw [hε]
        exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
      have heq : ε.toReal = ε := EReal.coe_toReal hε (LT.lt.ne_bot εpos)
      have : 0 < ε.toReal := by
        rw [← EReal.coe_lt_coe_iff]
        exact lt_of_lt_of_eq εpos (id (Eq.symm heq))
      specialize h ε.toReal this
      apply Eventually.mp h
      apply eventually_nhdsWithin_of_forall
      rintro y hy h
      rw [← heq, ← EReal.coe_neg, differential_fun, gt_iff_lt, EReal.coe_lt_coe_iff]
      rw [lt_div_iff₀ (norm_sub_pos_iff.2 hy)]
      linarith
    by_cases hnb : b = ⊥
    · use -1
      constructor
      · specialize h' 1 (zero_lt_one' EReal)
        filter_upwards [h'] with y
        exact le_of_lt
      · rw [hnb]
        exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
    · use b / 2
      have heq : b.toReal = b := EReal.coe_toReal (LT.lt.ne_top hb) hnb
      change b < Real.toEReal 0 at hb
      rw [← heq, EReal.coe_lt_coe_iff] at hb
      constructor
      · have : Real.toEReal 0 < -(b / Real.toEReal 2) := by
          rw [← heq, ← EReal.coe_div, ← EReal.coe_neg, EReal.coe_lt_coe_iff]
          linarith
        specialize h' (-(b / 2)) this
        simp only [neg_neg] at h'
        rw [mem_setOf]
        filter_upwards [h'] with y
        exact le_of_lt
      · suffices b < b / Real.toEReal 2 by exact this
        rw [← heq, ← EReal.coe_div, EReal.coe_lt_coe_iff]
        linarith

/-- frechet subdifferential is a subset of limit subdifferential -/
theorem subdifferential_subset (f : E → ℝ) (x : E) :
    f_subdifferential f x ⊆ subdifferential f x :=
  fun v vin ↦ ⟨(fun _ ↦ x), tendsto_const_nhds, tendsto_const_nhds,
  ⟨fun _ ↦ v, fun _ ↦ ⟨vin, tendsto_const_nhds⟩⟩⟩

/-- the limit subdifferential is a convex set -/
theorem subdifferential_closed (f : E → ℝ) (x : E) : IsClosed (subdifferential f x) := by
  apply IsSeqClosed.isClosed
  intro vn v vnin vntov
  have h' (xk : ℕ → E) (uk: ℕ → E) (u : E) (n : ℕ) (npos : 0 < n) (xkt : Tendsto xk atTop (𝓝 x))
      (fxkt : Tendsto (fun k ↦ f (xk k)) atTop (𝓝 (f x))) (ukt : Tendsto uk atTop (𝓝 u)) :
      ∃ N, ‖(uk N) - u‖ < 1 / (2 * n) ∧ ‖(xk N) - x‖ < 1 / (2 * n)
        ∧ ‖(f (xk N)) - (f x)‖ < 1 / (2 * n) :=by
    have ttrans (ak : ℕ → E) (a: E) (akt : Tendsto ak atTop (𝓝 a)):
        (∃ N, ∀ k, N ≤ k → ‖(ak k) - a‖ < 1 / (2 * n)):=by
      rw [tendsto_atTop_nhds] at akt
      specialize akt (Metric.ball a (1 / (2 * n))) _ _
      simp; apply Nat.zero_lt_of_ne_zero
      apply Nat.ne_zero_iff_zero_lt.mpr npos
      exact Metric.isOpen_ball
      rcases akt with ⟨N, hN⟩
      use N; intro k kge
      specialize hN k kge
      exact mem_ball_iff_norm.mp hN
    have ttransr (ak: ℕ → ℝ) (a: ℝ) (akt : Tendsto ak atTop (𝓝 (a))) :
        ∃ N, ∀ k, N ≤ k → ‖(ak k) - a‖ < (1 / (2 * n)):=by
      rw [tendsto_atTop_nhds] at akt
      specialize akt (Metric.ball a (1 / (2 * n))) _ _
      simp; apply Nat.zero_lt_of_ne_zero
      apply Nat.ne_zero_iff_zero_lt.mpr npos
      exact Metric.isOpen_ball
      rcases akt with ⟨N, hN⟩
      use N; intro k kge
      specialize hN k kge
      exact mem_ball_iff_norm.mp hN
    rcases ttrans xk x xkt with ⟨xkN, hxkN⟩
    rcases ttransr (fun k ↦ f (xk k)) (f x) fxkt with ⟨fxkN, hfxkN⟩
    rcases ttrans uk u ukt with ⟨ukN, hukN⟩
    let N := max (max xkN fxkN) ukN
    use N
    constructor
    · specialize hukN N _
      exact Nat.le_max_right (max xkN fxkN) ukN
      assumption
    constructor
    repeat
    · specialize hxkN N _
      apply le_trans
      apply le_max_left xkN fxkN
      apply le_max_left
      assumption
    · specialize hfxkN N _
      apply le_trans
      apply le_max_right xkN fxkN
      apply le_max_left
      assumption
  rw [subdifferential, mem_setOf] at *
  have h'' : ∀ (n: ℕ), ∃ (xnk: ℕ → E), Tendsto xnk atTop (𝓝 x)
      ∧ Tendsto (fun k ↦ f (xnk k)) atTop (𝓝 (f x))
        ∧ (∃ v, ∀ (n_1 : ℕ), v n_1 ∈ f_subdifferential f (xnk n_1)
          ∧ Tendsto v atTop (𝓝 (vn n))):= by
    intro n; specialize vnin n; rw [mem_setOf] at vnin
    rcases vnin with ⟨xnk, xnkt, fxnkt, other⟩
    use xnk
  apply Classical.axiomOfChoice at h''
  rcases h'' with ⟨xnk, allh⟩
  let xnkt:= fun n ↦ (allh n).left
  let fxnkt:= fun n ↦ (allh n).right.left
  let propv:= fun n ↦ (allh n).right.right
  apply Classical.axiomOfChoice at propv
  rcases propv with ⟨vnk,allh'⟩
  let vnkt:= fun n ↦ (allh' n 1).right
  have npos (n : ℕ) : 0 <n+1 :=by simp
  let hNn := fun n ↦ (h' (xnk (n+1)) (vnk (n+1)) (vn (n+1)) (n+1) (npos n) (xnkt (n+1))
    (fxnkt (n+1)) (vnkt (n+1)))
  apply  Classical.axiomOfChoice at hNn
  rcases hNn with ⟨Nn, hNn'⟩
  use fun n ↦ (xnk (n + 1)) ((Nn (n)))
  constructor
  · rw [tendsto_atTop_nhds]
    intro u xinu uopen
    rw [Metric.isOpen_iff] at uopen
    specialize uopen x xinu
    rcases uopen with ⟨ε, εpos, εin⟩
    rcases Real.exists_floor (1/ε) with ⟨ε',hε',hε''⟩
    have hN: ∃ (N: ℕ), N ≤ (1/ε) ∧ (1/ε) ≤ (N+1):=by
      have hN': ∃ (N: ℕ), N = ε':=by
        refine CanLift.prf ε' ?_
        by_contra εneg
        push_neg at εneg
        specialize hε'' 0 _
        apply le_of_lt
        simp at εpos; simp
        apply εpos; linarith
      rcases hN' with ⟨N,hN'⟩
      use N
      have hN'' : (N : ℝ) = (ε' : ℝ):= Eq.symm
        (Real.ext_cauchy (congrArg Real.cauchy (congrArg Int.cast (id (Eq.symm hN')))))
      constructor
      rw [hN'']
      exact hε'
      rw [hN'']
      by_contra this
      push_neg at this
      specialize hε'' (ε' +1) _
      apply le_of_lt
      simp; simp at this; apply this
      have this: ¬ ε' + 1 ≤ ε' := by linarith
      apply this; apply hε''
    rcases hN with ⟨N,_,Nge⟩
    use (N)
    intro n nge
    apply mem_of_subset_of_mem
    · apply εin
    rw [Metric.ball,mem_setOf, dist_eq_norm]
    apply lt_of_lt_of_le
    · apply (hNn' n).right.left
    simp; apply le_trans
    · apply le_of_lt
      apply div_two_lt_of_pos
      apply inv_pos.mpr
      linarith
    apply (inv_le_comm₀ _ _).mp
    · simp at Nge
      apply le_trans
      · apply Nge
      simp; assumption
    · simp at εpos
      assumption
    linarith
  constructor
  · rw [tendsto_atTop_nhds]
    intro u fxinu uopen
    rw [Metric.isOpen_iff] at uopen
    specialize uopen (f x) fxinu
    rcases uopen with ⟨ε, εpos, εin⟩
    rcases Real.exists_floor (1/ε) with ⟨ε',hε',hε''⟩
    have hN: ∃ (N: ℕ), N ≤ (1/ε) ∧ (1/ε) ≤ (N+1):=by
      have hN': ∃ (N: ℕ), N = ε':=by
        refine CanLift.prf ε' ?_
        by_contra εneg
        push_neg at εneg
        specialize hε'' 0 _
        apply le_of_lt
        simp at εpos
        simp
        apply εpos
        linarith
      rcases hN' with ⟨N,hN'⟩
      use N
      have hN'' : (N:ℝ) = (ε':ℝ):=
        Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (congrArg Int.cast (id (Eq.symm hN')))))
      constructor
      rw [hN'']
      exact hε'
      rw [hN'']
      by_contra this
      push_neg at this
      specialize hε'' (ε' +1) _
      apply le_of_lt
      simp
      simp at this
      apply this
      have this: ¬ ε' + 1 ≤ ε':=by linarith
      apply this
      apply hε''
    rcases hN with ⟨N,_,Nge⟩
    use N
    intro n nge
    apply mem_of_subset_of_mem
    · apply εin
    rw [Metric.ball,mem_setOf, dist_eq_norm]
    apply lt_of_lt_of_le
    · apply (hNn' n).right.right
    simp
    apply le_trans
    · apply le_of_lt
      apply div_two_lt_of_pos
      apply inv_pos.mpr
      linarith
    apply (inv_le_comm₀ _ _).mp
    · simp at Nge
      apply le_trans
      · apply Nge
      simp; assumption
    · simp at εpos
      assumption
    linarith
  · use fun n ↦ (vnk (n+1)) ((Nn (n)))
    intro n
    constructor
    · specialize allh' (n+1) (Nn n)
      apply allh'.left
    rw [tendsto_atTop_nhds]
    intro u vinu uopen
    rw [Metric.isOpen_iff] at uopen
    specialize uopen (v) vinu
    rcases uopen with ⟨ε, εpos, εin⟩
    rcases Real.exists_floor (1/ε) with ⟨ε',hε',hε''⟩
    have hN: ∃ (N: ℕ), N ≤ (1/ε) ∧ (1/ε) ≤ (N+1):=by
      have hN': ∃ (N: ℕ), N = ε':=by
        refine CanLift.prf ε' ?_
        by_contra εneg
        push_neg at εneg
        specialize hε'' 0 _
        apply le_of_lt
        simp at εpos
        simp
        apply εpos
        linarith
      rcases hN' with ⟨N,hN'⟩
      use N
      have hN'' : (N:ℝ)=(ε':ℝ):=
        Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (congrArg Int.cast (id (Eq.symm hN')))))
      constructor
      rw [hN'']
      exact hε'
      rw [hN'']
      by_contra this
      push_neg at this
      specialize hε'' (ε' +1) _
      apply le_of_lt
      simp
      simp at this
      apply this
      have this: ¬ ε' + 1 ≤ ε':=by linarith
      apply this
      apply hε''
    rcases hN with ⟨N,Nle,Nge⟩
    let δ:= (1:ℝ)/(2* (N+1))
    have le': ∃ N', ∀ k , N' ≤ k → ‖vn (k+1) - v‖ < δ:=by
      rw [tendsto_atTop_nhds] at vntov
      specialize vntov (Metric.ball v δ) _ _
      apply Metric.mem_ball_self
      refine one_div_pos.mpr ?specialize_1.h.a
      apply mul_pos
      simp
      linarith
      exact Metric.isOpen_ball
      rcases vntov with ⟨N, hN⟩
      use (N-1); intro k kge
      specialize hN (k+1) _
      exact Nat.le_add_of_sub_le kge
      apply mem_ball_iff_norm.mp
      assumption
    rcases le' with ⟨N',hN'⟩
    use (max N N'); intro n nge
    apply mem_of_subset_of_mem
    · apply εin
    rw [Metric.ball,mem_setOf, dist_eq_norm]
    apply lt_of_lt_of_le
    · rw [← add_sub_cancel (vn (n+1)) (vnk (n + 1) (Nn n)), add_comm, ← add_sub]
      apply lt_of_le_of_lt
      · apply norm_add_le
      have this : ‖vnk (n + 1) (Nn n) - vn (n + 1)‖ + ‖vn (n + 1) - v‖ < (1:ℝ)/(N+1):=by
        specialize hN' n _
        apply le_trans
        apply le_max_right
        exact N
        assumption
        specialize hNn' n
        let vnkle:= hNn'.left
        have vnkle': ‖vnk (n + 1) (Nn n) - vn (n + 1)‖ < δ:=by
          apply lt_of_lt_of_le vnkle
          apply (one_div_le_one_div _ _).mpr
          simp
          apply le_trans
          apply le_max_left
          apply N'
          assumption
          simp
          exact Nat.cast_add_one_pos n
          simp
          exact Nat.cast_add_one_pos N
        have that: δ + δ = 1 / (↑N + 1):=by
          rw [← mul_two, div_mul]; simp
        rw [← that]
        apply add_lt_add
        repeat' assumption
      apply this
    apply (one_div_le _ _).mpr
    · assumption
    · exact Nat.cast_add_one_pos N
    simp at εpos
    assumption

/-- the Frechet subdifferential is a closed set -/
theorem f_subdiff_closed (f : E → ℝ) (x : E) : IsClosed (f_subdifferential f x) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro v hv'
  rw [mem_compl_iff, has_f_subdiff_iff] at hv';
  push_neg at hv'
  rcases hv' with ⟨ε, εpos, hε⟩
  rw [Filter.Eventually, mem_nhds_iff] at hε
  push_neg at hε
  have hh : f_subdifferential f x =
      {u | ∀ ε > 0, ∀ᶠ (y : E) in 𝓝 x, f y - f x - (inner (ℝ) u (y - x)) ≥ -ε * ‖y - x‖} := by
    ext u
    rw [has_f_subdiff_iff,mem_setOf]
  rw [hh]
  by_contra h
  push_neg at h
  have ε2pos: 0 < (ε / 2):=by linarith
  specialize h (ε / 2)  ε2pos
  rw [not_subset] at h
  rcases h with ⟨a, amem,anotmem⟩
  rw [notMem_compl_iff, mem_setOf] at anotmem
  specialize anotmem (ε / 2)  ε2pos
  rw [Filter.Eventually, mem_nhds_iff] at anotmem
  rcases anotmem with ⟨ta, tasubset,taopen,xinta⟩
  have tasubset': ta ⊆ {x_1 | f x_1 - f x - (inner (ℝ) v (x_1 - x)) ≥ -ε * ‖x_1 - x‖} := by
    intro y yinta; rw [mem_setOf, ge_iff_le]
    rw [← add_sub_cancel a v, inner_add_left, ← sub_sub,
      sub_eq_add_neg (f y - f x - inner (ℝ) a (y - x))]
    have εtrans: -ε  = -(ε / 2) + -(ε / 2) :=by linarith
    rw [εtrans, add_mul]
    apply add_le_add
    · exact tasubset yinta
    · simp
      apply le_trans; apply real_inner_le_norm
      apply mul_le_mul_of_nonneg_right
      rw [← dist_eq_norm']
      rw [Metric.ball, mem_setOf] at amem
      exact le_of_lt amem
      apply norm_nonneg
  specialize hε ta tasubset' taopen
  apply hε
  apply xinta

/-- the Frechet subdifferential is a convex set -/
theorem f_subdiff_convex (f : E → ℝ) (x : E) : Convex ℝ (f_subdifferential f x):= by
  intro u hu v hv a b ha hb hab
  rw [has_f_subdiff_iff] at *
  intro ε εpos
  filter_upwards [hu _ εpos, hv _ εpos] with y hyu hyv
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [← one_mul (f y), ← one_mul (f x), ← hab, add_mul, add_mul, sub_add_eq_sub_sub,
    add_comm ,sub_add_eq_sub_sub, ← add_sub , ← mul_sub a (f y) (f x), add_comm,  ← add_sub,
    ← mul_sub, add_comm, ← add_sub, ← mul_sub, add_comm, ← add_sub, ← mul_sub]
  rw [← one_mul (-ε * ‖y - x‖), ← hab, add_mul]
  rw [ge_iff_le] at *
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hyu ha
  · exact mul_le_mul_of_nonneg_left hyv hb

/-- if f is a convex function, Frechet subdifferential is equal to subgradient -/
theorem convex_f_f_subdiff_eq_subgradient (f : E → ℝ) (x : E)
    (hconv : ConvexOn ℝ univ f) : f_subdifferential f x = SubderivAt f x := by
  rw [SubderivAt]
  ext g
  rw [mem_setOf, HasSubgradientAt]
  constructor
  · intro hg
    by_contra h'
    push_neg at h'
    rcases h' with ⟨y', hy'⟩
    rw [has_f_subdiff_iff] at hg
    rw [ConvexOn] at hconv
    rcases hconv with ⟨convset,convfun⟩
    have xin: x ∈ univ:= by
      simp
    have yin': y' ∈ univ:= by
      simp
    specialize convfun xin yin'
    have pos: 0 < (1 / 2) * ((f x) + inner (ℝ) g (y' - x) - f y') / ‖y' - x‖:=by
      apply div_pos
      · apply mul_pos
        simp; simp
        apply hy'
      · apply norm_pos_iff.mpr
        by_contra yeq'
        rw [sub_eq_zero] at yeq'
        rw [yeq'] at hy'
        simp at hy'
    rw [← gt_iff_lt] at pos
    specialize hg ((1 / 2) * ((f x) + inner (ℝ) g (y' - x) - f y')/‖y' - x‖)
    specialize hg pos
    simp at hg
    rw [Filter.Eventually,mem_nhds_iff] at hg
    rcases hg with ⟨T,tin,topen,xint⟩
    let S:= {x_1 | ∃(r : ℝ), 0 < r  ∧  r < 1 ∧ x_1 = r • x + (1 -r) • y'}
    let ST:= S ∩ T
    have STnonempty: ∃ x_1, x_1 ∈ ST:=by
      rw [Metric.isOpen_iff] at topen
      specialize topen x xint
      rcases topen with ⟨δ, posδ,hδ⟩
      let δ':= min δ ‖y' - x‖
      let δ'' := 1 - (1 / 2) * (δ' / ‖y' - x‖)
      use (δ'') • x + (1 - δ'') • y'
      apply mem_inter
      · rw [mem_setOf]
        use δ''
        constructor
        · apply sub_pos_of_lt
          simp
          refine (inv_mul_lt_iff₀ ?h.left.a.h).mpr ?h.left.a.a
          · simp
          · simp
            apply lt_of_le_of_lt
            apply (div_le_one _).mpr
            apply min_le_right
            apply norm_pos_iff.mpr
            by_contra yeq'
            rw [sub_eq_zero] at yeq'
            rw [yeq'] at hy'
            rw [sub_self, inner_zero_right,add_zero, lt_iff_not_ge] at hy'
            apply hy'
            simp
            simp
        constructor
        · change 1 - 1 / 2 * (δ' / ‖y' - x‖) < 1
          simp
          apply div_pos
          · apply lt_min
            apply posδ
            apply norm_pos_iff.mpr
            by_contra yeq'
            rw [sub_eq_zero] at yeq'
            rw [yeq'] at hy'
            rw [sub_self, inner_zero_right,add_zero, lt_iff_not_ge] at hy'
            apply hy'
            simp
          · apply norm_pos_iff.mpr
            by_contra yeq'
            rw [sub_eq_zero] at yeq'
            rw [yeq'] at hy'
            rw [sub_self, inner_zero_right,add_zero, lt_iff_not_ge] at hy'
            apply hy'
            simp
        simp
      apply mem_of_subset_of_mem hδ
      rw [Metric.ball, mem_setOf,dist_eq_norm]
      have this: δ'' • x + (1 - δ'') • y' - x = (1 - δ'') • (y' - x):=by
        rw [smul_sub,sub_smul 1 δ'',sub_smul 1 δ'']
        rw [add_sub, sub_sub_sub_eq, add_comm (1 • y'), one_smul, one_smul]
        rw [sub_sub]
      rw [this, norm_smul]
      simp
      rw [← sub_add]; simp
      rw [abs_eq_self.mpr (by positivity : 0 ≤ δ' / ‖y' - x‖)]
      rw [mul_assoc]
      have ht : δ' / ‖y' - x‖ * ‖y' - x‖ = δ':=by
        have nonzero: ‖y' - x‖ ≠ 0:=by
          by_contra yeq'
          rw [norm_eq_zero,sub_eq_zero] at yeq'
          rw [yeq'] at hy'
          rw [sub_self, inner_zero_right,add_zero, lt_iff_not_ge] at hy'
          apply hy'
          simp
        refine div_mul_cancel₀ δ' nonzero
      have hp : |δ' / ‖y' - x‖| = δ' / ‖y' - x‖ := by rw [abs_eq_self]; positivity
      rw [ht]
      rw [inv_eq_one_div]
      have : δ' ≤ δ := min_le_left δ ‖y' - x‖
      linarith [lt_two_mul_self posδ]
    rcases STnonempty with ⟨x1,hx1⟩
    rw [mem_inter_iff] at hx1
    rcases hx1 with ⟨x1s,x1t⟩
    rw [mem_setOf] at x1s
    rcases x1s with ⟨r,rpos,rltone,x1eq⟩
    have x1in: x1 ∈ {x_1 | inner (ℝ) g (x_1 - x) ≤
        f x_1 - f x + 2⁻¹ * (f x + inner (ℝ) g (y' - x) - f y') / ‖y' - x‖ * ‖x_1 - x‖}:=by
      apply mem_of_subset_of_mem tin
      assumption
    rw [mem_setOf,x1eq] at x1in
    rw [add_comm] at x1in
    have this: (1 - r) • y' + r • x - x = (1 - r) • (y' - x):=by
      rw [smul_sub,sub_smul 1 r,sub_smul 1 r]
      rw [sub_sub_sub_eq, add_comm (1 • y'), one_smul, one_smul,add_comm]
      rw [add_sub_add_comm, add_sub,add_sub]
      simp
      rw [add_comm, add_comm (r • x - r • y'),add_sub]
    rw [this] at x1in
    rw [inner_smul_right, norm_smul] at x1in
    have rnonneg: 0 ≤ r:=by linarith
    have rleone: 0 ≤ 1-r:=by linarith
    have r2pos: 0 < (1 -r)/2:=by linarith
    have req: r + (1-r) = 1:=by simp
    specialize convfun rnonneg rleone req
    have nonneg: 0 ≤ f y' - f x - inner (ℝ) g (y' - x):=by
      apply nonneg_of_mul_nonneg_right _ r2pos
      rw [mul_sub, ← sub_self_div_two (1 - r), sub_mul, sub_mul (1 - r)]
      simp
      apply le_trans x1in
      rw [add_comm ((1 - r) • y'), sub_add, sub_le_iff_le_add]
      apply le_trans convfun
      simp;
      rw [abs_eq_self.mpr rleone]
      rw [← mul_assoc]; rw [← sub_le_iff_le_add]
      rw [← sub_add, add_comm (r*f x), add_comm (f x), ← add_sub, ← add_sub, mul_add]
      nth_rw 2 [← one_mul (f x)]
      rw [← sub_mul]
      nth_rw 2 [ ← neg_sub ]
      rw [neg_mul,← sub_eq_add_neg ((1 - r) * f y'),← mul_sub, mul_assoc, mul_comm (1 - r) ‖y' - x‖]
      rw [← mul_assoc, div_mul, div_self]
      simp
      rw [mul_comm (2⁻¹ * inner (ℝ) g (y' - x) + 2⁻¹ * (f x - f y')),
        mul_add, add_comm ((1 - r) * (2⁻¹ * inner (ℝ) g (y' - x)))]
      rw [← add_assoc, ← mul_assoc, ← mul_assoc,inv_eq_one_div]
      linarith
      by_contra yeq'
      rw [norm_eq_zero,sub_eq_zero] at yeq'
      rw [yeq'] at hy'
      rw [sub_self, inner_zero_right,add_zero, lt_iff_not_ge] at hy'
      apply hy'
      simp
    have nonneg': ¬ 0 > f y' - f x - inner (ℝ) g (y' - x):=by linarith
    apply nonneg'
    simp
    linarith
  · intro h
    rw [has_f_subdiff_iff]
    intro ε εpos
    filter_upwards
    intro y
    rw [ge_iff_le]
    apply le_trans
    · simp
      apply neg_le.mpr
      · have pos: - 0 ≤ ε * ‖y - x‖:=by
          simp
          rw [mul_comm]
          apply (mul_nonneg_iff_left_nonneg_of_pos εpos).mpr
          simp
        apply pos
    simp
    specialize h y
    simp at h
    linarith

/-- correlation of the Frechet subdifferential between negative function -/
theorem f_subdiff_neg_f_subdiff_unique (hu : u ∈ f_subdifferential f x)
    (hv : v ∈ f_subdifferential (-f) x) : u = - v := by
  rw [has_f_subdiff_iff] at *
  have h : ∀ ε > 0, ∀ᶠ y in 𝓝 x, inner (ℝ) (u + v) (y - x) ≤ ε * ‖y - x‖ := by
    intro ε εpos
    have ε2pos : 0 < ε / 2 := by positivity
    filter_upwards [hu _ ε2pos, hv _ ε2pos] with y huy hvy
    rw [InnerProductSpace.add_left]
    simp only [Pi.neg_apply, sub_neg_eq_add] at hvy
    linarith
  by_cases heq : u + v = 0
  · exact eq_neg_of_add_eq_zero_left heq
  apply eq_of_forall_dist_le
  rw [dist_eq_norm, sub_neg_eq_add]
  intro ε εpos
  specialize h ε εpos
  rw [Metric.eventually_nhds_iff_ball] at h
  obtain ⟨δ, δpos, hd⟩ := h
  have hne := norm_ne_zero_iff.mpr heq
  have hb : x + (δ / 2 / ‖u + v‖) • (u + v) ∈ Metric.ball x δ := by
    rw [mem_ball_iff_norm', sub_add_cancel_left]
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_div, abs_norm]
    rw [div_mul_cancel₀ _ hne, abs_of_nonneg (by positivity)]
    linarith
  specialize hd (x + ((δ / 2) / ‖u + v‖) • (u + v)) hb
  rw [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_div, abs_norm] at hd
  rw [real_inner_self_eq_norm_mul_norm, ← mul_assoc, div_mul_cancel₀ _ hne] at hd
  rw [div_mul_cancel₀ _ hne, abs_of_nonneg (by positivity), mul_comm] at hd
  exact le_of_mul_le_mul_right hd (by positivity)

/-- the calculation rule for addition -/
theorem f_subdiff_add (hf : u ∈ f_subdifferential f x) (hg : v ∈ f_subdifferential g x) :
    u + v ∈ f_subdifferential (f + g) x := by
  rw [has_f_subdiff_iff] at *
  intro ε εpos
  have ε2pos : 0 < ε / 2 := by positivity
  filter_upwards [hf _ ε2pos, hg _ ε2pos] with y hfy hgy
  simp only [Pi.add_apply, neg_mul, ge_iff_le, neg_le_sub_iff_le_add]
  rw [InnerProductSpace.add_left]
  linarith

/-- the calculation rule for functions timing a positive constant -/
theorem f_subdiff_smul (h : u ∈ f_subdifferential (c • f) x) (cpos : 0 < c) :
    c⁻¹ • u ∈ f_subdifferential f x := by
  rw [has_f_subdiff_iff] at *
  intro ε εpos
  filter_upwards [h _ (mul_pos cpos εpos)] with y hy
  rw [real_inner_smul_left]
  simp only [Pi.smul_apply, smul_eq_mul, neg_mul, neg_le_sub_iff_le_add] at hy
  apply (mul_le_mul_iff_right₀ cpos).mp
  field_simp
  linarith

/-- if f is convex , then Frechet subdifferential equals subdifferential equals subgradient -/
theorem convex_f_f_subdiff_eq_subdiff (f : E → ℝ) (x : E)
    (hconv : ConvexOn ℝ univ f) : f_subdifferential f x = subdifferential f x := by
  rw [subdifferential]
  ext v
  rw [mem_setOf]
  constructor
  · intro h
    use fun (_k : ℕ) ↦ x
    constructor
    · simp
    constructor
    · simp
    use fun _k ↦ v
    intro _k
    constructor
    · assumption
    simp
  · intro h
    rw [convex_f_f_subdiff_eq_subgradient f x hconv]
    rcases h with ⟨u, utendsx, futendsfx,vn, hvn⟩
    rw [SubderivAt, mem_setOf, HasSubgradientAt]
    intro y
    have hvnin: ∀ (n : ℕ), f y ≥ f (u n) + inner (ℝ) (vn n) (y - (u n)):=by
      intro n
      specialize hvn n
      rcases hvn with ⟨hvnin,vntendsv⟩
      rw [convex_f_f_subdiff_eq_subgradient f (u n) hconv] at hvnin
      rw [SubderivAt, mem_setOf, HasSubgradientAt] at hvnin
      apply hvnin
    have vntendsv: Tendsto vn atTop (𝓝 v):=by
      specialize hvn 1
      exact hvn.right
    have tendsto: Tendsto (fun n ↦ f (u n) +
        inner (ℝ) (vn n) (y - (u n))) atTop (𝓝 (f x + inner (ℝ) v (y - x))):=by
      apply Tendsto.add futendsfx
      apply Tendsto.inner vntendsv
      exact (tendsto_const_sub_iff y).mpr utendsx
    simp
    simp at hvnin
    apply le_of_tendsto_of_frequently
    · apply tendsto
    exact Filter.Frequently.of_forall hvnin

/-- first order optimality condition for unconstrained optimization problem -/
theorem first_order_optimality_condition (f : E → ℝ) (x₀ : E) (hx : IsLocalMin f x₀) :
    (0 : E) ∈ f_subdifferential f x₀ := by
  rw [has_f_subdiff_iff]
  intro ε εpos
  filter_upwards [hx] with y hy
  have : 0 ≤ ε * ‖y - x₀‖ := by positivity
  simp only [inner_zero_left, sub_zero, neg_mul, ge_iff_le, neg_le_sub_iff_le_add]
  linarith

/-- first order optimality condition for unconstrained optimization problem -/
theorem first_order_optimality_condition' (f : E → ℝ) (x₀ : E) (hx : IsLocalMin f x₀) :
    (0 : E) ∈ subdifferential f x₀ := by
  obtain hcon := subdifferential_subset f x₀
  apply hcon; exact first_order_optimality_condition f x₀ hx

end

section

open Filter BigOperators Set Topology

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g : E → ℝ} {x y u v : E} {c : ℝ}

/-- an equal statement for differential function in Frechet subdifferential -/
theorem HasGradientAt_iff_f_subdiff :
    HasGradientAt f u x ↔ u ∈ f_subdifferential f x ∧ -u ∈ f_subdifferential (-f) x := by
  rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  rw [has_f_subdiff_iff, has_f_subdiff_iff]
  constructor
  · intro h
    constructor
    · intro ε εpos
      filter_upwards [h εpos] with y hy
      rw [Real.norm_eq_abs, abs_le] at hy
      linarith
    · intro ε εpos
      filter_upwards [h εpos] with y hy
      rw [Real.norm_eq_abs, abs_le] at hy
      simp only [Pi.neg_apply, sub_neg_eq_add, inner_neg_left, neg_mul]
      linarith
  · intro ⟨h1, h2⟩ c cpos
    filter_upwards [h1 c cpos, h2 c cpos] with y h1y h2y
    simp only [Pi.neg_apply, sub_neg_eq_add, inner_neg_left, neg_mul] at h2y
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith

/-- the Frechet subdifferential of a differentiable function is its gradient set -/
theorem f_subdiff_gradiant (f : E → ℝ) (f' : E → E) (z : E) (hf : HasGradientAt f (f' z) z) :
    f_subdifferential f z = {f' z} := by
  ext u
  rw [mem_singleton_iff]
  rw [HasGradientAt_iff_f_subdiff] at hf
  constructor
  · exact fun h ↦(neg_neg (f' z)) ▸ (f_subdiff_neg_f_subdiff_unique h hf.2)
  · exact fun h ↦ h ▸ hf.1

/-- the subdifferential of a differentiable function is its gradient set -/
theorem subdiff_gradient (f : E → ℝ) (f' : E → E) (hf : ∀ x₁, HasGradientAt f (f' x₁) x₁)
    (gradcon : Continuous f') (z : E) : subdifferential f z = {f' z} := by
  rw [subdifferential]
  ext x
  constructor
  · intro xin
    rw [mem_setOf] at *
    rcases xin with ⟨u, ⟨utendz, ⟨utendfz, ⟨v, hv⟩⟩⟩⟩
    have veq : ∀ (n : ℕ), v n = f' (u n) := by
      intro n
      rcases hv n with ⟨vin,vtend⟩
      rw [f_subdiff_gradiant f f' ] at vin
      exact vin
      exact hf (u n)
    apply tendsto_nhds_unique (hv 1).right
    rw [tendsto_congr veq]
    apply tendsto_atTop_nhds.mpr
    intro U uin uopen
    rw [continuous_def] at gradcon
    rw [tendsto_atTop_nhds] at utendz
    have zinvu : z ∈ ((f') ⁻¹' U) := by simp; assumption
    rcases utendz ((f') ⁻¹' U) zinvu (gradcon U uopen) with ⟨N, hN⟩
    use N
    intro n nge
    change u n ∈ (f') ⁻¹' U
    apply hN n nge
  · intro xin
    rw [mem_setOf,xin]
    use fun _ ↦ z
    constructor
    · simp
    constructor
    · simp
    use fun _ ↦ f' z
    intro _ ;constructor;
    · rw [f_subdiff_gradiant f f']
      · rfl
      apply hf z
    simp only [tendsto_const_nhds_iff]

theorem f_subdiff_add_smooth (h : u ∈ f_subdifferential f x) (hg : HasGradientAt g v x) :
    u + v ∈ f_subdifferential (f + g) x :=
  f_subdiff_add h (HasGradientAt_iff_f_subdiff.mp hg).1

lemma f_subdiff_prox (h : prox_prop f y x) : y - x ∈ f_subdifferential f x := by
  have : IsLocalMin (fun u ↦ f u + ‖u - y‖ ^ 2 / 2) x := by
    have := h.localize
    rwa [IsLocalMinOn, nhdsWithin_univ] at this
  have hd := first_order_optimality_condition _ _ this
  have hg :=  HasGradientAt.neg (@gradient_of_sq _ _ _ _ y x)
  have := f_subdiff_add_smooth hd hg
  simp only [neg_sub, zero_add] at this
  have hf : f = (fun u ↦ f u + ‖u - y‖ ^ 2 / 2) + fun x ↦ -(‖x - y‖ ^ 2 / 2) := by
    ext x
    simp only [Pi.add_apply, add_neg_cancel_right]
  exact hf ▸ this

/-- if one function is differentiable, the Frechet subdifferential of the sum of two functions
can be transverted to the sum of Frechet subdifferential for each function -/
theorem f_subdiff_add' (f : E → ℝ) (g : E → ℝ) (g' : E → E) (x : E)
    (hg : ∀ x₁, HasGradientAt g (g' x₁) x₁) (z : E) :
    z ∈ f_subdifferential (f + g) x ↔ ∃ zf ∈ f_subdifferential f x , ∃ zg ∈ f_subdifferential g x ,
    z = zf + zg := by
  constructor
  · intro zin
    use z - g' x
    constructor
    · rw [has_f_subdiff_iff] at *
      intro ε εpos
      specialize hg x
      rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hg
      have ε2pos : 0 < ε / 2 := by positivity
      specialize hg ε2pos
      filter_upwards [zin _ ε2pos, hg ] with a za ga
      simp at ga
      have h: - (g a - g x - inner (ℝ) (g' x) (a - x)) ≥ -(ε / 2) * ‖a - x‖:=by
        change -(ε / 2) * ‖a - x‖ ≤ - (g a - g x - inner (ℝ) (g' x) (a - x))
        rw [neg_mul, neg_le_neg_iff]
        apply le_trans; apply le_abs_self; assumption
      rw [inner_sub_left];
      simp; simp at h za
      linarith
    · use g' x
      constructor
      · rw [f_subdiff_gradiant g g']
        · simp
        exact hg x
      · simp
  · intro zin
    rcases zin with ⟨zf,zfin,zg,zgin,fgadd⟩
    rw [fgadd]
    apply f_subdiff_add;
    repeat' assumption

/-- if one function is smooth, the subdifferential of the sum of two functions
can be transverted to the sum of subdifferential for each function -/
theorem subdiff_add (f : E → ℝ) (g : E → ℝ) (g' : E → E) (x : E)
    (hg : ∀ x₁, HasGradientAt g (g' x₁) x₁) (gcon : Continuous g)
      (gradcon : Continuous g') (z : E) :
        z ∈ subdifferential (f + g) x ↔ ∃ zf ∈ subdifferential f x,
          ∃ zg ∈ subdifferential g x, z = zf + zg := by
  constructor
  · intro zin
    rw [subdifferential,mem_setOf] at zin
    rcases zin with ⟨u,hux,hufx,hv⟩
    rcases hv with ⟨v,vlim⟩
    use z - g' x
    constructor
    · rw [subdifferential,mem_setOf]
      constructor
      · constructor
        · use hux
        constructor
        · have glim: Tendsto (fun n ↦ -g (u n)) atTop (𝓝 (-g x)):=by
            have contneg: Continuous (-g):=by
              exact continuous_neg_iff.mpr gcon
            apply tendsto_atTop_nhds.mpr
            intro U uin uopen
            rw [continuous_def] at contneg
            rw [tendsto_atTop_nhds] at hux
            have invuopen:IsOpen ((-g) ⁻¹' U):=by
              exact contneg U uopen
            have xinvu: x ∈ ((-g) ⁻¹' U):=by
              simp;exact uin
            rcases hux ((-g) ⁻¹' U) xinvu invuopen with ⟨N,hN ⟩
            use N
            intro n nge
            change u n ∈ (-g) ⁻¹' U
            apply hN n nge
          have functrans: (fun n ↦ f (u n)) = (fun n ↦ ((f+g) (u n)) + (-g (u n))):=by
            ext n
            simp
          rw [functrans]
          have nhds_trans: 𝓝 (f x) = (𝓝 ((f + g) x + -g x)):=by
            simp
          rw [nhds_trans]
          apply Filter.Tendsto.add hufx glim
        use fun n ↦ (v n) - (g' (u n))
        intro n
        rcases vlim n with ⟨vin,vtends⟩
        constructor
        · rw [f_subdiff_add'] at vin
          · rw [f_subdiff_gradiant g g'] at vin
            · rcases vin with ⟨zf,zfin,zg,zgin,fgadd⟩
              simp at zgin; simp
              rw [fgadd, zgin]
              simp; assumption
            exact hg (u n)
          · use g'
          exact hg
        have gradlim: Tendsto (fun n ↦   g' (u n)) atTop (𝓝 (  g' x)):=by
          apply tendsto_atTop_nhds.mpr
          intro U uin uopen
          rw [continuous_def] at gradcon
          rw [tendsto_atTop_nhds] at hux
          have invuopen:IsOpen ((g') ⁻¹' U):=by
              exact gradcon U uopen
          have xinvu: x ∈ ((g') ⁻¹' U):=by
              simp;exact uin
          rcases hux ((g') ⁻¹' U) xinvu invuopen with ⟨N,hN ⟩
          use N
          intro n nge
          change u n ∈ (g') ⁻¹' U
          apply hN n nge
        apply Tendsto.sub vtends
        assumption

    · use g' x
      constructor
      · rw [subdiff_gradient g g' hg gradcon]
        simp
      · simp

  · intro zin
    rcases zin with ⟨zf,zfin,zg,zgin,fgadd⟩
    rw [fgadd,subdifferential,mem_setOf]
    rw [subdifferential,mem_setOf] at zfin zgin
    rcases zfin with ⟨uf,ufx,uffx,hfv⟩
    rcases hfv with ⟨vf,vflim⟩
    rcases zgin with ⟨ug,ugx,uggx,hgv⟩
    rcases hgv with ⟨vg,vglim⟩
    constructor
    constructor
    · use ufx
    constructor
    · apply Filter.Tendsto.add
      · exact uffx
      apply tendsto_atTop_nhds.mpr
      intro U uin uopen
      rw [continuous_def] at gcon
      rw [tendsto_atTop_nhds] at ufx
      have invuopen:IsOpen ((g) ⁻¹' U):=by
        exact gcon U uopen
      have xinvu: x ∈ ((g) ⁻¹' U):=by
        simp; exact uin
      rcases ufx ((g) ⁻¹' U) xinvu invuopen with ⟨N,hN ⟩
      use N
      intro n nge
      change uf n ∈ (g) ⁻¹' U
      apply hN n nge
    · use fun n ↦ (vf n) + g' (uf n)
      intro n
      constructor
      · rcases vglim n with ⟨vgin,vgtends⟩
        rcases vflim n with ⟨vfin,vftends⟩
        · rw [f_subdiff_add' f g g']
          · rw [f_subdiff_gradiant g g'];
            · rw [f_subdiff_gradiant g g'] at vgin
              · simp at vgin
                use vf n
                constructor
                · assumption
                use g' (uf n)
                constructor
                · simp
                simp
              apply hg (ug n)
            apply hg (uf n)
          repeat' assumption
      · apply Filter.Tendsto.add
        · rcases vflim n with ⟨_,vflim⟩
          apply vflim
        have limgrad: (An: ℕ → E) → (x : E) → (Tendsto An atTop (𝓝 x))→ Tendsto (fun n ↦ g' (An n))
            atTop (𝓝 (g' x)):=by
          intro An x antends
          apply tendsto_atTop_nhds.mpr
          intro U uin uopen
          rw [continuous_def] at gradcon
          rw [tendsto_atTop_nhds] at antends
          have invuopen:IsOpen ((g') ⁻¹' U):=by
              exact gradcon U uopen
          have xinvu: x ∈ ((g') ⁻¹' U):=by
              simp;exact uin
          rcases antends ((g') ⁻¹' U) xinvu invuopen with ⟨N,hN ⟩
          use N
          intro n nge
          change An n ∈ (g') ⁻¹' U
          apply hN n nge
        rcases vglim n with ⟨vgin,vgtends⟩
        rw [f_subdiff_gradiant g g'] at vgin
        · have funtrans: ∀ (n : ℕ),  vg n = g' (ug n):=by
            intro k; rcases vglim k with ⟨vgin',vgtends'⟩;
            rw [f_subdiff_gradiant g g'] at vgin'
            repeat' assumption
            apply hg (ug k)
          rw [tendsto_congr funtrans] at vgtends
          have zgeq: zg = g' x:=by
            apply tendsto_nhds_unique vgtends
            apply limgrad ;apply ugx
          rw [zgeq]
          apply limgrad; apply ufx;
        apply hg (ug n)

lemma f_subdiff_smul_prox (h : prox_prop (c • f) u x) (cpos : 0 < c) :
    c⁻¹ • (u - x) ∈ f_subdifferential f x := f_subdiff_smul (f_subdiff_prox h) cpos

/-- the relation between subdifferential and poximal set -/
theorem rela_proximal_operator_partial (f : E → ℝ) (x : E) (u : E) :
    u ∈ prox_set f x → (x - u) ∈ subdifferential f u:=by
  intro uporx
  rw [prox_set, mem_setOf, prox_prop] at uporx
  have h: (0 : E) ∈ subdifferential (fun u ↦ f u + ‖u - x‖ ^ 2 / 2) u:=by
    apply mem_of_mem_of_subset
    apply first_order_optimality_condition'
    · apply IsMinOn.isLocalMin
      apply uporx; simp
    rfl
  have ngradient : ∀ x₁, HasGradientAt (fun u ↦  ‖u - x‖ ^ 2 / 2) (x₁ - x) x₁ := by
    intro x₁; exact gradient_of_sq x₁
  have _ncovex: ConvexOn ℝ Set.univ (fun u ↦  ‖u - x‖ ^ 2 / 2):=by
    apply convex_of_norm_sq x; exact convex_univ
  have ncon: Continuous (fun u ↦  ‖u - x‖ ^ 2 / 2):=by
    have funtrans:(fun u ↦  ‖u - x‖ ^ 2 / 2) = (fun u ↦  (1/2)*‖u - x‖ ^ 2):=by
      simp
      ext y; rw [mul_comm, div_eq_mul_inv]
    rw [funtrans]
    apply Continuous.mul
    simp
    exact continuous_const
    apply Continuous.pow
    apply Continuous.norm
    exact continuous_sub_right x
  have gradcon: Continuous fun u ↦ u-x:=by exact continuous_sub_right x
  obtain h' := (subdiff_add f (fun u ↦ ‖u - x‖ ^ 2 / 2) (fun x₁ ↦ x₁ - x)
    u ngradient ncon gradcon 0).mp h
  rcases h' with ⟨zf,zfin,zg,zgin,gfadd⟩
  have nsubdifference : subdifferential (fun u ↦ ‖u - x‖ ^ 2 / 2) u = {y|y = u - x}:=by
    exact subdiff_gradient (fun u ↦ ‖u - x‖ ^ 2 / 2) (fun u ↦ u - x) ngradient gradcon u
  rw [nsubdifference,mem_setOf] at zgin
  rw [zgin] at gfadd
  have zfeq : zf = - (u - x):=by
    apply add_eq_zero_iff_eq_neg.mp
    apply gfadd.symm
  rw [zfeq] at zfin
  simp at zfin
  assumption

end
