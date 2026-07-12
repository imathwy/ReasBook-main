import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0012_Definition_II_1_extra_7»

open Set

-- Proof sketch: glue finitely many local primitives along a finite subdivision of `[a,b]`,
-- then compare any two such primitives by observing that their difference is locally constant
-- on the connected interval and hence constant.
/-- Helper for Theorem I: two primitives defined on overlapping open neighborhoods agree up to an
additive constant on a smaller ball around any common point. -/
theorem local_sub_eq_const_on_ball_of_common_primitive
    {ω : ℂ → ℂ} {U V : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hzU : z₀ ∈ U) (hzV : z₀ ∈ V)
    {F G : ℂ → ℂ}
    (hF : IsPrimitiveOn U (Complex.realScalarOneForm ω) F)
    (hG : IsPrimitiveOn V (Complex.realScalarOneForm ω) G) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℂ,
      EqOn (fun z ↦ G z - F z) (fun _ ↦ c) (Metric.ball z₀ r) := by
  -- Shrink to a ball contained in the overlap so the standard constant-difference lemma applies.
  have hzUV : z₀ ∈ U ∩ V := ⟨hzU, hzV⟩
  have hUV_open : IsOpen (U ∩ V) := hU.inter hV
  rcases Metric.isOpen_iff.mp hUV_open z₀ hzUV with ⟨r, hr, hball⟩
  have hF_ball : IsPrimitiveOn (Metric.ball z₀ r) (Complex.realScalarOneForm ω) F :=
    hF.mono fun z hz ↦ (hball hz).1
  have hG_ball : IsPrimitiveOn (Metric.ball z₀ r) (Complex.realScalarOneForm ω) G :=
    hG.mono fun z hz ↦ (hball hz).2
  rcases IsPrimitiveOn.sub_eqOn_const_of_isOpen_isPreconnected
      (D := Metric.ball z₀ r) Metric.isOpen_ball (convex_ball z₀ r).isPreconnected
      hG_ball hF_ball with
    ⟨c, hc⟩
  exact ⟨r, hr, c, hc⟩

/-- Helper for Cartan section05 0013_Theorem_I: adding a constant to a local primitive leaves the
derivative field unchanged. -/
theorem IsPrimitiveOn.addConst
    {ω : ℂ → ℂ} {U : Set ℂ} {F : ℂ → ℂ}
    (hF : IsPrimitiveOn U (Complex.realScalarOneForm ω) F) (c : ℂ) :
    IsPrimitiveOn U (Complex.realScalarOneForm ω) (fun z ↦ F z + c) := by
  -- The derivative of a constant shift is the original derivative.
  intro z hz
  simpa using (hF z hz).add_const c

/-- Helper for Cartan section05 0013_Theorem_I: if two primitives differ by a constant on a
codomain ball, then their pullbacks along `γ` agree after shifting the second one by that
constant. -/
theorem shiftedPrimitive_eqOn_preimageBall
    {a b : ℝ} {γ : C(Set.Icc a b, ℂ)} {τ : Set.Icc a b}
    {F G : ℂ → ℂ} {r : ℝ} {c k : ℂ}
    (hc : EqOn (fun z ↦ G z - F z) (fun _ ↦ c) (Metric.ball (γ τ) r)) :
    EqOn (fun t : Set.Icc a b ↦ G (γ t) + (k - c)) (fun t ↦ F (γ t) + k)
      (γ ⁻¹' Metric.ball (γ τ) r) := by
  -- Pull the constant-difference identity back along `γ` and rearrange the resulting equality.
  intro t ht
  have hdiff : G (γ t) - F (γ t) = c := hc ht
  calc
    G (γ t) + (k - c) = (G (γ t) - F (γ t)) + (F (γ t) + (k - c)) := by ring
    _ = c + (F (γ t) + (k - c)) := by rw [hdiff]
    _ = F (γ t) + k := by ring

/-- Helper for Theorem I: the difference of two primitives along the same path is locally constant
on the parameter interval. -/
theorem primitive_difference_isLocallyConstant
    {a b : ℝ} {γ : C(Set.Icc a b, ℂ)} {ω : ℂ → ℂ}
    {f g : C(Set.Icc a b, ℂ)}
    (hf : IsPrimitiveAlongPath (Complex.realScalarOneForm ω) univ γ f)
    (hg : IsPrimitiveAlongPath (Complex.realScalarOneForm ω) univ γ g) :
    IsLocallyConstant (fun t : Set.Icc a b ↦ g t - f t) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro τ
  rcases hf.local_primitive τ with
    ⟨sf, hsf_open, hτsf, Uf, hUf_open, hγτUf, -, hγsf, F, hF, hEqf⟩
  rcases hg.local_primitive τ with
    ⟨sg, hsg_open, hτsg, Ug, hUg_open, hγτUg, -, hγsg, G, hG, hEqg⟩
  -- Compare the two local primitive witnesses on a common ball around `γ τ`.
  rcases local_sub_eq_const_on_ball_of_common_primitive hUf_open hUg_open hγτUf hγτUg hF hG with
    ⟨r, hr, c, hc⟩
  let s : Set (Set.Icc a b) := (sf ∩ sg) ∩ γ ⁻¹' Metric.ball (γ τ) r
  have hs_open : IsOpen s := by
    refine (hsf_open.inter hsg_open).inter ?_
    exact γ.continuous.isOpen_preimage _ Metric.isOpen_ball
  have hτs : τ ∈ s := by
    refine ⟨⟨hτsf, hτsg⟩, ?_⟩
    exact Metric.mem_ball_self hr
  have hτconst : g τ - f τ = c := by
    calc
      g τ - f τ = G (γ τ) - F (γ τ) := by
        rw [hEqg hτsg, hEqf hτsf]
        rfl
      _ = c := hc (Metric.mem_ball_self hr)
  refine ⟨s, hs_open, hτs, ?_⟩
  intro t ht
  have htsf : t ∈ sf := ht.1.1
  have htsg : t ∈ sg := ht.1.2
  have htball : γ t ∈ Metric.ball (γ τ) r := ht.2
  -- On the common parameter neighborhood, both functions are pullbacks of primitives whose
  -- difference is the constant `c`.
  calc
    g t - f t = G (γ t) - F (γ t) := by
      rw [hEqg htsg, hEqf htsf]
      rfl
    _ = c := hc htball
    _ = g τ - f τ := hτconst.symm

/-- Helper for Theorem I: once one primitive along the path exists, every other one differs from
it by a constant. -/
theorem primitive_along_path_unique_up_to_constant
    {a b : ℝ} {γ : C(Set.Icc a b, ℂ)} {ω : ℂ → ℂ}
    {f g : C(Set.Icc a b, ℂ)}
    (hf : IsPrimitiveAlongPath (Complex.realScalarOneForm ω) univ γ f)
    (hg : IsPrimitiveAlongPath (Complex.realScalarOneForm ω) univ γ g) :
    ∃ c : ℂ, g = f + ContinuousMap.const _ c := by
  by_cases hab : a ≤ b
  · -- A locally constant difference is constant on the connected interval subtype.
    have hloc : IsLocallyConstant (fun t : Set.Icc a b ↦ g t - f t) :=
      primitive_difference_isLocallyConstant hf hg
    haveI : PreconnectedSpace (Set.Icc a b) :=
      Subtype.preconnectedSpace isPreconnected_Icc
    let t₀ : Set.Icc a b := ⟨a, ⟨le_rfl, hab⟩⟩
    let c : ℂ := g t₀ - f t₀
    refine ⟨c, ?_⟩
    ext t
    have hconst : g t - f t = c := by
      simpa [c, t₀] using hloc.apply_eq_of_preconnectedSpace t t₀
    have hEq : g t = c + f t := (sub_eq_iff_eq_add).mp hconst
    simpa [c, add_comm, add_left_comm, add_assoc] using hEq
  · -- If `a ≤ b` fails, the interval subtype is empty, so extensionality is trivial.
    refine ⟨0, ?_⟩
    ext t
    exact (hab (t.2.1.trans t.2.2)).elim

/-- Cartan section05 0013_Theorem_I (Theorem I): if every point of the segment parameterizing `γ`
has a neighborhood in the image of `γ` on which `ω` admits a holomorphic primitive, then there
exists a primitive along `γ` for the differential form `ω(z) dz`, and any two such primitives
differ by an additive constant. -/
theorem curvilinear_primitive_exists_and_unique_up_to_constant
    {a b : ℝ} {γ : C(Set.Icc a b, ℂ)} {ω : ℂ → ℂ}
    (hω : ∀ τ : Icc a b,
      ∃ U : Set ℂ, IsOpen U ∧ γ τ ∈ U ∧
        ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (ω z) z) :
    ∃ f : C(Set.Icc a b, ℂ),
      IsPrimitiveAlongPath (Complex.realScalarOneForm ω) univ γ f ∧
        ∀ g : C(Set.Icc a b, ℂ),
          IsPrimitiveAlongPath (Complex.realScalarOneForm ω) univ γ g →
            ∃ c : ℂ, g = f + ContinuousMap.const _ c := by
  classical
  -- Route correction: the uniqueness half is isolated below; the remaining work is the compact
  -- gluing construction that turns the local primitives from `hω` into one global primitive.
  obtain ⟨f, hf⟩ : ∃ f : C(Set.Icc a b, ℂ),
      IsPrimitiveAlongPath (Complex.realScalarOneForm ω) univ γ f := by
    by_cases hab : a ≤ b
    · let U : Set.Icc a b → Set ℂ := fun τ => Classical.choose (hω τ)
      let F : Set.Icc a b → ℂ → ℂ := fun τ =>
        Classical.choose ((Classical.choose_spec (hω τ)).2.2)
      have hU_open : ∀ τ : Set.Icc a b, IsOpen (U τ) := by
        intro τ
        exact (Classical.choose_spec (hω τ)).1
      have hγU : ∀ τ : Set.Icc a b, γ τ ∈ U τ := by
        intro τ
        exact (Classical.choose_spec (hω τ)).2.1
      have hF : ∀ τ : Set.Icc a b, IsPrimitiveOn (U τ) (Complex.realScalarOneForm ω) (F τ) := by
        intro τ z hz
        simpa [Complex.realScalarOneForm_eq_smul] using
          (Classical.choose_spec ((Classical.choose_spec (hω τ)).2.2) z hz).complexToReal_fderiv
      let c : Set.Icc a b → Set (Set.Icc a b) := fun τ => γ ⁻¹' U τ
      have hc_open : ∀ τ : Set.Icc a b, IsOpen (c τ) := by
        intro τ
        exact γ.continuous.isOpen_preimage _ (hU_open τ)
      have hc_cover : (univ : Set (Set.Icc a b)) ⊆ ⋃ τ, c τ := by
        intro τ _
        exact mem_iUnion.2 ⟨τ, hγU τ⟩
      -- Use the explicit `addNSMul` subdivision so adjacent breakpoints are the only ones that
      -- can occur before the terminal plateau at `b`.
      obtain ⟨δ, hδpos, hLebesgue⟩ :=
        lebesgue_number_lemma_of_metric isCompact_univ hc_open hc_cover
      let step : ℝ := δ / 2
      have hstep_pos : 0 < step := by
        simpa [step] using half_pos hδpos
      let t : ℕ → Set.Icc a b := Set.Icc.addNSMul hab step
      have ht0 : ((t 0 : Set.Icc a b) : ℝ) = a := by
        simpa [t] using (Set.Icc.addNSMul_zero hab (δ := step))
      have htmono : Monotone t := by
        simpa [t] using (Set.Icc.monotone_addNSMul hab (δ := step) hstep_pos.le)
      let saturatesFrom : ℕ → Prop := fun N => ∀ n ≥ N, ((t n : Set.Icc a b) : ℝ) = b
      have hsaturates : ∃ N, saturatesFrom N := by
        simpa [saturatesFrom, t] using
          (Set.Icc.addNSMul_eq_right hab (δ := step) hstep_pos)
      let m : ℕ := Nat.find hsaturates
      have hm : ∀ n ≥ m, ((t n : Set.Icc a b) : ℝ) = b := Nat.find_spec hsaturates
      have hsub : ∀ n : ℕ, ∃ τ : Set.Icc a b, Set.Icc (t n) (t (n + 1)) ⊆ c τ := by
        intro n
        obtain ⟨τ, hτ⟩ := hLebesgue (t n) trivial
        refine ⟨τ, ?_⟩
        intro x hx
        exact hτ <|
          (Set.Icc.abs_sub_addNSMul_le hab (δ := step) hstep_pos.le n hx).trans_lt
            (half_lt_self hδpos)
      let center : ℕ → Set.Icc a b := fun n => Classical.choose (hsub n)
      have hcenter_mem : ∀ n : ℕ, Set.Icc (t n) (t (n + 1)) ⊆ c (center n) := by
        intro n
        exact Classical.choose_spec (hsub n)
      have hsegment_primitive :
          ∀ n : ℕ, IsPrimitiveOn (U (center n)) (Complex.realScalarOneForm ω) (F (center n)) :=
        fun n => hF (center n)
      have hoverlap :
          ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∃ κ : ℂ,
            EqOn (fun z ↦ F (center (n + 1)) z - F (center n) z) (fun _ ↦ κ)
              (Metric.ball (γ (t (n + 1))) r) := by
        intro n
        have hleft : γ (t (n + 1)) ∈ U (center n) := by
          exact hcenter_mem n ⟨htmono (Nat.le_succ n), le_rfl⟩
        have hright : γ (t (n + 1)) ∈ U (center (n + 1)) := by
          exact hcenter_mem (n + 1) ⟨le_rfl, htmono (Nat.le_succ (n + 1))⟩
        -- The remaining gluing step only needs the constant-difference data at adjacent
        -- breakpoints.
        exact local_sub_eq_const_on_ball_of_common_primitive
          (hU_open (center n)) (hU_open (center (n + 1))) hleft hright
          (hsegment_primitive n) (hsegment_primitive (n + 1))
      have htn_ne_b : ∀ {n : ℕ}, n < m → ((t n : Set.Icc a b) : ℝ) ≠ b := by
        intro n hn hEq
        have hsat_n : saturatesFrom n := by
          intro k hk
          have hnk : t n ≤ t k := htmono hk
          change ((t n : Set.Icc a b) : ℝ) ≤ ((t k : Set.Icc a b) : ℝ) at hnk
          have hkb : ((t k : Set.Icc a b) : ℝ) ≤ b := (t k).2.2
          linarith
        exact (Nat.not_le_of_lt hn) (Nat.find_min' hsaturates hsat_n)
      have ht_eq_of_le_b :
          ∀ n : ℕ, a + n • step ≤ b → ((t n : Set.Icc a b) : ℝ) = a + n • step := by
        intro n hn
        have han : a ≤ a + n • step := by
          nlinarith [nsmul_nonneg hstep_pos.le n]
        calc
          ((t n : Set.Icc a b) : ℝ) = max a (min b (a + n • step)) := by
            simp [t, Set.Icc.addNSMul, Set.coe_projIcc]
          _ = a + n • step := by
            rw [min_eq_right hn, max_eq_right han]
      have harg_le_b_of_lt_m : ∀ {n : ℕ}, n < m → a + n • step ≤ b := by
        intro n hn
        by_contra hgt
        have hb_le : b ≤ a + n • step := le_of_not_ge hgt
        have hEq : ((t n : Set.Icc a b) : ℝ) = b := by
          calc
            ((t n : Set.Icc a b) : ℝ) = max a (min b (a + n • step)) := by
              simp [t, Set.Icc.addNSMul, Set.coe_projIcc]
            _ = b := by
              rw [min_eq_left hb_le, max_eq_right hab]
        exact htn_ne_b hn hEq
      have ht_strict : ∀ {n : ℕ}, n < m → t n < t (n + 1) := by
        intro n hn
        have htn : ((t n : Set.Icc a b) : ℝ) = a + n • step :=
          ht_eq_of_le_b n (harg_le_b_of_lt_m hn)
        by_cases hn1 : a + (n + 1) • step ≤ b
        · have htn1 : ((t (n + 1) : Set.Icc a b) : ℝ) = a + (n + 1) • step :=
            ht_eq_of_le_b (n + 1) hn1
          change ((t n : Set.Icc a b) : ℝ) < ((t (n + 1) : Set.Icc a b) : ℝ)
          rw [htn, htn1]
          rw [succ_nsmul]
          nlinarith [hstep_pos]
        · have htn_lt_b : ((t n : Set.Icc a b) : ℝ) < b := by
            exact lt_of_le_of_ne (t n).2.2 (htn_ne_b hn)
          have htn1 : ((t (n + 1) : Set.Icc a b) : ℝ) = b := by
            have hb_le : b ≤ a + (n + 1) • step := le_of_not_ge hn1
            calc
              ((t (n + 1) : Set.Icc a b) : ℝ) = max a (min b (a + (n + 1) • step)) := by
                simp [t, Set.Icc.addNSMul, Set.coe_projIcc]
              _ = b := by
                rw [min_eq_left hb_le, max_eq_right hab]
          change ((t n : Set.Icc a b) : ℝ) < ((t (n + 1) : Set.Icc a b) : ℝ)
          rw [htn1]
          exact htn_lt_b
      let overlapRadius : ℕ → ℝ := fun n => Classical.choose (hoverlap n)
      let overlapConst : ℕ → ℂ := fun n =>
        Classical.choose ((Classical.choose_spec (hoverlap n)).2)
      have hoverlapRadius_pos : ∀ n : ℕ, 0 < overlapRadius n := by
        intro n
        exact (Classical.choose_spec (hoverlap n)).1
      have hoverlapEq :
          ∀ n : ℕ,
            EqOn (fun z ↦ F (center (n + 1)) z - F (center n) z)
              (fun _ ↦ overlapConst n) (Metric.ball (γ (t (n + 1))) (overlapRadius n)) := by
        intro n
        exact Classical.choose_spec ((Classical.choose_spec (hoverlap n)).2)
      let k : ℕ → ℂ := Nat.rec 0 fun n acc => acc - overlapConst n
      let G : ℕ → Set.Icc a b → ℂ := fun n τ => F (center n) (γ τ) + k n
      have hk_succ : ∀ n : ℕ, k (n + 1) = k n - overlapConst n := by
        intro n
        rfl
      have hshiftEq :
          ∀ n : ℕ,
            EqOn (G (n + 1)) (G n)
              (γ ⁻¹' Metric.ball (γ (t (n + 1))) (overlapRadius n)) := by
        intro n
        simpa [G, hk_succ n] using
          (shiftedPrimitive_eqOn_preimageBall (γ := γ) (τ := t (n + 1))
            (F := F (center n)) (G := F (center (n + 1)))
            (r := overlapRadius n) (c := overlapConst n) (k := k n) (hoverlapEq n))
      have hGprimitive :
          ∀ n : ℕ,
            IsPrimitiveOn (U (center n)) (Complex.realScalarOneForm ω)
              (fun z ↦ F (center n) z + k n) := by
        intro n
        exact (hsegment_primitive n).addConst (k n)
      let ownerExists : Set.Icc a b → Prop := fun τ => ∃ n : ℕ, τ ≤ t (n + 1)
      have hownerExists : ∀ τ : Set.Icc a b, ownerExists τ := by
        intro τ
        refine ⟨m, ?_⟩
        change (τ : ℝ) ≤ ((t (m + 1) : Set.Icc a b) : ℝ)
        simpa [hm (m + 1) (Nat.le_succ m)] using τ.2.2
      have howner_witness_m : ∀ τ : Set.Icc a b, τ ≤ t (m + 1) := by
        intro τ
        change (τ : ℝ) ≤ ((t (m + 1) : Set.Icc a b) : ℝ)
        simpa [hm (m + 1) (Nat.le_succ m)] using τ.2.2
      let owner : Set.Icc a b → ℕ := fun τ => Nat.find (hownerExists τ)
      have howner_spec : ∀ τ : Set.Icc a b, τ ≤ t (owner τ + 1) := by
        intro τ
        exact Nat.find_spec (hownerExists τ)
      have howner_le_m : ∀ τ : Set.Icc a b, owner τ ≤ m := by
        intro τ
        simpa [owner] using
          (Nat.find_min' (hownerExists τ) (howner_witness_m τ) : Nat.find (hownerExists τ) ≤ m)
      have howner_left_lt : ∀ {τ : Set.Icc a b}, 0 < owner τ → t (owner τ) < τ := by
        intro τ hτ
        rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hτ) with ⟨n, hn⟩
        have hnot : ¬ τ ≤ t (n + 1) := by
          intro hle
          have hmin : owner τ ≤ n := by
            simpa [owner, hn] using
              (Nat.find_min' (hownerExists τ) hle : Nat.find (hownerExists τ) ≤ n)
          have hsucc_le : n.succ ≤ n := by
            simp [hn] at hmin
          exact Nat.not_succ_le_self n hsucc_le
        have hlt : t (n + 1) < τ := lt_of_not_ge hnot
        simpa [hn] using hlt
      have howner_eq_zero_of_le_first :
          ∀ {x : Set.Icc a b}, x ≤ t 1 → owner x = 0 := by
        intro x hx
        have hle : owner x ≤ 0 := by
          simpa [owner] using
            (Nat.find_min' (hownerExists x) hx : Nat.find (hownerExists x) ≤ 0)
        exact Nat.eq_zero_of_le_zero hle
      have howner_eq_of_between :
          ∀ {n : ℕ} {x : Set.Icc a b}, 0 < n → t n < x → x ≤ t (n + 1) → owner x = n := by
        intro n x hn hxlower hxupper
        have hle : owner x ≤ n := Nat.find_min' (hownerExists x) hxupper
        have hge : n ≤ owner x := by
          by_contra hlt
          have hlt' : owner x < n := Nat.lt_of_not_ge hlt
          have hxowner : x ≤ t (owner x + 1) := howner_spec x
          have hbound : t (owner x + 1) ≤ t n := htmono (Nat.succ_le_of_lt hlt')
          exact (not_le_of_gt hxlower) (hxowner.trans hbound)
        exact le_antisymm hle hge
      let f0 : Set.Icc a b → ℂ := fun τ => G (owner τ) τ
      have hlocal_raw :
          ∀ τ : Set.Icc a b,
            ∃ s : Set (Set.Icc a b), IsOpen s ∧ τ ∈ s ∧
              ∃ V : Set ℂ, IsOpen V ∧ γ τ ∈ V ∧ V ⊆ univ ∧ MapsTo γ s V ∧
                ∃ primitive : ℂ → ℂ,
                  (∀ z ∈ V, HasFDerivAt primitive (Complex.realScalarOneForm ω z) z) ∧
                    EqOn f0 (primitive ∘ γ) s := by
        intro τ
        let n := owner τ
        have hτleft : t n ≤ τ := by
          by_cases hn0 : n = 0
          · change ((t n : Set.Icc a b) : ℝ) ≤ (τ : ℝ)
            simpa [hn0, ht0] using τ.2.1
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
            simpa [n] using (howner_left_lt hnpos).le
        have hτright : τ ≤ t (n + 1) := howner_spec τ
        have hτc : τ ∈ c (center n) := hcenter_mem n ⟨hτleft, hτright⟩
        by_cases hstrict : τ < t (n + 1)
        · -- Away from a breakpoint, the least owner is locally constant.
          by_cases hn0 : n = 0
          · have hτc0 : τ ∈ c (center 0) := by simpa [hn0] using hτc
            have hstrict0 : τ < t 1 := by simpa [hn0] using hstrict
            let s : Set (Set.Icc a b) := c (center 0) ∩ Set.Iio (t 1)
            have hs_open : IsOpen s := (hc_open (center 0)).inter isOpen_Iio
            have hτs : τ ∈ s := by
              exact ⟨hτc0, hstrict0⟩
            have hs_maps : MapsTo γ s (U (center 0)) := by
              intro x hx
              exact hx.1
            have hs_eq : EqOn f0 (fun x ↦ F (center 0) (γ x) + k 0) s := by
              intro x hx
              have howner0 : owner x = 0 :=
                howner_eq_zero_of_le_first (le_of_lt hx.2)
              simp [f0, G, howner0]
            refine ⟨s, hs_open, hτs, U (center 0), hU_open (center 0), hτc0, by simp,
              hs_maps, fun z ↦ F (center 0) z + k 0, hGprimitive 0, ?_⟩
            intro x hx
            simpa [Function.comp] using hs_eq hx
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
            let s : Set (Set.Icc a b) := c (center n) ∩ Set.Ioi (t n) ∩ Set.Iio (t (n + 1))
            have hs_open : IsOpen s := by
              simpa [s, inter_assoc] using
                ((hc_open (center n)).inter isOpen_Ioi).inter isOpen_Iio
            have hτs : τ ∈ s := by
              exact ⟨⟨hτc, by simpa [n] using howner_left_lt hnpos⟩, hstrict⟩
            have hs_maps : MapsTo γ s (U (center n)) := by
              intro x hx
              exact hx.1.1
            have hs_eq : EqOn f0 (fun x ↦ F (center n) (γ x) + k n) s := by
              intro x hx
              have hown : owner x = n :=
                howner_eq_of_between hnpos hx.1.2 (le_of_lt hx.2)
              simp [f0, G, hown]
            refine ⟨s, hs_open, hτs, U (center n), hU_open (center n), hτc, by simp,
              hs_maps, fun z ↦ F (center n) z + k n, hGprimitive n, ?_⟩
            intro x hx
            simpa [Function.comp] using hs_eq hx
        · have hbreak : τ = t (n + 1) := le_antisymm hτright (le_of_not_gt hstrict)
          by_cases hτb : (τ : ℝ) = b
          · -- At the terminal endpoint, only the last active segment matters.
            by_cases hn0 : n = 0
            · have hτc0 : τ ∈ c (center 0) := by simpa [hn0] using hτc
              let s : Set (Set.Icc a b) := c (center 0)
              have hs_maps : MapsTo γ s (U (center 0)) := by
                intro x hx
                exact hx
              have hs_eq : EqOn f0 (fun x ↦ F (center 0) (γ x) + k 0) s := by
                intro x hx
                have hxle : x ≤ t 1 := by
                  change (x : ℝ) ≤ ((t 1 : Set.Icc a b) : ℝ)
                  calc
                    (x : ℝ) ≤ b := x.2.2
                    _ = (τ : ℝ) := hτb.symm
                    _ = ((t 1 : Set.Icc a b) : ℝ) := by
                      simpa [hn0] using congrArg Subtype.val hbreak
                have hown : owner x = 0 := howner_eq_zero_of_le_first hxle
                simp [f0, G, hown]
              refine ⟨s, hc_open (center 0), hτc0, U (center 0), hU_open (center 0), hτc0,
                by simp, hs_maps, fun z ↦ F (center 0) z + k 0, hGprimitive 0, ?_⟩
              intro x hx
              simpa [Function.comp] using hs_eq hx
            · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
              let s : Set (Set.Icc a b) := c (center n) ∩ Set.Ioi (t n)
              have hs_open : IsOpen s := (hc_open (center n)).inter isOpen_Ioi
              have hτs : τ ∈ s := by
                exact ⟨hτc, howner_left_lt hnpos⟩
              have hs_maps : MapsTo γ s (U (center n)) := by
                intro x hx
                exact hx.1
              have hs_eq : EqOn f0 (fun x ↦ F (center n) (γ x) + k n) s := by
                intro x hx
                have hxle : x ≤ t (n + 1) := by
                  change (x : ℝ) ≤ ((t (n + 1) : Set.Icc a b) : ℝ)
                  calc
                    (x : ℝ) ≤ b := x.2.2
                    _ = (τ : ℝ) := hτb.symm
                    _ = ((t (n + 1) : Set.Icc a b) : ℝ) := by
                      simpa using congrArg Subtype.val hbreak
                have hown : owner x = n :=
                  howner_eq_of_between hnpos hx.2 hxle
                simp [f0, G, hown]
              refine ⟨s, hs_open, hτs, U (center n), hU_open (center n), hτc, by simp,
                hs_maps, fun z ↦ F (center n) z + k n, hGprimitive n, ?_⟩
              intro x hx
              simpa [Function.comp] using hs_eq hx
          · -- Route correction: at an interior breakpoint use the adjacent overlap ball so the
            -- two normalized formulas agree on a full parameter neighborhood.
            have hτltb : (τ : ℝ) < b := lt_of_le_of_ne τ.2.2 hτb
            have hn1ltm : n + 1 < m := by
              by_contra hnm
              have hb' : ((t (n + 1) : Set.Icc a b) : ℝ) = b := hm (n + 1) (le_of_not_gt hnm)
              exact hτb (by simpa [hbreak] using hb')
            have hnext : t (n + 1) < t (n + 2) := ht_strict hn1ltm
            let s : Set (Set.Icc a b) :=
              ((c (center n) ∩ (γ ⁻¹' Metric.ball (γ τ) (overlapRadius n))) ∩
                (if hn : n = 0 then univ else Set.Ioi (t n))) ∩ Set.Iio (t (n + 2))
            have hs_open : IsOpen s := by
              by_cases hn : n = 0
              · simpa [s, hn, inter_assoc] using
                  ((((hc_open (center n)).inter
                      (γ.continuous.isOpen_preimage _ Metric.isOpen_ball)).inter
                        isOpen_univ).inter isOpen_Iio)
              · simpa [s, hn, inter_assoc] using
                  ((((hc_open (center n)).inter
                      (γ.continuous.isOpen_preimage _ Metric.isOpen_ball)).inter
                        isOpen_Ioi).inter isOpen_Iio)
            have hτs : τ ∈ s := by
              refine ⟨⟨⟨hτc, Metric.mem_ball_self (hoverlapRadius_pos n)⟩, ?_⟩, ?_⟩
              · by_cases hn : n = 0
                · simp [hn]
                · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
                  have hleftτ : t n < τ := by
                    simpa [n] using (howner_left_lt (τ := τ) (by simpa [n] using hnpos))
                  simp [hn, hleftτ]
              · simpa [hbreak] using hnext
            have hs_maps : MapsTo γ s (U (center n)) := by
              intro x hx
              exact hx.1.1.1
            have hs_eq : EqOn f0 (fun x ↦ F (center n) (γ x) + k n) s := by
              intro x hx
              by_cases hxle : x ≤ t (n + 1)
              · by_cases hn : n = 0
                · have hown : owner x = 0 := howner_eq_zero_of_le_first (by simpa [hn] using hxle)
                  simp [hn, f0, G, hown]
                · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
                  have hxlower : t n < x := by
                    simpa [hn] using hx.1.2
                  have hown : owner x = n :=
                    howner_eq_of_between hnpos hxlower hxle
                  simp [f0, G, hown]
              · have hxgt : t (n + 1) < x := lt_of_not_ge hxle
                have hxlt : x < t (n + 2) := hx.2
                have hown : owner x = n + 1 := by
                  have hnpos : 0 < n + 1 := Nat.succ_pos n
                  exact howner_eq_of_between hnpos hxgt (le_of_lt hxlt)
                have hball :
                    x ∈ γ ⁻¹' Metric.ball (γ (t (n + 1))) (overlapRadius n) := by
                  simpa [hbreak] using hx.1.1.2
                calc
                  f0 x = G (n + 1) x := by simp [f0, hown]
                  _ = G n x := hshiftEq n hball
                  _ = F (center n) (γ x) + k n := rfl
            refine ⟨s, hs_open, hτs, U (center n), hU_open (center n), hτc, by simp,
              hs_maps, fun z ↦ F (center n) z + k n, hGprimitive n, ?_⟩
            intro x hx
            simpa [Function.comp] using hs_eq hx
      -- Bundle the owner-defined raw function using the local primitive formulas to prove
      -- continuity pointwise.
      have hf0_cont : Continuous f0 := by
        refine continuous_iff_continuousAt.mpr ?_
        intro τ
        rcases hlocal_raw τ with
          ⟨s, hs_open, hτs, V, -, hγτV, -, -, primitive, hprimitive, hEq⟩
        have hprim_cont : ContinuousAt (primitive ∘ γ) τ := by
          exact (hprimitive (γ τ) hγτV).continuousAt.comp (γ.continuousAt τ)
        have hEqNear : f0 =ᶠ[nhds τ] primitive ∘ γ :=
          Filter.mem_of_superset (hs_open.mem_nhds hτs) hEq
        exact hprim_cont.congr hEqNear.symm
      let f : C(Set.Icc a b, ℂ) := ⟨f0, hf0_cont⟩
      refine ⟨f, ?_⟩
      intro τ
      rcases hlocal_raw τ with
        ⟨s, hs_open, hτs, V, hV_open, hγτV, hVsub, hs_maps, primitive, hprimitive, hEq⟩
      refine ⟨s, hs_open, hτs, V, hV_open, hγτV, hVsub, hs_maps, primitive, hprimitive, ?_⟩
      intro x hx
      simpa [f, Function.comp] using hEq hx
    · refine ⟨ContinuousMap.const _ 0, ?_⟩
      -- If `a ≤ b` fails, the interval subtype is empty, so the local primitive condition is
      -- vacuous.
      intro τ
      exact (hab (τ.2.1.trans τ.2.2)).elim
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact primitive_along_path_unique_up_to_constant hf hg
