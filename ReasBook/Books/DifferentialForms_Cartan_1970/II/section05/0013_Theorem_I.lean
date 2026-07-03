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
      (D := Metric.ball z₀ r) Metric.isOpen_ball (convex_ball z₀ r).isPreconnected hG_ball hF_ball with
    ⟨c, hc⟩
  exact ⟨r, hr, c, hc⟩

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

/-- Theorem I: if every point of the segment parameterizing `γ` has a neighborhood in the image of
`γ` on which `ω` admits a holomorphic primitive, then there exists a primitive along `γ` for the
differential form `ω(z) dz`, and any two such primitives differ by an additive constant. -/
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
    -- TODO: use compactness of `Set.Icc a b` to choose finitely many local primitives subordinate
    -- to an ordered cover of the parameter interval, normalize them by constants on overlaps, and
    -- glue the resulting local pullbacks with `ContinuousMap.liftCover`.
    sorry
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact primitive_along_path_unique_up_to_constant hf hg
