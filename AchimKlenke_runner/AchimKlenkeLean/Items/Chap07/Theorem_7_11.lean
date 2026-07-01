import AchimKlenkeLean.Items.Chap07.Corollary_7_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set EuclideanSpace
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin n)

/-- Helper for Theorem 7.11: an affine functional of an integrable random vector is integrable. -/
private lemma integrable_affine_comp_of_integrable {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → State} (hX : Integrable X P) (a : State →ᵃ[ℝ] ℝ) :
    Integrable (fun ω ↦ a (X ω)) P := by
  let L : State →L[ℝ] ℝ :=
    { toLinearMap := a.linear
      cont := a.linear.continuous_of_finiteDimensional }
  have hdecomp : (fun ω ↦ a (X ω)) = fun ω ↦ L (X ω) + a 0 := by
    funext ω
    have := congrArg (fun f : State → ℝ ↦ f (X ω)) a.decomp
    simpa [L] using this
  rw [hdecomp]
  exact (L.integrable_comp hX).add (integrable_const (a 0))

/-- Helper for Theorem 7.11: the expectation of an affine functional is the affine functional of
the expectation. -/
private lemma affine_expectation_eq_expectation_apply {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → State} (hX : Integrable X P) (a : State →ᵃ[ℝ] ℝ) :
    P[fun ω ↦ a (X ω)] = a (P[X]) := by
  let L : State →L[ℝ] ℝ :=
    { toLinearMap := a.linear
      cont := a.linear.continuous_of_finiteDimensional }
  have hdecomp : (fun ω ↦ a (X ω)) = fun ω ↦ L (X ω) + a 0 := by
    funext ω
    have := congrArg (fun f : State → ℝ ↦ f (X ω)) a.decomp
    simpa [L] using this
  rw [hdecomp, integral_add (L.integrable_comp hX) (integrable_const (a 0)),
    L.integral_comp_comm hX, integral_const, probReal_univ, one_smul]
  have := congrArg (fun f : State → ℝ ↦ f (P[X])) a.decomp
  simpa [L] using this.symm

/-- Helper for Theorem 7.11: an affine lower bound controls the negative part of `φ ∘ X`. -/
private lemma lintegral_neg_comp_lt_top_of_affine_lower_bound {P : Measure Ω}
    [IsProbabilityMeasure P] {G : Set State} {X : Ω → State} {φ : State → ℝ}
    {a : State →ᵃ[ℝ] ℝ} (hXG : ∀ᵐ ω ∂P, X ω ∈ G)
    (ha_lower : ∀ x ∈ G, a x ≤ φ x) (ha_int : Integrable (fun ω ↦ a (X ω)) P) :
    (∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) < ⊤ := by
  have hneg_int : Integrable (fun ω ↦ -a (X ω)) P := ha_int.neg
  have hbound : ∀ᵐ ω ∂P, ENNReal.ofReal (-φ (X ω)) ≤ ENNReal.ofReal (-a (X ω)) := by
    filter_upwards [hXG] with ω hω
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (ha_lower _ hω))
  exact lt_of_le_of_lt (lintegral_mono_ae hbound) hneg_int.lintegral_lt_top

/-- Helper for Theorem 7.11: a touching affine minorant yields the extended Jensen lower bound. -/
private lemma ereal_jensen_ge_of_affine_lower_bound {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Set State} {X : Ω → State} {φ : State → ℝ} {a : State →ᵃ[ℝ] ℝ}
    (hXG : ∀ᵐ ω ∂P, X ω ∈ G) (ha_lower : ∀ x ∈ G, a x ≤ φ x)
    (ha_eq : a (P[X]) = φ (P[X])) (ha_int : Integrable (fun ω ↦ a (X ω)) P)
    (ha_expect : P[fun ω ↦ a (X ω)] = a (P[X])) :
    (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
        ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) ≥
      (φ (P[X]) : EReal) := by
  have hlower : ∀ᵐ ω ∂P, a (X ω) ≤ φ (X ω) := by
    filter_upwards [hXG] with ω hω
    exact ha_lower _ hω
  have hpos : ∀ᵐ ω ∂P, ENNReal.ofReal (a (X ω)) ≤ ENNReal.ofReal (φ (X ω)) := by
    filter_upwards [hlower] with ω hω
    exact ENNReal.ofReal_le_ofReal hω
  have hneg : ∀ᵐ ω ∂P, ENNReal.ofReal (-φ (X ω)) ≤ ENNReal.ofReal (-a (X ω)) := by
    filter_upwards [hlower] with ω hω
    exact ENNReal.ofReal_le_ofReal (neg_le_neg hω)
  have hmain :
      (((∫⁻ ω, ENNReal.ofReal (a (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-a (X ω)) ∂P) : EReal)) ≤
        (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) := by
    exact EReal.sub_le_sub
      (by exact_mod_cast lintegral_mono_ae hpos)
      (by exact_mod_cast lintegral_mono_ae hneg)
  have hident :
      (((∫⁻ ω, ENNReal.ofReal (a (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-a (X ω)) ∂P) : EReal)) =
        (∫ ω, a (X ω) ∂P : ℝ) := by
    have hpos_ne_top : (∫⁻ ω, ENNReal.ofReal (a (X ω)) ∂P) ≠ ⊤ := ha_int.lintegral_lt_top.ne
    have hneg_int : Integrable (fun ω ↦ -a (X ω)) P := ha_int.neg
    have hneg_ne_top : (∫⁻ ω, ENNReal.ofReal (-a (X ω)) ∂P) ≠ ⊤ := hneg_int.lintegral_lt_top.ne
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part ha_int]
    rw [← EReal.coe_ennreal_toReal hpos_ne_top, ← EReal.coe_ennreal_toReal hneg_ne_top]
    norm_num
  calc
    (φ (P[X]) : EReal) = (a (P[X]) : EReal) := by simp [ha_eq]
    _ = (∫ ω, a (X ω) ∂P : ℝ) := by simp [ha_expect]
    _ = (((∫⁻ ω, ENNReal.ofReal (a (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-a (X ω)) ∂P) : EReal)) := hident.symm
    _ ≤ (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) := hmain

/-- Helper for Theorem 7.11: an owner-style supporting affine map yields an ambient affine map. -/
private lemma affine_minorant_of_mem_supporting_affine_maps_on
    {G : Set State} {φ : State → ℝ} {g : G → ℝ}
    (hg : g ∈ supporting_affine_maps_on G φ) :
    ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ G, a x ≤ φ x) ∧ ∀ x : G, a x = g x := by
  rcases mem_supporting_affine_maps_on_iff.mp hg with ⟨hminor, l, c, rfl⟩
  let a : State →ᵃ[ℝ] ℝ := l.toAffineMap + AffineMap.const ℝ State c
  refine ⟨a, ?_, ?_⟩
  · intro x hx
    have := hminor ⟨x, hx⟩
    simpa [a, Pi.add_apply] using this
  · intro x
    simp [a, Pi.add_apply]

/-- Helper for Theorem 7.11: on `interior G`, strict-epigraph separation yields an affine
minorant touching `φ` at `m`. -/
private lemma affine_minorant_touching_on_interior {G : Set State} {φ : State → ℝ} {m : State}
    (hm : m ∈ interior G) (hφ : ConvexOn ℝ G φ) :
    ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ interior G, a x ≤ φ x) ∧ a m = φ m := by
  let S : Set (State × ℝ) := {p | p.1 ∈ interior G ∧ φ p.1 < p.2}
  have hcont : ContinuousOn φ (interior G) := hφ.continuousOn_interior
  have hS_open_aux :
      IsOpen ((interior G ×ˢ (Set.univ : Set ℝ)) ∩
        (fun p : State × ℝ ↦ φ p.1 - p.2) ⁻¹' Set.Iio 0) := by
    have hψ : ContinuousOn (fun p : State × ℝ ↦ φ p.1 - p.2)
        (interior G ×ˢ (Set.univ : Set ℝ)) := by
      intro p hp
      have hφp : ContinuousAt φ p.1 :=
        (hcont p.1 hp.1).continuousAt (isOpen_interior.mem_nhds hp.1)
      exact ((hφp.comp continuousAt_fst).sub continuousAt_snd).continuousWithinAt
    simpa using hψ.isOpen_inter_preimage (isOpen_interior.prod isOpen_univ) isOpen_Iio
  have hS_open : IsOpen S := by
    have hEq : S = ((interior G ×ˢ (Set.univ : Set ℝ)) ∩
        (fun p : State × ℝ ↦ φ p.1 - p.2) ⁻¹' Set.Iio 0) := by
      ext p
      simp [S, sub_lt_iff_lt_add']
    rw [hEq]
    exact hS_open_aux
  have hS_conv : Convex ℝ S := by
    simpa [S] using (hφ.subset interior_subset hφ.1.interior).convex_strict_epigraph
  have hq_not_mem : (m, φ m) ∉ S := by
    simp [S, hm]
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open hS_conv hS_open hq_not_mem
  let c : ℝ := f (0, (1 : ℝ))
  let L : State →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ f (x, 0)
      map_add' := by
        intro x y
        simpa using f.map_add (x, (0 : ℝ)) (y, 0)
      map_smul' := by
        intro t x
        simpa using f.map_smul t (x, (0 : ℝ)) }
  have hsplit : ∀ x t, f (x, t) = L x + c * t := by
    intro x t
    rw [show (x, t) = (x, (0 : ℝ)) + (0, t) by simp, map_add]
    have hzero : f (0, t) = c * t := by
      calc
        f (0, t) = f (t • (0, (1 : ℝ))) := by simp
        _ = t * f (0, (1 : ℝ)) := by
          rw [map_smul]
          simp [smul_eq_mul]
        _ = c * t := by ring
    simp [L, hzero, c]
  have hc_pos : 0 < c := by
    have hmem : (m, φ m + 1) ∈ S := by
      simp [S, hm, zero_lt_one]
    have hlt := hf (m, φ m + 1) hmem
    rw [hsplit m (φ m), hsplit m (φ m + 1)] at hlt
    linarith
  let aFun : State → ℝ := fun x ↦ φ m + (L m - L x) / c
  let aLinear : State →ₗ[ℝ] ℝ := (-(1 / c : ℝ)) • L
  let a : State →ᵃ[ℝ] ℝ :=
    { toFun := aFun
      linear := aLinear
      map_vadd' := by
        intro p v
        dsimp [aFun, aLinear]
        rw [map_add]
        field_simp [hc_pos.ne']
        ring }
  have ha_apply : ∀ x, a x = aFun x := by
    intro x
    rfl
  have ha_eq : a m = φ m := by
    rw [ha_apply]
    dsimp [aFun]
    ring_nf
  have ha_lower_interior : ∀ x ∈ interior G, a x ≤ φ x := by
    intro x hx
    by_contra hxa
    have hlt : φ x < aFun x := by
      rw [← ha_apply x]
      exact lt_of_not_ge hxa
    let ε : ℝ := (aFun x - φ x) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hmem : (x, φ x + ε) ∈ S := by
      refine ⟨hx, ?_⟩
      linarith
    have hsep : L m + c * φ m < L x + c * φ x + c * ε := by
      have hraw := hf (x, φ x + ε) hmem
      rw [hsplit m (φ m), hsplit x (φ x + ε)] at hraw
      linarith
    have hlt' : L x + c * φ x < L m + c * φ m := by
      have hmult := mul_lt_mul_of_pos_right hlt hc_pos
      dsimp [aFun] at hmult
      field_simp [hc_pos.ne'] at hmult
      linarith
    have hmid : L x + c * φ x + c * ε = (L m + c * φ m + (L x + c * φ x)) / 2 := by
      dsimp [ε, aFun]
      field_simp [hc_pos.ne']
      ring
    nlinarith [hlt', hsep, hmid]
  exact ⟨a, ha_lower_interior, ha_eq⟩

/-- Helper for Theorem 7.11: if the barycenter lies in the interior of a convex domain, then the
supporting affine map on `interior G` extends canonically to a supporting affine map on `G`. -/
private lemma supporting_affine_minorant_of_mem_interior {G : Set State} {φ : State → ℝ}
    {m : State} (hm : m ∈ interior G) (hφ : ConvexOn ℝ G φ) :
    ∃ g ∈ supporting_affine_maps_on G φ, g ⟨m, interior_subset hm⟩ = φ m := by
  obtain ⟨a, ha_lower_interior, ha_eq⟩ := affine_minorant_touching_on_interior hm hφ
  have ha_lower : ∀ x ∈ G, a x ≤ φ x := by
    intro x hx
    let y : State := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • m
    have hy : y ∈ interior G := by
      exact hφ.1.combo_self_interior_mem_interior hx hm
        (by positivity) (by positivity) (by norm_num)
    have hay : a y ≤ φ y := ha_lower_interior y hy
    have hφy : φ y ≤ (1 / 2 : ℝ) * φ x + (1 / 2 : ℝ) * φ m := by
      have hconv := hφ.2 hx (interior_subset hm)
        (by positivity) (by positivity) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      simpa [y, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hconv
    have hay_eq : a y = (1 / 2 : ℝ) * a x + (1 / 2 : ℝ) * a m := by
      have hy_line : y = AffineMap.lineMap x m (1 / 2 : ℝ) := by
        rw [AffineMap.lineMap_apply_module]
        dsimp [y]
        ring_nf
      rw [hy_line]
      calc
        a (AffineMap.lineMap x m (1 / 2 : ℝ)) = AffineMap.lineMap (a x) (a m) (1 / 2 : ℝ) := by
          exact a.apply_lineMap x m (1 / 2 : ℝ)
        _ = (1 - (1 / 2 : ℝ)) * a x + (1 / 2 : ℝ) * a m := by
          rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
        _ = (1 / 2 : ℝ) * a x + (1 / 2 : ℝ) * a m := by ring
    rw [ha_eq] at hay_eq
    linarith
  refine ⟨Set.restrict G a, ?_, ?_⟩
  · exact ⟨fun x ↦ ha_lower x x.2, a, rfl⟩
  · simpa using ha_eq

/-- Helper for Theorem 7.11: if the contact point lies in the intrinsic interior of a convex
carrier, then one can pass to the affine-span subtype, support there, and extend the affine map
back to the ambient space. -/
private lemma supporting_affine_minorant_of_mem_intrinsicInterior {G : Set State}
    {φ : State → ℝ} {m : State} (hm : m ∈ intrinsicInterior ℝ G) (hφ : ConvexOn ℝ G φ) :
    ∃ g ∈ supporting_affine_maps_on G φ, g ⟨m, intrinsicInterior_subset hm⟩ = φ m := by
  -- TODO: transport the intrinsic-interior point to the direction-space model of `affineSpan ℝ G`,
  -- apply the interior supporting-hyperplane lemma there, and extend the resulting affine map
  -- back to `State`.
  sorry

/-- Helper for Theorem 7.11: if the expectation already lies in the ambient interior of `G`, then
the supporting affine map on `G` can be unpacked into an ambient affine minorant. -/
private lemma affine_minorant_touching_expectation_of_mem_interior
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    {φ : State → ℝ} (hm : P[X] ∈ interior G) (hφ : ConvexOn ℝ G φ) :
    ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ G, a x ≤ φ x) ∧ a (P[X]) = φ (P[X]) := by
  obtain ⟨g, hg, htouch⟩ := supporting_affine_minorant_of_mem_interior hm hφ
  obtain ⟨a, ha_lower, ha_eq⟩ := affine_minorant_of_mem_supporting_affine_maps_on hg
  refine ⟨a, ha_lower, ?_⟩
  calc
    a (P[X]) = g ⟨P[X], interior_subset hm⟩ := ha_eq ⟨P[X], interior_subset hm⟩
    _ = φ (P[X]) := htouch

/-- Helper for Theorem 7.11: if the expectation lies in the intrinsic interior of `G`, then the
supporting affine map on `G` can still be unpacked into an ambient affine minorant. -/
private lemma affine_minorant_touching_expectation_of_mem_intrinsicInterior
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    {φ : State → ℝ} (hm : P[X] ∈ intrinsicInterior ℝ G) (hφ : ConvexOn ℝ G φ) :
    ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ G, a x ≤ φ x) ∧ a (P[X]) = φ (P[X]) := by
  obtain ⟨g, hg, htouch⟩ := supporting_affine_minorant_of_mem_intrinsicInterior hm hφ
  obtain ⟨a, ha_lower, ha_eq⟩ := affine_minorant_of_mem_supporting_affine_maps_on hg
  refine ⟨a, ha_lower, ?_⟩
  calc
    a (P[X]) = g ⟨P[X], intrinsicInterior_subset hm⟩ := ha_eq ⟨P[X], intrinsicInterior_subset hm⟩
    _ = φ (P[X]) := htouch

/-- Helper for Theorem 7.11: the expectation of an integrable random vector taking values almost
surely in a convex set lies in the closure of that convex set. -/
private lemma expectation_mem_closure_of_ae_mem_convex
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    (hX : Integrable X P) (hXG : ∀ᵐ ω ∂P, X ω ∈ G) (hG : Convex ℝ G) :
    P[X] ∈ closure G := by
  simpa using
    hG.closure.integral_mem isClosed_closure
      (hXG.mono fun ω hω ↦ subset_closure hω) hX

/-- Helper for Theorem 7.11: once the barycenter is known to lie in the closure of a convex set,
failing to lie in the intrinsic interior means it lies in the intrinsic frontier. -/
private lemma expectation_mem_intrinsicFrontier_of_not_mem_intrinsicInterior
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    (hX : Integrable X P) (hXG : ∀ᵐ ω ∂P, X ω ∈ G) (hG : Convex ℝ G)
    (hm : P[X] ∉ intrinsicInterior ℝ G) :
    P[X] ∈ intrinsicFrontier ℝ G := by
  have hclosure : P[X] ∈ closure G := expectation_mem_closure_of_ae_mem_convex hX hXG hG
  rw [← closure_diff_intrinsicInterior G]
  exact ⟨hclosure, hm⟩

/-- Helper for Theorem 7.11: an affine map on a nonempty affine subspace extends to the ambient
space by projecting its linear part onto the direction along a chosen linear complement. -/
private lemma extend_affine_map_from_affineSubspace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (s : AffineSubspace ℝ F) [Nonempty s] (b : s →ᵃ[ℝ] ℝ) :
    ∃ a : F →ᵃ[ℝ] ℝ, ∀ x : s, a x = b x := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl s.direction
  let p0 : s := Classical.arbitrary s
  let L : F →ₗ[ℝ] ℝ := b.linear.comp (s.direction.linearProjOfIsCompl q hq)
  let c : ℝ := b p0 - L p0
  let a : F →ᵃ[ℝ] ℝ :=
    { toFun := fun x ↦ L x + c
      linear := L
      map_vadd' := by
        intro p v
        simp [c, map_add, add_assoc, add_left_comm, add_comm] }
  refine ⟨a, ?_⟩
  intro x
  have hproj_x : s.direction.linearProjOfIsCompl q hq (x -ᵥ p0) = x -ᵥ p0 := by
    exact Submodule.linearProjOfIsCompl_apply_left hq (x -ᵥ p0)
  have hproj_sub :
      (s.direction.linearProjOfIsCompl q hq x : F) -
          s.direction.linearProjOfIsCompl q hq p0 =
        (x : F) - p0 := by
    calc
      (s.direction.linearProjOfIsCompl q hq x : F) -
          s.direction.linearProjOfIsCompl q hq p0 =
        ↑((s.direction.linearProjOfIsCompl q hq) ((x : F) - p0)) := by
          simp [LinearMap.map_sub]
      _ = ↑(x -ᵥ p0) := congrArg Subtype.val hproj_x
      _ = (x : F) - p0 := rfl
  have hproj_vsub :
      s.direction.linearProjOfIsCompl q hq x -
          s.direction.linearProjOfIsCompl q hq p0 =
        x -ᵥ p0 := by
    exact Subtype.ext hproj_sub
  change L x + c = b x
  dsimp [c]
  have hb : b x = b.linear (x -ᵥ p0) + b p0 := by
    simpa using b.map_vadd' p0 (x -ᵥ p0)
  have hlin :
      b.linear (s.direction.linearProjOfIsCompl q hq x) -
          b.linear (s.direction.linearProjOfIsCompl q hq p0) =
        b.linear (x -ᵥ p0) := by
    rw [← b.linear.map_sub]
    simpa using congrArg b.linear hproj_vsub
  have hLx : L x = b.linear (s.direction.linearProjOfIsCompl q hq x) := by
    rfl
  have hLp0 : L p0 = b.linear (s.direction.linearProjOfIsCompl q hq p0) := by
    rfl
  rw [hLx, hLp0]
  linarith [hb, hlin]

/-- Helper for Theorem 7.11: after shrinking to a convex carrier containing the essential range of
`X`, a convex function admits a touching affine minorant at the barycenter. -/
private lemma affine_minorant_touching_expectation_on_carrier
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    {φ : State → ℝ} (hX : Integrable X P) (hXG : ∀ᵐ ω ∂P, X ω ∈ G)
    (hφ : ConvexOn ℝ G φ) :
    ∃ K : Set State, K ⊆ G ∧ Convex ℝ K ∧
      (∀ᵐ ω ∂P, X ω ∈ K) ∧
      ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ K, a x ≤ φ x) ∧ a (P[X]) = φ (P[X]) := by
  by_cases hm : P[X] ∈ intrinsicInterior ℝ G
  · obtain ⟨a, ha_lower, ha_eq⟩ :=
      affine_minorant_touching_expectation_of_mem_intrinsicInterior hm hφ
    exact ⟨G, subset_rfl, hφ.1, hXG, a, ha_lower, ha_eq⟩
  · have hm_frontier : P[X] ∈ intrinsicFrontier ℝ G :=
      expectation_mem_intrinsicFrontier_of_not_mem_intrinsicInterior hX hXG hφ.1 hm
    -- TODO: package the intrinsic-frontier branch as a translated exposed-slice reduction on the
    -- affine-span carrier: from `hm_frontier`, produce a proper convex `K ⊆ G` containing `X`
    -- almost surely, prove `affineSpan ℝ K < affineSpan ℝ G`, recurse there, and extend the
    -- resulting affine minorant back with `extend_affine_map_from_affineSubspace`.
    let _ := hm_frontier
    sorry

/-- Theorem 7.11: Jensen's inequality on `EuclideanSpace ℝ (Fin n)`. If an integrable random
vector `X` takes values almost surely in a convex set `G`, then the negative part of `φ ∘ X` has
finite expectation, and the extended expectation of `φ(X)`, written canonically as the difference
of the lower integrals of its positive and negative parts, is at least `φ` evaluated at the
expectation of `X`. -/
-- Proof sketch: apply the finite-dimensional Jensen argument to `X`; use a touching supporting
-- affine minorant on a convex carrier containing the essential range of `X`, then integrate the
-- affine lower bound.
theorem convexOn_erealExpectation_comp_ge_euclidean {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Set State} {X : Ω → State} {φ : State → ℝ} (hX : Integrable X P)
    (hXG : ∀ᵐ ω ∂P, X ω ∈ G) (hφ : ConvexOn ℝ G φ) :
    (∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) < ⊤ ∧
      (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) ≥
        (φ (P[X]) : EReal) := by
  obtain ⟨K, _, _, hXK, a, ha_lower, ha_eq⟩ :=
    affine_minorant_touching_expectation_on_carrier hX hXG hφ
  have ha_int : Integrable (fun ω ↦ a (X ω)) P := integrable_affine_comp_of_integrable hX a
  have ha_expect : P[fun ω ↦ a (X ω)] = a (P[X]) := affine_expectation_eq_expectation_apply hX a
  refine ⟨lintegral_neg_comp_lt_top_of_affine_lower_bound hXK ha_lower ha_int, ?_⟩
  exact ereal_jensen_ge_of_affine_lower_bound hXK ha_lower ha_eq ha_int ha_expect
