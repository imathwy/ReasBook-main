import Mathlib
import cartan.II.section05.«0001_Definition_II_1_extra_1»
import cartan.II.section05.«0033_Definition_II_1_extra_20»
import cartan.II.section05.«0036_Corollary_II_1_extra_23»
import cartan.II.section06.«0005_Corollary_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology unitInterval

noncomputable section

universe u

-- Semantic recall note: no `lean_leansearch` MCP tool was exposed in this session, so the
-- statement shape below follows local oriented-boundary precedent and the available Mathlib
-- contour-integral API.

/-- Theorem III.5-extra-2 (1): if the singular points of `f` in `D` are isolated in the
source-text sense, namely the singular set has no accumulation point in `D`, then only finitely
many of them can lie in a fixed compact subset `K ⊆ D`. The separate punctured-holomorphic
hypothesis records that these locally discrete singular points are genuine isolated singularities
of `f`. -/
theorem finite_nondifferentiable_points_in_compact_of_isolated
    {K D : Set ℂ} {f : ℂ → ℂ} (hK : IsCompact K) (hKD : K ⊆ D)
    (hdiscrete :
      ∀ z ∈ D, ∃ r > 0,
        Metric.ball z r ∩ {w | w ∈ D ∧ ¬ DifferentiableAt ℂ f w} ⊆ {z})
    (hisolated :
      ∀ z ∈ D, ¬ DifferentiableAt ℂ f z →
        ∃ r > 0,
          Metric.closedBall z r ⊆ D ∧
          DifferentiableOn ℂ f (Metric.ball z r \ ({z} : Set ℂ))) :
    Set.Finite (K ∩ {z | ¬ DifferentiableAt ℂ f z}) := by
  let _ := hisolated
  let S : Set ℂ := {z | DifferentiableAt ℂ f z}
  have hS_codiscrete : S ∈ Filter.codiscreteWithin D := by
    rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
    intro z hz
    rcases hdiscrete z hz with ⟨r, hr, hball⟩
    refine ⟨Metric.ball z r \ ({z} : Set ℂ), ?_, ?_⟩
    · simpa [Set.diff_eq, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
        (inter_mem_nhdsWithin ({z} : Set ℂ)ᶜ
          (Metric.ball_mem_nhds z hr))
    ext w
    constructor
    · intro hw
      have hwSing : w ∈ {w | w ∈ D ∧ ¬ DifferentiableAt ℂ f w} := by
        exact ⟨hw.2.1, hw.2.2⟩
      have hwEq : w = z := by
        exact hball ⟨hw.1.1, hwSing⟩
      exact hw.1.2 hwEq
    · intro hw
      exact False.elim hw
  have hKfinite : (K \ S).Finite :=
    hK.finite_diff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hKD hS_codiscrete)
  -- Rewrite the compact difference against the differentiability locus as the singular subset.
  simpa [S, Set.diff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hKfinite

/-- `LocalResidueCircle K D f z residue_z` means that there exists a positive small circle around
`z`, contained in both `interior K` and `D`, on which the circle integral of `f` realizes the
prescribed residue. -/
def LocalResidueCircle (K D : Set ℂ) (f : ℂ → ℂ) (z residue_z : ℂ) : Prop :=
  ∃ radius > 0,
    Metric.closedBall z radius ⊆ interior K ∧
      Metric.closedBall z radius ⊆ D ∧
        (∮ w in C(z, radius), f w) = (2 * Real.pi * Complex.I : ℂ) * residue_z

/-- Source-faithful local residue data for a finite singularity set: the residue circle is small
enough to stay inside the compact owner and to avoid every other listed singularity. This is the
extra isolation condition used in the textbook proof when the small discs around the singularities
are chosen disjoint. -/
def IsolatedLocalResidueCircle
    (K D : Set ℂ) (s : Finset ℂ) (f : ℂ → ℂ) (z residue_z : ℂ) : Prop :=
  ∃ radius > 0,
    Metric.closedBall z radius ⊆ interior K ∧
      Metric.closedBall z radius ⊆ D ∧
        (∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z radius) ∧
          DifferentiableOn ℂ f (Metric.ball z radius \ ({z} : Set ℂ)) ∧
            (∮ w in C(z, radius), f w) = (2 * Real.pi * Complex.I : ℂ) * residue_z

/-- Helper for Theorem III.5-extra-2: if `f` is continuous on the closed annulus
`ρ ≤ dist z w ≤ R` and holomorphic on its interior, then the two circle integrals agree. -/
lemma circleIntegral_eq_of_punctured_ball_shrink
    {f : ℂ → ℂ} {z : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hcont : ContinuousOn f (Metric.closedBall z R \ Metric.ball z ρ))
    (hdiff : DifferentiableOn ℂ f (Metric.ball z R \ Metric.closedBall z ρ)) :
    (∮ w in C(z, R), f w) = ∮ w in C(z, ρ), f w := by
  have hAnnulusOpen : IsOpen (Metric.ball z R \ Metric.closedBall z ρ) :=
    Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  -- Apply the annulus Cauchy-Goursat theorem after converting the interior differentiability
  -- back to ordinary differentiability.
  simpa using Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hρ hρR Set.countable_empty hcont
      (fun w hw ↦ (hdiff w hw.1).differentiableAt (hAnnulusOpen.mem_nhds hw.1))

/-- Helper for Theorem III.5-extra-2: shrinking an isolated local residue circle to half its
radius preserves the residue formula and leaves the other singularities outside twice the new
radius. -/
lemma exists_half_radius_isolated_local_residue_circle
    {K D : Set ℂ} {s : Finset ℂ} {f residue : ℂ → ℂ} {z : ℂ}
    (hD : IsOpen D) (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ))) (hz : z ∈ s)
    (hres : IsolatedLocalResidueCircle K D s f z (residue z)) :
    ∃ ρ > 0,
      Metric.closedBall z ρ ⊆ interior K ∧
        Metric.closedBall z ρ ⊆ D ∧
          (∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z ρ) ∧
            DifferentiableOn ℂ f (Metric.ball z ρ \ ({z} : Set ℂ)) ∧
              (∀ w ∈ s, w ≠ z → 2 * ρ < dist z w) ∧
                (∮ w in C(z, ρ), f w) = (2 * Real.pi * Complex.I : ℂ) * residue z := by
  rcases hres with ⟨R, hR, hRK, hRD, hsep, hdiffR, hcircleR⟩
  let ρ : ℝ := R / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact half_pos hR
  have hρR : ρ ≤ R := by
    dsimp [ρ]
    linarith
  have hρK : Metric.closedBall z ρ ⊆ interior K := by
    exact (Metric.closedBall_subset_closedBall hρR).trans hRK
  have hρD : Metric.closedBall z ρ ⊆ D := by
    exact (Metric.closedBall_subset_closedBall hρR).trans hRD
  have hρsep :
      ∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z ρ := by
    intro w hw hwz hwBall
    exact hsep w hw hwz ((Metric.closedBall_subset_closedBall hρR) hwBall)
  have hρdiff :
      DifferentiableOn ℂ f (Metric.ball z ρ \ ({z} : Set ℂ)) := by
    refine hdiffR.mono ?_
    intro w hw
    refine ⟨(Metric.ball_subset_ball hρR) hw.1, hw.2⟩
  have hsClosed : IsClosed (↑s : Set ℂ) := s.finite_toSet.isClosed
  have hDsOpen : IsOpen (D \ (↑s : Set ℂ)) := hD.sdiff hsClosed
  have hClosedAnnulusSubset :
      Metric.closedBall z R \ Metric.ball z ρ ⊆ D \ (↑s : Set ℂ) := by
    intro w hw
    refine ⟨hRD hw.1, ?_⟩
    intro hwS
    by_cases hwz : w = z
    · subst hwz
      exact hw.2 (Metric.mem_ball_self hρ)
    · exact hsep w hwS hwz hw.1
  have hOpenAnnulusSubset :
      Metric.ball z R \ Metric.closedBall z ρ ⊆ D \ (↑s : Set ℂ) := by
    intro w hw
    refine ⟨hRD (Metric.ball_subset_closedBall hw.1), ?_⟩
    intro hwS
    by_cases hwz : w = z
    · subst hwz
      exact hw.2 (Metric.mem_closedBall_self hρ.le)
    · exact hsep w hwS hwz (Metric.ball_subset_closedBall hw.1)
  have hcontAnnulus :
      ContinuousOn f (Metric.closedBall z R \ Metric.ball z ρ) :=
    hhol.continuousOn.mono hClosedAnnulusSubset
  have hdiffAnnulus :
      DifferentiableOn ℂ f (Metric.ball z R \ Metric.closedBall z ρ) :=
    hhol.mono hOpenAnnulusSubset
  have hcircleρ : (∮ w in C(z, R), f w) = ∮ w in C(z, ρ), f w :=
    circleIntegral_eq_of_punctured_ball_shrink hρ hρR hcontAnnulus hdiffAnnulus
  have hdist :
      ∀ w ∈ s, w ≠ z → 2 * ρ < dist z w := by
    intro w hw hwz
    have hlt : R < dist z w := by
      by_contra hle
      exact hsep w hw hwz (by simpa [Metric.mem_closedBall, dist_comm] using hle)
    dsimp [ρ]
    linarith
  refine ⟨ρ, hρ, hρK, hρD, hρsep, hρdiff, hdist, ?_⟩
  -- Rewrite the large-circle residue formula through the annulus-invariance comparison.
  calc
    (∮ w in C(z, ρ), f w) = ∮ w in C(z, R), f w := hcircleρ.symm
    _ = (2 * Real.pi * Complex.I : ℂ) * residue z := hcircleR

/-- Helper for Theorem III.5-extra-2: strict separation of radii implies pairwise disjoint closed
excision discs. -/
lemma pairwise_disjoint_closedBall_of_radius_separation
    {s : Finset ℂ} {ρ : ℂ → ℝ}
    (hρnonneg : ∀ z ∈ s, 0 ≤ ρ z)
    (hsep : ∀ z ∈ s, ∀ w ∈ s, w ≠ z → ρ z + ρ w < dist z w) :
    ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)) := by
  intro z hz w hw hzw
  rw [disjoint_closedBall_closedBall_iff (hρnonneg z hz) (hρnonneg w hw)]
  exact hsep z hz w hw hzw.symm

/-- Helper for Theorem III.5-extra-2: a boundary path of an oriented boundary misses every closed
ball that is already contained in `interior K`. -/
lemma boundary_path_disjoint_of_closedBall_subset_interior
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) {z : ℂ} {r : ℝ}
    (hball : Metric.closedBall z r ⊆ interior K) :
    ∀ i, Disjoint (Set.range (Γ i).toPath) (Metric.closedBall z r) := by
  intro i
  refine Set.disjoint_left.2 ?_
  intro w hwΓ hwBall
  have hwFrontier : w ∈ frontier K := hΓ.range_toPath_subset_frontier i hwΓ
  have hwInterior : w ∈ interior K := hball hwBall
  -- The excision discs lie strictly inside `K`, whereas every oriented-boundary path lives on
  -- `frontier K`, so the two sets are disjoint.
  exact (Set.disjoint_left.1 disjoint_interior_frontier) hwInterior hwFrontier

/-- Helper for Theorem III.5-extra-2: if each excision closed ball lies in `interior K`, then the
boundary paths are disjoint from the finite set of excision centers. -/
lemma boundary_path_disjoint_of_centers_closedBall_subset_interior
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) {s : Finset ℂ} {ρ : ℂ → ℝ}
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K) :
    ∀ i, Disjoint (Set.range (Γ i).toPath) (↑s : Set ℂ) := by
  intro i
  refine Set.disjoint_left.2 ?_
  intro w hwΓ hwS
  have hwInterior : w ∈ interior K := by
    have hwBall : w ∈ Metric.closedBall w (ρ w) := Metric.mem_closedBall_self (hρpos w hwS).le
    exact hρK w hwS hwBall
  have hwFrontier : w ∈ frontier K := hΓ.range_toPath_subset_frontier i hwΓ
  -- The centers lie strictly inside `K`, while each boundary path stays on `frontier K`.
  exact (Set.disjoint_left.1 disjoint_interior_frontier) hwInterior hwFrontier

/-- Helper for Theorem III.5-extra-2: once `K ⊆ D`, removing the open balls around the finite set
still leaves a subset of the punctured domain `D \ s`. -/
lemma punctured_owner_subset_punctured_domain_of_excised_balls
    {K D : Set ℂ} {s : Finset ℂ} {ρ : ℂ → ℝ}
    (hKD : K ⊆ D) (hρpos : ∀ z ∈ s, 0 < ρ z) :
    K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z) ⊆ D \ (↑s : Set ℂ) := by
  intro w hw
  refine ⟨hKD hw.1, ?_⟩
  intro hwS
  have hwBall : w ∈ Metric.ball w (ρ w) := Metric.mem_ball_self (hρpos w hwS)
  exact hw.2 (by exact Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨hwS, hwBall⟩⟩)

/-- Helper for Theorem III.5-extra-2: holomorphy on the punctured domain gives a closed
real-linear form there, so the later excision argument can finish by the oriented-boundary zero
theorem without any further analytic reduction. -/
lemma realScalarOneForm_isClosedOn_punctured_domain
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ} {s : Finset ℂ}
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ))) :
    IsClosedOn (Complex.realScalarOneForm f) (D \ (↑s : Set ℂ)) := by
  let puncturedD : Set ℂ := D \ (↑s : Set ℂ)
  have hpunctured_open : IsOpen puncturedD := hD.sdiff s.finite_toSet.isClosed
  intro z hz
  rcases holomorphic_has_local_primitive hpunctured_open hhol hz with ⟨r, hr, hball, hExact⟩
  -- Convert the local complex primitive on the punctured ball into a primitive for the underlying
  -- real form `f(z) dz`.
  refine ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball, ?_⟩
  simpa [puncturedD, Complex.realScalarOneForm] using hExact.hasPrimitiveOn

/-- Helper for Theorem III.5-extra-2: the positively oriented circle centered at `a` with radius
`r`, written as an explicit loop for the later excision bookkeeping. -/
def boundary_circle_path (a : ℂ) (r : ℝ) : Path (a + r) (a + r) :=
  Path.mk
    ⟨fun t ↦ circleMap a r (2 * Real.pi * (t : ℝ)), by
      fun_prop⟩
    (by
      -- At `t = 0`, the loop starts at the positive real boundary point.
      simp [circleMap])
    (by
      -- At `t = 1`, the angle is `2π`, so the path closes.
      simp [circleMap, Complex.exp_two_pi_mul_I])

/-- Helper for Theorem III.5-extra-2: unpacking a loop through `toClosedPath.toPath` only inserts
the endpoint cast forced by the closed-path packaging. -/
lemma loop_toClosedPath_toPath_eq_cast {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.toPath =
      γ.cast (by simpa [Path.toClosedPath] using γ.source)
        (by simpa [Path.toClosedPath] using γ.source) := by
  -- After destructing the loop, the wrapper and its unpacking are definitionally the same path.
  cases γ
  rfl

/-- Helper for Theorem III.5-extra-2: the real-curve parametrization of a loop closed path is the
original path extension written in real coordinates. -/
lemma toClosedPath_realCurve_eq {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.realCurve = Complex.equivRealProd ∘ γ.extend := by
  -- After destructing the loop, the real-curve wrapper is definitionally the original extension.
  cases γ
  rfl

/-- Helper for Theorem III.5-extra-2: on the unit interval, the explicit boundary-circle loop is
the standard `circleMap` parametrization. -/
lemma boundary_circle_path_extend_eq_circleMap {a : ℂ} {r t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (boundary_circle_path a r).extend t = circleMap a r (2 * Real.pi * t) := by
  -- Inside the unit interval, `Path.extend` is just evaluation of the original loop.
  simpa [boundary_circle_path] using
    (Path.extend_apply (γ := boundary_circle_path a r) ht)

/-- Helper for Theorem III.5-extra-2: the positive boundary circle has image exactly the
geometric sphere it bounds. -/
lemma range_boundary_circle_path_eq_sphere {a : ℂ} {r : ℝ} (hr : 0 < r) :
    Set.range (boundary_circle_path a r) = Metric.sphere a r := by
  -- Every boundary-path value lies on the sphere, and every spherical point occurs at some angle.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simpa [boundary_circle_path, abs_of_pos hr] using
      circleMap_mem_sphere' a r (2 * Real.pi * (t : ℝ))
  · intro hz
    have hz' : z ∈ Metric.sphere a |r| := by
      simpa [abs_of_pos hr] using hz
    rw [← image_circleMap_Ioc a r] at hz'
    rcases hz' with ⟨θ, hθ, rfl⟩
    refine ⟨⟨θ / (2 * Real.pi), ?_, ?_⟩, ?_⟩
    · exact div_nonneg hθ.1.le (by positivity)
    · exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2 (by simpa using hθ.2)
    · have hscale : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
        field_simp [Real.pi_ne_zero]
      simp [boundary_circle_path, hscale]

/-- Helper for Theorem III.5-extra-2: the boundary circle is globally `C¹`, hence piecewise
differentiable. -/
lemma boundary_circle_path_isPiecewiseDifferentiable (a : ℂ) (r : ℝ) :
    (boundary_circle_path a r).IsPiecewiseDifferentiable := by
  -- The explicit circle parametrization is smooth on the whole unit interval.
  have hdiff : (boundary_circle_path a r).IsDifferentiable := by
    rw [Path.IsDifferentiable]
    let g : ℝ → ℂ := fun t ↦ circleMap a r (2 * Real.pi * t)
    have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ 2 * Real.pi * t) := by
      simpa [one_mul] using (contDiff_const.mul contDiff_id)
    have hg : ContDiff ℝ 1 g := by
      simpa [g] using (contDiff_circleMap a r).comp hlin
    refine hg.contDiffOn.congr ?_
    intro t ht
    simpa [g] using boundary_circle_path_extend_eq_circleMap (a := a) (r := r) (t := t) ht
  exact hdiff.isPiecewiseDifferentiable

/-- Helper for Theorem III.5-extra-2: the positive boundary circle identifies only equal
parameters or the two endpoints of the unit interval. -/
lemma boundary_circle_path_simple_eq_or_endpoints {a : ℂ} {r : ℝ} (hr : r ≠ 0)
    {s t : Set.Icc (0 : ℝ) 1} (h : boundary_circle_path a r s = boundary_circle_path a r t) :
    s = t ∨ ((s : ℝ) = 0 ∧ (t : ℝ) = 1) ∨ ((s : ℝ) = 1 ∧ (t : ℝ) = 0) := by
  let α : ℝ := 2 * Real.pi * (s : ℝ)
  let β : ℝ := 2 * Real.pi * (t : ℝ)
  have hcircle : circleMap a r α = circleMap a r β := by
    simpa [boundary_circle_path, α, β] using h
  have hlen : |(0 : ℝ) - 2 * Real.pi| ≤ 2 * Real.pi := by
    simpa [abs_of_nonneg Real.two_pi_pos.le]
  have hinj :=
    injOn_circleMap_of_abs_sub_le (c := a) (R := r) (a := (0 : ℝ)) (b := 2 * Real.pi) hr hlen
  by_cases hs0 : (s : ℝ) = 0
  · by_cases ht0 : (t : ℝ) = 0
    · exact Or.inl (Subtype.ext (hs0.trans ht0.symm))
    · have htpos : 0 < (t : ℝ) := by
        exact lt_of_le_of_ne t.2.1 (by
          intro htEq
          exact ht0 htEq.symm)
      have hβmem : β ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [β]
          nlinarith [Real.two_pi_pos, htpos]
        · dsimp [β]
          nlinarith [Real.two_pi_pos, t.2.2]
      have h2πmem : (2 * Real.pi : ℝ) ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · nlinarith [Real.pi_pos]
        · exact le_rfl
      have hβ2π : circleMap a r β = circleMap a r (2 * Real.pi) := by
        calc
          circleMap a r β = circleMap a r 0 := by
            simpa [α, hs0] using hcircle.symm
          _ = circleMap a r (2 * Real.pi) := by
            simp [circleMap, Complex.exp_two_pi_mul_I]
      have hβeq : β = 2 * Real.pi := hinj hβmem h2πmem hβ2π
      have ht1 : (t : ℝ) = 1 := by
        dsimp [β] at hβeq
        nlinarith [Real.two_pi_pos, hβeq]
      right
      left
      exact ⟨hs0, ht1⟩
  · by_cases ht0 : (t : ℝ) = 0
    · have hspos : 0 < (s : ℝ) := by
        exact lt_of_le_of_ne s.2.1 (by
          intro hsEq
          exact hs0 hsEq.symm)
      have hαmem : α ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [α]
          nlinarith [Real.two_pi_pos, hspos]
        · dsimp [α]
          nlinarith [Real.two_pi_pos, s.2.2]
      have h2πmem : (2 * Real.pi : ℝ) ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · nlinarith [Real.pi_pos]
        · exact le_rfl
      have hα2π : circleMap a r α = circleMap a r (2 * Real.pi) := by
        calc
          circleMap a r α = circleMap a r 0 := by
            simpa [β, ht0] using hcircle
          _ = circleMap a r (2 * Real.pi) := by
            simp [circleMap, Complex.exp_two_pi_mul_I]
      have hαeq : α = 2 * Real.pi := hinj hαmem h2πmem hα2π
      have hs1 : (s : ℝ) = 1 := by
        dsimp [α] at hαeq
        nlinarith [Real.two_pi_pos, hαeq]
      right
      right
      exact ⟨hs1, ht0⟩
    · have hspos : 0 < (s : ℝ) := by
        exact lt_of_le_of_ne s.2.1 (by
          intro hsEq
          exact hs0 hsEq.symm)
      have htpos : 0 < (t : ℝ) := by
        exact lt_of_le_of_ne t.2.1 (by
          intro htEq
          exact ht0 htEq.symm)
      have hαmem : α ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [α]
          nlinarith [Real.two_pi_pos, hspos]
        · dsimp [α]
          nlinarith [Real.two_pi_pos, s.2.2]
      have hβmem : β ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [β]
          nlinarith [Real.two_pi_pos, htpos]
        · dsimp [β]
          nlinarith [Real.two_pi_pos, t.2.2]
      have hαeqβ : α = β := hinj hαmem hβmem hcircle
      have hst : (s : ℝ) = (t : ℝ) := by
        dsimp [α, β] at hαeqβ
        nlinarith [Real.two_pi_pos, hαeqβ]
      exact Or.inl (Subtype.ext hst)

/-- Helper for Theorem III.5-extra-2: reversing the boundary circle preserves its geometric image,
so the clockwise loop still traces the same sphere. -/
lemma range_clockwise_boundary_circle_toPath_eq_sphere {a : ℂ} {r : ℝ} (hr : 0 < r) :
    Set.range (((boundary_circle_path a r).symm).toClosedPath.toPath) = Metric.sphere a r := by
  -- Removing the closed-path wrapper and then reversing the path does not change the image set.
  calc
    Set.range (((boundary_circle_path a r).symm).toClosedPath.toPath) =
        Set.range ((boundary_circle_path a r).symm) := by
          rw [loop_toClosedPath_toPath_eq_cast]
          simp
    _ = Set.range (boundary_circle_path a r) := Path.symm_range _
    _ = Metric.sphere a r := range_boundary_circle_path_eq_sphere hr

/-- Helper for Theorem III.5-extra-2: integrating a complex-valued `1`-form along the explicit
positive boundary circle is the textbook `θ`-integral after `θ = 2π t`. -/
lemma curveIntegral_boundary_circle_path_eq_intervalIntegral
    {ω : ℂ → ℂ →L[ℝ] ℂ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in boundary_circle_path a r, ω z =
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
  let h : ℝ → ℂ := fun θ ↦ ω (circleMap a r θ) (deriv (circleMap a r) θ)
  have hcongr :
      ∫ t in (0 : ℝ)..1,
          ω ((boundary_circle_path a r).extend t) (deriv ((boundary_circle_path a r).extend) t) =
        ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := by
    -- On `(0,1)`, the loop extension agrees with the standard circle parametrization.
    have hcongr_ae :
        (fun t ↦
            ω ((boundary_circle_path a r).extend t) (deriv ((boundary_circle_path a r).extend) t))
          =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)]
              (fun t ↦ (2 * Real.pi : ℝ) • h (t * (2 * Real.pi))) := by
      rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have hlocal :
          (boundary_circle_path a r).extend =ᶠ[nhds t]
            fun s : ℝ ↦ circleMap a r (s * (2 * Real.pi)) := by
        have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
        filter_upwards [hIoo] with s hs
        rw [Path.extend_apply (boundary_circle_path a r) ⟨hs.1.le, hs.2.le⟩]
        simp [boundary_circle_path, mul_comm]
      have hderiv :
          deriv (boundary_circle_path a r).extend t =
            (2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi)) := by
        rw [Filter.EventuallyEq.deriv_eq hlocal]
        simpa using
          (((hasDerivAt_circleMap a r (t * (2 * Real.pi))).scomp t
            (hasDerivAt_mul_const (2 * Real.pi : ℝ))).deriv)
      have hext :
          (boundary_circle_path a r).extend t = circleMap a r (t * (2 * Real.pi)) :=
        Filter.EventuallyEq.eq_of_nhds hlocal
      -- Evaluate the form on the chain-rule tangent vector.
      calc
        ω ((boundary_circle_path a r).extend t) (deriv ((boundary_circle_path a r).extend) t) =
            ω (circleMap a r (t * (2 * Real.pi)))
              ((2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi))) := by
          rw [hext, hderiv]
        _ = (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := by
          change
            ω (circleMap a r (t * (2 * Real.pi)))
                ((2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi))) =
              (2 * Real.pi : ℝ) •
                ω (circleMap a r (t * (2 * Real.pi))) (deriv (circleMap a r) (t * (2 * Real.pi)))
          rw [map_smul]
    exact intervalIntegral.integral_congr_ae_restrict hcongr_ae
  have hsmul :
      ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) =
        (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := by
    simpa using intervalIntegral.integral_smul (a := (0 : ℝ)) (b := 1)
      (r := (2 * Real.pi : ℝ)) (f := fun t ↦ h (t * (2 * Real.pi)))
  -- First rewrite the path integral as a parameter integral, then perform `θ = 2π t`.
  rw [curveIntegral_eq_intervalIntegral_deriv]
  calc
    ∫ t in (0 : ℝ)..1,
        ω ((boundary_circle_path a r).extend t) (deriv ((boundary_circle_path a r).extend) t) =
      ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := hcongr
    _ = (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := hsmul
    _ = ∫ θ in (0 : ℝ) * (2 * Real.pi)..1 * (2 * Real.pi), h θ := by
      simpa using (intervalIntegral.smul_integral_comp_mul_right
        (f := h) (a := (0 : ℝ)) (b := 1) (c := 2 * Real.pi))
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi, h θ := by
      simp
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
        MeasureTheory.restrict_Ioc_eq_restrict_Icc]

/-- Helper for Theorem III.5-extra-2: the closed-path wrapper used by the oriented-boundary API
does not change the positive-circle integral. -/
lemma curveIntegral_boundary_circle_toClosedPath_eq_intervalIntegral
    {ω : ℂ → ℂ →L[ℝ] ℂ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in (boundary_circle_path a r).toClosedPath.toPath, ω z =
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
  -- Remove the harmless endpoint cast inserted by `toClosedPath.toPath`.
  calc
    ∫ᶜ z in (boundary_circle_path a r).toClosedPath.toPath, ω z =
        ∫ᶜ z in boundary_circle_path a r, ω z := by
          rw [loop_toClosedPath_toPath_eq_cast]
          simp
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
      exact curveIntegral_boundary_circle_path_eq_intervalIntegral (ω := ω)

/-- Helper for Theorem III.5-extra-2: the explicit positive boundary-circle path realizes the
standard complex `circleIntegral`. -/
lemma curveIntegral_boundary_circle_eq_circleIntegral
    {f : ℂ → ℂ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in boundary_circle_path a r, (f dz) z = ∮ w in C(a, r), f w := by
  -- Rewrite the path integral through the harmless closed-path wrapper, then unfold the standard
  -- `circleIntegral` parametrization.
  calc
    ∫ᶜ z in boundary_circle_path a r, (f dz) z =
        ∫ᶜ z in (boundary_circle_path a r).toClosedPath.toPath, (f dz) z := by
          rw [loop_toClosedPath_toPath_eq_cast]
          simp
    _ = ∫ᶜ z in (boundary_circle_path a r).toClosedPath.toPath, Complex.realScalarOneForm f z := by
          simpa [Complex.realScalarOneForm] using
            (curveIntegral_restrictScalars
              (γ := (boundary_circle_path a r).toClosedPath.toPath)
              (ω := fun z ↦ (f dz) z) (𝕜 := ℂ) (𝕝 := ℝ)).symm
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
          (Complex.realScalarOneForm f) (circleMap a r θ) (deriv (circleMap a r) θ) := by
          exact curveIntegral_boundary_circle_toClosedPath_eq_intervalIntegral
            (ω := Complex.realScalarOneForm f) (a := a) (r := r)
    _ = ∮ w in C(a, r), f w := by
      rw [circleIntegral_def_Icc]
      let g : ℝ → ℂ := fun θ ↦
        (Complex.realScalarOneForm f) (circleMap a r θ) (deriv (circleMap a r) θ)
      let h : ℝ → ℂ := fun θ ↦ f (circleMap a r θ) * deriv (circleMap a r) θ
      have hAE : g =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))] h := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
        simp [g, h, Complex.realScalarOneForm, smul_eq_mul, mul_comm]
      simpa [g, h, mul_comm] using intervalIntegral.integral_congr_ae_restrict hAE

/-- Helper for Theorem III.5-extra-2: reversing the explicit boundary circle changes the sign of
the integral, so the clockwise inner boundary contributes the negative circle integral. -/
lemma curveIntegral_clockwise_boundary_circle_eq_neg_circleIntegral
    {f : ℂ → ℂ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in ((boundary_circle_path a r).symm.toClosedPath).toPath, (f dz) z =
      -(∮ w in C(a, r), f w) := by
  -- The inner excision circles are clockwise, so they are the reversed positive loops.
  calc
    ∫ᶜ z in ((boundary_circle_path a r).symm.toClosedPath).toPath, (f dz) z =
        ∫ᶜ z in (boundary_circle_path a r).symm, (f dz) z := by
          rw [loop_toClosedPath_toPath_eq_cast]
          simp
    _ = -∫ᶜ z in boundary_circle_path a r, (f dz) z := by
      simpa using curveIntegral_symm (γ := boundary_circle_path a r) (ω := fun z ↦ (f dz) z)
    _ = -(∮ w in C(a, r), f w) := by
      rw [curveIntegral_boundary_circle_eq_circleIntegral]

/-- Helper for Theorem III.5-extra-2: the punctured owner's boundary family consists of the
original outer boundary components together with one clockwise circle for each excised disc. -/
def finite_excision_boundary_family
    {ι : Type u} [Fintype ι] (Γ : ι → ClosedPath ℂ) (s : Finset ℂ) (ρ : ℂ → ℝ) :
    ι ⊕ s.attach → ClosedPath ℂ
  | Sum.inl i => Γ i
  | Sum.inr z => ((boundary_circle_path z.1 (ρ z.1)).symm).toClosedPath

/-- Helper for Theorem III.5-extra-2: summing a circle-integral expression over `s.attach`
is definitionally the same as summing it over `s`. -/
lemma sum_attach_circleIntegral_eq_sum
    {f : ℂ → ℂ} {s : Finset ℂ} {ρ : ℂ → ℝ} :
    (∑ z : s.attach, ∮ w in C(z.1, ρ z.1), f w) =
      Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
  -- Remove the subtype index once so the later boundary-sum rewrite can work on the textbook
  -- finite sum over the singularity centers themselves.
  calc
    (∑ z : s.attach, ∮ w in C(z.1, ρ z.1), f w) =
        Finset.sum s.attach.attach (fun z ↦ ∮ w in C(z.1.1, ρ z.1.1), f w) := by
          rw [Finset.univ_eq_attach]
    _ = Finset.sum s.attach (fun z ↦ ∮ w in C(z.1, ρ z.1), f w) := by
          exact (s.attach).sum_attach (fun z : ↥s ↦ ∮ w in C(z.1, ρ z.1), f w)
    _ = Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
          exact s.sum_attach (fun z ↦ ∮ w in C(z, ρ z), f w)

/-- Helper for Theorem III.5-extra-2: once the punctured owner has the expected boundary family,
its total boundary integral is the outer sum minus the positive inner circle integrals. -/
lemma sum_curveIntegral_finite_excision_boundary_family
    {ι : Type u} [Fintype ι] (Γ : ι → ClosedPath ℂ) {f : ℂ → ℂ}
    (s : Finset ℂ) (ρ : ℂ → ℝ) :
    ∑ j, ∫ᶜ z in (finite_excision_boundary_family Γ s ρ j).toPath, (f dz) z =
      (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) -
        Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
  -- Split the punctured boundary family into the original outer components and the attached inner
  -- clockwise circles.
  rw [Fintype.sum_sum_type]
  -- Rewrite the inner clockwise contributions as negative positively oriented circle integrals.
  simp_rw [finite_excision_boundary_family,
    curveIntegral_clockwise_boundary_circle_eq_neg_circleIntegral]
  -- Collapse the attached finite sum back to the textbook sum indexed by the excised centers.
  calc
    (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) +
        ∑ z : s.attach, -(∮ w in C(z.1, ρ z.1), f w) =
      (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) -
        ∑ z : s.attach, ∮ w in C(z.1, ρ z.1), f w := by
          rw [sub_eq_add_neg]
          congr 1
          simpa [Finset.univ_eq_attach] using
            (Finset.sum_neg_distrib
              (s := s.attach) (f := fun z : s.attach ↦ ∮ w in C(z.1, ρ z.1), f w)).symm
    _ = (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) -
        Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
          rw [sum_attach_circleIntegral_eq_sum]

/-- Helper for Theorem III.5-extra-2: the explicit excision boundary family already has pairwise
disjoint path ranges once the outer boundary misses each excision disc and the discs are pairwise
disjoint. -/
lemma pairwiseDisjoint_ranges_finite_excision_boundary_family
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    {s : Finset ℂ} {ρ : ℂ → ℝ} (hΓ : IsOrientedBoundaryOf K Γ)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w))) :
    Pairwise fun i j ↦
      Disjoint (Set.range ((finite_excision_boundary_family Γ s ρ i).toPath))
        (Set.range ((finite_excision_boundary_family Γ s ρ j).toPath)) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          -- The outer boundary components keep the original pairwise disjointness.
          have hij' : i ≠ j := by
            intro hEq
            apply hij
            exact congrArg Sum.inl hEq
          simpa [finite_excision_boundary_family] using hΓ.pairwiseDisjoint_ranges hij'
      | inr z =>
          -- An outer component misses the whole closed excision disc, hence also its boundary.
          have houter :
              Disjoint (Set.range (Γ i).toPath) (Metric.closedBall z.1.1 (ρ z.1.1)) :=
            boundary_path_disjoint_of_closedBall_subset_interior
              (Γ := Γ) hΓ (hball := hρK z.1.1 z.1.2) i
          refine houter.mono_right ?_
          intro w hw
          have hw' :
              w ∈ Set.range (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.toPath) := by
            simpa [finite_excision_boundary_family] using hw
          rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos z.1.1 z.1.2)] at hw'
          exact Metric.sphere_subset_closedBall hw'
  | inr z =>
      cases j with
      | inl j =>
          -- Symmetry reduces the inner-outer case to the previous outer-inner disjointness.
          have houter :
              Disjoint (Set.range (Γ j).toPath) (Metric.closedBall z.1.1 (ρ z.1.1)) :=
            boundary_path_disjoint_of_closedBall_subset_interior
              (Γ := Γ) hΓ (hball := hρK z.1.1 z.1.2) j
          have houter' :
              Disjoint (Set.range (Γ j).toPath)
                (Set.range (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.toPath)) :=
            houter.mono_right (by
              intro w hw
              rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos z.1.1 z.1.2)] at hw
              exact Metric.sphere_subset_closedBall hw)
          simpa [finite_excision_boundary_family] using houter'.symm
      | inr w =>
          -- Distinct excision circles lie in disjoint closed discs, so their path images are disjoint.
          have hzw : z.1.1 ≠ w.1.1 := by
            intro hEq
            apply hij
            exact congrArg Sum.inr (Subtype.ext (Subtype.ext hEq))
          have hclosed :
              Disjoint (Metric.closedBall z.1.1 (ρ z.1.1)) (Metric.closedBall w.1.1 (ρ w.1.1)) :=
            hpair z.1.1 z.1.2 w.1.1 w.1.2 hzw
          have hzsubset :
              Set.range (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.toPath) ⊆
                Metric.closedBall z.1.1 (ρ z.1.1) := by
            intro u hu
            rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos z.1.1 z.1.2)] at hu
            exact Metric.sphere_subset_closedBall hu
          have hwsubset :
              Set.range (((boundary_circle_path w.1.1 (ρ w.1.1)).symm).toClosedPath.toPath) ⊆
                Metric.closedBall w.1.1 (ρ w.1.1) := by
            intro u hu
            rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos w.1.1 w.1.2)] at hu
            exact Metric.sphere_subset_closedBall hu
          have hdisj :
              Disjoint
                (Set.range (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.toPath))
                (Set.range (((boundary_circle_path w.1.1 (ρ w.1.1)).symm).toClosedPath.toPath)) :=
            hclosed.mono hzsubset hwsubset
          simpa [finite_excision_boundary_family] using hdisj

/-- Helper for Theorem III.5-extra-2: removing an open set from a closed owner splits the
frontier into the surviving owner frontier and the removed-set frontier inside the owner. -/
lemma frontier_diff_open_of_isClosed {α : Type*} [TopologicalSpace α] {A W : Set α}
    (hA : IsClosed A) (hW : IsOpen W) :
    frontier (A \ W) = (frontier A \ W) ∪ (A ∩ frontier W) := by
  have hdiff : IsClosed (A \ W) := by
    -- A closed owner remains closed after deleting an open subset.
    simpa [Set.diff_eq] using hA.inter hW.isClosed_compl
  ext x
  constructor
  · intro hx
    -- Start from the closed-owner frontier formula and split according to `x ∈ interior A`.
    rw [hdiff.frontier_eq, Set.mem_diff] at hx
    rcases hx with ⟨hxAW, hxnotIntAW⟩
    have hxA : x ∈ A := hxAW.1
    have hxW : x ∉ W := hxAW.2
    by_cases hxIntA : x ∈ interior A
    · right
      refine ⟨hxA, ?_⟩
      rw [hW.frontier_eq, Set.mem_diff]
      refine ⟨?_, hxW⟩
      have hxnotIntWc : x ∉ interior Wᶜ := by
        intro hxIntWc
        apply hxnotIntAW
        rw [Set.diff_eq, interior_inter]
        exact ⟨hxIntA, hxIntWc⟩
      by_contra hxClosureW
      apply hxnotIntWc
      rw [interior_compl]
      exact hxClosureW
    · left
      rw [Set.mem_diff, hA.frontier_eq, Set.mem_diff]
      exact ⟨⟨hxA, hxIntA⟩, hxW⟩
  · intro hx
    rcases hx with hx | hx
    · -- A surviving owner-frontier point cannot become interior after deleting `W`.
      rw [Set.mem_diff, hA.frontier_eq, Set.mem_diff] at hx
      rcases hx with ⟨⟨hxA, hxnotIntA⟩, hxW⟩
      rw [hdiff.frontier_eq, Set.mem_diff]
      refine ⟨⟨hxA, hxW⟩, ?_⟩
      intro hxIntAW
      exact hxnotIntA ((interior_mono Set.diff_subset) hxIntAW)
    · -- A point on the removed-set frontier stays on the frontier of the smaller owner.
      rcases hx with ⟨hxA, hxFrontW⟩
      rw [hW.frontier_eq, Set.mem_diff] at hxFrontW
      rcases hxFrontW with ⟨hxClosureW, hxW⟩
      rw [hdiff.frontier_eq, Set.mem_diff]
      refine ⟨⟨hxA, hxW⟩, ?_⟩
      intro hxIntAW
      have hxnotIntWc : x ∉ interior Wᶜ := by
        rw [interior_compl]
        simpa [Set.mem_compl_iff] using hxClosureW
      apply hxnotIntWc
      exact (interior_mono (by
        intro y hy
        exact hy.2)) hxIntAW

/-- Helper for Theorem III.5-extra-2: removing one open ball from a closed owner splits the
frontier into the surviving outer frontier and the new boundary sphere. -/
lemma frontier_diff_ball_eq_of_closedBall_subset_interior
    {K : Set ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r) (hKclosed : IsClosed K)
    (hball : Metric.closedBall a r ⊆ interior K) :
    frontier (K \ Metric.ball a r) = frontier K ∪ Metric.sphere a r := by
  have hfrontier_disjoint : frontier K \ Metric.ball a r = frontier K := by
    ext z
    constructor
    · intro hz
      exact hz.1
    · intro hz
      refine ⟨hz, ?_⟩
      intro hzBall
      have hzInterior : z ∈ interior K := hball (Metric.ball_subset_closedBall hzBall)
      exact (Set.disjoint_left.1 disjoint_interior_frontier) hzInterior hz
  have hsphere_subset : Metric.sphere a r ⊆ K := by
    intro z hz
    exact interior_subset (hball (Metric.sphere_subset_closedBall hz))
  have hfrontier_ball :
      K ∩ frontier (Metric.ball a r) = Metric.sphere a r := by
    rw [frontier_ball a hr.ne']
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨hsphere_subset hz, hz⟩
  -- Route correction: isolate the one-hole frontier computation before the later finite induction.
  rw [frontier_diff_open_of_isClosed hKclosed Metric.isOpen_ball, hfrontier_disjoint, hfrontier_ball]

/-- Helper for Theorem III.5-extra-2: if a closed excision disc is disjoint from another closed
disc already contained in `interior K`, then that second disc stays inside the interior after the
first open ball is removed. -/
lemma closedBall_subset_interior_diff_ball_of_disjoint
    {K : Set ℂ} {a z : ℂ} {ra rz : ℝ}
    (hzK : Metric.closedBall z rz ⊆ interior K)
    (hdisj : Disjoint (Metric.closedBall a ra) (Metric.closedBall z rz)) :
    Metric.closedBall z rz ⊆ interior (K \ Metric.ball a ra) := by
  intro w hw
  have hwInteriorK : w ∈ interior K := hzK hw
  have hwNotClosed : w ∉ Metric.closedBall a ra := by
    intro hwClosed
    exact Set.disjoint_left.1 hdisj hwClosed hw
  have hwBallCompl : (Metric.ball a ra)ᶜ ∈ 𝓝 w := by
    have hwClosedCompl : (Metric.closedBall a ra)ᶜ ∈ 𝓝 w :=
      Metric.isClosed_closedBall.isOpen_compl.mem_nhds hwNotClosed
    refine Filter.mem_of_superset hwClosedCompl ?_
    intro u hu
    exact fun huBall ↦ hu (Metric.ball_subset_closedBall huBall)
  -- Intersect the old interior neighborhood with the complement of the removed ball.
  rw [mem_interior_iff_mem_nhds] at hwInteriorK ⊢
  simpa [Set.diff_eq] using Filter.inter_mem hwInteriorK hwBallCompl

/-- Helper for Theorem III.5-extra-2: the reversed boundary circle is globally `C¹`, hence
piecewise differentiable just like the positive circle. -/
lemma boundary_circle_path_symm_isPiecewiseDifferentiable (a : ℂ) (r : ℝ) :
    (boundary_circle_path a r).symm.IsPiecewiseDifferentiable := by
  have hdiff : (boundary_circle_path a r).symm.IsDifferentiable := by
    rw [Path.IsDifferentiable]
    let g : ℝ → ℂ := fun t ↦ circleMap a r (2 * Real.pi * (1 - t))
    have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ 2 * Real.pi * (1 - t)) := by
      fun_prop
    have hg : ContDiff ℝ 1 g := by
      simpa [g] using (contDiff_circleMap a r).comp hlin
    refine hg.contDiffOn.congr ?_
    intro t ht
    rw [Path.extend_apply ((boundary_circle_path a r).symm) ht]
    simp [boundary_circle_path, Path.symm, unitInterval.symm, g, sub_eq_add_neg, add_comm,
      mul_comm, mul_left_comm]
  exact hdiff.isPiecewiseDifferentiable

/-- Helper for Theorem III.5-extra-2: the clockwise boundary circle is simple up to identifying
its endpoints, exactly as for the counterclockwise circle. -/
lemma clockwise_boundary_circle_simple_eq_or_endpoints {a : ℂ} {r : ℝ} (hr : r ≠ 0)
    {s t : Set.Icc (0 : ℝ) 1}
    (h :
      (((boundary_circle_path a r).symm).toClosedPath.toPath) s =
        (((boundary_circle_path a r).symm).toClosedPath.toPath) t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I)) := by
  have hsymm :
      (boundary_circle_path a r).symm s = (boundary_circle_path a r).symm t := by
    -- Remove the closed-path wrapper: the remaining equality is exactly equality on the reversed
    -- path itself.
    simpa [loop_toClosedPath_toPath_eq_cast] using h
  have hforward : boundary_circle_path a r (σ s) = boundary_circle_path a r (σ t) := by
    -- Path reversal is evaluation after the involution `σ : I → I`.
    simpa [Path.symm] using hsymm
  rcases boundary_circle_path_simple_eq_or_endpoints (a := a) (r := r) hr hforward with
    hst | hst | hst
  · -- Apply `σ` once more to move injectivity back from the positive circle to the clockwise one.
    exact Or.inl (by simpa using congrArg σ hst)
  · right
    right
    have hs1 : s = (1 : I) := by
      apply unitInterval.symm_eq_zero.mp
      exact Subtype.ext hst.1
    have ht0 : t = (0 : I) := by
      apply unitInterval.symm_eq_one.mp
      exact Subtype.ext hst.2
    simpa [hs1, ht0]
  · right
    left
    have hs0 : s = (0 : I) := by
      apply unitInterval.symm_eq_one.mp
      exact Subtype.ext hst.1
    have ht1 : t = (1 : I) := by
      apply unitInterval.symm_eq_zero.mp
      exact Subtype.ext hst.2
    simpa [hs0, ht1]

/-- Helper for Theorem III.5-extra-2: finite disjoint excision splits the punctured owner's
frontier into the original outer frontier together with the boundary spheres of the removed discs. -/
lemma frontier_diff_iUnion_ball_eq_of_pairwise_disjoint_closedBall_subset_interior
    {K : Set ℂ} {s : Finset ℂ} {ρ : ℂ → ℝ} (hKclosed : IsClosed K)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w))) :
    frontier (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) =
      frontier K ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.sphere z (ρ z) := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
      -- With no excised balls, the punctured owner is just `K`.
      simp
  | @insert a s ha ih =>
      have hρpos' : ∀ z ∈ s, 0 < ρ z := by
        intro z hz
        exact hρpos z (by simp [hz])
      have hρK' : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior (K \ Metric.ball a (ρ a)) := by
        intro z hz
        -- Every remaining closed ball stays inside the new interior because the inserted closed
        -- ball is disjoint from it.
        refine closedBall_subset_interior_diff_ball_of_disjoint (hρK z (by simp [hz])) ?_
        have hza : z ≠ a := by
          intro hza
          apply ha
          simpa [hza] using hz
        exact hpair a (by simp) z (by simp [hz]) hza.symm
      have hpair' :
          ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
            Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)) := by
        intro z hz w hw hzw
        exact hpair z (by simp [hz]) w (by simp [hw]) hzw
      have hclosed' : IsClosed (K \ Metric.ball a (ρ a)) := by
        -- Removing one open ball from a closed owner preserves closedness.
        simpa [Set.diff_eq] using hKclosed.inter Metric.isOpen_ball.isClosed_compl
      have hUnionBalls :
          (⋃ z ∈ (↑(insert a s) : Set ℂ), Metric.ball z (ρ z)) =
            Metric.ball a (ρ a) ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z) := by
        ext x
        simp [Set.mem_iUnion, Finset.mem_insert, or_left_comm, or_assoc]
      have hUnionSpheres :
          (⋃ z ∈ (↑(insert a s) : Set ℂ), Metric.sphere z (ρ z)) =
            Metric.sphere a (ρ a) ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.sphere z (ρ z) := by
        ext x
        simp [Set.mem_iUnion, Finset.mem_insert, or_left_comm, or_assoc]
      have hDiffExcision :
          K \ (Metric.ball a (ρ a) ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) =
            (K \ Metric.ball a (ρ a)) \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z) := by
        ext x
        simp [Set.mem_diff, not_or, and_assoc, and_left_comm]
      -- Remove the new hole first, then apply the induction hypothesis inside the smaller owner.
      calc
        frontier (K \ ⋃ z ∈ (↑(insert a s) : Set ℂ), Metric.ball z (ρ z)) =
            frontier ((K \ Metric.ball a (ρ a)) \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) := by
              rw [hUnionBalls, hDiffExcision]
        _ =
            frontier (K \ Metric.ball a (ρ a)) ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.sphere z (ρ z) :=
              ih hclosed' hρpos' hρK' hpair'
        _ =
            (frontier K ∪ Metric.sphere a (ρ a)) ∪
              ⋃ z ∈ (↑s : Set ℂ), Metric.sphere z (ρ z) := by
                rw [frontier_diff_ball_eq_of_closedBall_subset_interior
                  (hρpos a (by simp)) hKclosed (hρK a (by simp))]
        _ =
            frontier K ∪ ⋃ z ∈ (↑(insert a s) : Set ℂ), Metric.sphere z (ρ z) := by
                rw [hUnionSpheres]
                ext x
                simp [or_left_comm, or_assoc, or_comm]

/-- Helper for Theorem III.5-extra-2: an outer boundary chart for `K` can be restricted away from
the finite excision discs, yielding a boundary chart for the punctured owner. -/
lemma outer_boundary_chart_restrict_away_from_excised_balls
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    {s : Finset ℂ} {ρ : ℂ → ℝ} (hΓ : IsOrientedBoundaryOf K Γ)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    {i : ι} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff : DifferentiableWithinAt ℝ (Γ i).realCurve (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv : derivWithin (Γ i).realCurve (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z))
        (Γ i).realCurve t₀ δ := by
  obtain ⟨δ, hδ⟩ := hΓ.exists_boundary_chart_at_regular_point i ht₀ hdiff hderiv
  let _ := hδ
  let _ := hρK
  -- TODO: starting from `hδ`, show the base curve point lies outside the finite closed union of
  -- excision balls, then restrict `δ.source` to a smaller neighborhood whose image avoids that
  -- closed union. The `p.2 > 0` side should land in `K \ holes`, while the `p.2 < 0` side still
  -- stays outside `K` and hence outside the punctured owner.
  sorry

/-- Helper for Theorem III.5-extra-2: every regular point of a clockwise excision circle admits a
local boundary straightening chart for the punctured owner. -/
lemma clockwise_boundary_circle_exists_boundary_chart_punctured_owner
    {K : Set ℂ} {s : Finset ℂ} {ρ : ℂ → ℝ} (z : s.attach)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)))
    {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ
        (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin
          (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve)
          (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        (K \ ⋃ w ∈ (↑s : Set ℂ), Metric.ball w (ρ w))
        (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve)
        t₀ δ := by
  let _ := hρpos
  let _ := hρK
  let _ := hpair
  let _ := hdiff
  let _ := hderiv
  -- TODO: build the explicit clockwise radial-tube chart around the excised circle. The chosen
  -- coordinates must send `p.2 > 0` into the punctured owner and `p.2 < 0` into the deleted disc,
  -- while shrinking the chart away from the other pairwise disjoint excision balls.
  sorry

/-- Helper for Theorem III.5-extra-2: the explicit excision boundary family has image equal to the
frontier of the punctured owner once the finite frontier decomposition is known. -/
lemma range_iUnion_finite_excision_boundary_family_eq_frontier
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    {s : Finset ℂ} {ρ : ℂ → ℝ} (hΓ : IsOrientedBoundaryOf K Γ)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w))) :
    (⋃ j, Set.range ((finite_excision_boundary_family Γ s ρ j).toPath)) =
      frontier (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) := by
  have hfrontier :=
    frontier_diff_iUnion_ball_eq_of_pairwise_disjoint_closedBall_subset_interior
      (K := K) (s := s) (ρ := ρ) hΓ.isCompact.isClosed hρpos hρK hpair
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
    cases j with
    | inl i =>
        have hxFrontier : x ∈ frontier K := by
          rw [← hΓ.iUnion_range_eq_frontier]
          exact Set.mem_iUnion.2 ⟨i, by simpa [finite_excision_boundary_family] using hj⟩
        rw [hfrontier]
        exact Or.inl hxFrontier
    | inr z =>
        have hjCircle :
            x ∈ Set.range
              ((((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath).toPath) := by
          simpa [finite_excision_boundary_family] using hj
        have hxSphere : x ∈ Metric.sphere z.1.1 (ρ z.1.1) := by
          rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos z.1.1 z.1.2)] at hjCircle
          exact hjCircle
        rw [hfrontier]
        exact Or.inr <| Set.mem_iUnion.2 ⟨z.1.1, Set.mem_iUnion.2 ⟨z.1.2, hxSphere⟩⟩
  · intro hx
    rw [hfrontier] at hx
    rcases hx with hxFrontier | hxSphere
    · rw [← hΓ.iUnion_range_eq_frontier] at hxFrontier
      rcases Set.mem_iUnion.1 hxFrontier with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨Sum.inl i, by simpa [finite_excision_boundary_family] using hi⟩
    · rcases Set.mem_iUnion.1 hxSphere with ⟨z, hzSphere⟩
      rcases Set.mem_iUnion.1 hzSphere with ⟨hz, hxSphere⟩
      let zz : s.attach := ⟨⟨z, hz⟩, by simp⟩
      have hxCircle :
          x ∈ Set.range
            ((((boundary_circle_path zz.1.1 (ρ zz.1.1)).symm).toClosedPath).toPath) := by
        rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos zz.1.1 zz.1.2)]
        exact hxSphere
      exact Set.mem_iUnion.2 ⟨Sum.inr zz, by simpa [finite_excision_boundary_family] using hxCircle⟩

/-- Helper for Theorem III.5-extra-2: source-faithful finite excision should identify the punctured
owner with the original outer boundary plus the clockwise inner circles. -/
lemma finite_excision_isOrientedBoundaryOf
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (s : Finset ℂ) (ρ : ℂ → ℝ)
    (hΓ : IsOrientedBoundaryOf K Γ)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w))) :
    IsOrientedBoundaryOf (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z))
      (finite_excision_boundary_family Γ s ρ) := by
  let _ := hΓ
  let _ := hρpos
  let _ := hρK
  let _ := hpair
  have hholesOpen : IsOpen (⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) := by
    refine isOpen_biUnion ?_
    intro (z : ℂ) hz
    simpa using isOpen_iUnion (fun _ : z ∈ (↑s : Set ℂ) ↦ Metric.isOpen_ball)
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The punctured owner is the compact owner intersected with the complement of the open holes.
    simpa [Set.diff_eq] using hΓ.isCompact.inter_right hholesOpen.isClosed_compl
  · intro j
    cases j with
    | inl i =>
        -- Outer boundary components are unchanged.
        simpa [finite_excision_boundary_family] using hΓ.piecewiseDifferentiable i
    | inr z =>
        -- Each inner component is the reversed explicit circle.
        simpa [finite_excision_boundary_family] using
          boundary_circle_path_symm_isPiecewiseDifferentiable z.1.1 (ρ z.1.1)
  · intro j s₀ t₀ hst
    cases j with
    | inl i =>
        -- Outer simple loops are inherited from the original oriented boundary.
        simpa [finite_excision_boundary_family] using hΓ.simple_loops i hst
    | inr z =>
        -- The clockwise circles reduce to the reversed-circle simplicity lemma.
        simpa [finite_excision_boundary_family] using
          clockwise_boundary_circle_simple_eq_or_endpoints
            (a := z.1.1) (r := ρ z.1.1) (hρpos z.1.1 z.1.2).ne' hst
  · -- Pairwise disjointness was proved once and for all from the disc geometry.
    exact pairwiseDisjoint_ranges_finite_excision_boundary_family
      (Γ := Γ) hΓ hρpos hρK hpair
  · -- Rewrite the image of the explicit boundary family to the frontier of the punctured owner.
    exact range_iUnion_finite_excision_boundary_family_eq_frontier
      (Γ := Γ) hΓ hρpos hρK hpair
  · intro j t₀ ht₀ hdiff hderiv
    -- Route correction: the global excision geometry is finished, so only the two local chart
    -- constructions remain: restriction for outer branches and an explicit radial tube for the
    -- clockwise inner circles.
    cases j with
    | inl i =>
        simpa [finite_excision_boundary_family] using
          outer_boundary_chart_restrict_away_from_excised_balls
            (Γ := Γ) (s := s) (ρ := ρ) hΓ hρK ht₀ hdiff hderiv
    | inr z =>
        simpa [finite_excision_boundary_family] using
          clockwise_boundary_circle_exists_boundary_chart_punctured_owner
            (K := K) (s := s) (ρ := ρ) z hρpos hρK hpair ht₀ hdiff hderiv

/-- Helper for Theorem III.5-extra-2: after excising finitely many pairwise disjoint interior
discs, the outer oriented-boundary integral equals the sum of the positively oriented inner circle
integrals. -/
-- TODO: re-prove the Chapter II punctured-boundary construction for a finite family of disjoint
-- interior discs, then apply `orientedBoundary_sum_curveIntegral_eq_zero` to the punctured region.
lemma orientedBoundary_sum_curveIntegral_eq_sum_small_circle_integrals
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ) {f : ℂ → ℂ}
    (s : Finset ℂ) (ρ : ℂ → ℝ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hρD : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ D)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)))
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ))) :
    ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
      Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
  classical
  have hboundary_disjoint :
      ∀ i, Disjoint (Set.range (Γ i).toPath) (↑s : Set ℂ) :=
    boundary_path_disjoint_of_centers_closedBall_subset_interior
      (Γ := Γ) hΓ hρpos hρK
  have hpunctured_subset :
      K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z) ⊆ D \ (↑s : Set ℂ) :=
    punctured_owner_subset_punctured_domain_of_excised_balls hKD hρpos
  have hω_closed :
      IsClosedOn (Complex.realScalarOneForm f) (D \ (↑s : Set ℂ)) :=
    realScalarOneForm_isClosedOn_punctured_domain hD hhol
  let _ := hD
  let _ := hρD
  let _ := hpair
  let _ := hhol
  let _ := hboundary_disjoint
  let _ := hpunctured_subset
  let _ := hω_closed
  let Δ := finite_excision_boundary_family Γ s ρ
  have hΔ :
      IsOrientedBoundaryOf (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) Δ := by
    -- This is now the only structural gap: the punctured owner needs the source-faithful
    -- oriented-boundary witness with outer components `Γ` and clockwise inner circles.
    simpa [Δ] using finite_excision_isOrientedBoundaryOf
      (Γ := Γ) (s := s) (ρ := ρ) hΓ hρpos hρK hpair
  have hzero :
      ∑ j, ∫ᶜ z in (Δ j).toPath, (f dz) z = 0 := by
    -- Once the punctured boundary family exists, the closed-form zero theorem applies directly.
    have hzero' :
        ∑ j, ∫ᶜ z in (Δ j).toPath, Complex.realScalarOneForm f z = 0 :=
      orientedBoundary_integral_eq_zero_of_isClosedOn
        (Γ := Δ) hΔ hpunctured_subset hω_closed
    calc
      ∑ j, ∫ᶜ z in (Δ j).toPath, (f dz) z =
          ∑ j, ∫ᶜ z in (Δ j).toPath, Complex.realScalarOneForm f z := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa [Complex.realScalarOneForm] using
              (curveIntegral_restrictScalars
                (γ := (Δ j).toPath) (ω := fun z ↦ (f dz) z) (𝕜 := ℂ) (𝕝 := ℝ)).symm
      _ = 0 := hzero'
  have hsplit :
      ∑ j, ∫ᶜ z in (Δ j).toPath, (f dz) z =
        (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) -
          Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
    -- The explicit boundary family has the outer pieces with positive sign and the inner circles
    -- with reversed orientation.
    simpa [Δ] using sum_curveIntegral_finite_excision_boundary_family
      (Γ := Γ) (f := f) (s := s) (ρ := ρ)
  -- After rewriting the punctured boundary sum, the zero theorem gives the desired comparison.
  rw [hsplit] at hzero
  exact sub_eq_zero.mp hzero

/-- Theorem III.5-extra-2 (2): source-form residue theorem for an oriented boundary, stated with
explicit isolated local residue data at the finitely many interior singularities enclosed by the
boundary. -/
theorem orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ) {f : ℂ → ℂ}
    (s : Finset ℂ) (residue : ℂ → ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ)))
    (hres : ∀ z ∈ s, IsolatedLocalResidueCircle K D s f z (residue z)) :
    ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
      (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
  classical
  let _ := hKD
  choose ρ₀ hρ₀pos hρ₀K hρ₀D hρ₀avoid hρ₀diff hρ₀sep hρ₀circle using
    fun z : s ↦
      exists_half_radius_isolated_local_residue_circle hD hhol z.2 (hres z.1 z.2)
  let ρ : ℂ → ℝ := fun z ↦ if hz : z ∈ s then ρ₀ ⟨z, hz⟩ else 0
  have hρpos : ∀ z ∈ s, 0 < ρ z := by
    intro z hz
    simp [ρ, hz, hρ₀pos]
  have hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K := by
    intro z hz
    simpa [ρ, hz] using hρ₀K ⟨z, hz⟩
  have hρD : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ D := by
    intro z hz
    simpa [ρ, hz] using hρ₀D ⟨z, hz⟩
  have hρsep :
      ∀ z ∈ s, ∀ w ∈ s, w ≠ z → ρ z + ρ w < dist z w := by
    intro z hz w hw hwz
    have hzlt : 2 * ρ z < dist z w := by
      simpa [ρ, hz] using hρ₀sep ⟨z, hz⟩ w hw hwz
    have hwlt : 2 * ρ w < dist z w := by
      have hwlt' : 2 * ρ₀ ⟨w, hw⟩ < dist w z :=
        hρ₀sep ⟨w, hw⟩ z hz hwz.symm
      simpa [ρ, hw, dist_comm] using hwlt'
    linarith
  have hpair :
      ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
        Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)) :=
    pairwise_disjoint_closedBall_of_radius_separation
      (fun z hz ↦ (hρpos z hz).le) hρsep
  have hboundary :
      ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
        Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) :=
    orientedBoundary_sum_curveIntegral_eq_sum_small_circle_integrals
      Γ s ρ hΓ hKD hD hρpos hρK hρD hpair hhol
  -- Route correction: the local residue circles are now normalized first; only the finite-excision
  -- geometry remains hidden behind the structural comparison lemma above.
  calc
    ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z = Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := hboundary
    _ = Finset.sum s (fun z ↦ (2 * Real.pi * Complex.I : ℂ) * residue z) := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      simpa [ρ, hz] using hρ₀circle ⟨z, hz⟩
    _ = (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
      simpa using (Finset.mul_sum s residue (2 * Real.pi * Complex.I : ℂ)).symm
