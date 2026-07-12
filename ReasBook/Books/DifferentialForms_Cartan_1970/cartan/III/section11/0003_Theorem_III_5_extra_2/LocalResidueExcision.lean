import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»

open scoped BigOperators Topology unitInterval

noncomputable section

universe u

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

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: if `f` is continuous on the closed
annulus `ρ ≤ dist z w ≤ R` and holomorphic on its interior, then the two circle integrals agree.
-/
lemma circleIntegral_eq_of_punctured_ball_shrink
    {f : ℂ → ℂ} {z : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hcont : ContinuousOn f (Metric.closedBall z R \ Metric.ball z ρ))
    (hdiff : DifferentiableOn ℂ f (Metric.ball z R \ Metric.closedBall z ρ)) :
    (∮ w in C(z, R), f w) = ∮ w in C(z, ρ), f w := by
  have hAnnulusOpen : IsOpen (Metric.ball z R \ Metric.closedBall z ρ) :=
    Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  simpa using Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hρ hρR Set.countable_empty hcont
      (fun w hw ↦ (hdiff w hw.1).differentiableAt (hAnnulusOpen.mem_nhds hw.1))

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: shrinking an isolated local residue
circle to half its radius preserves the residue formula and leaves the other singularities outside
twice the new radius. -/
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
  let _ := hDsOpen
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
  calc
    (∮ w in C(z, ρ), f w) = ∮ w in C(z, R), f w := hcircleρ.symm
    _ = (2 * Real.pi * Complex.I : ℂ) * residue z := hcircleR

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: strict separation of radii implies
pairwise disjoint closed excision discs. -/
lemma pairwise_disjoint_closedBall_of_radius_separation
    {s : Finset ℂ} {ρ : ℂ → ℝ}
    (hρnonneg : ∀ z ∈ s, 0 ≤ ρ z)
    (hsep : ∀ z ∈ s, ∀ w ∈ s, w ≠ z → ρ z + ρ w < dist z w) :
    ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)) := by
  intro z hz w hw hzw
  rw [disjoint_closedBall_closedBall_iff (hρnonneg z hz) (hρnonneg w hw)]
  exact hsep z hz w hw hzw.symm

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: a boundary path of an oriented
boundary misses every closed ball that is already contained in `interior K`. -/
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
  exact (Set.disjoint_left.1 disjoint_interior_frontier) hwInterior hwFrontier

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: if each excision closed ball lies in
`interior K`, then the boundary paths are disjoint from the finite set of excision centers. -/
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
  exact (Set.disjoint_left.1 disjoint_interior_frontier) hwInterior hwFrontier

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: once `K ⊆ D`, removing the open balls
around the finite set still leaves a subset of the punctured domain `D \ s`. -/
lemma punctured_owner_subset_punctured_domain_of_excised_balls
    {K D : Set ℂ} {s : Finset ℂ} {ρ : ℂ → ℝ}
    (hKD : K ⊆ D) (hρpos : ∀ z ∈ s, 0 < ρ z) :
    K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z) ⊆ D \ (↑s : Set ℂ) := by
  intro w hw
  refine ⟨hKD hw.1, ?_⟩
  intro hwS
  have hwBall : w ∈ Metric.ball w (ρ w) := Metric.mem_ball_self (hρpos w hwS)
  exact hw.2 (by exact Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨hwS, hwBall⟩⟩)

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: holomorphy on the punctured domain
gives a closed real-linear form there, so the later excision argument can finish by the
oriented-boundary zero theorem without any further analytic reduction. -/
lemma realScalarOneForm_isClosedOn_punctured_domain
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ} {s : Finset ℂ}
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ))) :
    IsClosedOn (Complex.realScalarOneForm f) (D \ (↑s : Set ℂ)) := by
  let puncturedD : Set ℂ := D \ (↑s : Set ℂ)
  have hpunctured_open : IsOpen puncturedD := hD.sdiff s.finite_toSet.isClosed
  intro z hz
  rcases holomorphic_has_local_primitive hpunctured_open hhol hz with ⟨r, hr, hball, hExact⟩
  refine ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball, ?_⟩
  simpa [puncturedD, Complex.realScalarOneForm] using hExact.hasPrimitiveOn
