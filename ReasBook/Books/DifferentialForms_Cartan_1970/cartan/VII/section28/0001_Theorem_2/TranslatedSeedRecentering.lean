import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».LocalHolomorphicSystems
import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».TranslatedSliceNeighborhoods
import Mathlib

open Filter
open Set

open scoped Topology unitInterval

/-- Helper for Cartan section28 0001_Theorem_2: a seed analytic germ at `(a, 0)` already contains
the analytic initial-value curve `u ↦ φ (a, t₀[r ↦ t₀ r + u])`. -/
theorem analyticAt_seedValueParameterSlice
    {k j : ℕ} {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j) {a : ℂ}
    (hseed :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
        (a, 0)) :
    AnalyticAt ℂ (fun u : ℂ ↦ φ (a, Function.update t0 r (t0 r + u))) 0 := by
  -- Restrict the two-variable germ to the constant-`x` section through the seed point.
  have hsection : AnalyticAt ℂ (fun u : ℂ ↦ (a, u)) 0 := by
    simpa using
      (analyticAt_const.prod (analyticAt_id : AnalyticAt ℂ (fun u : ℂ ↦ u) 0))
  simpa using hseed.comp_of_eq hsection rfl

/-- Helper for Cartan section28 0001_Theorem_2: a seed analytic germ in the active scalar
parameter extends to a smaller open neighborhood still contained in the ambient parameter
neighborhood. -/
theorem seedValueAnalyticOnNeighborhood
    {k j : ℕ} {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {Vr' : Set ℂ} {t0 : Fin j → ℂ} (r : Fin j)
    (hVr' : IsOpen Vr') (h0Vr' : (0 : ℂ) ∈ Vr')
    {a : ℂ}
    (hseed :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
        (a, 0)) :
    ∃ Vr0 : Set ℂ,
      IsOpen Vr0 ∧
      (0 : ℂ) ∈ Vr0 ∧
      Vr0 ⊆ Vr' ∧
      AnalyticOnNhd ℂ (fun u : ℂ ↦ φ (a, Function.update t0 r (t0 r + u))) Vr0 := by
  -- First read off the scalar seed-value germ from the two-variable translated germ.
  have hSeedValue :
      AnalyticAt ℂ (fun u : ℂ ↦ φ (a, Function.update t0 r (t0 r + u))) 0 :=
    analyticAt_seedValueParameterSlice (φ := φ) (t0 := t0) r hseed
  rcases hSeedValue.exists_mem_nhds_analyticOnNhd with ⟨Vs, hVs0, hφVs⟩
  have hinter : Vs ∩ Vr' ∈ 𝓝 (0 : ℂ) := Filter.inter_mem hVs0 (hVr'.mem_nhds h0Vr')
  rcases _root_.mem_nhds_iff.mp hinter with ⟨Vr0, hVr0sub, hVr0, h0Vr0⟩
  refine ⟨Vr0, hVr0, h0Vr0, ?_, ?_⟩
  · intro u hu
    exact (hVr0sub hu).2
  · intro u hu
    -- The smaller open set still lies inside the analytic neighborhood produced by the seed germ.
    exact hφVs u (hVr0sub hu).1

/-- Helper for Cartan section28 0001_Theorem_2: after translating the independent variable by a
seed point and subtracting the analytic seed value, the pulled-back right-hand side remains
analytic on the explicit recentered coefficient domain. -/
theorem seedRecenteredRhsAnalyticOnDomain
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    {t0 : Fin j → ℂ} (r : Fin j) {a : ℂ}
    {ba : ℂ → Fin k → ℂ} {Vr0 : Set ℂ}
    (hbaVr0 : AnalyticOnNhd ℂ ba Vr0) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
        F (a + p.1) (ba p.2.2 + p.2.1) (Function.update t0 r (t0 r + p.2.2)))
      {p : ℂ × (Fin k → ℂ) × ℂ |
        p.2.2 ∈ Vr0 ∧
          (a + p.1, ba p.2.2 + p.2.1, Function.update t0 r (t0 r + p.2.2)) ∈ Ω} := by
  intro p hp
  have hbase :
      AnalyticAt ℂ
        (fun q : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F q.1 q.2.1 q.2.2)
        (a + p.1, ba p.2.2 + p.2.1, Function.update t0 r (t0 r + p.2.2)) :=
    hF _ hp.2
  have hupdate :
      AnalyticAt ℂ (fun u : ℂ ↦ Function.update t0 r (t0 r + u)) p.2.2 := by
    -- Each frozen parameter coordinate is constant, and the active coordinate is affine in `u`.
    refine AnalyticAt.pi fun i ↦ ?_
    by_cases hir : i = r
    · subst hir
      simpa [Function.update] using
        (analyticAt_const.add (analyticAt_id : AnalyticAt ℂ (fun u : ℂ ↦ u) p.2.2))
    · have hconst :
          (fun u : ℂ ↦ Function.update t0 r (t0 r + u) i) = fun _ ↦ t0 i := by
        funext u
        simp [Function.update, hir]
      rw [hconst]
      exact analyticAt_const
  have hy :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) × ℂ ↦ q.2.1) p := by
    simpa using
      (analyticAt_fst.comp
        (analyticAt_snd : AnalyticAt ℂ (fun q : ℂ × ((Fin k → ℂ) × ℂ) ↦ q.2) p))
  have hu :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) × ℂ ↦ q.2.2) p := by
    simpa using
      (analyticAt_snd.comp
        (analyticAt_snd : AnalyticAt ℂ (fun q : ℂ × ((Fin k → ℂ) × ℂ) ↦ q.2) p))
  have hba :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) × ℂ ↦ ba q.2.2) p := by
    simpa using (hbaVr0 _ hp.1).comp_of_eq hu rfl
  have hparam :
      AnalyticAt ℂ
        (fun q : ℂ × (Fin k → ℂ) × ℂ ↦ Function.update t0 r (t0 r + q.2.2))
        p := by
    simpa using hupdate.comp_of_eq hu rfl
  have hpair :
      AnalyticAt ℂ
        (fun q : ℂ × (Fin k → ℂ) × ℂ ↦
          (ba q.2.2 + q.2.1, Function.update t0 r (t0 r + q.2.2)))
        p := by
    simpa using (hba.add hy).prod hparam
  have hmap :
      AnalyticAt ℂ
        (fun q : ℂ × (Fin k → ℂ) × ℂ ↦
          (a + q.1, ba q.2.2 + q.2.1, Function.update t0 r (t0 r + q.2.2)))
        p := by
    -- The recentered triple map is analytic because each component is analytic.
    simpa using (analyticAt_const.add analyticAt_fst).prod hpair
  simpa using hbase.comp_of_eq hmap rfl

/-- Helper for Cartan section28 0001_Theorem_2: translating the `x`-domain by a seed point `a`
produces the recentered domain needed for the seed-continuation argument. -/
theorem translatedXDomainAroundSeed
    {Bx : Set ℂ} (hBx : IsOpen Bx) (hBxPreconnected : IsPreconnected Bx)
    {a x0 : ℂ} (ha : a ∈ Bx) (hx0 : x0 ∈ Bx) :
    IsOpen {ξ : ℂ | a + ξ ∈ Bx} ∧
      IsPreconnected {ξ : ℂ | a + ξ ∈ Bx} ∧
      (0 : ℂ) ∈ {ξ : ℂ | a + ξ ∈ Bx} ∧
      (x0 - a : ℂ) ∈ {ξ : ℂ | a + ξ ∈ Bx} := by
  constructor
  · -- The recentered domain is the preimage of `Bx` under the affine shift `ξ ↦ a + ξ`.
    simpa using hBx.preimage (continuous_const.add continuous_id)
  constructor
  · -- Translation by `a` is a homeomorphism, so it preserves preconnectedness.
    simpa using ((Homeomorph.addLeft a).isPreconnected_preimage).2 hBxPreconnected
  constructor
  · -- The recentered origin corresponds to the seed point `a`.
    simpa using ha
  · -- The target point becomes the translated point `x₀ - a`.
    simpa using hx0

/-- Helper for Cartan section28 0001_Theorem_2: recentering the translated `x`-domain at a
reachable seed time `u` packages the shifted domain data needed to continue along the same path. -/
theorem translatedSubpathDomainBetweenReachableTimes
    {Ba : Set ℂ} (hBaOpen : IsOpen Ba) (hBaPreconnected : IsPreconnected Ba)
    {x1 : ℂ} (γ : Path 0 x1)
    (hγBa : ∀ s : I, γ s ∈ Ba)
    {u v : I} :
    IsOpen {ξ : ℂ | γ u + ξ ∈ Ba} ∧
      IsPreconnected {ξ : ℂ | γ u + ξ ∈ Ba} ∧
      (0 : ℂ) ∈ {ξ : ℂ | γ u + ξ ∈ Ba} ∧
      (γ v - γ u : ℂ) ∈ {ξ : ℂ | γ u + ξ ∈ Ba} := by
  -- This is the generic affine-domain package `translatedXDomainAroundSeed` with seed `γ u`
  -- and target `γ v` on the already chosen path.
  simpa using
    translatedXDomainAroundSeed hBaOpen hBaPreconnected (hγBa u) (hγBa v)

/-- Helper for Cartan section28 0001_Theorem_2: after translating the independent variable by a
seed point `a` and subtracting the seed value, each frozen parameter slice still solves the
corresponding recentered system on the shifted `x`-domain. -/
theorem seedRecenteredSliceSolutionOnTranslatedDomain
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)} {Vr' : Set ℂ}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    (hVr'map : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr' Vx)
    {a : ℂ} (ha : a ∈ Bx)
    {u : ℂ} (hu : u ∈ Vr') :
    IsHolomorphicSystemSolutionOn
      {p : ℂ × (Fin k → ℂ) |
        (a + p.1,
          φ (a, Function.update t0 r (t0 r + u)) + p.2,
          Function.update t0 r (t0 r + u)) ∈ Ω}
      (fun ξ y ↦
        F (a + ξ) (φ (a, Function.update t0 r (t0 r + u)) + y)
          (Function.update t0 r (t0 r + u)))
      0
      0
      {ξ : ℂ | a + ξ ∈ Bx}
      (fun ξ ↦
        φ (a + ξ, Function.update t0 r (t0 r + u)) -
          φ (a, Function.update t0 r (t0 r + u))) := by
  let τ : ℂ → Fin j → ℂ := fun v ↦ Function.update t0 r (t0 r + v)
  have hbase : IsHolomorphicSystemSolutionOn
      {p : ℂ × (Fin k → ℂ) | (p.1, p.2, τ u) ∈ Ω}
      (fun x y ↦ F x y (τ u))
      0
      0
      Bx
      (fun x ↦ φ (x, τ u)) :=
    hsolBx (τ u) (hVr'map hu)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The translated domain is the affine preimage of the original `x`-domain.
    simpa using hbase.isOpen.preimage (continuous_const.add continuous_id)
  · -- The translated origin corresponds to the seed point `a`.
    simpa using ha
  · intro ξ hξ
    -- Shift the analytic slice by `a` and then subtract the constant seed value.
    have hAt : AnalyticAt ℂ (fun z : ℂ ↦ φ (z, τ u)) (a + ξ) :=
      hbase.analytic _ hξ
    have hshift : AnalyticAt ℂ (fun z : ℂ ↦ a + z) ξ :=
      analyticAt_const.add analyticAt_id
    exact (hAt.comp_of_eq hshift rfl).sub analyticAt_const
  · intro ξ hξ
    -- The translated graph condition is inherited from the original slice after recentering `y`.
    simpa [τ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hbase.mapsTo hξ
  · -- The recentered slice vanishes at the translated origin.
    simp [τ]
  · intro ξ hξ
    -- The differential equation transports across `x ↦ a + ξ`, and subtracting a constant does
    -- not change the derivative.
    have hderiv :
        HasDerivAt
          (fun ζ : ℂ ↦ φ (a + ζ, τ u))
          (F (a + ξ) (φ (a + ξ, τ u)) (τ u))
          ξ :=
      (hbase.deriv_eq hξ).comp_const_add a ξ
    simpa [τ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hderiv.sub_const (φ (a, τ u))

/-- Helper for Cartan section28 0001_Theorem_2: recentering the translated parameter germ at a
seed point `a` and subtracting the analytic seed-value curve yields a jointly analytic germ at the
translated origin. -/
theorem seedRecenteredOriginAnalyticAt
    {k j : ℕ} {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j) {a : ℂ}
    (hseed :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
        (a, 0))
    (hseedValue :
      AnalyticAt ℂ
        (fun u : ℂ ↦ φ (a, Function.update t0 r (t0 r + u)))
        0) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ ↦
        φ (a + p.1, Function.update t0 r (t0 r + p.2)) -
          φ (a, Function.update t0 r (t0 r + p.2)))
      ((0 : ℂ), 0) := by
  -- First translate the original seed germ from `(a, 0)` back to the origin in `(x, u)`-space.
  have hshift :
      AnalyticAt ℂ (fun p : ℂ × ℂ ↦ (a + p.1, p.2)) ((0 : ℂ), 0) := by
    simpa using
      (analyticAt_const.add
          (analyticAt_fst : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.1) ((0 : ℂ), 0))).prod
        (analyticAt_snd : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.2) ((0 : ℂ), 0))
  have htranslatedSeed :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (a + p.1, Function.update t0 r (t0 r + p.2)))
        ((0 : ℂ), 0) := by
    simpa using hseed.comp_of_eq hshift (by simp)
  -- Then subtract the analytic seed-value curve, viewed as a function of the translated
  -- parameter variable alone.
  have hseedCurve :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (a, Function.update t0 r (t0 r + p.2)))
        ((0 : ℂ), 0) := by
    have hu :
        AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.2) ((0 : ℂ), 0) :=
      analyticAt_snd
    simpa using hseedValue.comp_of_eq hu rfl
  simpa using htranslatedSeed.sub hseedCurve

/-- Helper for Cartan section28 0001_Theorem_2: recentering a jointly analytic germ at a reachable
seed point `ξ` and subtracting the seed-value curve preserves analyticity at the translated
origin. -/
theorem recenteredSeedDifferenceAnalyticAt
    {k : ℕ} {ψa : ℂ × ℂ → Fin k → ℂ} {ξ : ℂ}
    (hξ :
      AnalyticAt ℂ ψa (ξ, 0)) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ ↦ ψa (ξ + p.1, p.2) - ψa (ξ, p.2))
      ((0 : ℂ), 0) := by
  have htranslatedSeed :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ ψa (ξ + p.1, p.2))
        ((0 : ℂ), 0) := by
    have hshift :
        AnalyticAt ℂ (fun p : ℂ × ℂ ↦ (ξ + p.1, p.2)) ((0 : ℂ), 0) := by
      -- Shift the reachable seed point back to the translated origin.
      simpa using
        (analyticAt_const.add
            (analyticAt_fst : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.1) ((0 : ℂ), 0))).prod
          (analyticAt_snd : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.2) ((0 : ℂ), 0))
    -- Re-express the seed germ in coordinates centered at `ξ`.
    simpa using hξ.comp_of_eq hshift (by simp)
  have hseedCurve :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ ψa (ξ, p.2))
        ((0 : ℂ), 0) := by
    have hu :
        AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.2) ((0 : ℂ), 0) :=
      analyticAt_snd
    have hsection :
        AnalyticAt ℂ (fun w : ℂ ↦ (ξ, w)) 0 := by
      -- Freeze the `x`-coordinate at the reachable seed and keep the parameter coordinate.
      simpa using
        (analyticAt_const.prod
          (analyticAt_id : AnalyticAt ℂ (fun w : ℂ ↦ w) 0))
    have hseedValue :
        AnalyticAt ℂ (fun w : ℂ ↦ ψa (ξ, w)) 0 := by
      -- Restrict the joint seed germ to the constant-`x` section through `ξ`.
      simpa using hξ.comp_of_eq hsection rfl
    -- Restrict the joint germ to the constant-`x` seed section.
    simpa using hseedValue.comp_of_eq hu rfl
  -- Subtracting the analytic seed curve produces the twice-recentered origin germ.
  simpa using htranslatedSeed.sub hseedCurve

/-- Helper for Cartan section28 0001_Theorem_2: an analytic recentered seed `(ξ, 0)` yields a
product neighborhood in translated coordinates still contained in the ambient translated
`x`-domain. -/
theorem recenteredCoordinateSliceLocalPatchAtSeed
    {k : ℕ} {ψa : ℂ × ℂ → Fin k → ℂ} {Ba : Set ℂ} {ξ : ℂ}
    (hBaOpen : IsOpen Ba) (hξBa : ξ ∈ Ba)
    (hξ :
      AnalyticAt ℂ ψa (ξ, 0)) :
    ∃ Bξ Vξ : Set ℂ,
      IsOpen Bξ ∧
      IsOpen Vξ ∧
      (0 : ℂ) ∈ Bξ ∧
      (0 : ℂ) ∈ Vξ ∧
      Bξ ⊆ {x : ℂ | ξ + x ∈ Ba} ∧
      AnalyticOnNhd ℂ
        (fun p : ℂ × ℂ ↦ ψa (ξ + p.1, p.2))
        (Bξ ×ˢ Vξ) := by
  let Bξdomain : Set ℂ := {x : ℂ | ξ + x ∈ Ba}
  have hBξdomainOpen : IsOpen Bξdomain := by
    -- The local translated `x`-domain is the affine preimage of `Ba`.
    simpa [Bξdomain] using hBaOpen.preimage (continuous_const.add continuous_id)
  have h0Bξdomain : (0 : ℂ) ∈ Bξdomain := by
    -- The translated origin corresponds exactly to the seed point `ξ`.
    simpa [Bξdomain] using hξBa
  have hshift :
      AnalyticAt ℂ (fun p : ℂ × ℂ ↦ (ξ + p.1, p.2)) ((0 : ℂ), 0) := by
    -- Translate the seed back to the origin in `(x, u)`-space.
    simpa using
      (analyticAt_const.add
          (analyticAt_fst : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.1) ((0 : ℂ), 0))).prod
        (analyticAt_snd : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.2) ((0 : ℂ), 0))
  have hTranslatedSeed :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ ψa (ξ + p.1, p.2))
        ((0 : ℂ), 0) := by
    -- Re-express the analytic seed germ in the translated coordinates.
    simpa using hξ.comp_of_eq hshift (by simp)
  -- The origin patch lemma now supplies the required product neighborhood at `ξ`.
  exact
    localProductPatchWithinOpenXDomain
      (ψ := fun p : ℂ × ℂ ↦ ψa (ξ + p.1, p.2))
      hBξdomainOpen h0Bξdomain hTranslatedSeed

/-- Helper for Cartan section28 0001_Theorem_2: analyticity at one path time propagates to a whole
open neighborhood of nearby times by pulling back the translated seed patch along the path. -/
theorem recenteredCoordinateSliceReachableNeighborhoodOnPath
    {k : ℕ} {ψa : ℂ × ℂ → Fin k → ℂ} {Ba : Set ℂ} {x1 : ℂ}
    (hBaOpen : IsOpen Ba)
    (γ : Path 0 x1)
    (hγBa : ∀ s : I, γ s ∈ Ba)
    {t : I}
    (ht :
      AnalyticAt ℂ ψa (γ t, 0)) :
    ∃ Jt : Set I,
      IsOpen Jt ∧
      t ∈ Jt ∧
      ∀ s ∈ Jt, AnalyticAt ℂ ψa (γ s, 0) := by
  rcases
      recenteredCoordinateSliceLocalPatchAtSeed
        (ψa := ψa) (Ba := Ba) hBaOpen (hγBa t) ht with
    ⟨Bξ, Vξ, hBξ, _hVξ, h0Bξ, h0Vξ, _hBξsub, hPatch⟩
  let Jt : Set I := {s : I | γ s - γ t ∈ Bξ}
  have hJt : IsOpen Jt := by
    -- Pull the translated `x`-patch back to the parameter interval along the path.
    have hcont : Continuous fun s : I ↦ γ s - γ t :=
      γ.continuous.sub continuous_const
    simpa [Jt] using hBξ.preimage hcont
  have htJt : t ∈ Jt := by
    -- At the seed time, the translated `x`-coordinate is `0`.
    simpa [Jt] using h0Bξ
  refine ⟨Jt, hJt, htJt, ?_⟩
  intro s hs
  have hsBξ : γ s - γ t ∈ Bξ := hs
  have hShiftedAt :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ ψa (γ t + p.1, p.2))
        (γ s - γ t, 0) :=
    hPatch _ ⟨hsBξ, h0Vξ⟩
  have htranslateBack :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ (p.1 - γ t, p.2))
        (γ s, 0) := by
    -- Undo the `x`-translation that centered the seed patch at the origin.
    simpa [sub_eq_add_neg] using
      ((analyticAt_fst : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.1) (γ s, 0)).sub
        analyticAt_const).prod
        (analyticAt_snd : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.2) (γ s, 0))
  -- Composing with the inverse translation recovers the original recentered slice.
  convert hShiftedAt.comp_of_eq htranslateBack (by simp) using 1
  funext p
  simp [sub_eq_add_neg, add_left_comm, add_comm]
