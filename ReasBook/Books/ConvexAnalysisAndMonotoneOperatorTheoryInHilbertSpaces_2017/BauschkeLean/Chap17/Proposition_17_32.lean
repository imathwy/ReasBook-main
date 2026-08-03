import Mathlib
import BauschkeLean.Chap16.Corollary_16_72
import BauschkeLean.Chap17.Proposition_17_2
import BauschkeLean.Chap17.Proposition_17_16

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Pointwise

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section

omit [CompleteSpace H]

/-- Helper for Proposition 17 32: coercing a convex real-valued function through `toEReal`
preserves convexity on its effective domain. -/
lemma convexOn_toEReal_of_convexOn_univ
    (φ : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    ConvexOn φ.toEReal (effectiveDomain φ.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · -- A real-valued function is finite everywhere after the canonical coercion.
    simp [Function.effectiveDomain_toEReal]
  · -- Hence the effective-domain inclusion is automatic.
    simp [Function.effectiveDomain_toEReal]
  · intro x hx y hy a ha0 ha1
    -- Rewrite the convexity inequality back to the original real-valued statement.
    have hreal :
        φ (a • x + (1 - a) • y) ≤ a * φ x + (1 - a) * φ y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by linarith)
    change ((φ (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a * φ x + (1 - a) * φ y : ℝ) : EReal)
    exact_mod_cast hreal

/-- Helper for Proposition 17 32: a continuous convex real-valued function packages canonically
as a member of `Γ₀`. -/
lemma real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (φ : H → ℝ) (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- Lower semicontinuity follows from continuity after coercing to `EReal`.
    simpa using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · -- Convexity is the `toEReal` transport established above.
    exact convexOn_toEReal_of_convexOn_univ φ hconv

end

/-- Helper for Proposition 17 32: continuity makes `range f` an interval in `ℝ`, so adding a
positive scalar to one relative-interior point yields the regularity witness required by
Corollary 16.72. -/
lemma self_mem_relativeInterior_singleton_real (r : ℝ) :
    r ∈ Set.relativeInterior ({r} : Set ℝ) := by
  rw [Set.mem_relativeInterior_iff]
  have hr_mem : r ∈ ({r} : Set ℝ) := by
    simp
  refine ⟨hr_mem, ?_⟩
  have hsub : ({r} : Set ℝ) - ({r} : Set ℝ) = ({0} : Set ℝ) := by
    ext y
    constructor
    · intro hy
      rcases Set.mem_sub.mp hy with ⟨a, ha, b, hb, hab⟩
      rcases Set.mem_singleton_iff.mp ha with rfl
      rcases Set.mem_singleton_iff.mp hb with rfl
      simpa using hab.symm
    · intro hy
      have hzero : y = 0 := Set.mem_singleton_iff.mp hy
      subst hzero
      exact Set.mem_sub.mpr ⟨r, hr_mem, r, hr_mem, sub_self r⟩
  have hcone_zero : Set.cone ({0} : Set ℝ) = ({0} : Set ℝ) := by
    ext y
    constructor
    · intro hy
      have hy' : y ∈ (((⊥ : Submodule ℝ ℝ).toConvexCone : ConvexCone ℝ ℝ) : Set ℝ) :=
        ConvexCone.hull_min (C := (⊥ : Submodule ℝ ℝ).toConvexCone)
          (fun z hz ↦ by simpa using hz) hy
      simpa using hy'
    · intro hy
      have hy' : y ∈ ((⊥ : Submodule ℝ ℝ) : Set ℝ) := by
        simpa using hy
      exact ConvexCone.subset_hull hy'
  have hspan_zero : (Submodule.span ℝ ({0} : Set ℝ) : Set ℝ) = ({0} : Set ℝ) := by
    ext y
    simp
  rw [hsub, hcone_zero, hspan_zero]

/-- Helper for Proposition 17 32: an interval of positive radius around `m` inside `s` makes `m`
belong to the relative interior of `s`. -/
lemma midpoint_mem_relativeInterior_of_Icc_subset
    {s : Set ℝ} {m ε : ℝ} (hε : 0 < ε) (hIcc : Set.Icc (m - ε) (m + ε) ⊆ s) :
    m ∈ Set.relativeInterior s := by
  let S : Set ℝ := s - ({m} : Set ℝ)
  have hm_mem_Icc : m ∈ Set.Icc (m - ε) (m + ε) := by
    constructor <;> linarith
  have hm_mem : m ∈ s := hIcc hm_mem_Icc
  rw [Set.mem_relativeInterior_iff]
  refine ⟨hm_mem, ?_⟩
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hm_plus_mem : m + ε ∈ s := by
    apply hIcc
    constructor <;> linarith
  have hm_minus_mem : m - ε ∈ s := by
    apply hIcc
    constructor <;> linarith
  have hm_singleton : m ∈ ({m} : Set ℝ) := by
    simp
  have hε_mem : ε ∈ S := by
    have hdiff : m + ε - m = ε := by
      ring
    exact Set.mem_sub.mpr ⟨m + ε, hm_plus_mem, m, hm_singleton, hdiff⟩
  have hnegε_mem : -ε ∈ S := by
    have hdiff : m - ε - m = -ε := by
      ring
    exact Set.mem_sub.mpr ⟨m - ε, hm_minus_mem, m, hm_singleton, hdiff⟩
  have hzero_mem : (0 : ℝ) ∈ S := by
    exact Set.mem_sub.mpr ⟨m, hm_mem, m, hm_singleton, sub_self m⟩
  have hcone_univ : Set.cone S = Set.univ := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      rw [Set.cone_def]
      by_cases hy_zero : y = 0
      · subst hy_zero
        exact ConvexCone.subset_hull hzero_mem
      · by_cases hy_nonneg : 0 ≤ y
        · have hy_pos : 0 < y := by
            refine lt_of_le_of_ne hy_nonneg ?_
            simpa [eq_comm] using hy_zero
          have hy_eq : (y / ε : ℝ) • ε = y := by
            have hy_mul : (y / ε : ℝ) * ε = y := by
              field_simp [hε_ne]
            simpa [smul_eq_mul] using hy_mul
          rw [← hy_eq]
          exact (ConvexCone.hull ℝ S).smul_mem (div_pos hy_pos hε)
            (ConvexCone.subset_hull hε_mem)
        · have hy_neg : y < 0 := lt_of_not_ge hy_nonneg
          have hy_eq : (((-y) / ε : ℝ) • (-ε)) = y := by
            have hy_mul : (((-y) / ε : ℝ) * (-ε)) = y := by
              field_simp [hε_ne]
            simpa [smul_eq_mul] using hy_mul
          rw [← hy_eq]
          have hscale_pos : 0 < (-y) / ε := by
            exact div_pos (by linarith) hε
          exact (ConvexCone.hull ℝ S).smul_mem hscale_pos
            (ConvexCone.subset_hull hnegε_mem)
  have hspan_eq_top : Submodule.span ℝ S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have hsingleton_subset : ({ε} : Set ℝ) ⊆ S := by
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact hε_mem
    have hy_singleton : y ∈ Submodule.span ℝ ({ε} : Set ℝ) := by
      rw [Submodule.mem_span_singleton]
      refine ⟨y / ε, ?_⟩
      have hy_mul : (y / ε : ℝ) * ε = y := by
        field_simp [hε_ne]
      simpa [smul_eq_mul] using hy_mul
    exact (Submodule.span_mono hsingleton_subset) hy_singleton
  have hspan_univ : (Submodule.span ℝ S : Set ℝ) = Set.univ := by
    simpa using congrArg (fun V : Submodule ℝ ℝ ↦ (V : Set ℝ)) hspan_eq_top
  simpa [S] using hcone_univ.trans hspan_univ.symm

section

omit [CompleteSpace H]

/-- Helper for Proposition 17 32: continuity makes `range f` an interval in `ℝ`, so adding a
positive scalar to one relative-interior point yields the regularity witness required by
Corollary 16.72. -/
-- Route correction: prove the range witness directly in `ℝ` from preconnectedness, rather than
-- importing the heavier finite-dimensional relative-interior API.
lemma range_ri_add_Ioi_nonempty
    (f : H → ℝ) (x₀ : H) (hcont : Continuous f) :
    Set.Nonempty ((Set.relativeInterior (Set.range f)) + Set.Ioi (0 : ℝ)) := by
  have hrange_preconn : IsPreconnected (Set.range f) := by
    simpa [Set.image_univ] using
      (_root_.convex_univ : Convex ℝ (Set.univ : Set H)).isPreconnected.image f hcont.continuousOn
  by_cases hconst : ∀ y : H, f y = f x₀
  · have hrange_singleton : Set.range f = ({f x₀} : Set ℝ) := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        rw [hconst y]
        simp
      · intro hz
        have hz' : z = f x₀ := Set.mem_singleton_iff.mp hz
        refine ⟨x₀, ?_⟩
        simp [hz']
    have hri : f x₀ ∈ Set.relativeInterior (Set.range f) := by
      rw [hrange_singleton]
      exact self_mem_relativeInterior_singleton_real (f x₀)
    have hone : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
      simp
    refine ⟨f x₀ + 1, ?_⟩
    change ∃ a ∈ Set.relativeInterior (Set.range f), ∃ b ∈ Set.Ioi (0 : ℝ), a + b = f x₀ + 1
    exact ⟨f x₀, hri, 1, hone, rfl⟩
  · have hnonconst : ∃ y : H, f y ≠ f x₀ := by
      by_contra hno
      apply hconst
      intro y
      by_contra hy
      exact hno ⟨y, hy⟩
    rcases hnonconst with ⟨y, hy_ne⟩
    by_cases hxy : f x₀ < f y
    · let m : ℝ := (f x₀ + f y) / 2
      let ε : ℝ := (f y - f x₀) / 2
      have hx0_mem : f x₀ ∈ Set.range f := ⟨x₀, rfl⟩
      have hy_mem : f y ∈ Set.range f := ⟨y, rfl⟩
      have hε_pos : 0 < ε := by
        dsimp [ε]
        linarith
      have hIcc : Set.Icc (m - ε) (m + ε) ⊆ Set.range f := by
        have hab : Set.Icc (f x₀) (f y) ⊆ Set.range f := hrange_preconn.Icc_subset hx0_mem hy_mem
        have hm_left : m - ε = f x₀ := by
          dsimp [m, ε]
          ring
        have hm_right : m + ε = f y := by
          dsimp [m, ε]
          ring
        simpa [hm_left, hm_right] using hab
      have hm_ri : m ∈ Set.relativeInterior (Set.range f) :=
        midpoint_mem_relativeInterior_of_Icc_subset hε_pos hIcc
      have hone : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
        simp
      refine ⟨m + 1, ?_⟩
      change ∃ a ∈ Set.relativeInterior (Set.range f), ∃ b ∈ Set.Ioi (0 : ℝ), a + b = m + 1
      exact ⟨m, hm_ri, 1, hone, rfl⟩
    · have hyx : f y < f x₀ := lt_of_le_of_ne (le_of_not_gt hxy) hy_ne
      let m : ℝ := (f y + f x₀) / 2
      let ε : ℝ := (f x₀ - f y) / 2
      have hy_mem : f y ∈ Set.range f := ⟨y, rfl⟩
      have hx0_mem : f x₀ ∈ Set.range f := ⟨x₀, rfl⟩
      have hε_pos : 0 < ε := by
        dsimp [ε]
        linarith
      have hIcc : Set.Icc (m - ε) (m + ε) ⊆ Set.range f := by
        have hab : Set.Icc (f y) (f x₀) ⊆ Set.range f := hrange_preconn.Icc_subset hy_mem hx0_mem
        have hm_left : m - ε = f y := by
          dsimp [m, ε]
          ring
        have hm_right : m + ε = f x₀ := by
          dsimp [m, ε]
          ring
        simpa [hm_left, hm_right] using hab
      have hm_ri : m ∈ Set.relativeInterior (Set.range f) :=
        midpoint_mem_relativeInterior_of_Icc_subset hε_pos hIcc
      have hone : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
        simp
      refine ⟨m + 1, ?_⟩
      change ∃ a ∈ Set.relativeInterior (Set.range f), ∃ b ∈ Set.Ioi (0 : ℝ), a + b = m + 1
      exact ⟨m, hm_ri, 1, hone, rfl⟩

end

/-- Helper for Proposition 17 32: for a convex scalar function, differentiability identifies the
canonical right derivative with the ordinary derivative. -/
lemma scalar_right_derivative_eq_deriv_of_differentiableAt
    {φ : ℝ → ℝ} (hconv : ConvexOn φ.toEReal (effectiveDomain φ.toEReal)) {r : ℝ}
    (hφdiff : DifferentiableAt ℝ φ r) :
    ERealFunction.rightDerivative φ.toEReal r = (((deriv φ r : ℝ)) : EReal) := by
  have hline : HasLineDerivAt ℝ φ (deriv φ r) r (1 : ℝ) := by
    -- The ordinary derivative gives the right slope in direction `1`.
    simpa using hφdiff.hasDerivAt.hasFDerivAt.hasLineDerivAt (1 : ℝ)
  have hreal :
      Filter.Tendsto
        (fun t : ℝ ↦ ((((φ (r + t * 1) - φ r) / t : ℝ)) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (((deriv φ r : ℝ)) : EReal)) := by
    -- Cast the real-valued right-slope limit to `EReal`.
    exact EReal.tendsto_coe.2 <| by
      simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hline.tendsto_slope_zero_right
  have hright : HasRightDerivativeAt φ.toEReal r (((deriv φ r : ℝ)) : EReal) := by
    refine ⟨by simp [Function.effectiveDomain_toEReal], ?_⟩
    -- Replace the `toEReal` quotient by the cast ordinary real quotient.
    refine Filter.Tendsto.congr' ?_ hreal
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [Function.toEReal_apply, smul_eq_mul]
    rw [← EReal.coe_sub, ← EReal.coe_div]
  -- Convexity upgrades the source right derivative to the canonical owner.
  simpa [ERealFunction.rightDerivative, HasRightDerivativeAt] using
    (directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := φ.toEReal) hconv hright)

/-- Helper for Proposition 17 32: for a convex scalar function, differentiability identifies the
canonical left derivative with the ordinary derivative. -/
lemma scalar_left_derivative_eq_deriv_of_differentiableAt
    {φ : ℝ → ℝ} (hconv : ConvexOn φ.toEReal (effectiveDomain φ.toEReal)) {r : ℝ}
    (hφdiff : DifferentiableAt ℝ φ r) :
    ERealFunction.leftDerivative φ.toEReal r = (((deriv φ r : ℝ)) : EReal) := by
  have hline : HasLineDerivAt ℝ φ (-(deriv φ r)) r (-1 : ℝ) := by
    -- The same derivative gives the slope in direction `-1`.
    simpa using hφdiff.hasDerivAt.hasFDerivAt.hasLineDerivAt (-1 : ℝ)
  have hreal :
      Filter.Tendsto
        (fun t : ℝ ↦ ((((φ (r + t * (-1)) - φ r) / t : ℝ)) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (-(((deriv φ r : ℝ)) : EReal))) := by
    -- Cast the real-valued left-slope limit to `EReal`.
    exact EReal.tendsto_coe.2 <| by
      simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hline.tendsto_slope_zero_right
  have hleft : HasLeftDerivativeAt φ.toEReal r (((deriv φ r : ℝ)) : EReal) := by
    refine ⟨by simp [Function.effectiveDomain_toEReal], ?_⟩
    -- Match the `toEReal` quotient with the cast real quotient along direction `-1`.
    refine Filter.Tendsto.congr' ?_ hreal
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [Function.toEReal_apply, smul_eq_mul]
    rw [← EReal.coe_sub, ← EReal.coe_div]
  have hdir :
      ERealFunction.directionalDerivative φ.toEReal r (-1) = -((((deriv φ r : ℝ)) : EReal)) :=
    directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := φ.toEReal) hconv hleft
  -- The left derivative is the negated directional derivative in direction `-1`.
  simpa [ERealFunction.leftDerivative] using congrArg Neg.neg hdir

/-- Helper for Proposition 17 32: a convex real function has singleton scalar subdifferential at a
differentiability point, with generator equal to the ordinary derivative. -/
lemma scalar_subdifferential_toEReal_eq_singleton_deriv
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ) {r : ℝ}
    (hφdiff : DifferentiableAt ℝ φ r) :
    (∂ φ.toEReal) r = ({deriv φ r} : Set ℝ) := by
  -- Rewrite the scalar subdifferential as the interval between one-sided derivatives.
  have hφconv_toEReal : ConvexOn φ.toEReal (effectiveDomain φ.toEReal) :=
    convexOn_toEReal_of_convexOn_univ φ hφconv
  have hr_mem : r ∈ effectiveDomain φ.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  rw [subdifferential_eq_Icc_oneSidedDerivatives
    (f := φ.toEReal) (hconv := hφconv_toEReal) hr_mem]
  change Real.toEReal ⁻¹' Set.Icc
      (ERealFunction.leftDerivative φ.toEReal r)
      (ERealFunction.rightDerivative φ.toEReal r) =
    ({deriv φ r} : Set ℝ)
  rw [scalar_left_derivative_eq_deriv_of_differentiableAt hφconv_toEReal hφdiff]
  rw [scalar_right_derivative_eq_deriv_of_differentiableAt hφconv_toEReal hφdiff]
  ext a
  -- A degenerate interval with equal endpoints is exactly a singleton.
  simp [Set.mem_preimage]

/-- Helper for Proposition 17 32: once the scalar index set is a singleton, the indexed union of
scaled sets collapses to the corresponding single scalar multiple. -/
lemma iUnion_smul_singleton_eq
    {E : Type*} [SMul ℝ E] (a : ℝ) (S : Set E) :
    (⋃ α ∈ ({a} : Set ℝ), α • S) = a • S := by
  ext x
  constructor
  · intro hx
    -- Membership in the double union forces the unique scalar index to be `a`.
    rcases Set.mem_iUnion.mp hx with ⟨α, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hα, hx⟩
    rcases Set.mem_singleton_iff.mp hα with hαeq
    simpa [hαeq] using hx
  · intro hx
    -- Conversely, the singleton index `a` witnesses membership in the union.
    exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨by simp, hx⟩⟩

-- Proof sketch: apply Corollary 16.72 to the scalar composition `φ ∘ f`, viewed through
-- `.toEReal`, to rewrite its subdifferential as the union of the scaled sets
-- `α • (∂ f.toEReal) x` for `α ∈ (∂ φ.toEReal) (f x)`. Then use
-- Proposition 17.31 (1) in the scalar space `H = ℝ` together with the ordinary differentiability
-- of `φ` at `f x` to identify `(∂ φ.toEReal) (f x)` with the singleton
-- `{deriv φ (f x)}`, so the union collapses to the claimed scalar multiple.
/-- Proposition 17 32: if `f : H → ℝ` is continuous and convex, and `φ : ℝ → ℝ` is convex,
increasing on `range f`, and differentiable at `f x`, then the subdifferential of `φ ∘ f` at `x`
is the scalar multiple `φ'(f(x)) ∂ f(x)`, represented here via `deriv φ (f x)` and `.toEReal`.
-/
theorem subdifferential_comp_eq_deriv_smul_of_differentiableAt
    (f : H → ℝ) (φ : ℝ → ℝ) (x : H) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφdiff : DifferentiableAt ℝ φ (f x)) (hmono : MonotoneOn φ (Set.range f)) :
    (∂ (φ ∘ f).toEReal) x = (deriv φ (f x)) • ((∂ f.toEReal) x) := by
  have hφcont : Continuous φ := by
    -- A convex real function is continuous on the open domain `Set.univ`.
    exact continuousOn_univ.mp (hφconv.continuousOn isOpen_univ)
  have hφΓ : φ.toEReal ∈ Γ₀(ℝ) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ φ hφcont hφconv
  have hregular :
      ((Set.relativeInterior (Set.range f) + Set.Ioi (0 : ℝ)) ∩
        Set.relativeInterior (effectiveDomain φ.toEReal)).Nonempty := by
    -- Since `φ.toEReal` is finite everywhere, the scalar regularity reduces to the range witness.
    rw [Function.effectiveDomain_toEReal]
    rcases range_ri_add_Ioi_nonempty f x hcont with ⟨z, hz⟩
    refine ⟨z, hz, ?_⟩
    refine Set.mem_relativeInterior_iff.mpr ⟨by simp, ?_⟩
    have huniv_sub : (Set.univ : Set ℝ) - ({z} : Set ℝ) = Set.univ := by
      ext y
      constructor
      · intro hy
        simp
      · intro hy
        refine Set.mem_sub.2 ?_
        exact ⟨y + z, by simp, z, by simp, by ring⟩
    have hcone_univ : Set.cone (Set.univ : Set ℝ) = Set.univ := by
      refine Set.Subset.antisymm ?_ ?_
      · intro y hy
        simp
      · intro y hy
        rw [Set.cone_def]
        exact (ConvexCone.mem_hull_of_convex
          (𝕜 := ℝ) (s := (Set.univ : Set ℝ)) (x := y) convex_univ).2 ⟨1, by norm_num, by simp⟩
    simp [huniv_sub, hcone_univ]
  have hmono_toEReal : MonotoneOn φ.toEReal (Set.range f) := by
    -- The `toEReal` coercion preserves the scalar monotonicity inequality.
    intro a ha b hb hab
    change (φ a : EReal) ≤ (φ b : EReal)
    exact_mod_cast hmono ha hb hab
  have hchain :=
    subdifferential_comp_eq_iUnion_smul_of_continuous_convexOn_univ_of_monotoneOn_range
      f φ.toEReal hcont hconv hφΓ hmono_toEReal hregular x (by
        simp [Function.effectiveDomain_toEReal])
  have hscalar :
      (∂ φ.toEReal) (f x) = ({deriv φ (f x)} : Set ℝ) :=
    scalar_subdifferential_toEReal_eq_singleton_deriv φ hφconv hφdiff
  -- Apply the scalar-composition chain rule and collapse the singleton index family.
  calc
    (∂ (φ ∘ f).toEReal) x
        = ⋃ α ∈ (∂ φ.toEReal) (f x), α • ((∂ f.toEReal) x) := by
            simpa [Function.comp_apply, Function.toEReal_apply] using hchain
    _ = ⋃ α ∈ ({deriv φ (f x)} : Set ℝ), α • ((∂ f.toEReal) x) := by
          rw [hscalar]
    _ = (deriv φ (f x)) • ((∂ f.toEReal) x) := by
          exact iUnion_smul_singleton_eq (a := deriv φ (f x)) ((∂ f.toEReal) x)

end DifferentiabilityOfConvexFunctions

end ERealFunction
