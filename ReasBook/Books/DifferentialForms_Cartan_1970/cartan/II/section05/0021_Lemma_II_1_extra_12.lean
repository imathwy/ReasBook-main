import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0020_Definition_II_1_extra_11»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set
open scoped Interval

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: two local primitives defined on
overlapping open neighborhoods agree up to an additive constant on a smaller ball around any common
point. -/
theorem local_sub_eq_const_on_ball_of_common_primitive
    {ω : E → E →L[ℝ] F} {U V : Set E} {z₀ : E}
    (hU : IsOpen U) (hV : IsOpen V) (hzU : z₀ ∈ U) (hzV : z₀ ∈ V)
    {f g : E → F} (hf : IsPrimitiveOn U ω f) (hg : IsPrimitiveOn V ω g) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : F,
      EqOn (fun z ↦ g z - f z) (fun _ ↦ c) (Metric.ball z₀ r) := by
  -- Shrink to a ball contained in the overlap so the standard constant-difference lemma applies.
  have hzUV : z₀ ∈ U ∩ V := ⟨hzU, hzV⟩
  have hUV_open : IsOpen (U ∩ V) := hU.inter hV
  rcases Metric.isOpen_iff.mp hUV_open z₀ hzUV with ⟨r, hr, hball⟩
  have hf_ball : IsPrimitiveOn (Metric.ball z₀ r) ω f :=
    hf.mono fun z hz ↦ (hball hz).1
  have hg_ball : IsPrimitiveOn (Metric.ball z₀ r) ω g :=
    hg.mono fun z hz ↦ (hball hz).2
  rcases IsPrimitiveOn.sub_eqOn_const_of_isOpen_isPreconnected
      (D := Metric.ball z₀ r) Metric.isOpen_ball (convex_ball z₀ r).isPreconnected hg_ball hf_ball
    with ⟨c, hc⟩
  exact ⟨r, hr, c, hc⟩

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: the difference of two primitives
following the same rectangle map is locally constant on the rectangle. -/
theorem primitiveFollowingOnRectangle_difference_isLocallyConstant
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)}
    {f g : C([[(a, a'), (b, b')]], F)}
    (hf : IsPrimitiveFollowingOnRectangle ω D δ f)
    (hg : IsPrimitiveFollowingOnRectangle ω D δ g) :
    IsLocallyConstant (fun p : [[(a, a'), (b, b')]] ↦ g p - f p) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro p
  rcases hf.local_primitive p with
    ⟨sf, hsf_open, hpsf, Uf, hUf_open, hδpUf, -, hmapsf, primitiveF, hprimitiveF, hEqf⟩
  rcases hg.local_primitive p with
    ⟨sg, hsg_open, hpsg, Ug, hUg_open, hδpUg, -, hmapsg, primitiveG, hprimitiveG, hEqg⟩
  -- Compare the two codomain primitives on a common ball around `δ p`.
  rcases local_sub_eq_const_on_ball_of_common_primitive hUf_open hUg_open hδpUf hδpUg
      hprimitiveF hprimitiveG with
    ⟨r, hr, c, hc⟩
  let s : Set ([[(a, a'), (b, b')]]) := (sf ∩ sg) ∩ δ ⁻¹' Metric.ball (δ p) r
  have hs_open : IsOpen s := by
    refine (hsf_open.inter hsg_open).inter ?_
    exact δ.continuous.isOpen_preimage _ Metric.isOpen_ball
  have hps : p ∈ s := by
    refine ⟨⟨hpsf, hpsg⟩, ?_⟩
    exact Metric.mem_ball_self hr
  have hpconst : g p - f p = c := by
    calc
      g p - f p = primitiveG (δ p) - primitiveF (δ p) := by
        rw [hEqg hpsg, hEqf hpsf]
        rfl
      _ = c := hc (Metric.mem_ball_self hr)
  refine ⟨s, hs_open, hps, ?_⟩
  intro q hq
  have hqsf : q ∈ sf := hq.1.1
  have hqsg : q ∈ sg := hq.1.2
  have hqball : δ q ∈ Metric.ball (δ p) r := hq.2
  -- Pull the constant-difference identity back along `δ` and rewrite via the local witnesses.
  calc
    g q - f q = primitiveG (δ q) - primitiveF (δ q) := by
      rw [hEqg hqsg, hEqf hqsf]
      rfl
    _ = c := hc hqball
    _ = g p - f p := hpconst.symm

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: on any parameter space, two functions
with local primitive descriptions along the same continuous map have locally constant difference. -/
theorem difference_isLocallyConstant_of_hasLocalPrimitive
    {X : Type*} [TopologicalSpace X]
    {ω : E → E →L[ℝ] F} {δ : X → E} (hδ : Continuous δ)
    {f g : X → F}
    (hf :
      ∀ p : X,
        ∃ s : Set X, IsOpen s ∧ p ∈ s ∧
          ∃ U : Set E, IsOpen U ∧ δ p ∈ U ∧ MapsTo δ s U ∧
            ∃ primitive : E → F,
              IsPrimitiveOn U ω primitive ∧
                EqOn f (primitive ∘ δ) s)
    (hg :
      ∀ p : X,
        ∃ s : Set X, IsOpen s ∧ p ∈ s ∧
          ∃ U : Set E, IsOpen U ∧ δ p ∈ U ∧ MapsTo δ s U ∧
            ∃ primitive : E → F,
              IsPrimitiveOn U ω primitive ∧
                EqOn g (primitive ∘ δ) s) :
    IsLocallyConstant (fun p : X ↦ g p - f p) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro p
  rcases hf p with
    ⟨sf, hsf_open, hpsf, Uf, hUf_open, hδpUf, hmapsf, primitiveF, hprimitiveF, hEqf⟩
  rcases hg p with
    ⟨sg, hsg_open, hpsg, Ug, hUg_open, hδpUg, hmapsg, primitiveG, hprimitiveG, hEqg⟩
  -- Compare the two codomain primitives on a common ball around `δ p`.
  rcases local_sub_eq_const_on_ball_of_common_primitive hUf_open hUg_open hδpUf hδpUg
      hprimitiveF hprimitiveG with
    ⟨r, hr, c, hc⟩
  let s : Set X := (sf ∩ sg) ∩ δ ⁻¹' Metric.ball (δ p) r
  have hs_open : IsOpen s := by
    refine (hsf_open.inter hsg_open).inter ?_
    exact hδ.isOpen_preimage _ Metric.isOpen_ball
  have hps : p ∈ s := by
    refine ⟨⟨hpsf, hpsg⟩, ?_⟩
    exact Metric.mem_ball_self hr
  have hpconst : g p - f p = c := by
    calc
      g p - f p = primitiveG (δ p) - primitiveF (δ p) := by
        rw [hEqg hpsg, hEqf hpsf]
        rfl
      _ = c := hc (Metric.mem_ball_self hr)
  refine ⟨s, hs_open, hps, ?_⟩
  intro q hq
  have hqsf : q ∈ sf := hq.1.1
  have hqsg : q ∈ sg := hq.1.2
  have hqball : δ q ∈ Metric.ball (δ p) r := hq.2
  -- Pull the codomain constant-difference identity back along `δ`.
  calc
    g q - f q = primitiveG (δ q) - primitiveF (δ q) := by
      rw [hEqg hqsg, hEqf hqsf]
      rfl
    _ = c := hc hqball
    _ = g p - f p := hpconst.symm

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: adding a constant to a local primitive
does not change the differential form it differentiates to. -/
theorem IsPrimitiveOn.addConst
    {ω : E → E →L[ℝ] F} {U : Set E} {primitive : E → F}
    (hprimitive : IsPrimitiveOn U ω primitive) (c : F) :
    IsPrimitiveOn U ω (fun z ↦ primitive z + c) := by
  -- A constant shift preserves the derivative pointwise on the primitive domain.
  intro z hz
  simpa using (hprimitive z hz).add_const c

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: a constant-difference identity between
two codomain primitives pulls back to equality of the corresponding shifted rectangle primitives on
any parameter patch mapped into that ball. -/
theorem shiftedPullbackPrimitive_eqOn_overlap
    {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)} {p : [[(a, a'), (b, b')]]}
    {s : Set ([[(a, a'), (b, b')]])} {r : ℝ} {c k : F}
    {primitiveF primitiveG : E → F}
    (hs_maps : MapsTo δ s (Metric.ball (δ p) r))
    (hc : EqOn (fun z ↦ primitiveG z - primitiveF z) (fun _ ↦ c) (Metric.ball (δ p) r)) :
    EqOn (fun q ↦ primitiveG (δ q) + (k - c)) (fun q ↦ primitiveF (δ q) + k) s := by
  -- Pull the codomain constant-difference relation back along `δ` and simplify the shift.
  intro q hq
  have hdiff : primitiveG (δ q) - primitiveF (δ q) = c := hc (hs_maps hq)
  have hEq : primitiveG (δ q) = c + primitiveF (δ q) := (sub_eq_iff_eq_add).mp hdiff
  calc
    primitiveG (δ q) + (k - c) = (c + primitiveF (δ q)) + (k - c) := by rw [hEq]
    _ = primitiveF (δ q) + k := by
      abel

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: if `δ p` lies in two primitive domains,
then the corresponding shifted pullbacks agree exactly on a preimage ball around `p`. -/
theorem shiftedPullbackPrimitive_eqOn_preimageBall_of_common_primitive
    {ω : E → E →L[ℝ] F} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)} {p : [[(a, a'), (b, b')]]}
    {U V : Set E} {primitiveF primitiveG : E → F} {k : F}
    (hU : IsOpen U) (hV : IsOpen V) (hpU : δ p ∈ U) (hpV : δ p ∈ V)
    (hprimitiveF : IsPrimitiveOn U ω primitiveF)
    (hprimitiveG : IsPrimitiveOn V ω primitiveG) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : F,
      EqOn (fun q ↦ primitiveG (δ q) + (k - c)) (fun q ↦ primitiveF (δ q) + k)
        (δ ⁻¹' Metric.ball (δ p) r) := by
  -- First compare the codomain primitives on a common ball around `δ p`.
  rcases local_sub_eq_const_on_ball_of_common_primitive hU hV hpU hpV
      hprimitiveF hprimitiveG with
    ⟨r, hr, c, hc⟩
  refine ⟨r, hr, c, ?_⟩
  -- Then pull the codomain equality back along `δ` and absorb the constant shift.
  exact shiftedPullbackPrimitive_eqOn_overlap (p := p) (s := δ ⁻¹' Metric.ball (δ p) r)
    (r := r) (c := c) (k := k) (primitiveF := primitiveF) (primitiveG := primitiveG)
    (hs_maps := fun q hq ↦ hq) hc

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: choosing the horizontal overlap
constants recursively along each row produces shifted pullback primitives that agree exactly on
every adjacent horizontal overlap ball. -/
theorem horizontalShiftData
    {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)}
    {primitive : ℕ → ℕ → E → F}
    {cornerX : ℕ → ℕ → [[(a, a'), (b, b')]]}
    (hoverlapX :
      ∀ i j, ∃ r : ℝ, 0 < r ∧ ∃ c : F,
        EqOn
          (fun q ↦ primitive (i + 1) j (δ q) + ((0 : F) - c))
          (fun q ↦ primitive i j (δ q) + (0 : F))
          (δ ⁻¹' Metric.ball (δ (cornerX i j)) r)) :
    ∃ overlapRadiusX : ℕ → ℕ → ℝ,
      ∃ overlapConstX : ℕ → ℕ → F,
        ∃ kx : ℕ → ℕ → F,
          (∀ i j, 0 < overlapRadiusX i j) ∧
          (∀ i j,
            EqOn
              (fun q ↦ primitive (i + 1) j (δ q) + ((0 : F) - overlapConstX i j))
              (fun q ↦ primitive i j (δ q) + (0 : F))
              (δ ⁻¹' Metric.ball (δ (cornerX i j)) (overlapRadiusX i j))) ∧
          (∀ j, kx 0 j = 0) ∧
          (∀ i j, kx (i + 1) j = kx i j - overlapConstX i j) ∧
          (∀ i j,
            EqOn
              (fun q ↦ primitive (i + 1) j (δ q) + kx (i + 1) j)
              (fun q ↦ primitive i j (δ q) + kx i j)
              (δ ⁻¹' Metric.ball (δ (cornerX i j)) (overlapRadiusX i j))) := by
  classical
  let overlapRadiusX : ℕ → ℕ → ℝ := fun i j => Classical.choose (hoverlapX i j)
  let overlapConstX : ℕ → ℕ → F := fun i j =>
    Classical.choose ((Classical.choose_spec (hoverlapX i j)).2)
  let kx : ℕ → ℕ → F := fun i j =>
    Nat.rec (motive := fun _ => F) 0 (fun n acc ↦ acc - overlapConstX n j) i
  have hoverlapRadiusX_pos : ∀ i j, 0 < overlapRadiusX i j := by
    intro i j
    exact (Classical.choose_spec (hoverlapX i j)).1
  have hoverlapEqX :
      ∀ i j,
        EqOn
          (fun q ↦ primitive (i + 1) j (δ q) + ((0 : F) - overlapConstX i j))
          (fun q ↦ primitive i j (δ q) + (0 : F))
          (δ ⁻¹' Metric.ball (δ (cornerX i j)) (overlapRadiusX i j)) := by
    intro i j
    exact Classical.choose_spec ((Classical.choose_spec (hoverlapX i j)).2)
  have hkx_zero : ∀ j, kx 0 j = 0 := by
    intro j
    rfl
  have hkx_succ : ∀ i j, kx (i + 1) j = kx i j - overlapConstX i j := by
    intro i j
    rfl
  have hshiftEqX :
      ∀ i j,
        EqOn
          (fun q ↦ primitive (i + 1) j (δ q) + kx (i + 1) j)
          (fun q ↦ primitive i j (δ q) + kx i j)
          (δ ⁻¹' Metric.ball (δ (cornerX i j)) (overlapRadiusX i j)) := by
    intro i j
    intro q hq
    have hbase := hoverlapEqX i j hq
    have hbase' :
        (primitive (i + 1) j (δ q) + ((0 : F) - overlapConstX i j)) + kx i j =
          (primitive i j (δ q) + (0 : F)) + kx i j := by
      simpa using congrArg (fun z : F ↦ z + kx i j) hbase
    -- The recursive shift adds the same constant `kx i j` to both neighboring formulas.
    calc
      primitive (i + 1) j (δ q) + kx (i + 1) j
          = primitive (i + 1) j (δ q) + (kx i j - overlapConstX i j) := by
              rw [hkx_succ i j]
      _ = primitive i j (δ q) + kx i j := by
            calc
              primitive (i + 1) j (δ q) + (kx i j - overlapConstX i j)
                  = (primitive (i + 1) j (δ q) + ((0 : F) - overlapConstX i j)) + kx i j := by
                      abel
              _ = (primitive i j (δ q) + (0 : F)) + kx i j := hbase'
              _ = primitive i j (δ q) + kx i j := by
                    abel
  refine ⟨overlapRadiusX, overlapConstX, kx, hoverlapRadiusX_pos, hoverlapEqX,
    hkx_zero, hkx_succ, hshiftEqX⟩

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: a point in a sufficiently small closed
rectangle cell stays within the controlling Lebesgue radius of its lower-left corner. -/
theorem rectanglePoint_dist_lt_of_mem_smallCell
    {x₀ y₀ x₁ y₁ ε : ℝ} {p : ℝ × ℝ}
    (hx₀ : x₀ ≤ p.1) (hy₀ : y₀ ≤ p.2)
    (hx₁ : p.1 ≤ x₁) (hy₁ : p.2 ≤ y₁)
    (hwidth : x₁ - x₀ ≤ ε / 2) (hheight : y₁ - y₀ ≤ ε / 2)
    (hε : 0 < ε) :
    dist p (x₀, y₀) < ε := by
  -- In the product metric, it is enough to bound each coordinate displacement by `ε / 2`.
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
  constructor
  · have hx : |p.1 - x₀| = p.1 - x₀ := abs_of_nonneg (sub_nonneg.mpr hx₀)
    rw [hx]
    linarith
  · have hy : |p.2 - y₀| = p.2 - y₀ := abs_of_nonneg (sub_nonneg.mpr hy₀)
    rw [hy]
    linarith

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: a closed vertical segment inside the
closed rectangle is preconnected. -/
theorem isPreconnected_verticalSegmentWithinRectangle
    {a a' b b' x y₀ y₁ : ℝ}
    (hx : x ∈ Set.uIcc a b) (hy₀ : y₀ ∈ Set.uIcc a' b') (hy₁ : y₁ ∈ Set.uIcc a' b') :
    IsPreconnected {p : [[(a, a'), (b, b')]] | p.1.1 = x ∧ p.1.2 ∈ Set.Icc y₀ y₁} := by
  let edgeParam : Set.Icc y₀ y₁ → [[(a, a'), (b, b')]] := fun y =>
    ⟨(x, (y : ℝ)), by
      have hy : ((y : ℝ)) ∈ Set.uIcc a' b' := by
        exact ⟨hy₀.1.trans y.2.1, y.2.2.trans hy₁.2⟩
      have hpair : ((x, (y : ℝ)) : ℝ × ℝ) ∈ Set.uIcc a b ×ˢ Set.uIcc a' b' := ⟨hx, hy⟩
      simpa [Set.uIcc_prod_uIcc] using hpair⟩
  have hedgeParam_cont : Continuous edgeParam := by
    -- Parametrize the vertical segment by the closed interval in the second coordinate.
    fun_prop
  have hrange :
      Set.range edgeParam = {p : [[(a, a'), (b, b')]] | p.1.1 = x ∧ p.1.2 ∈ Set.Icc y₀ y₁} := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨rfl, y.2⟩
    · intro hp
      refine ⟨⟨p.1.2, hp.2⟩, ?_⟩
      apply Subtype.ext
      ext <;> simp [edgeParam, hp.1]
  haveI : PreconnectedSpace (Set.Icc y₀ y₁) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  -- The image of a preconnected interval under the vertical-segment parametrization is
  -- preconnected.
  simpa [hrange] using isPreconnected_range (f := edgeParam) hedgeParam_cont

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: a closed horizontal segment inside the
closed rectangle is preconnected. -/
theorem isPreconnected_horizontalSegmentWithinRectangle
    {a a' b b' x₀ x₁ y : ℝ}
    (hx₀ : x₀ ∈ Set.uIcc a b) (hx₁ : x₁ ∈ Set.uIcc a b) (hy : y ∈ Set.uIcc a' b') :
    IsPreconnected {p : [[(a, a'), (b, b')]] | p.1.1 ∈ Set.Icc x₀ x₁ ∧ p.1.2 = y} := by
  let edgeParam : Set.Icc x₀ x₁ → [[(a, a'), (b, b')]] := fun x =>
    ⟨((x : ℝ), y), by
      have hx : ((x : ℝ)) ∈ Set.uIcc a b := by
        exact ⟨hx₀.1.trans x.2.1, x.2.2.trans hx₁.2⟩
      have hpair : (((x : ℝ), y) : ℝ × ℝ) ∈ Set.uIcc a b ×ˢ Set.uIcc a' b' := ⟨hx, hy⟩
      simpa [Set.uIcc_prod_uIcc] using hpair⟩
  have hedgeParam_cont : Continuous edgeParam := by
    -- Parametrize the horizontal segment by the closed interval in the first coordinate.
    fun_prop
  have hrange :
      Set.range edgeParam = {p : [[(a, a'), (b, b')]] | p.1.1 ∈ Set.Icc x₀ x₁ ∧ p.1.2 = y} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.2, rfl⟩
    · intro hp
      refine ⟨⟨p.1.1, hp.1⟩, ?_⟩
      apply Subtype.ext
      ext <;> simp [edgeParam, hp.2]
  haveI : PreconnectedSpace (Set.Icc x₀ x₁) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  -- The image of a preconnected interval under the horizontal-segment parametrization is
  -- preconnected.
  simpa [hrange] using isPreconnected_range (f := edgeParam) hedgeParam_cont

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: any open cover of the closed rectangle
admits a uniform `addNSMul` grid whose closed cells each lie in one member of the cover. -/
theorem rectangleLebesgueSubdivision
    {a a' b b' : ℝ} {ι : Type*} {c : ι → Set ([[(a, a'), (b, b')]])}
    (hc_open : ∀ i, IsOpen (c i))
    (hc_cover : (univ : Set ([[(a, a'), (b, b')]])) ⊆ ⋃ i, c i) :
    ∃ t : ℕ → Set.Icc (min a b) (max a b),
      t 0 = ⟨min a b, by simp⟩ ∧
      Monotone t ∧
      (∃ mt, ∀ n ≥ mt, t n = ⟨max a b, by simp⟩) ∧
      (∀ {n : ℕ}, (((t n : Set.Icc (min a b) (max a b)) : ℝ) ≠ max a b) → t n < t (n + 1)) ∧
      ∃ u : ℕ → Set.Icc (min a' b') (max a' b'),
        u 0 = ⟨min a' b', by simp⟩ ∧
        Monotone u ∧
        (∃ mu, ∀ n ≥ mu, u n = ⟨max a' b', by simp⟩) ∧
        (∀ {n : ℕ}, (((u n : Set.Icc (min a' b') (max a' b')) : ℝ) ≠ max a' b') →
          u n < u (n + 1)) ∧
        ∀ i j, ∃ k : ι,
          {p : [[(a, a'), (b, b')]] |
              p.1.1 ∈ Set.Icc ((t i : Set.Icc (min a b) (max a b)) : ℝ)
                (((t (i + 1) : Set.Icc (min a b) (max a b)) : ℝ)) ∧
              p.1.2 ∈ Set.Icc ((u j : Set.Icc (min a' b') (max a' b')) : ℝ)
                (((u (j + 1) : Set.Icc (min a' b') (max a' b')) : ℝ))} ⊆ c k := by
  let x0 := min a b
  let x1 := max a b
  let y0 := min a' b'
  let y1 := max a' b'
  have hx : x0 ≤ x1 := by
    simp [x0, x1]
  have hy : y0 ≤ y1 := by
    simp [y0, y1]
  have hcompact_rect :
      IsCompact ([[((a : ℝ), (a' : ℝ)), ((b : ℝ), (b' : ℝ))]] : Set (ℝ × ℝ)) := by
    simpa [Set.uIcc_prod_uIcc] using
      (isCompact_uIcc : IsCompact (Set.uIcc a b)).prod
        (isCompact_uIcc : IsCompact (Set.uIcc a' b'))
  have hcompact : IsCompact (univ : Set ([[(a, a'), (b, b')]])) := by
    letI : CompactSpace ([[(a, a'), (b, b')]]) := isCompact_iff_compactSpace.mp hcompact_rect
    exact isCompact_univ
  -- Use one Lebesgue number for the whole rectangle cover, then subdivide both coordinates by
  -- the same `addNSMul` step so every closed cell stays inside one control ball.
  obtain ⟨δ, hδpos, hLebesgue⟩ :=
    lebesgue_number_lemma_of_metric hcompact hc_open hc_cover
  let step : ℝ := δ / 2
  have hstep_pos : 0 < step := by
    simpa [step] using half_pos hδpos
  let t : ℕ → Set.Icc x0 x1 := Set.Icc.addNSMul hx step
  let u : ℕ → Set.Icc y0 y1 := Set.Icc.addNSMul hy step
  have ht0 : t 0 = ⟨x0, by simpa [x0, x1] using hx⟩ := by
    apply Subtype.ext
    simpa [t] using (Set.Icc.addNSMul_zero hx (δ := step))
  have hu0 : u 0 = ⟨y0, by simpa [y0, y1] using hy⟩ := by
    apply Subtype.ext
    simpa [u] using (Set.Icc.addNSMul_zero hy (δ := step))
  have htmono : Monotone t := by
    simpa [t] using (Set.Icc.monotone_addNSMul hx (δ := step) hstep_pos.le)
  have humono : Monotone u := by
    simpa [u] using (Set.Icc.monotone_addNSMul hy (δ := step) hstep_pos.le)
  have htsat : ∃ mt, ∀ n ≥ mt, t n = ⟨x1, by simpa [x0, x1] using hx⟩ := by
    rcases Set.Icc.addNSMul_eq_right hx (δ := step) hstep_pos with ⟨mt, hmt⟩
    refine ⟨mt, ?_⟩
    intro n hn
    apply Subtype.ext
    simpa [t] using hmt n hn
  have husat : ∃ mu, ∀ n ≥ mu, u n = ⟨y1, by simpa [y0, y1] using hy⟩ := by
    rcases Set.Icc.addNSMul_eq_right hy (δ := step) hstep_pos with ⟨mu, hmu⟩
    refine ⟨mu, ?_⟩
    intro n hn
    apply Subtype.ext
    simpa [u] using hmu n hn
  rcases htsat with ⟨mt, hmt⟩
  rcases husat with ⟨mu, hmu⟩
  have ht_eq_of_le_right :
      ∀ n : ℕ, x0 + n • step ≤ x1 → ((t n : Set.Icc x0 x1) : ℝ) = x0 + n • step := by
    intro n hn
    have hx0n : x0 ≤ x0 + n • step := by
      nlinarith [nsmul_nonneg hstep_pos.le n]
    calc
      ((t n : Set.Icc x0 x1) : ℝ) = max x0 (min x1 (x0 + n • step)) := by
        simp [t, Set.Icc.addNSMul, Set.coe_projIcc]
      _ = x0 + n • step := by
        rw [min_eq_right hn, max_eq_right hx0n]
  have hu_eq_of_le_right :
      ∀ n : ℕ, y0 + n • step ≤ y1 → ((u n : Set.Icc y0 y1) : ℝ) = y0 + n • step := by
    intro n hn
    have hy0n : y0 ≤ y0 + n • step := by
      nlinarith [nsmul_nonneg hstep_pos.le n]
    calc
      ((u n : Set.Icc y0 y1) : ℝ) = max y0 (min y1 (y0 + n • step)) := by
        simp [u, Set.Icc.addNSMul, Set.coe_projIcc]
      _ = y0 + n • step := by
        rw [min_eq_right hn, max_eq_right hy0n]
  have ht_strict_of_ne_right :
      ∀ {n : ℕ}, (((t n : Set.Icc x0 x1) : ℝ) ≠ x1) → t n < t (n + 1) := by
    intro n hn
    have hn_lt_mt : n < mt := by
      by_contra hnm
      have htn_right : t n = ⟨x1, by simpa [x0, x1] using hx⟩ := hmt n (le_of_not_gt hnm)
      exact hn (by simpa using congrArg Subtype.val htn_right)
    by_cases hn1 : x0 + (n + 1) • step ≤ x1
    · have htn : ((t n : Set.Icc x0 x1) : ℝ) = x0 + n • step := by
        refine ht_eq_of_le_right n ?_
        rw [succ_nsmul] at hn1
        nlinarith [hn1, hstep_pos]
      have htn1 : ((t (n + 1) : Set.Icc x0 x1) : ℝ) = x0 + (n + 1) • step :=
        ht_eq_of_le_right (n + 1) hn1
      change ((t n : Set.Icc x0 x1) : ℝ) < ((t (n + 1) : Set.Icc x0 x1) : ℝ)
      rw [htn, htn1]
      rw [succ_nsmul]
      nlinarith [hstep_pos]
    · have htn1 : ((t (n + 1) : Set.Icc x0 x1) : ℝ) = x1 := by
        have hx1_le : x1 ≤ x0 + (n + 1) • step := le_of_not_ge hn1
        calc
          ((t (n + 1) : Set.Icc x0 x1) : ℝ) = max x0 (min x1 (x0 + (n + 1) • step)) := by
            simp [t, Set.Icc.addNSMul, Set.coe_projIcc]
          _ = x1 := by
            rw [min_eq_left hx1_le, max_eq_right hx]
      have htn_lt : ((t n : Set.Icc x0 x1) : ℝ) < x1 := lt_of_le_of_ne (t n).2.2 hn
      change ((t n : Set.Icc x0 x1) : ℝ) < ((t (n + 1) : Set.Icc x0 x1) : ℝ)
      rw [htn1]
      exact htn_lt
  have hu_strict_of_ne_right :
      ∀ {n : ℕ}, (((u n : Set.Icc y0 y1) : ℝ) ≠ y1) → u n < u (n + 1) := by
    intro n hn
    have hn_lt_mu : n < mu := by
      by_contra hnm
      have hun_right : u n = ⟨y1, by simpa [y0, y1] using hy⟩ := hmu n (le_of_not_gt hnm)
      exact hn (by simpa using congrArg Subtype.val hun_right)
    by_cases hn1 : y0 + (n + 1) • step ≤ y1
    · have hun : ((u n : Set.Icc y0 y1) : ℝ) = y0 + n • step := by
        refine hu_eq_of_le_right n ?_
        rw [succ_nsmul] at hn1
        nlinarith [hn1, hstep_pos]
      have hun1 : ((u (n + 1) : Set.Icc y0 y1) : ℝ) = y0 + (n + 1) • step :=
        hu_eq_of_le_right (n + 1) hn1
      change ((u n : Set.Icc y0 y1) : ℝ) < ((u (n + 1) : Set.Icc y0 y1) : ℝ)
      rw [hun, hun1]
      rw [succ_nsmul]
      nlinarith [hstep_pos]
    · have hun1 : ((u (n + 1) : Set.Icc y0 y1) : ℝ) = y1 := by
        have hy1_le : y1 ≤ y0 + (n + 1) • step := le_of_not_ge hn1
        calc
          ((u (n + 1) : Set.Icc y0 y1) : ℝ) = max y0 (min y1 (y0 + (n + 1) • step)) := by
            simp [u, Set.Icc.addNSMul, Set.coe_projIcc]
          _ = y1 := by
            rw [min_eq_left hy1_le, max_eq_right hy]
      have hun_lt : ((u n : Set.Icc y0 y1) : ℝ) < y1 := lt_of_le_of_ne (u n).2.2 hn
      change ((u n : Set.Icc y0 y1) : ℝ) < ((u (n + 1) : Set.Icc y0 y1) : ℝ)
      rw [hun1]
      exact hun_lt
  refine ⟨t, ht0, htmono, ⟨mt, hmt⟩, ht_strict_of_ne_right, u, hu0, humono, ⟨mu, hmu⟩,
    hu_strict_of_ne_right, ?_⟩
  intro i j
  let corner : [[(a, a'), (b, b')]] := by
    refine ⟨(((t i : Set.Icc x0 x1) : ℝ), ((u j : Set.Icc y0 y1) : ℝ)), ?_⟩
    simpa [Set.uIcc_prod_uIcc, Set.mem_uIcc, x0, x1, y0, y1] using
      (show ((((t i : Set.Icc x0 x1) : ℝ), ((u j : Set.Icc y0 y1) : ℝ)) : ℝ × ℝ) ∈
          Set.uIcc a b ×ˢ Set.uIcc a' b' from
        ⟨by simpa [Set.mem_uIcc, x0, x1] using (t i).2,
          by simpa [Set.mem_uIcc, y0, y1] using (u j).2⟩)
  obtain ⟨k, hk⟩ := hLebesgue corner trivial
  refine ⟨k, ?_⟩
  intro p hp
  have hwidth_nonneg : 0 ≤ ((t (i + 1) : Set.Icc x0 x1) : ℝ) - ((t i : Set.Icc x0 x1) : ℝ) :=
    sub_nonneg.mpr (htmono (Nat.le_succ i))
  have hheight_nonneg : 0 ≤ ((u (j + 1) : Set.Icc y0 y1) : ℝ) - ((u j : Set.Icc y0 y1) : ℝ) :=
    sub_nonneg.mpr (humono (Nat.le_succ j))
  have hwidth :
      ((t (i + 1) : Set.Icc x0 x1) : ℝ) - ((t i : Set.Icc x0 x1) : ℝ) ≤ δ / 2 := by
    have hcell :
        t (i + 1) ∈ Set.Icc (t i) (t (i + 1)) := ⟨htmono (Nat.le_succ i), le_rfl⟩
    simpa [t, step, abs_of_nonneg hwidth_nonneg] using
      (Set.Icc.abs_sub_addNSMul_le hx hstep_pos.le i hcell)
  have hheight :
      ((u (j + 1) : Set.Icc y0 y1) : ℝ) - ((u j : Set.Icc y0 y1) : ℝ) ≤ δ / 2 := by
    have hcell :
        u (j + 1) ∈ Set.Icc (u j) (u (j + 1)) := ⟨humono (Nat.le_succ j), le_rfl⟩
    simpa [u, step, abs_of_nonneg hheight_nonneg] using
      (Set.Icc.abs_sub_addNSMul_le hy hstep_pos.le j hcell)
  -- Every point in the closed grid cell stays inside the Lebesgue ball around the lower-left
  -- corner, so the whole cell lands in the chosen cover element.
  apply hk
  change dist p.1 corner.1 < δ
  exact rectanglePoint_dist_lt_of_mem_smallCell
    hp.1.1 hp.2.1 hp.1.2 hp.2.2 hwidth hheight hδpos

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: once a parameter patch is known to map
into the control ball around one image point, the local primitive at that image point can be
reused uniformly on the whole patch. -/
theorem patchPrimitiveData_of_ballMaps
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)} {s : Set ([[(a, a'), (b, b')]])}
    {p : [[(a, a'), (b, b')]]}
    (hlocal : HasPrimitiveWithinAt D ω (δ p))
    (hs_maps :
      MapsTo δ s
        (Metric.ball (δ p) (Classical.choose (HasPrimitiveWithinAt.exists_ball hlocal)))) :
    ∃ primitive : E → F,
      IsPrimitiveOn
          (Metric.ball (δ p) (Classical.choose (HasPrimitiveWithinAt.exists_ball hlocal)))
          ω primitive ∧
        Metric.ball (δ p) (Classical.choose (HasPrimitiveWithinAt.exists_ball hlocal)) ⊆ D ∧
        MapsTo δ s
          (Metric.ball (δ p) (Classical.choose (HasPrimitiveWithinAt.exists_ball hlocal))) := by
  let r : ℝ := Classical.choose (HasPrimitiveWithinAt.exists_ball hlocal)
  have hrD : Metric.ball (δ p) r ⊆ D := by
    exact (Classical.choose_spec (HasPrimitiveWithinAt.exists_ball hlocal)).2.1
  have hprimitiveOn : HasPrimitiveOn (Metric.ball (δ p) r) ω := by
    exact (Classical.choose_spec (HasPrimitiveWithinAt.exists_ball hlocal)).2.2
  rcases hprimitiveOn with ⟨primitive, hprimitive⟩
  -- Unpack the chosen primitive witness on the controlling ball and keep the same map target.
  refine ⟨primitive, ?_, ?_, ?_⟩
  · simpa [r] using hprimitive
  · simpa [r] using hrD
  · simpa [r] using hs_maps

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: each closed grid cell chosen by the
Lebesgue subdivision carries one codomain primitive on the owner ball that controls that cell. -/
theorem gridCellPrimitiveData
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)}
    {t : ℕ → Set.Icc (min a b) (max a b)}
    {u : ℕ → Set.Icc (min a' b') (max a' b')}
    {center : ℕ → ℕ → [[(a, a'), (b, b')]]}
    (hlocal : ∀ p : [[(a, a'), (b, b')]], HasPrimitiveWithinAt D ω (δ p))
    (hcell_maps :
      ∀ i j,
        MapsTo δ
          {p : [[(a, a'), (b, b')]] |
              p.1.1 ∈ Set.Icc ((t i : Set.Icc (min a b) (max a b)) : ℝ)
                (((t (i + 1) : Set.Icc (min a b) (max a b)) : ℝ)) ∧
              p.1.2 ∈ Set.Icc ((u j : Set.Icc (min a' b') (max a' b')) : ℝ)
                (((u (j + 1) : Set.Icc (min a' b') (max a' b')) : ℝ))}
          (Metric.ball (δ (center i j))
            (Classical.choose
              (HasPrimitiveWithinAt.exists_ball (hlocal (center i j)))))) :
    ∀ i j, ∃ primitive : E → F,
      IsPrimitiveOn
          (Metric.ball (δ (center i j))
            (Classical.choose
              (HasPrimitiveWithinAt.exists_ball (hlocal (center i j))))) ω primitive ∧
        Metric.ball (δ (center i j))
            (Classical.choose
              (HasPrimitiveWithinAt.exists_ball (hlocal (center i j)))) ⊆ D ∧
        MapsTo δ
          {p : [[(a, a'), (b, b')]] |
              p.1.1 ∈ Set.Icc ((t i : Set.Icc (min a b) (max a b)) : ℝ)
                (((t (i + 1) : Set.Icc (min a b) (max a b)) : ℝ)) ∧
              p.1.2 ∈ Set.Icc ((u j : Set.Icc (min a' b') (max a' b')) : ℝ)
                (((u (j + 1) : Set.Icc (min a' b') (max a' b')) : ℝ))}
          (Metric.ball (δ (center i j))
            (Classical.choose
              (HasPrimitiveWithinAt.exists_ball (hlocal (center i j))))) := by
  intro i j
  -- Specialize the generic control-ball extraction to the owner of the `(i,j)` grid cell.
  exact patchPrimitiveData_of_ballMaps (hlocal (center i j)) (hcell_maps i j)

attribute [local instance] Classical.propDecidable

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: an eventually right-saturated
monotone subdivision of a closed interval assigns at least one owner index to every point. -/
theorem subdivisionOwnerExists
    {l u : ℝ} (hlu : l ≤ u) {t : ℕ → Set.Icc l u}
    (htsat : ∃ m, ∀ n ≥ m, t n = ⟨u, ⟨hlu, le_rfl⟩⟩) :
    ∀ x : Set.Icc l u, ∃ n : ℕ, x ≤ t (n + 1) := by
  intro x
  let m : ℕ := Nat.find htsat
  have hm : ∀ n ≥ m, t n = ⟨u, ⟨hlu, le_rfl⟩⟩ := Nat.find_spec htsat
  refine ⟨m, ?_⟩
  -- The terminal plateau at the right endpoint is always an admissible owner witness.
  change (x : ℝ) ≤ ((t (m + 1) : Set.Icc l u) : ℝ)
  rw [hm (m + 1) (Nat.le_succ m)]
  exact x.2.2

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: the least subdivision index whose next
breakpoint lies to the right of `x`. -/
noncomputable def subdivisionOwner
    {l u : ℝ} (hlu : l ≤ u) (t : ℕ → Set.Icc l u)
    (htsat : ∃ m, ∀ n ≥ m, t n = ⟨u, ⟨hlu, le_rfl⟩⟩) (x : Set.Icc l u) : ℕ :=
  Nat.find (subdivisionOwnerExists hlu htsat x)

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: the owner index satisfies the defining
right-bound inequality. -/
theorem subdivisionOwner_spec
    {l u : ℝ} (hlu : l ≤ u) {t : ℕ → Set.Icc l u}
    (htsat : ∃ m, ∀ n ≥ m, t n = ⟨u, ⟨hlu, le_rfl⟩⟩) (x : Set.Icc l u) :
    x ≤ t (subdivisionOwner hlu t htsat x + 1) := by
  -- Unfold the owner definition and read off the minimal witness returned by `Nat.find`.
  exact Nat.find_spec (subdivisionOwnerExists hlu htsat x)

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: a positive owner index forces the
preceding breakpoint to lie strictly to the left of the point. -/
theorem subdivisionOwner_left_lt
    {l u : ℝ} (hlu : l ≤ u) {t : ℕ → Set.Icc l u}
    (htsat : ∃ m, ∀ n ≥ m, t n = ⟨u, ⟨hlu, le_rfl⟩⟩)
    {x : Set.Icc l u} (hx : 0 < subdivisionOwner hlu t htsat x) :
    t (subdivisionOwner hlu t htsat x) < x := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hx) with ⟨n, hn⟩
  have hnot : ¬ x ≤ t (n + 1) := by
    intro hle
    have hmin :
        subdivisionOwner hlu t htsat x ≤ n := by
      simpa [subdivisionOwner, hn] using
        (Nat.find_min' (subdivisionOwnerExists hlu htsat x) hle :
          Nat.find (subdivisionOwnerExists hlu htsat x) ≤ n)
    have hsucc_le : n.succ ≤ n := by
      simpa [hn] using hmin
    exact Nat.not_succ_le_self n hsucc_le
  have hlt : t (n + 1) < x := lt_of_not_ge hnot
  -- Reinterpret the predecessor inequality using the successor presentation of the owner.
  simpa [hn] using hlt

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: if `x` lies before the first breakpoint,
its owner is the initial interval. -/
theorem subdivisionOwner_eq_zero_of_le_first
    {l u : ℝ} (hlu : l ≤ u) {t : ℕ → Set.Icc l u}
    (htsat : ∃ m, ∀ n ≥ m, t n = ⟨u, ⟨hlu, le_rfl⟩⟩)
    {x : Set.Icc l u} (hx : x ≤ t 1) :
    subdivisionOwner hlu t htsat x = 0 := by
  have hle : subdivisionOwner hlu t htsat x ≤ 0 := by
    simpa [subdivisionOwner] using
      (Nat.find_min' (subdivisionOwnerExists hlu htsat x) hx :
        Nat.find (subdivisionOwnerExists hlu htsat x) ≤ 0)
  exact Nat.eq_zero_of_le_zero hle

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: on a strict gap between consecutive
breakpoints, the least owner is exactly the corresponding interval index. -/
theorem subdivisionOwner_eq_of_between
    {l u : ℝ} (hlu : l ≤ u) {t : ℕ → Set.Icc l u} (htmono : Monotone t)
    (htsat : ∃ m, ∀ n ≥ m, t n = ⟨u, ⟨hlu, le_rfl⟩⟩)
    {n : ℕ} {x : Set.Icc l u}
    (hxlower : t n < x) (hxupper : x ≤ t (n + 1)) :
    subdivisionOwner hlu t htsat x = n := by
  have hle : subdivisionOwner hlu t htsat x ≤ n :=
    Nat.find_min' (subdivisionOwnerExists hlu htsat x) hxupper
  have hge : n ≤ subdivisionOwner hlu t htsat x := by
    by_contra hlt
    have hlt' : subdivisionOwner hlu t htsat x < n := Nat.lt_of_not_ge hlt
    have hxowner : x ≤ t (subdivisionOwner hlu t htsat x + 1) :=
      subdivisionOwner_spec hlu htsat x
    have hbound : t (subdivisionOwner hlu t htsat x + 1) ≤ t n :=
      htmono (Nat.succ_le_of_lt hlt')
    exact (not_le_of_gt hxlower) (hxowner.trans hbound)
  -- The minimality witness and the strict lower bound pin the owner down uniquely.
  exact le_antisymm hle hge

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: on any preconnected parameter patch
mapped into two primitive domains, the pulled-back primitives differ by a single additive
constant. -/
theorem pullbackPrimitive_sub_eqOn_const_of_isPreconnected
    {ω : E → E →L[ℝ] F} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)} {s : Set ([[(a, a'), (b, b')]])}
    (hs_preconnected : IsPreconnected s)
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {primitiveF primitiveG : E → F}
    (hprimitiveF : IsPrimitiveOn U ω primitiveF)
    (hprimitiveG : IsPrimitiveOn V ω primitiveG)
    (hs_mapsU : MapsTo δ s U) (hs_mapsV : MapsTo δ s V) :
    ∃ c : F,
      EqOn (fun q ↦ primitiveG (δ q) - primitiveF (δ q)) (fun _ ↦ c) s := by
  classical
  by_cases hns : s.Nonempty
  · let diff : s → F := fun q ↦ primitiveG (δ q.1) - primitiveF (δ q.1)
    have hloc : IsLocallyConstant diff := by
      rw [IsLocallyConstant.iff_exists_open]
      intro p
      have hpU : δ p.1 ∈ U := hs_mapsU p.2
      have hpV : δ p.1 ∈ V := hs_mapsV p.2
      rcases local_sub_eq_const_on_ball_of_common_primitive hU hV hpU hpV
          hprimitiveF hprimitiveG with
        ⟨r, hr, c, hc⟩
      let t : Set s := {q : s | δ q.1 ∈ Metric.ball (δ p.1) r}
      refine ⟨t, ?_, ?_, ?_⟩
      · -- Pull back the codomain overlap ball to a neighborhood in the subtype `s`.
        simpa [t] using
          ((δ.continuous.comp continuous_subtype_val).isOpen_preimage
            (Metric.ball (δ p.1) r) Metric.isOpen_ball)
      · show δ p.1 ∈ Metric.ball (δ p.1) r
        exact Metric.mem_ball_self hr
      · intro q hq
        have hqball : δ q.1 ∈ Metric.ball (δ p.1) r := hq
        have hpball : δ p.1 ∈ Metric.ball (δ p.1) r := Metric.mem_ball_self hr
        -- On this neighborhood, both pullbacks evaluate to the same constant `c`.
        calc
          diff q = c := by
            simpa [diff] using hc hqball
          _ = diff p := by
            simpa [diff] using (hc hpball).symm
    haveI : PreconnectedSpace s := Subtype.preconnectedSpace hs_preconnected
    let q₀ : s := ⟨Classical.choose hns, Classical.choose_spec hns⟩
    refine ⟨diff q₀, ?_⟩
    intro q hq
    -- A locally constant function on a preconnected subtype is globally constant.
    have hEqSubtype : diff ⟨q, hq⟩ = diff q₀ :=
      hloc.apply_eq_of_preconnectedSpace _ _
    simpa [diff, q₀] using hEqSubtype
  · refine ⟨0, ?_⟩
    intro q hq
    exact (hns ⟨q, hq⟩).elim

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: on a preconnected parameter patch, two
shifted pullback primitives that already agree at one point agree everywhere on that patch. -/
theorem shiftedPullbackPrimitive_eqOn_of_isPreconnected_of_eqAt
    {ω : E → E →L[ℝ] F} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)} {s : Set ([[(a, a'), (b, b')]])}
    (hs_preconnected : IsPreconnected s)
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {primitiveF primitiveG : E → F}
    (hprimitiveF : IsPrimitiveOn U ω primitiveF)
    (hprimitiveG : IsPrimitiveOn V ω primitiveG)
    (hs_mapsU : MapsTo δ s U) (hs_mapsV : MapsTo δ s V)
    {kF kG : F} {q₀ : [[(a, a'), (b, b')]]} (hq₀ : q₀ ∈ s)
    (heq₀ : primitiveG (δ q₀) + kG = primitiveF (δ q₀) + kF) :
    EqOn (fun q ↦ primitiveG (δ q) + kG) (fun q ↦ primitiveF (δ q) + kF) s := by
  rcases pullbackPrimitive_sub_eqOn_const_of_isPreconnected
      (δ := δ) (s := s) hs_preconnected hU hV hprimitiveF hprimitiveG hs_mapsU hs_mapsV with
    ⟨c, hc⟩
  have hshiftAtBase : primitiveG (δ q₀) - primitiveF (δ q₀) = kF - kG := by
    -- Repackage the base-point equality as the corresponding difference identity.
    exact (sub_eq_sub_iff_add_eq_add).mpr (by
      simpa [add_comm, add_left_comm, add_assoc] using heq₀)
  have hc_value : c = kF - kG := by
    calc
      c = primitiveG (δ q₀) - primitiveF (δ q₀) := (hc hq₀).symm
      _ = kF - kG := hshiftAtBase
  intro q hq
  have hdiff : primitiveG (δ q) - primitiveF (δ q) = kF - kG := by
    calc
      primitiveG (δ q) - primitiveF (δ q) = c := hc hq
      _ = kF - kG := hc_value
  -- Replace the difference constant by the value fixed at the base point and simplify.
  exact (by
    have hsum : primitiveG (δ q) + kG = kF + primitiveF (δ q) :=
      (sub_eq_sub_iff_add_eq_add).mp hdiff
    simpa [add_comm, add_left_comm, add_assoc] using hsum)

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: if an open cover already carries local
pullback primitives that agree exactly on overlaps, then the `ContinuousMap.liftCover` glued from
those local maps is a primitive following `δ` on the whole rectangle. -/
theorem primitiveFollowingOnRectangle_of_liftCover
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)} {ι : Type*}
    {S : ι → Set ([[(a, a'), (b, b')]])} {φ : (i : ι) → C(↑(S i), F)}
    (hS_open : ∀ i : ι, IsOpen (S i))
    (hφ :
      ∀ (i j : ι) (x : [[(a, a'), (b, b')]]) (hxi : x ∈ S i) (hxj : x ∈ S j),
        φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
    (hS : ∀ x : [[(a, a'), (b, b')]], ∃ i, S i ∈ nhds x)
    (hprimitive :
      ∀ i : ι, ∃ U : Set E, IsOpen U ∧ U ⊆ D ∧ MapsTo δ (S i) U ∧
        ∃ primitive : E → F,
          IsPrimitiveOn U ω primitive ∧
            ∀ q : S i, φ i q = primitive (δ q)) :
    IsPrimitiveFollowingOnRectangle ω D δ (ContinuousMap.liftCover S φ hφ hS) := by
  intro p
  rcases hS p with ⟨i, hi⟩
  have hpi : p ∈ S i := mem_of_mem_nhds hi
  rcases hprimitive i with ⟨U, hU_open, hUD, hmaps, primitive, hprimitive, hEq⟩
  refine ⟨S i, hS_open i, hpi, U, hU_open, hmaps hpi, hUD, hmaps, primitive, hprimitive, ?_⟩
  intro q hq
  -- Rewrite the glued map by the chosen local chart and then use the local primitive witness.
  calc
    ContinuousMap.liftCover S φ hφ hS q = φ i ⟨q, hq⟩ := by
      simpa using
        (ContinuousMap.liftCover_coe (S := S) (φ := φ) (hφ := hφ) (hS := hS)
          (i := i) (x := ⟨q, hq⟩))
    _ = primitive (δ q) := hEq ⟨q, hq⟩

/-- Helper for Cartan section05 0021_Lemma_II_1_extra_12: once one primitive following the
rectangle map exists, every other one differs from it by an additive constant. -/
theorem primitiveFollowingOnRectangle_unique_up_to_constant
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)}
    {f g : C([[(a, a'), (b, b')]], F)}
    (hf : IsPrimitiveFollowingOnRectangle ω D δ f)
    (hg : IsPrimitiveFollowingOnRectangle ω D δ g) :
    ∃ c : F, g = f + ContinuousMap.const _ c := by
  -- The rectangle subtype is preconnected because it is the product of two closed intervals.
  haveI : PreconnectedSpace ([[(a, a'), (b, b')]]) := by
    refine Subtype.preconnectedSpace ?_
    simpa [Set.uIcc_prod_uIcc] using
      ((convex_uIcc a b).prod (convex_uIcc a' b')).isPreconnected
  by_cases hnonempty : Nonempty ([[(a, a'), (b, b')]])
  · let p₀ : [[(a, a'), (b, b')]] := Classical.choice hnonempty
    let c : F := g p₀ - f p₀
    have hloc :
        IsLocallyConstant (fun p : [[(a, a'), (b, b')]] ↦ g p - f p) :=
      primitiveFollowingOnRectangle_difference_isLocallyConstant hf hg
    refine ⟨c, ?_⟩
    ext p
    have hconst : g p - f p = c := by
      simpa [c, p₀] using hloc.apply_eq_of_preconnectedSpace p p₀
    have hEq : g p = c + f p := (sub_eq_iff_eq_add).mp hconst
    simpa [c, add_comm, add_left_comm, add_assoc] using hEq
  · refine ⟨0, ?_⟩
    ext p
    exact (hnonempty ⟨p⟩).elim

-- Proof sketch: cover the compact rectangle by finitely many open patches on which `δ` lands in a
-- neighborhood admitting a primitive of `ω`, glue the resulting local pullback primitives first
-- along one coordinate direction and then along the other, and compare two global primitives by
-- showing their difference is locally constant and hence constant on the connected rectangle.
/-- Cartan section05 0021_Lemma_II_1_extra_12: if every point of the closed rectangle has a neighborhood on which `δ`
lands in a domain where `ω` admits a primitive, then there exists a primitive of `ω` following `δ`
on the whole rectangle, and it is unique up to addition of a constant on that rectangle. -/
theorem primitive_following_on_rectangle_exists_and_unique_up_to_constant
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)}
    (hlocal : ∀ p : [[(a, a'), (b, b')]], HasPrimitiveWithinAt D ω (δ p)) :
    ∃ f : C([[(a, a'), (b, b')]], F),
      IsPrimitiveFollowingOnRectangle ω D δ f ∧
        ∀ g : C([[(a, a'), (b, b')]], F), IsPrimitiveFollowingOnRectangle ω D δ g →
          ∃ c : F, g = f + ContinuousMap.const _ c := by
  -- Route correction: the uniqueness half is now isolated in
  -- `primitiveFollowingOnRectangle_unique_up_to_constant`. The two reusable bridges now proved are
  -- the small-cell metric estimate `rectanglePoint_dist_lt_of_mem_smallCell` and the overlap
  -- normalization lemma `pullbackPrimitive_sub_eqOn_const_of_isPreconnected`; the remaining
  -- blocker is the exact-overlap normalization and gluing step after the finite grid cover is
  -- chosen.
  classical
  let radius : [[(a, a'), (b, b')]] → ℝ := fun p =>
    Classical.choose (HasPrimitiveWithinAt.exists_ball (hlocal p))
  let cover : [[(a, a'), (b, b')]] → Set ([[(a, a'), (b, b')]]) := fun p =>
    δ ⁻¹' Metric.ball (δ p) (radius p)
  have hradius_pos : ∀ p : [[(a, a'), (b, b')]], 0 < radius p := by
    intro p
    exact (Classical.choose_spec (HasPrimitiveWithinAt.exists_ball (hlocal p))).1
  have hcover_open : ∀ p : [[(a, a'), (b, b')]], IsOpen (cover p) := by
    intro p
    refine δ.continuous.isOpen_preimage _ Metric.isOpen_ball
  have hcover_univ :
      (univ : Set ([[(a, a'), (b, b')]])) ⊆ ⋃ p : [[(a, a'), (b, b')]], cover p := by
    intro p _
    refine mem_iUnion.2 ⟨p, ?_⟩
    exact Metric.mem_ball_self (hradius_pos p)
  -- The finite grid/owner stage is now explicit: every closed grid cell is controlled by one
  -- local primitive ball coming from `hlocal`.
  obtain ⟨t, ht0, htmono, htsat, ht_strict_of_ne_right, u, hu0, humono, husat,
      hu_strict_of_ne_right, hcell_cover⟩ :=
    rectangleLebesgueSubdivision (c := cover) hcover_open hcover_univ
  let center : ℕ → ℕ → [[(a, a'), (b, b')]] := fun i j =>
    Classical.choose (hcell_cover i j)
  let cell : ℕ → ℕ → Set ([[(a, a'), (b, b')]]) := fun i j =>
    {p : [[(a, a'), (b, b')]] |
        p.1.1 ∈ Set.Icc ((t i : Set.Icc (min a b) (max a b)) : ℝ)
          (((t (i + 1) : Set.Icc (min a b) (max a b)) : ℝ)) ∧
        p.1.2 ∈ Set.Icc ((u j : Set.Icc (min a' b') (max a' b')) : ℝ)
          (((u (j + 1) : Set.Icc (min a' b') (max a' b')) : ℝ))}
  let ownerBall : ℕ → ℕ → Set E := fun i j =>
    Metric.ball (δ (center i j))
      (Classical.choose (HasPrimitiveWithinAt.exists_ball (hlocal (center i j))))
  have hcell_maps :
      ∀ i j, cell i j ⊆ cover (center i j) := by
    intro i j
    simpa [cell] using Classical.choose_spec (hcell_cover i j)
  have hcell_mapsTo :
      ∀ i j, MapsTo δ (cell i j) (ownerBall i j) := by
    intro i j q hq
    -- Rewrite the cell-ownership statement from the preimage cover to a direct `MapsTo` fact.
    simpa [cell, ownerBall, cover, radius] using hcell_maps i j hq
  have hcell_primitive :
      ∀ i j, ∃ primitive : E → F,
        IsPrimitiveOn (ownerBall i j) ω primitive ∧
          ownerBall i j ⊆ D ∧ MapsTo δ (cell i j) (ownerBall i j) := by
    -- Route correction: reuse the packaged grid-cell extraction so the main theorem now focuses
    -- only on the row and rectangle gluing steps.
    exact gridCellPrimitiveData (hlocal := hlocal) (δ := δ) (t := t) (u := u)
      (center := center) hcell_mapsTo
  let primitive : ℕ → ℕ → E → F := fun i j => Classical.choose (hcell_primitive i j)
  have hprimitive :
      ∀ i j, IsPrimitiveOn (ownerBall i j) ω (primitive i j) := by
    intro i j
    exact (Classical.choose_spec (hcell_primitive i j)).1
  have hownerBall_sub :
      ∀ i j, ownerBall i j ⊆ D := by
    intro i j
    exact (Classical.choose_spec (hcell_primitive i j)).2.1
  let cornerX : ℕ → ℕ → [[(a, a'), (b, b')]] := fun i j =>
    ⟨(((t (i + 1) : Set.Icc (min a b) (max a b)) : ℝ),
        ((u j : Set.Icc (min a' b') (max a' b')) : ℝ)), by
      simpa [Set.uIcc_prod_uIcc, Set.mem_uIcc] using
        (show ((((t (i + 1) : Set.Icc (min a b) (max a b)) : ℝ),
            ((u j : Set.Icc (min a' b') (max a' b')) : ℝ)) : ℝ × ℝ) ∈
            Set.uIcc a b ×ˢ Set.uIcc a' b' from
          ⟨by simpa [Set.mem_uIcc] using (t (i + 1)).2,
            by simpa [Set.mem_uIcc] using (u j).2⟩)⟩
  have hcornerX_mem_left : ∀ i j, cornerX i j ∈ cell i j := by
    intro i j
    refine ⟨?_, ?_⟩
    · exact ⟨htmono (Nat.le_succ i), le_rfl⟩
    · exact ⟨le_rfl, humono (Nat.le_succ j)⟩
  have hcornerX_mem_right : ∀ i j, cornerX i j ∈ cell (i + 1) j := by
    intro i j
    refine ⟨?_, ?_⟩
    · exact ⟨le_rfl, htmono (Nat.le_succ (i + 1))⟩
    · exact ⟨le_rfl, humono (Nat.le_succ j)⟩
  have hoverlapX :
      ∀ i j, ∃ r : ℝ, 0 < r ∧ ∃ c : F,
        EqOn
          (fun q ↦ primitive (i + 1) j (δ q) + ((0 : F) - c))
          (fun q ↦ primitive i j (δ q) + (0 : F))
          (δ ⁻¹' Metric.ball (δ (cornerX i j)) r) := by
    intro i j
    -- Adjacent horizontal cells share the corner `cornerX i j`, so the two chosen codomain
    -- primitives already agree up to a constant on a smaller preimage ball around that point.
    refine shiftedPullbackPrimitive_eqOn_preimageBall_of_common_primitive
      (p := cornerX i j) (U := ownerBall i j) (V := ownerBall (i + 1) j)
      (primitiveF := primitive i j) (primitiveG := primitive (i + 1) j) (k := (0 : F))
      Metric.isOpen_ball Metric.isOpen_ball ?_ ?_ (hprimitive i j) (hprimitive (i + 1) j)
    · exact (hcell_mapsTo i j) (hcornerX_mem_left i j)
    · exact (hcell_mapsTo (i + 1) j) (hcornerX_mem_right i j)
  obtain ⟨overlapRadiusX, overlapConstX, kx, hoverlapRadiusX_pos, hoverlapEqX,
      hkx_zero, hkx_succ, hshiftEqX⟩ :=
    horizontalShiftData (δ := δ) (primitive := primitive) (cornerX := cornerX) hoverlapX
  have hshiftedPrimitive :
      ∀ i j, IsPrimitiveOn (ownerBall i j) ω (fun z ↦ primitive i j z + kx i j) := by
    intro i j
    -- Each row normalization only adds a constant, so the primitive identity is unchanged.
    exact (hprimitive i j).addConst (kx i j)
  have hxminmax : min a b ≤ max a b := by
    simp
  let ownerX : Set.Icc (min a b) (max a b) → ℕ :=
    subdivisionOwner hxminmax t htsat
  have hownerX_spec : ∀ x : Set.Icc (min a b) (max a b), x ≤ t (ownerX x + 1) := by
    intro x
    -- Use the shared least-owner API so the later y-owner stage can reuse the same lemmas.
    simpa [ownerX] using subdivisionOwner_spec hxminmax htsat x
  have hownerX_left_lt :
      ∀ {x : Set.Icc (min a b) (max a b)}, 0 < ownerX x → t (ownerX x) < x := by
    intro x hx
    simpa [ownerX] using
      (subdivisionOwner_left_lt hxminmax htsat (x := x) hx)
  have hownerX_eq_zero_of_le_first :
      ∀ {x : Set.Icc (min a b) (max a b)}, x ≤ t 1 → ownerX x = 0 := by
    intro x hx
    simpa [ownerX] using subdivisionOwner_eq_zero_of_le_first hxminmax htsat hx
  have hownerX_eq_of_between :
      ∀ {n : ℕ} {x : Set.Icc (min a b) (max a b)},
        0 < n → t n < x → x ≤ t (n + 1) → ownerX x = n := by
    intro n x hn hxlower hxupper
    simpa [ownerX] using
      (subdivisionOwner_eq_of_between hxminmax htmono htsat hxlower hxupper)
  let xCoord : [[(a, a'), (b, b')]] → Set.Icc (min a b) (max a b) := fun p =>
    ⟨p.1.1, by
      have hp : ((p : ℝ × ℝ) ∈ Set.uIcc (a, a') (b, b')) := p.2
      have hp' : ((p : ℝ × ℝ) ∈ Set.uIcc a b ×ˢ Set.uIcc a' b') := by
        simpa [Set.uIcc_prod_uIcc] using hp
      exact hp'.1⟩
  let rowBand : ℕ → Set ([[(a, a'), (b, b')]]) := fun j =>
    {p : [[(a, a'), (b, b')]] |
      p.1.2 ∈ Set.Icc ((u j : Set.Icc (min a' b') (max a' b')) : ℝ)
        (((u (j + 1) : Set.Icc (min a' b') (max a' b')) : ℝ))}
  have hownerX_mem_cell :
      ∀ {j : ℕ} {p : [[(a, a'), (b, b')]]}, p ∈ rowBand j →
        p ∈ cell (ownerX (xCoord p)) j := by
    intro j p hp
    refine ⟨?_, hp⟩
    have hleft : t (ownerX (xCoord p)) ≤ xCoord p := by
      by_cases hzero : ownerX (xCoord p) = 0
      · have hxleft : ((t 0 : Set.Icc (min a b) (max a b)) : ℝ) ≤ (xCoord p : ℝ) := by
          simpa [ht0] using (xCoord p).2.1
        simpa [hzero] using hxleft
      · have hpos : 0 < ownerX (xCoord p) := Nat.pos_of_ne_zero hzero
        exact (hownerX_left_lt hpos).le
    have hright : xCoord p ≤ t (ownerX (xCoord p) + 1) := hownerX_spec (xCoord p)
    exact ⟨hleft, hright⟩
  let sharedVerticalEdge : ℕ → ℕ → Set ([[(a, a'), (b, b')]]) := fun i j =>
    cell i j ∩ cell (i + 1) j
  have hsharedVerticalEdge_sub_left :
      ∀ i j, sharedVerticalEdge i j ⊆ cell i j := by
    intro i j p hp
    exact hp.1
  have hsharedVerticalEdge_sub_right :
      ∀ i j, sharedVerticalEdge i j ⊆ cell (i + 1) j := by
    intro i j p hp
    exact hp.2
  have hcornerX_mem_sharedVerticalEdge :
      ∀ i j, cornerX i j ∈ sharedVerticalEdge i j := by
    intro i j
    exact ⟨hcornerX_mem_left i j, hcornerX_mem_right i j⟩
  have hsharedVerticalEdge_preconnected :
      ∀ i j, IsPreconnected (sharedVerticalEdge i j) := by
    intro i j
    have hshared_eq_vertical :
        sharedVerticalEdge i j =
          {p : [[(a, a'), (b, b')]] |
            p.1.1 = ((t (i + 1) : Set.Icc (min a b) (max a b)) : ℝ) ∧
              p.1.2 ∈ Set.Icc ((u j : Set.Icc (min a' b') (max a' b')) : ℝ)
                (((u (j + 1) : Set.Icc (min a' b') (max a' b')) : ℝ))} := by
      ext p
      constructor
      · intro hp
        exact ⟨le_antisymm hp.1.1.2 hp.2.1.1, hp.1.2⟩
      · intro hp
        refine ⟨?_, ?_⟩
        · exact ⟨⟨by simpa [hp.1] using htmono (Nat.le_succ i), by simpa [hp.1]⟩, hp.2⟩
        · exact ⟨⟨by simpa [hp.1], by simpa [hp.1] using htmono (Nat.le_succ (i + 1))⟩, hp.2⟩
    -- Rewrite the shared edge to the explicit vertical segment and apply the generic geometry
    -- helper once, instead of rebuilding the parametrization here.
    rw [hshared_eq_vertical]
    exact isPreconnected_verticalSegmentWithinRectangle
      (hx := by simpa [Set.mem_uIcc] using (t (i + 1)).2)
      (hy₀ := by simpa [Set.mem_uIcc] using (u j).2)
      (hy₁ := by simpa [Set.mem_uIcc] using (u (j + 1)).2)
  have hshiftEqX_sharedVerticalEdge :
      ∀ i j,
        EqOn
          (fun q ↦ primitive (i + 1) j (δ q) + kx (i + 1) j)
          (fun q ↦ primitive i j (δ q) + kx i j)
          (sharedVerticalEdge i j) := by
    intro i j
    -- Upgrade the corner equality to the whole shared edge by preconnectedness.
    refine shiftedPullbackPrimitive_eqOn_of_isPreconnected_of_eqAt
      (δ := δ) (s := sharedVerticalEdge i j) (U := ownerBall i j) (V := ownerBall (i + 1) j)
      (primitiveF := primitive i j) (primitiveG := primitive (i + 1) j)
      (hU := Metric.isOpen_ball) (hV := Metric.isOpen_ball)
      (hprimitiveF := hprimitive i j) (hprimitiveG := hprimitive (i + 1) j)
      (hs_preconnected := hsharedVerticalEdge_preconnected i j)
      (hs_mapsU := fun q hq ↦ hcell_mapsTo i j (hsharedVerticalEdge_sub_left i j hq))
      (hs_mapsV := fun q hq ↦ hcell_mapsTo (i + 1) j (hsharedVerticalEdge_sub_right i j hq))
      (q₀ := cornerX i j) (hq₀ := hcornerX_mem_sharedVerticalEdge i j) ?_
    exact hshiftEqX i j (Metric.mem_ball_self (hoverlapRadiusX_pos i j))
  have rowBreakpointPatchEqOn :
      ∀ {j n : ℕ} (q : ↑(rowBand j)), q.1 ∈ sharedVerticalEdge n j →
        ∃ s : Set (↑(rowBand j)),
          IsOpen s ∧ q ∈ s ∧
          MapsTo (fun x : ↑(rowBand j) ↦ δ x.1) s (ownerBall n j) ∧
          MapsTo (fun x : ↑(rowBand j) ↦ δ x.1) s (ownerBall (n + 1) j) ∧
          EqOn
            (fun x : ↑(rowBand j) ↦ primitive (n + 1) j (δ x.1) + kx (n + 1) j)
            (fun x : ↑(rowBand j) ↦ primitive n j (δ x.1) + kx n j) s := by
    intro j n q hqedge
    have hqU : δ q.1 ∈ ownerBall n j :=
      hcell_mapsTo n j (hsharedVerticalEdge_sub_left n j hqedge)
    have hqV : δ q.1 ∈ ownerBall (n + 1) j :=
      hcell_mapsTo (n + 1) j (hsharedVerticalEdge_sub_right n j hqedge)
    -- Compare the two shifted codomain primitives on a small ball centered at `δ q.1`.
    rcases local_sub_eq_const_on_ball_of_common_primitive
        (U := ownerBall n j) (V := ownerBall (n + 1) j) (z₀ := δ q.1)
        Metric.isOpen_ball Metric.isOpen_ball hqU hqV
        (hshiftedPrimitive n j) (hshiftedPrimitive (n + 1) j) with
      ⟨rEq, hrEq, c, hc⟩
    rcases Metric.isOpen_iff.mp (Metric.isOpen_ball : IsOpen (ownerBall n j)) (δ q.1) hqU with
      ⟨rU, hrU, hballU⟩
    rcases Metric.isOpen_iff.mp (Metric.isOpen_ball : IsOpen (ownerBall (n + 1) j)) (δ q.1) hqV with
      ⟨rV, hrV, hballV⟩
    let r : ℝ := min rEq (min rU rV)
    have hr : 0 < r := by
      exact lt_min hrEq (lt_min hrU hrV)
    have hr_le_rEq : r ≤ rEq := min_le_left _ _
    have hr_le_rU : r ≤ rU := le_trans (min_le_right _ _) (min_le_left _ _)
    have hr_le_rV : r ≤ rV := le_trans (min_le_right _ _) (min_le_right _ _)
    have hc_zero : c = 0 := by
      have hqeq :
          primitive (n + 1) j (δ q.1) + kx (n + 1) j =
            primitive n j (δ q.1) + kx n j :=
        hshiftEqX_sharedVerticalEdge n j hqedge
      calc
        c = (primitive (n + 1) j (δ q.1) + kx (n + 1) j) -
              (primitive n j (δ q.1) + kx n j) := by
                symm
                simpa using hc (Metric.mem_ball_self hrEq)
        _ = 0 := by
              rw [hqeq]
              abel
    let s : Set (↑(rowBand j)) := {x : ↑(rowBand j) | δ x.1 ∈ Metric.ball (δ q.1) r}
    have hs_open : IsOpen s := by
      -- Pull the codomain ball back to the fixed row band.
      simpa [s] using
        ((δ.continuous.comp continuous_subtype_val).isOpen_preimage
          (Metric.ball (δ q.1) r) Metric.isOpen_ball)
    have hqs : q ∈ s := by
      exact Metric.mem_ball_self hr
    have hs_mapsU : MapsTo (fun x : ↑(rowBand j) ↦ δ x.1) s (ownerBall n j) := by
      intro x hx
      exact hballU ((Metric.ball_subset_ball hr_le_rU) hx)
    have hs_mapsV : MapsTo (fun x : ↑(rowBand j) ↦ δ x.1) s (ownerBall (n + 1) j) := by
      intro x hx
      exact hballV ((Metric.ball_subset_ball hr_le_rV) hx)
    have hs_eq :
        EqOn
          (fun x : ↑(rowBand j) ↦ primitive (n + 1) j (δ x.1) + kx (n + 1) j)
          (fun x : ↑(rowBand j) ↦ primitive n j (δ x.1) + kx n j) s := by
      intro x hx
      have hdiff :
          (primitive (n + 1) j (δ x.1) + kx (n + 1) j) -
              (primitive n j (δ x.1) + kx n j) = 0 := by
        have hdiffEq := hc ((Metric.ball_subset_ball hr_le_rEq) hx)
        simpa [hc_zero] using hdiffEq
      exact sub_eq_zero.mp hdiff
    exact ⟨s, hs_open, hqs, hs_mapsU, hs_mapsV, hs_eq⟩
  let rowX : ∀ j, ↑(rowBand j) → ℝ := fun _ x =>
    ((xCoord x.1 : Set.Icc (min a b) (max a b)) : ℝ)
  have hrowX_cont : ∀ j, Continuous (rowX j) := by
    intro j
    -- The row coordinate is just the first projection on the row-band subtype.
    change Continuous fun x : ↑(rowBand j) => x.1.1.1
    fun_prop
  let rowF0 : ∀ j, ↑(rowBand j) → F := fun j x =>
    primitive (ownerX (xCoord x.1)) j (δ x.1) + kx (ownerX (xCoord x.1)) j
  have rowOwnerLocalPrimitiveAt :
      ∀ {j : ℕ} (q : ↑(rowBand j)),
        ∃ s : Set (↑(rowBand j)), IsOpen s ∧ q ∈ s ∧
          ∃ U : Set E, IsOpen U ∧ δ q.1 ∈ U ∧ U ⊆ D ∧
            MapsTo (fun x : ↑(rowBand j) ↦ δ x.1) s U ∧
            ∃ primitiveOn : E → F,
              IsPrimitiveOn U ω primitiveOn ∧
                EqOn (rowF0 j) (fun x : ↑(rowBand j) ↦ primitiveOn (δ x.1)) s := by
    intro j q
    let n : ℕ := ownerX (xCoord q.1)
    have hqleft : ((t n : Set.Icc (min a b) (max a b)) : ℝ) ≤ (xCoord q.1 : ℝ) := by
      by_cases hn : n = 0
      · have hxleft : ((t 0 : Set.Icc (min a b) (max a b)) : ℝ) ≤ (xCoord q.1 : ℝ) := by
          simpa [ht0] using (xCoord q.1).2.1
        simpa [n, hn] using hxleft
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        exact (hownerX_left_lt (x := xCoord q.1) (by simpa [n] using hnpos)).le
    have hqright : (xCoord q.1 : ℝ) ≤ ((t (n + 1) : Set.Icc (min a b) (max a b)) : ℝ) := by
      simpa [n] using (hownerX_spec (xCoord q.1))
    have hqcell : q.1 ∈ cell n j := by
      simpa [n] using (hownerX_mem_cell (j := j) q.2)
    have hqowner : δ q.1 ∈ ownerBall n j := hcell_mapsTo n j hqcell
    by_cases hstrict :
        (xCoord q.1 : ℝ) < ((t (n + 1) : Set.Icc (min a b) (max a b)) : ℝ)
    · by_cases hn : n = 0
      · let s : Set (↑(rowBand j)) :=
          ((fun x : ↑(rowBand j) ↦ δ x.1) ⁻¹' ownerBall 0 j) ∩
            rowX j ⁻¹' Set.Iio ((t 1 : Set.Icc (min a b) (max a b)) : ℝ)
        have hs_open : IsOpen s := by
          -- Stay inside the first owner ball and before the first breakpoint.
          simpa [s] using
            (((δ.continuous.comp continuous_subtype_val).isOpen_preimage
              (ownerBall 0 j) Metric.isOpen_ball).inter
                ((hrowX_cont j).isOpen_preimage _ isOpen_Iio))
        have hqs : q ∈ s := by
          refine ⟨?_, ?_⟩
          · simpa [s, n, hn] using hqowner
          · simpa [s, rowX, n, hn] using hstrict
        have hs_eq :
            EqOn (rowF0 j)
              (fun x : ↑(rowBand j) ↦ primitive 0 j (δ x.1) + kx 0 j) s := by
          intro x hx
          have hown : ownerX (xCoord x.1) = 0 := by
            have hxle : xCoord x.1 ≤ t 1 := by
              exact le_of_lt (by simpa [rowX] using hx.2)
            exact hownerX_eq_zero_of_le_first hxle
          simp [rowF0, hown]
        refine ⟨s, hs_open, hqs, ownerBall 0 j, Metric.isOpen_ball, ?_, hownerBall_sub 0 j,
          ?_, (fun z ↦ primitive 0 j z + kx 0 j), hshiftedPrimitive 0 j, ?_⟩
        · simpa [n, hn] using hqowner
        · intro x hx
          exact hx.1
        · intro x hx
          simpa [Function.comp] using hs_eq hx
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let s : Set (↑(rowBand j)) :=
          (((fun x : ↑(rowBand j) ↦ δ x.1) ⁻¹' ownerBall n j) ∩
              rowX j ⁻¹' Set.Ioi ((t n : Set.Icc (min a b) (max a b)) : ℝ)) ∩
            rowX j ⁻¹' Set.Iio ((t (n + 1) : Set.Icc (min a b) (max a b)) : ℝ)
        have hs_open : IsOpen s := by
          -- Away from a breakpoint, the owner index is locally constant on the row.
          simpa [s, inter_assoc] using
            ((((δ.continuous.comp continuous_subtype_val).isOpen_preimage
                (ownerBall n j) Metric.isOpen_ball).inter
                  ((hrowX_cont j).isOpen_preimage _ isOpen_Ioi)).inter
                ((hrowX_cont j).isOpen_preimage _ isOpen_Iio))
        have hqs : q ∈ s := by
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · exact hqowner
          · simpa [rowX] using (hownerX_left_lt (x := xCoord q.1) (by simpa [n] using hnpos))
          · simpa [rowX] using hstrict
        have hs_eq :
            EqOn (rowF0 j)
              (fun x : ↑(rowBand j) ↦ primitive n j (δ x.1) + kx n j) s := by
          intro x hx
          have hown : ownerX (xCoord x.1) = n := by
            have hxlower : ((t n : Set.Icc (min a b) (max a b)) : ℝ) < (xCoord x.1 : ℝ) := by
              simpa [rowX] using hx.1.2
            have hxupper : xCoord x.1 ≤ t (n + 1) := by
              exact le_of_lt (by simpa [rowX] using hx.2)
            exact hownerX_eq_of_between hnpos hxlower hxupper
          simp [rowF0, hown]
        refine ⟨s, hs_open, hqs, ownerBall n j, Metric.isOpen_ball, hqowner, hownerBall_sub n j,
          ?_, (fun z ↦ primitive n j z + kx n j), hshiftedPrimitive n j, ?_⟩
        · intro x hx
          exact hx.1.1
        · intro x hx
          simpa [Function.comp] using hs_eq hx
    · have hbreak :
          (xCoord q.1 : ℝ) = ((t (n + 1) : Set.Icc (min a b) (max a b)) : ℝ) :=
        le_antisymm hqright (le_of_not_gt hstrict)
      by_cases hqrightmost : (xCoord q.1 : ℝ) = max a b
      · by_cases hn : n = 0
        · let s : Set (↑(rowBand j)) := (fun x : ↑(rowBand j) ↦ δ x.1) ⁻¹' ownerBall 0 j
          have hs_eq :
              EqOn (rowF0 j)
                (fun x : ↑(rowBand j) ↦ primitive 0 j (δ x.1) + kx 0 j) s := by
            intro x hx
            have hown : ownerX (xCoord x.1) = 0 := by
              have hxle : xCoord x.1 ≤ t 1 := by
                calc
                  (xCoord x.1 : ℝ) ≤ max a b := (xCoord x.1).2.2
                  _ = (xCoord q.1 : ℝ) := hqrightmost.symm
                  _ = ((t 1 : Set.Icc (min a b) (max a b)) : ℝ) := by
                        simpa [n, hn] using hbreak
              exact hownerX_eq_zero_of_le_first hxle
            simp [rowF0, hown]
          refine ⟨s,
            ((δ.continuous.comp continuous_subtype_val).isOpen_preimage
              (ownerBall 0 j) Metric.isOpen_ball),
            ?_, ownerBall 0 j, Metric.isOpen_ball, ?_, hownerBall_sub 0 j, ?_,
            (fun z ↦ primitive 0 j z + kx 0 j), hshiftedPrimitive 0 j, ?_⟩
          · simpa [s, n, hn] using hqowner
          · simpa [n, hn] using hqowner
          · intro x hx
            exact hx
          · intro x hx
            simpa [Function.comp] using hs_eq hx
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          let s : Set (↑(rowBand j)) :=
            ((fun x : ↑(rowBand j) ↦ δ x.1) ⁻¹' ownerBall n j) ∩
              rowX j ⁻¹' Set.Ioi ((t n : Set.Icc (min a b) (max a b)) : ℝ)
          have hs_open : IsOpen s := by
            -- At the terminal breakpoint, only the last active owner matters.
            simpa [s] using
              (((δ.continuous.comp continuous_subtype_val).isOpen_preimage
                  (ownerBall n j) Metric.isOpen_ball).inter
                ((hrowX_cont j).isOpen_preimage _ isOpen_Ioi))
          have hqs : q ∈ s := by
            refine ⟨hqowner, ?_⟩
            simpa [rowX] using (hownerX_left_lt (x := xCoord q.1) (by simpa [n] using hnpos))
          have hs_eq :
              EqOn (rowF0 j)
                (fun x : ↑(rowBand j) ↦ primitive n j (δ x.1) + kx n j) s := by
            intro x hx
            have hown : ownerX (xCoord x.1) = n := by
              have hxupper : xCoord x.1 ≤ t (n + 1) := by
                calc
                  (xCoord x.1 : ℝ) ≤ max a b := (xCoord x.1).2.2
                  _ = (xCoord q.1 : ℝ) := hqrightmost.symm
                  _ = ((t (n + 1) : Set.Icc (min a b) (max a b)) : ℝ) := by
                        simpa [n] using hbreak
              exact hownerX_eq_of_between hnpos (by simpa [rowX] using hx.2) hxupper
            simp [rowF0, hown]
          refine ⟨s, hs_open, hqs, ownerBall n j, Metric.isOpen_ball, hqowner, hownerBall_sub n j,
            ?_, (fun z ↦ primitive n j z + kx n j), hshiftedPrimitive n j, ?_⟩
          · intro x hx
            exact hx.1
          · intro x hx
            simpa [Function.comp] using hs_eq hx
      · have htn1_ne :
            ((t (n + 1) : Set.Icc (min a b) (max a b)) : ℝ) ≠ max a b := by
          intro hEq
          exact hqrightmost (hbreak.trans hEq)
        have hnext : t (n + 1) < t (n + 2) := ht_strict_of_ne_right htn1_ne
        have hqedge : q.1 ∈ sharedVerticalEdge n j := by
          refine ⟨?_, ?_⟩
          · exact ⟨⟨hqleft, by simpa [hbreak]⟩, q.2⟩
          · refine ⟨?_, q.2⟩
            refine ⟨le_of_eq hbreak.symm, ?_⟩
            calc
              (xCoord q.1 : ℝ) = ((t (n + 1) : Set.Icc (min a b) (max a b)) : ℝ) := hbreak
              _ ≤ ((t (n + 2) : Set.Icc (min a b) (max a b)) : ℝ) := htmono (Nat.le_succ (n + 1))
        rcases rowBreakpointPatchEqOn (j := j) (n := n) q hqedge with
          ⟨sPatch, hsPatch_open, hqsPatch, hsPatch_mapsU, -, hsPatchEq⟩
        let s : Set (↑(rowBand j)) :=
          ((sPatch ∩ (if hn : n = 0 then univ
              else rowX j ⁻¹' Set.Ioi ((t n : Set.Icc (min a b) (max a b)) : ℝ))) ∩
            rowX j ⁻¹' Set.Iio ((t (n + 2) : Set.Icc (min a b) (max a b)) : ℝ))
        have hs_open : IsOpen s := by
          -- Around an interior breakpoint, use the exact overlap patch and trim only by the
          -- neighboring breakpoints.
          by_cases hn : n = 0
          · simpa [s, hn, inter_assoc] using
              (((hsPatch_open.inter isOpen_univ).inter
                ((hrowX_cont j).isOpen_preimage _ isOpen_Iio)))
          · simpa [s, hn, inter_assoc] using
              (((hsPatch_open.inter ((hrowX_cont j).isOpen_preimage _ isOpen_Ioi)).inter
                ((hrowX_cont j).isOpen_preimage _ isOpen_Iio)))
        have hqs : q ∈ s := by
          refine ⟨⟨hqsPatch, ?_⟩, ?_⟩
          · by_cases hn : n = 0
            · simp [hn]
            · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
              have hleftq : ((t n : Set.Icc (min a b) (max a b)) : ℝ) < (xCoord q.1 : ℝ) := by
                simpa [n] using (hownerX_left_lt (x := xCoord q.1) (by simpa [n] using hnpos))
              simpa [hn, rowX] using hleftq
          · simpa [rowX, hbreak] using hnext
        have hs_eq :
            EqOn (rowF0 j)
              (fun x : ↑(rowBand j) ↦ primitive n j (δ x.1) + kx n j) s := by
          intro x hx
          by_cases hxle :
              (xCoord x.1 : ℝ) ≤ ((t (n + 1) : Set.Icc (min a b) (max a b)) : ℝ)
          · by_cases hn : n = 0
            · have hown : ownerX (xCoord x.1) = 0 := by
                have hxupper : xCoord x.1 ≤ t 1 := by
                  simpa [n, hn] using hxle
                exact hownerX_eq_zero_of_le_first hxupper
              simp [rowF0, hown, hn]
            · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
              have hxlower : ((t n : Set.Icc (min a b) (max a b)) : ℝ) < (xCoord x.1 : ℝ) := by
                simpa [hn, rowX] using hx.1.2
              have hown : ownerX (xCoord x.1) = n :=
                hownerX_eq_of_between hnpos hxlower hxle
              simp [rowF0, hown]
          · have hxgt :
                ((t (n + 1) : Set.Icc (min a b) (max a b)) : ℝ) < (xCoord x.1 : ℝ) :=
              lt_of_not_ge hxle
            have hxlt : (xCoord x.1 : ℝ) < ((t (n + 2) : Set.Icc (min a b) (max a b)) : ℝ) := by
              simpa [rowX] using hx.2
            have hown : ownerX (xCoord x.1) = n + 1 := by
              exact hownerX_eq_of_between (Nat.succ_pos n) hxgt (le_of_lt hxlt)
            calc
              rowF0 j x = primitive (n + 1) j (δ x.1) + kx (n + 1) j := by
                simp [rowF0, hown]
              _ = primitive n j (δ x.1) + kx n j := hsPatchEq hx.1.1
              _ = (fun z ↦ primitive n j z + kx n j) (δ x.1) := rfl
        refine ⟨s, hs_open, hqs, ownerBall n j, Metric.isOpen_ball, hqowner, hownerBall_sub n j,
          ?_, (fun z ↦ primitive n j z + kx n j), hshiftedPrimitive n j, ?_⟩
        · intro x hx
          exact hsPatch_mapsU hx.1.1
        · intro x hx
          simpa [Function.comp] using hs_eq hx
  have rowPrimitiveOfFixedRow :
      ∀ j : ℕ, ∃ f : C(↑(rowBand j), F),
        ∀ q : ↑(rowBand j),
          ∃ s : Set (↑(rowBand j)), IsOpen s ∧ q ∈ s ∧
            ∃ U : Set E, IsOpen U ∧ δ q.1 ∈ U ∧ U ⊆ D ∧
              MapsTo (fun x : ↑(rowBand j) ↦ δ x.1) s U ∧
              ∃ primitiveOn : E → F,
                IsPrimitiveOn U ω primitiveOn ∧
                  EqOn f (fun x : ↑(rowBand j) ↦ primitiveOn (δ x.1)) s := by
    intro j
    let f0 : ↑(rowBand j) → F := rowF0 j
    have hf0_cont : Continuous f0 := by
      -- Bundle the owner-defined row formula by proving continuity from the local primitive
      -- witnesses established above.
      refine continuous_iff_continuousAt.mpr ?_
      intro q
      rcases rowOwnerLocalPrimitiveAt (j := j) q with
        ⟨s, hs_open, hqs, U, -, hδqU, -, -, primitiveOn, hprimitiveOn, hEq⟩
      have hδrow_cont : ContinuousAt (fun x : ↑(rowBand j) ↦ δ x.1) q := by
        exact (δ.continuousAt q.1).comp continuous_subtype_val.continuousAt
      have hprim_cont : ContinuousAt (fun x : ↑(rowBand j) ↦ primitiveOn (δ x.1)) q := by
        have hcomp :
            ContinuousAt
              ((fun z : E ↦ primitiveOn z) ∘ (fun x : ↑(rowBand j) ↦ δ x.1)) q := by
          exact ContinuousAt.comp
            (f := fun x : ↑(rowBand j) ↦ δ x.1) (g := primitiveOn)
            ((hprimitiveOn (δ q.1) hδqU).continuousAt) hδrow_cont
        simpa [Function.comp] using hcomp
      have hEqNear :
          f0 =ᶠ[nhds q] (fun x : ↑(rowBand j) ↦ primitiveOn (δ x.1)) :=
        Filter.mem_of_superset (hs_open.mem_nhds hqs) hEq
      exact hprim_cont.congr hEqNear.symm
    let f : C(↑(rowBand j), F) := ⟨f0, hf0_cont⟩
    refine ⟨f, ?_⟩
    intro q
    rcases rowOwnerLocalPrimitiveAt (j := j) q with
      ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, hs_maps, primitiveOn, hprimitiveOn, hEq⟩
    refine ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, hs_maps, primitiveOn, hprimitiveOn, ?_⟩
    intro x hx
    simpa [f, f0] using hEq hx
  let rowPrimitive : ∀ j : ℕ, C(↑(rowBand j), F) := fun j =>
    Classical.choose (rowPrimitiveOfFixedRow j)
  have hrowPrimitive_local :
      ∀ j : ℕ, ∀ q : ↑(rowBand j),
        ∃ s : Set (↑(rowBand j)), IsOpen s ∧ q ∈ s ∧
          ∃ U : Set E, IsOpen U ∧ δ q.1 ∈ U ∧ U ⊆ D ∧
            MapsTo (fun x : ↑(rowBand j) ↦ δ x.1) s U ∧
            ∃ primitiveOn : E → F,
              IsPrimitiveOn U ω primitiveOn ∧
                EqOn (rowPrimitive j) (fun x : ↑(rowBand j) ↦ primitiveOn (δ x.1)) s := by
    intro j q
    exact (Classical.choose_spec (rowPrimitiveOfFixedRow j)) q
  let sharedHorizontalEdge : ℕ → Set ([[(a, a'), (b, b')]]) := fun j =>
    rowBand j ∩ rowBand (j + 1)
  have hsharedHorizontalEdge_preconnected :
      ∀ j, IsPreconnected (sharedHorizontalEdge j) := by
    intro j
    have hshared_eq_horizontal :
        sharedHorizontalEdge j =
          {p : [[(a, a'), (b, b')]] |
            p.1.1 ∈ Set.Icc (min a b) (max a b) ∧
              p.1.2 = ((u (j + 1) : Set.Icc (min a' b') (max a' b')) : ℝ)} := by
      ext p
      constructor
      · intro hp
        refine ⟨?_, le_antisymm hp.1.2 hp.2.1⟩
        exact (xCoord p).2
      · intro hp
        refine ⟨?_, ?_⟩
        · exact ⟨by simpa [hp.2] using humono (Nat.le_succ j), le_of_eq hp.2⟩
        · exact ⟨le_of_eq hp.2.symm, by simpa [hp.2] using humono (Nat.le_succ (j + 1))⟩
    -- Rewrite the shared horizontal edge to the explicit horizontal segment and reuse the generic
    -- geometry lemma once.
    rw [hshared_eq_horizontal]
    exact isPreconnected_horizontalSegmentWithinRectangle
      (hx₀ := by simp [Set.uIcc])
      (hx₁ := by simp [Set.uIcc])
      (hy := by simpa [Set.uIcc] using (u (j + 1)).2)
  have rowPrimitiveDifferenceConst :
      ∀ j, ∃ c : F,
        ∀ p, ∀ hp : p ∈ sharedHorizontalEdge j,
          rowPrimitive (j + 1) ⟨p, hp.2⟩ - rowPrimitive j ⟨p, hp.1⟩ = c := by
    intro j
    let edgeMap : ↑(sharedHorizontalEdge j) → E := fun q => δ q.1
    let leftRow : ↑(sharedHorizontalEdge j) → F := fun q => rowPrimitive j ⟨q.1, q.2.1⟩
    let rightRow : ↑(sharedHorizontalEdge j) → F := fun q => rowPrimitive (j + 1) ⟨q.1, q.2.2⟩
    have hedgeMap_cont : Continuous edgeMap := by
      exact δ.continuous.comp continuous_subtype_val
    have hleftLocal :
        ∀ q : ↑(sharedHorizontalEdge j),
          ∃ s : Set (↑(sharedHorizontalEdge j)), IsOpen s ∧ q ∈ s ∧
            ∃ U : Set E, IsOpen U ∧ edgeMap q ∈ U ∧
              MapsTo edgeMap s U ∧
              ∃ primitiveOn : E → F,
                IsPrimitiveOn U ω primitiveOn ∧
                  EqOn leftRow (primitiveOn ∘ edgeMap) s := by
      intro q
      rcases hrowPrimitive_local j ⟨q.1, q.2.1⟩ with
        ⟨s, hs_open, hqs, U, hU_open, hδqU, -, hs_maps, primitiveOn, hprimitiveOn, hEq⟩
      let sEdge : Set (↑(sharedHorizontalEdge j)) := {x | (⟨x.1, x.2.1⟩ : ↑(rowBand j)) ∈ s}
      have hsEdge_open : IsOpen sEdge := by
        have hinc : Continuous (fun x : ↑(sharedHorizontalEdge j) ↦ (⟨x.1, x.2.1⟩ : ↑(rowBand j))) := by
          fun_prop
        simpa [sEdge] using hinc.isOpen_preimage s hs_open
      have hqsEdge : q ∈ sEdge := by
        simpa [sEdge] using hqs
      refine ⟨sEdge, hsEdge_open, hqsEdge, U, hU_open, hδqU, ?_, primitiveOn, hprimitiveOn, ?_⟩
      · intro x hx
        exact hs_maps (by simpa [sEdge] using hx)
      · intro x hx
        simpa [leftRow, edgeMap] using hEq (by simpa [sEdge] using hx)
    have hrightLocal :
        ∀ q : ↑(sharedHorizontalEdge j),
          ∃ s : Set (↑(sharedHorizontalEdge j)), IsOpen s ∧ q ∈ s ∧
            ∃ U : Set E, IsOpen U ∧ edgeMap q ∈ U ∧
              MapsTo edgeMap s U ∧
              ∃ primitiveOn : E → F,
                IsPrimitiveOn U ω primitiveOn ∧
                  EqOn rightRow (primitiveOn ∘ edgeMap) s := by
      intro q
      rcases hrowPrimitive_local (j + 1) ⟨q.1, q.2.2⟩ with
        ⟨s, hs_open, hqs, U, hU_open, hδqU, -, hs_maps, primitiveOn, hprimitiveOn, hEq⟩
      let sEdge : Set (↑(sharedHorizontalEdge j)) := {x | (⟨x.1, x.2.2⟩ : ↑(rowBand (j + 1))) ∈ s}
      have hsEdge_open : IsOpen sEdge := by
        have hinc :
            Continuous (fun x : ↑(sharedHorizontalEdge j) ↦ (⟨x.1, x.2.2⟩ : ↑(rowBand (j + 1)))) := by
          fun_prop
        simpa [sEdge] using hinc.isOpen_preimage s hs_open
      have hqsEdge : q ∈ sEdge := by
        simpa [sEdge] using hqs
      refine ⟨sEdge, hsEdge_open, hqsEdge, U, hU_open, hδqU, ?_, primitiveOn, hprimitiveOn, ?_⟩
      · intro x hx
        exact hs_maps (by simpa [sEdge] using hx)
      · intro x hx
        simpa [rightRow, edgeMap] using hEq (by simpa [sEdge] using hx)
    have hloc :
        IsLocallyConstant (fun q : ↑(sharedHorizontalEdge j) ↦ rightRow q - leftRow q) :=
      difference_isLocallyConstant_of_hasLocalPrimitive
        (δ := edgeMap) hedgeMap_cont hleftLocal hrightLocal
    by_cases hedge_nonempty : (sharedHorizontalEdge j).Nonempty
    · haveI : PreconnectedSpace (↑(sharedHorizontalEdge j)) :=
        Subtype.preconnectedSpace (hsharedHorizontalEdge_preconnected j)
      let q₀ : ↑(sharedHorizontalEdge j) :=
        ⟨Classical.choose hedge_nonempty, Classical.choose_spec hedge_nonempty⟩
      refine ⟨rightRow q₀ - leftRow q₀, ?_⟩
      intro p hp
      have hconst :
          rightRow ⟨p, hp⟩ - leftRow ⟨p, hp⟩ = rightRow q₀ - leftRow q₀ := by
        simpa [q₀] using hloc.apply_eq_of_preconnectedSpace ⟨p, hp⟩ q₀
      simpa [leftRow, rightRow] using hconst
    · refine ⟨0, ?_⟩
      intro p hp
      exact (hedge_nonempty ⟨p, hp⟩).elim
  let overlapConstY : ℕ → F := fun j => Classical.choose (rowPrimitiveDifferenceConst j)
  let ky : ℕ → F := fun j =>
    Nat.rec (motive := fun _ => F) 0 (fun n acc ↦ acc - overlapConstY n) j
  have hoverlapEqY :
      ∀ j p (hp : p ∈ sharedHorizontalEdge j),
        rowPrimitive (j + 1) ⟨p, hp.2⟩ - rowPrimitive j ⟨p, hp.1⟩ = overlapConstY j := by
    intro j p hp
    exact Classical.choose_spec (rowPrimitiveDifferenceConst j) p hp
  have hky_zero : ky 0 = 0 := by
    rfl
  have hky_succ : ∀ j, ky (j + 1) = ky j - overlapConstY j := by
    intro j
    rfl
  have hshiftEqY :
      ∀ j p (hp : p ∈ sharedHorizontalEdge j),
        rowPrimitive (j + 1) ⟨p, hp.2⟩ + ky (j + 1) =
          rowPrimitive j ⟨p, hp.1⟩ + ky j := by
    intro j p hp
    have hbase := hoverlapEqY j p hp
    have hEq :
        rowPrimitive (j + 1) ⟨p, hp.2⟩ =
          overlapConstY j + rowPrimitive j ⟨p, hp.1⟩ :=
      (sub_eq_iff_eq_add).mp hbase
    -- The recursive vertical shift adds the same constant `ky j` to both neighboring rows.
    calc
      rowPrimitive (j + 1) ⟨p, hp.2⟩ + ky (j + 1)
          = rowPrimitive (j + 1) ⟨p, hp.2⟩ + (ky j - overlapConstY j) := by
              rw [hky_succ]
      _ = (overlapConstY j + rowPrimitive j ⟨p, hp.1⟩) + (ky j - overlapConstY j) := by
            rw [hEq]
      _ = rowPrimitive j ⟨p, hp.1⟩ + ky j := by
            abel
  have hyminmax : min a' b' ≤ max a' b' := by
    simp
  let yCoord : [[(a, a'), (b, b')]] → Set.Icc (min a' b') (max a' b') := fun p =>
    ⟨p.1.2, by
      have hp : ((p : ℝ × ℝ) ∈ Set.uIcc (a, a') (b, b')) := p.2
      have hp' : ((p : ℝ × ℝ) ∈ Set.uIcc a b ×ˢ Set.uIcc a' b') := by
        simpa [Set.uIcc_prod_uIcc] using hp
      exact hp'.2⟩
  let ownerY : Set.Icc (min a' b') (max a' b') → ℕ :=
    subdivisionOwner hyminmax u husat
  have hownerY_spec :
      ∀ y : Set.Icc (min a' b') (max a' b'), y ≤ u (ownerY y + 1) := by
    intro y
    simpa [ownerY] using subdivisionOwner_spec hyminmax husat y
  have hownerY_left_lt :
      ∀ {y : Set.Icc (min a' b') (max a' b')}, 0 < ownerY y → u (ownerY y) < y := by
    intro y hy
    simpa [ownerY] using
      (subdivisionOwner_left_lt hyminmax husat (x := y) hy)
  have hownerY_eq_zero_of_le_first :
      ∀ {y : Set.Icc (min a' b') (max a' b')}, y ≤ u 1 → ownerY y = 0 := by
    intro y hy
    simpa [ownerY] using subdivisionOwner_eq_zero_of_le_first hyminmax husat hy
  have hownerY_eq_of_between :
      ∀ {n : ℕ} {y : Set.Icc (min a' b') (max a' b')},
        0 < n → u n < y → y ≤ u (n + 1) → ownerY y = n := by
    intro n y hn hylower hyupper
    simpa [ownerY] using
      (subdivisionOwner_eq_of_between hyminmax humono husat hylower hyupper)
  let rectY : [[(a, a'), (b, b')]] → ℝ := fun p =>
    ((yCoord p : Set.Icc (min a' b') (max a' b')) : ℝ)
  have hrectY_cont : Continuous rectY := by
    -- The row coordinate is just the second projection on the rectangle subtype.
    change Continuous fun p : [[(a, a'), (b, b')]] => p.1.2
    fun_prop
  have hownerY_mem_band :
      ∀ p : [[(a, a'), (b, b')]], p ∈ rowBand (ownerY (yCoord p)) := by
    intro p
    refine ⟨?_, ?_⟩
    · by_cases hzero : ownerY (yCoord p) = 0
      · have hyleft : ((u 0 : Set.Icc (min a' b') (max a' b')) : ℝ) ≤ (yCoord p : ℝ) := by
          simpa [hu0] using (yCoord p).2.1
        simpa [hzero] using hyleft
      · have hpos : 0 < ownerY (yCoord p) := Nat.pos_of_ne_zero hzero
        exact (hownerY_left_lt hpos).le
    · exact hownerY_spec (yCoord p)
  -- Route correction: the row stage is complete, so the remaining work is to turn subtype-local
  -- row witnesses into ambient witnesses and then replay the owner split in the `u`-direction.
  have ambientShiftedRowLocalPrimitiveAt :
      ∀ {j : ℕ} {q : [[(a, a'), (b, b')]]}, q ∈ rowBand j →
        ∃ s : Set ([[(a, a'), (b, b')]]), IsOpen s ∧ q ∈ s ∧
          ∃ U : Set E, IsOpen U ∧ δ q ∈ U ∧ U ⊆ D ∧
            MapsTo δ (s ∩ rowBand j) U ∧
            ∃ primitiveOn : E → F,
              IsPrimitiveOn U ω primitiveOn ∧
                ∀ p : ↑(rowBand j), p.1 ∈ s →
                  rowPrimitive j p + ky j = primitiveOn (δ p.1) := by
    intro j q hq
    rcases hrowPrimitive_local j ⟨q, hq⟩ with
      ⟨sSub, hsSub_open, hqsSub, U, hU_open, hδqU, hUD, hsSub_maps, primitiveSub,
        hprimitiveSub, hEqSub⟩
    have hsSub_nhds : sSub ∈ nhds (⟨q, hq⟩ : ↑(rowBand j)) := hsSub_open.mem_nhds hqsSub
    rcases (mem_nhds_subtype (rowBand j) ⟨q, hq⟩ sSub).1 hsSub_nhds with
      ⟨t, ht_nhds, ht_sub⟩
    rcases mem_nhds_iff.mp ht_nhds with ⟨s, hs_sub, hs_open, hqs⟩
    let primitiveOn : E → F := fun z ↦ primitiveSub z + ky j
    refine ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, ?_, primitiveOn,
      hprimitiveSub.addConst (ky j), ?_⟩
    · intro p hp
      have hpSub : (⟨p, hp.2⟩ : ↑(rowBand j)) ∈ sSub := by
        exact ht_sub (by simpa using hs_sub hp.1)
      exact hsSub_maps hpSub
    · intro p hp
      have hpSub : p ∈ sSub := by
        exact ht_sub (by simpa using hs_sub hp)
      calc
        rowPrimitive j p + ky j = primitiveSub (δ p.1) + ky j := by
          rw [hEqSub hpSub]
        _ = primitiveOn (δ p.1) := rfl
  -- Compare two adjacent normalized rows on an ambient patch around a horizontal breakpoint.
  have horizontalBreakpointCommonPrimitiveAt :
      ∀ {n : ℕ} {q : [[(a, a'), (b, b')]]}, q ∈ sharedHorizontalEdge n →
        ∃ s : Set ([[(a, a'), (b, b')]]), IsOpen s ∧ q ∈ s ∧
          ∃ U : Set E, IsOpen U ∧ δ q ∈ U ∧ U ⊆ D ∧
            MapsTo δ s U ∧
            ∃ primitiveOn : E → F,
              IsPrimitiveOn U ω primitiveOn ∧
                (∀ p, ∀ hp : p ∈ s ∩ rowBand n,
                  rowPrimitive n ⟨p, hp.2⟩ + ky n = primitiveOn (δ p)) ∧
                ∀ p, ∀ hp : p ∈ s ∩ rowBand (n + 1),
                  rowPrimitive (n + 1) ⟨p, hp.2⟩ + ky (n + 1) = primitiveOn (δ p) := by
    intro n q hq
    rcases ambientShiftedRowLocalPrimitiveAt (j := n) (q := q) hq.1 with
      ⟨sLower, hsLower_open, hqLower, ULower, hULower_open, hδqLower, hULowerD,
        hsLower_maps, primitiveLower, hprimitiveLower, hEqLower⟩
    rcases ambientShiftedRowLocalPrimitiveAt (j := n + 1) (q := q) hq.2 with
      ⟨sUpper, hsUpper_open, hqUpper, UUpper, hUUpper_open, hδqUpper, hUUpperD,
        hsUpper_maps, primitiveUpper, hprimitiveUpper, hEqUpper⟩
    rcases local_sub_eq_const_on_ball_of_common_primitive
        (U := ULower) (V := UUpper) (z₀ := δ q)
        hULower_open hUUpper_open hδqLower hδqUpper hprimitiveLower hprimitiveUpper with
      ⟨rDiff, hrDiff, c, hc⟩
    rcases Metric.isOpen_iff.mp hULower_open (δ q) hδqLower with ⟨rLower, hrLower, hballLower⟩
    rcases Metric.isOpen_iff.mp hUUpper_open (δ q) hδqUpper with ⟨rUpper, hrUpper, hballUpper⟩
    let r : ℝ := min rDiff (min rLower rUpper)
    have hr : 0 < r := by
      exact lt_min hrDiff (lt_min hrLower hrUpper)
    have hr_le_diff : r ≤ rDiff := min_le_left _ _
    have hr_le_lower : r ≤ rLower := le_trans (min_le_right _ _) (min_le_left _ _)
    have hr_le_upper : r ≤ rUpper := le_trans (min_le_right _ _) (min_le_right _ _)
    have hc_zero : c = 0 := by
      have hbaseLower :
          rowPrimitive n ⟨q, hq.1⟩ + ky n = primitiveLower (δ q) :=
        hEqLower ⟨q, hq.1⟩ hqLower
      have hbaseUpper :
          rowPrimitive (n + 1) ⟨q, hq.2⟩ + ky (n + 1) = primitiveUpper (δ q) :=
        hEqUpper ⟨q, hq.2⟩ hqUpper
      calc
        c = primitiveUpper (δ q) - primitiveLower (δ q) := by
          symm
          exact hc (Metric.mem_ball_self hrDiff)
        _ = 0 := by
          have hbaseEq : primitiveUpper (δ q) = primitiveLower (δ q) := by
            calc
              primitiveUpper (δ q) = rowPrimitive (n + 1) ⟨q, hq.2⟩ + ky (n + 1) := by
                symm
                exact hbaseUpper
              _ = rowPrimitive n ⟨q, hq.1⟩ + ky n := hshiftEqY n q hq
              _ = primitiveLower (δ q) := hbaseLower
          rw [hbaseEq]
          abel
    let s : Set ([[(a, a'), (b, b')]]) :=
      (sLower ∩ sUpper) ∩ δ ⁻¹' Metric.ball (δ q) r
    have hs_open : IsOpen s := by
      -- Intersect the two ambient row patches with the common codomain overlap ball.
      refine (hsLower_open.inter hsUpper_open).inter ?_
      exact δ.continuous.isOpen_preimage _ Metric.isOpen_ball
    have hqs : q ∈ s := by
      refine ⟨⟨hqLower, hqUpper⟩, Metric.mem_ball_self hr⟩
    refine ⟨s, hs_open, hqs, Metric.ball (δ q) r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_,
      ?_, primitiveLower, ?_, ?_, ?_⟩
    · intro z hz
      exact hULowerD (hballLower ((Metric.ball_subset_ball hr_le_lower) hz))
    · intro p hp
      exact hp.2
    · exact hprimitiveLower.mono fun z hz ↦
        hballLower ((Metric.ball_subset_ball hr_le_lower) hz)
    · intro p hp
      exact hEqLower ⟨p, hp.2⟩ hp.1.1.1
    · intro p hp
      have hupperVal :
          rowPrimitive (n + 1) ⟨p, hp.2⟩ + ky (n + 1) = primitiveUpper (δ p) :=
        hEqUpper ⟨p, hp.2⟩ hp.1.1.2
      have hdiffEq : primitiveUpper (δ p) - primitiveLower (δ p) = 0 := by
        have hdiff := hc ((Metric.ball_subset_ball hr_le_diff) hp.1.2)
        simpa [hc_zero] using hdiff
      calc
        rowPrimitive (n + 1) ⟨p, hp.2⟩ + ky (n + 1) = primitiveUpper (δ p) := hupperVal
        _ = primitiveLower (δ p) := sub_eq_zero.mp hdiffEq
  let rectF0 : [[(a, a'), (b, b')]] → F := fun p =>
    rowPrimitive (ownerY (yCoord p)) ⟨p, hownerY_mem_band p⟩ + ky (ownerY (yCoord p))
  have rectF0_eq_of_owner :
      ∀ {p : [[(a, a'), (b, b')]]} {n : ℕ},
        ownerY (yCoord p) = n → ∀ hp : p ∈ rowBand n,
          rectF0 p = rowPrimitive n ⟨p, hp⟩ + ky n := by
    intro p n howner hp
    subst n
    have hpEq :
        (⟨p, hp⟩ : ↑(rowBand (ownerY (yCoord p)))) = ⟨p, hownerY_mem_band p⟩ := by
      apply Subtype.ext
      rfl
    calc
      rectF0 p =
          rowPrimitive (ownerY (yCoord p)) ⟨p, hownerY_mem_band p⟩ + ky (ownerY (yCoord p)) := by
            rfl
      _ = rowPrimitive (ownerY (yCoord p)) ⟨p, hp⟩ + ky (ownerY (yCoord p)) := by
            rw [hpEq]
  -- Use the same owner decomposition in the `u`-direction to get a local primitive formula for
  -- the global rectangle candidate.
  have rectangleOwnerLocalPrimitiveAt :
      ∀ q : [[(a, a'), (b, b')]],
        ∃ s : Set ([[(a, a'), (b, b')]]), IsOpen s ∧ q ∈ s ∧
          ∃ U : Set E, IsOpen U ∧ δ q ∈ U ∧ U ⊆ D ∧
            MapsTo δ s U ∧
            ∃ primitiveOn : E → F,
              IsPrimitiveOn U ω primitiveOn ∧
                EqOn rectF0 (fun p ↦ primitiveOn (δ p)) s := by
    intro q
    let n : ℕ := ownerY (yCoord q)
    have hqlower : ((u n : Set.Icc (min a' b') (max a' b')) : ℝ) ≤ (yCoord q : ℝ) := by
      by_cases hn : n = 0
      · have hyleft : ((u 0 : Set.Icc (min a' b') (max a' b')) : ℝ) ≤ (yCoord q : ℝ) := by
          simpa [hu0] using (yCoord q).2.1
        simpa [n, hn] using hyleft
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        exact (hownerY_left_lt (y := yCoord q) (by simpa [n] using hnpos)).le
    have hqupper : (yCoord q : ℝ) ≤ ((u (n + 1) : Set.Icc (min a' b') (max a' b')) : ℝ) := by
      simpa [n] using hownerY_spec (yCoord q)
    have hqband : q ∈ rowBand n := by
      simpa [n] using hownerY_mem_band q
    by_cases hstrict :
        (yCoord q : ℝ) < ((u (n + 1) : Set.Icc (min a' b') (max a' b')) : ℝ)
    · by_cases hn : n = 0
      · rcases ambientShiftedRowLocalPrimitiveAt
            (j := 0) (q := q) (by simpa [n, hn] using hqband) with
          ⟨sPatch, hsPatch_open, hqsPatch, U, hU_open, hδqU, hUD, hsPatch_maps, primitiveOn,
            hprimitiveOn, hEqPatch⟩
        let s : Set ([[(a, a'), (b, b')]]) :=
          sPatch ∩ rectY ⁻¹' Set.Iio ((u 1 : Set.Icc (min a' b') (max a' b')) : ℝ)
        have hs_open : IsOpen s := by
          -- Below the first horizontal breakpoint the owner is forced to be `0`.
          simpa [s] using
            (hsPatch_open.inter ((hrectY_cont).isOpen_preimage _ isOpen_Iio))
        have hqs : q ∈ s := by
          exact ⟨hqsPatch, by simpa [rectY, n, hn] using hstrict⟩
        have hs_maps : MapsTo δ s U := by
          intro p hp
          have hpBand : p ∈ rowBand 0 := by
            refine ⟨?_, le_of_lt ?_⟩
            · have hyleft : ((u 0 : Set.Icc (min a' b') (max a' b')) : ℝ) ≤ (yCoord p : ℝ) := by
                simpa [hu0] using (yCoord p).2.1
              simpa using hyleft
            · simpa [rectY] using hp.2
          exact hsPatch_maps ⟨hp.1, hpBand⟩
        have hs_eq :
            EqOn rectF0 (fun p ↦ primitiveOn (δ p)) s := by
          intro p hp
          have hpUpper : yCoord p ≤ u 1 := by
            exact le_of_lt (by simpa [rectY] using hp.2)
          have howner : ownerY (yCoord p) = 0 := hownerY_eq_zero_of_le_first hpUpper
          have hpBand : p ∈ rowBand 0 := by
            refine ⟨?_, hpUpper⟩
            have hyleft : ((u 0 : Set.Icc (min a' b') (max a' b')) : ℝ) ≤ (yCoord p : ℝ) := by
              simpa [hu0] using (yCoord p).2.1
            simpa using hyleft
          have hrect0 : rectF0 p = rowPrimitive 0 ⟨p, hpBand⟩ + ky 0 :=
            rectF0_eq_of_owner (n := 0) howner hpBand
          calc
            rectF0 p = rowPrimitive 0 ⟨p, hpBand⟩ + ky 0 := hrect0
            _ = primitiveOn (δ p) := by
              simpa using hEqPatch ⟨p, hpBand⟩ hp.1
        refine ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, hs_maps, primitiveOn, hprimitiveOn,
          hs_eq⟩
      · rcases ambientShiftedRowLocalPrimitiveAt (j := n) (q := q) hqband with
          ⟨sPatch, hsPatch_open, hqsPatch, U, hU_open, hδqU, hUD, hsPatch_maps, primitiveOn,
            hprimitiveOn, hEqPatch⟩
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let s : Set ([[(a, a'), (b, b')]]) :=
          (sPatch ∩ rectY ⁻¹' Set.Ioi ((u n : Set.Icc (min a' b') (max a' b')) : ℝ)) ∩
            rectY ⁻¹' Set.Iio ((u (n + 1) : Set.Icc (min a' b') (max a' b')) : ℝ)
        have hs_open : IsOpen s := by
          -- Away from horizontal breakpoints the vertical owner stays constant.
          simpa [s, inter_assoc] using
            ((hsPatch_open.inter ((hrectY_cont).isOpen_preimage _ isOpen_Ioi)).inter
              ((hrectY_cont).isOpen_preimage _ isOpen_Iio))
        have hqs : q ∈ s := by
          refine ⟨⟨hqsPatch, ?_⟩, ?_⟩
          · simpa [rectY, n] using
              (hownerY_left_lt (y := yCoord q) (by simpa [n] using hnpos))
          · simpa [rectY] using hstrict
        have hs_maps : MapsTo δ s U := by
          intro p hp
          have hpBand : p ∈ rowBand n := by
            refine ⟨le_of_lt ?_, le_of_lt ?_⟩
            · simpa [rectY] using hp.1.2
            · simpa [rectY] using hp.2
          exact hsPatch_maps ⟨hp.1.1, hpBand⟩
        have hs_eq :
            EqOn rectF0 (fun p ↦ primitiveOn (δ p)) s := by
          intro p hp
          have hylower : ((u n : Set.Icc (min a' b') (max a' b')) : ℝ) < (yCoord p : ℝ) := by
            simpa [rectY] using hp.1.2
          have hyupper : yCoord p ≤ u (n + 1) := by
            exact le_of_lt (by simpa [rectY] using hp.2)
          have howner : ownerY (yCoord p) = n :=
            hownerY_eq_of_between hnpos hylower hyupper
          have hpBand : p ∈ rowBand n := ⟨le_of_lt hylower, hyupper⟩
          calc
            rectF0 p = rowPrimitive n ⟨p, hpBand⟩ + ky n :=
              rectF0_eq_of_owner howner hpBand
            _ = primitiveOn (δ p) := by
              simpa [n] using hEqPatch ⟨p, hpBand⟩ hp.1.1
        refine ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, hs_maps, primitiveOn, hprimitiveOn,
          hs_eq⟩
    · have hbreak :
          (yCoord q : ℝ) = ((u (n + 1) : Set.Icc (min a' b') (max a' b')) : ℝ) :=
        le_antisymm hqupper (le_of_not_gt hstrict)
      by_cases hqtop : (yCoord q : ℝ) = max a' b'
      · by_cases hn : n = 0
        · rcases ambientShiftedRowLocalPrimitiveAt
              (j := 0) (q := q) (by simpa [n, hn] using hqband) with
            ⟨sPatch, hsPatch_open, hqsPatch, U, hU_open, hδqU, hUD, hsPatch_maps, primitiveOn,
              hprimitiveOn, hEqPatch⟩
          let s : Set ([[(a, a'), (b, b')]]) := sPatch
          have hs_maps : MapsTo δ s U := by
            intro p hp
            have hpUpper : yCoord p ≤ u 1 := by
              calc
                (yCoord p : ℝ) ≤ max a' b' := (yCoord p).2.2
                _ = (yCoord q : ℝ) := hqtop.symm
                _ = ((u 1 : Set.Icc (min a' b') (max a' b')) : ℝ) := by
                      simpa [n, hn] using hbreak
            have hpBand : p ∈ rowBand 0 := by
              refine ⟨?_, hpUpper⟩
              have hyleft : ((u 0 : Set.Icc (min a' b') (max a' b')) : ℝ) ≤ (yCoord p : ℝ) := by
                simpa [hu0] using (yCoord p).2.1
              simpa using hyleft
            exact hsPatch_maps ⟨hp, hpBand⟩
          have hs_eq :
              EqOn rectF0 (fun p ↦ primitiveOn (δ p)) s := by
            intro p hp
            have hpUpper : yCoord p ≤ u 1 := by
              calc
                (yCoord p : ℝ) ≤ max a' b' := (yCoord p).2.2
                _ = (yCoord q : ℝ) := hqtop.symm
                _ = ((u 1 : Set.Icc (min a' b') (max a' b')) : ℝ) := by
                      simpa [n, hn] using hbreak
            have howner : ownerY (yCoord p) = 0 := hownerY_eq_zero_of_le_first hpUpper
            have hpBand : p ∈ rowBand 0 := by
              refine ⟨?_, hpUpper⟩
              have hyleft : ((u 0 : Set.Icc (min a' b') (max a' b')) : ℝ) ≤ (yCoord p : ℝ) := by
                simpa [hu0] using (yCoord p).2.1
              simpa using hyleft
            have hrect0 : rectF0 p = rowPrimitive 0 ⟨p, hpBand⟩ + ky 0 :=
              rectF0_eq_of_owner (n := 0) howner hpBand
            calc
              rectF0 p = rowPrimitive 0 ⟨p, hpBand⟩ + ky 0 := hrect0
              _ = primitiveOn (δ p) := by
                simpa using hEqPatch ⟨p, hpBand⟩ hp
          refine ⟨s, hsPatch_open, hqsPatch, U, hU_open, hδqU, hUD, hs_maps, primitiveOn,
            hprimitiveOn, hs_eq⟩
        · rcases ambientShiftedRowLocalPrimitiveAt (j := n) (q := q) hqband with
            ⟨sPatch, hsPatch_open, hqsPatch, U, hU_open, hδqU, hUD, hsPatch_maps, primitiveOn,
              hprimitiveOn, hEqPatch⟩
          have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          let s : Set ([[(a, a'), (b, b')]]) :=
            sPatch ∩ rectY ⁻¹' Set.Ioi ((u n : Set.Icc (min a' b') (max a' b')) : ℝ)
          have hs_open : IsOpen s := by
            -- At the terminal row, only the last active owner remains.
            simpa [s] using
              (hsPatch_open.inter ((hrectY_cont).isOpen_preimage _ isOpen_Ioi))
          have hqs : q ∈ s := by
            refine ⟨hqsPatch, ?_⟩
            simpa [rectY, n] using
              (hownerY_left_lt (y := yCoord q) (by simpa [n] using hnpos))
          have hs_maps : MapsTo δ s U := by
            intro p hp
            have hpUpper : yCoord p ≤ u (n + 1) := by
              calc
                (yCoord p : ℝ) ≤ max a' b' := (yCoord p).2.2
                _ = (yCoord q : ℝ) := hqtop.symm
                _ = ((u (n + 1) : Set.Icc (min a' b') (max a' b')) : ℝ) := by
                      simpa [n] using hbreak
            have hpBand : p ∈ rowBand n := by
              refine ⟨le_of_lt ?_, hpUpper⟩
              simpa [rectY] using hp.2
            exact hsPatch_maps ⟨hp.1, hpBand⟩
          have hs_eq :
              EqOn rectF0 (fun p ↦ primitiveOn (δ p)) s := by
            intro p hp
            have hpUpper : yCoord p ≤ u (n + 1) := by
              calc
                (yCoord p : ℝ) ≤ max a' b' := (yCoord p).2.2
                _ = (yCoord q : ℝ) := hqtop.symm
                _ = ((u (n + 1) : Set.Icc (min a' b') (max a' b')) : ℝ) := by
                      simpa [n] using hbreak
            have hylower : ((u n : Set.Icc (min a' b') (max a' b')) : ℝ) < (yCoord p : ℝ) := by
              simpa [rectY] using hp.2
            have howner : ownerY (yCoord p) = n :=
              hownerY_eq_of_between hnpos hylower hpUpper
            have hpBand : p ∈ rowBand n := ⟨le_of_lt hylower, hpUpper⟩
            calc
              rectF0 p = rowPrimitive n ⟨p, hpBand⟩ + ky n :=
                rectF0_eq_of_owner howner hpBand
              _ = primitiveOn (δ p) := by
                simpa [n] using hEqPatch ⟨p, hpBand⟩ hp.1
          refine ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, hs_maps, primitiveOn, hprimitiveOn,
            hs_eq⟩
      · have hun1_ne :
            ((u (n + 1) : Set.Icc (min a' b') (max a' b')) : ℝ) ≠ max a' b' := by
          intro hEq
          exact hqtop (hbreak.trans hEq)
        have hnext : u (n + 1) < u (n + 2) := hu_strict_of_ne_right hun1_ne
        have hqedge : q ∈ sharedHorizontalEdge n := by
          refine ⟨hqband, ?_⟩
          refine ⟨le_of_eq hbreak.symm, ?_⟩
          calc
            (q.1.2 : ℝ) = ((u (n + 1) : Set.Icc (min a' b') (max a' b')) : ℝ) := hbreak
            _ ≤ ((u (n + 2) : Set.Icc (min a' b') (max a' b')) : ℝ) :=
              humono (Nat.le_succ (n + 1))
        by_cases hn : n = 0
        · rcases horizontalBreakpointCommonPrimitiveAt
            (n := 0) (q := q) (by simpa [n, hn] using hqedge) with
            ⟨sPatch, hsPatch_open, hqsPatch, U, hU_open, hδqU, hUD, hsPatch_maps, primitiveOn,
              hprimitiveOn, hEqLower, hEqUpper⟩
          let s : Set ([[(a, a'), (b, b')]]) :=
            sPatch ∩ rectY ⁻¹' Set.Iio ((u 2 : Set.Icc (min a' b') (max a' b')) : ℝ)
          have hs_open : IsOpen s := by
            simpa [s] using
              (hsPatch_open.inter ((hrectY_cont).isOpen_preimage _ isOpen_Iio))
          have hqs : q ∈ s := by
            refine ⟨hqsPatch, ?_⟩
            simpa [rectY, n, hn, hbreak] using hnext
          have hs_eq :
              EqOn rectF0 (fun p ↦ primitiveOn (δ p)) s := by
            intro p hp
            by_cases hpUpper : yCoord p ≤ u 1
            · have howner : ownerY (yCoord p) = 0 := hownerY_eq_zero_of_le_first hpUpper
              have hpBand : p ∈ rowBand 0 := by
                refine ⟨?_, hpUpper⟩
                have hyleft : ((u 0 : Set.Icc (min a' b') (max a' b')) : ℝ) ≤ (yCoord p : ℝ) := by
                  simpa [hu0] using (yCoord p).2.1
                simpa using hyleft
              calc
                rectF0 p = rowPrimitive 0 ⟨p, hpBand⟩ + ky 0 := by
                  simpa using rectF0_eq_of_owner howner hpBand
                _ = primitiveOn (δ p) := by
                  exact hEqLower p ⟨hp.1, hpBand⟩
            · have hpLower : ((u 1 : Set.Icc (min a' b') (max a' b')) : ℝ) < (yCoord p : ℝ) :=
                lt_of_not_ge hpUpper
              have hpTop : (yCoord p : ℝ) < ((u 2 : Set.Icc (min a' b') (max a' b')) : ℝ) := by
                simpa [rectY] using hp.2
              have howner : ownerY (yCoord p) = 1 := by
                exact hownerY_eq_of_between (Nat.succ_pos 0) hpLower (le_of_lt hpTop)
              have hpBand : p ∈ rowBand 1 := ⟨le_of_lt hpLower, le_of_lt hpTop⟩
              calc
                rectF0 p = rowPrimitive 1 ⟨p, hpBand⟩ + ky 1 := by
                  simpa using rectF0_eq_of_owner howner hpBand
                _ = primitiveOn (δ p) := by
                  exact hEqUpper p ⟨hp.1, hpBand⟩
          refine ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, ?_, primitiveOn, hprimitiveOn, hs_eq⟩
          intro p hp
          exact hsPatch_maps hp.1
        · rcases horizontalBreakpointCommonPrimitiveAt (n := n) (q := q) hqedge with
            ⟨sPatch, hsPatch_open, hqsPatch, U, hU_open, hδqU, hUD, hsPatch_maps, primitiveOn,
              hprimitiveOn, hEqLower, hEqUpper⟩
          let s : Set ([[(a, a'), (b, b')]]) :=
            (sPatch ∩ rectY ⁻¹' Set.Ioi ((u n : Set.Icc (min a' b') (max a' b')) : ℝ)) ∩
              rectY ⁻¹' Set.Iio ((u (n + 2) : Set.Icc (min a' b') (max a' b')) : ℝ)
          have hs_open : IsOpen s := by
            simpa [s, inter_assoc] using
              ((hsPatch_open.inter ((hrectY_cont).isOpen_preimage _ isOpen_Ioi)).inter
                ((hrectY_cont).isOpen_preimage _ isOpen_Iio))
          have hqs : q ∈ s := by
            refine ⟨⟨hqsPatch, ?_⟩, ?_⟩
            · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
              have hleftq : ((u n : Set.Icc (min a' b') (max a' b')) : ℝ) < (yCoord q : ℝ) := by
                simpa [n] using
                  (hownerY_left_lt (y := yCoord q) (by simpa [n] using hnpos))
              simpa [rectY] using hleftq
            · simpa [rectY, hbreak] using hnext
          have hs_eq :
              EqOn rectF0 (fun p ↦ primitiveOn (δ p)) s := by
            intro p hp
            by_cases hpUpper : yCoord p ≤ u (n + 1)
            · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
              have hpLower : ((u n : Set.Icc (min a' b') (max a' b')) : ℝ) < (yCoord p : ℝ) := by
                simpa [rectY] using hp.1.2
              have howner : ownerY (yCoord p) = n :=
                hownerY_eq_of_between hnpos hpLower hpUpper
              have hpBand : p ∈ rowBand n := ⟨le_of_lt hpLower, hpUpper⟩
              calc
                rectF0 p = rowPrimitive n ⟨p, hpBand⟩ + ky n := by
                  exact rectF0_eq_of_owner howner hpBand
                _ = primitiveOn (δ p) := by
                  simpa [n] using hEqLower p ⟨hp.1.1, hpBand⟩
            · have hpLower : ((u (n + 1) : Set.Icc (min a' b') (max a' b')) : ℝ) < (yCoord p : ℝ) :=
                lt_of_not_ge hpUpper
              have hpTop : (yCoord p : ℝ) < ((u (n + 2) : Set.Icc (min a' b') (max a' b')) : ℝ) := by
                simpa [rectY] using hp.2
              have howner : ownerY (yCoord p) = n + 1 := by
                exact hownerY_eq_of_between (Nat.succ_pos n) hpLower (le_of_lt hpTop)
              have hpBand : p ∈ rowBand (n + 1) := ⟨le_of_lt hpLower, le_of_lt hpTop⟩
              calc
                rectF0 p = rowPrimitive (n + 1) ⟨p, hpBand⟩ + ky (n + 1) := by
                  exact rectF0_eq_of_owner howner hpBand
                _ = primitiveOn (δ p) := by
                  simpa using hEqUpper p ⟨hp.1.1, hpBand⟩
          refine ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, ?_, primitiveOn, hprimitiveOn, hs_eq⟩
          intro p hp
          exact hsPatch_maps hp.1.1
  let f0 : [[(a, a'), (b, b')]] → F := rectF0
  have hf0_cont : Continuous f0 := by
    -- Once each point admits one ambient primitive formula, continuity follows by eventual
    -- equality to the corresponding pullback.
    refine continuous_iff_continuousAt.mpr ?_
    intro q
    rcases rectangleOwnerLocalPrimitiveAt q with
      ⟨s, hs_open, hqs, U, -, hδqU, -, -, primitiveOn, hprimitiveOn, hEq⟩
    have hprim_cont : ContinuousAt (fun p : [[(a, a'), (b, b')]] ↦ primitiveOn (δ p)) q := by
      have hcomp :
          ContinuousAt ((fun z : E ↦ primitiveOn z) ∘ δ) q := by
        exact ContinuousAt.comp (f := δ) (g := primitiveOn)
          ((hprimitiveOn (δ q) hδqU).continuousAt) (δ.continuousAt q)
      simpa [Function.comp] using hcomp
    have hEqNear : f0 =ᶠ[nhds q] (fun p : [[(a, a'), (b, b')]] ↦ primitiveOn (δ p)) :=
      Filter.mem_of_superset (hs_open.mem_nhds hqs) hEq
    exact hprim_cont.congr hEqNear.symm
  let f : C([[(a, a'), (b, b')]], F) := ⟨f0, hf0_cont⟩
  have hf : IsPrimitiveFollowingOnRectangle ω D δ f := by
    intro q
    rcases rectangleOwnerLocalPrimitiveAt q with
      ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, hs_maps, primitiveOn, hprimitiveOn, hEq⟩
    refine ⟨s, hs_open, hqs, U, hU_open, hδqU, hUD, hs_maps, primitiveOn, hprimitiveOn, ?_⟩
    intro p hp
    simpa [f, f0] using hEq hp
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact primitiveFollowingOnRectangle_unique_up_to_constant hf hg
