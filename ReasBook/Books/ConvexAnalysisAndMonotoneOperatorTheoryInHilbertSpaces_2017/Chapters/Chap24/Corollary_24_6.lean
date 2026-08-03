import BauschkeLean.Chap02.Definition_2_23
import BauschkeLean.Chap02.Example_2_57
import BauschkeLean.Chap02.Proposition_2_58
import BauschkeLean.Chap05.Example_5_18
import BauschkeLean.Chap12.Proposition_12_28
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap18.Corollary_18_19
import BauschkeLean.Chap20.Example_20_6
import BauschkeLean.Chap24.Proposition_24_4

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped Gradient InnerProductSpace

universe u

namespace ContinuousLinearMap

section Characterizations

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall/local precedent: `lean_leansearch` only surfaced the ambient self-adjoint API,
-- so this item follows the local `Prox[f, hf]` owner from Chapters 12 and 24 together with the
-- Chapter 18 linear-monotonicity surface `L.toLinearMap.IsMonotone`.

/-- Helper for Corollary 24.6: the Chapter 24 gradient formula for `(f + q)^*` supplies the
whole-space Gâteaux derivative field needed in Proposition 2.58. -/
lemma hasGateauxDerivativeOn_conjugateAddHalfSquaredNorm_toReal
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    HasGateauxDerivativeOn
      (fun y : H ↦ (((f + halfSquaredNorm).asEReal∗) y).toReal)
      (fun x ↦ InnerProductSpace.toDual ℝ H (Prox[f, hf] x))
      Set.univ := by
  intro x hx
  -- First identify the unit conjugate Moreau envelope gradient with `Prox[f, hf]`.
  have hgrad_raw :
      HasGradientAt
        (fun y : H ↦ (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) y).toReal)
        (Prox[f, hf] x) x := by
    have hgrad_owner :=
      moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
        (f := gammaZeroConjugate f hf)
        (γ := (1 : PosReal))
        (hf := gammaZeroConjugate_mem_gammaZero hf)
        (x := x)
    have hprox_eq_raw :=
      (congrFun
        (proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
          (f := f) (hf := hf))
        x).trans hgrad_owner.gradient
    simpa [hprox_eq_raw] using hgrad_owner
  -- Then rewrite the source-facing owner `(f + q)^*` to that canonical envelope.
  have hconj_eq :
      (fun y : H ↦ (((f + halfSquaredNorm).asEReal∗) y).toReal) =
        fun y : H ↦ (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) y).toReal := by
    funext y
    exact congrArg EReal.toReal <|
      congrFun
        (ERealFunction.conjugate_add_halfSquaredNorm_eq_unit_conjugateMoreauEnvelope
          (f := f) (hf := hf))
        y
  have hgrad :
      HasGradientAt
        (fun y : H ↦ (((f + halfSquaredNorm).asEReal∗) y).toReal)
        (Prox[f, hf] x) x := by
    rw [hconj_eq]
    exact hgrad_raw
  -- Proposition 2.58 is formulated with the Gâteaux derivative surface, so convert once here.
  simpa [HasGateauxDerivativeAt] using hgrad.hasFDerivAt.hasGateauxDerivativeAt

/-- Helper for Corollary 24.6: a firmly nonexpansive linear map is monotone and has norm at most
`1`. -/
lemma isMonotone_and_norm_le_one_of_firmlyNonexpansive
    {L : H →L[ℝ] H} (hFirm : FirmlyNonexpansive L) :
    L.toLinearMap.IsMonotone ∧ ‖L‖ ≤ 1 := by
  constructor
  · intro x
    -- Specialize the pointwise monotonicity inequality at `(x, 0)` and rewrite linearly.
    have hFirmOn : FirmlyNonexpansiveOn (Set.univ : Set H) (fun y : Set.univ ↦ L y) := by
      simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using hFirm
    have hmono := hFirmOn.monotone ⟨x, by simp⟩ ⟨0, by simp⟩
    simpa [real_inner_comm] using hmono
  · -- Convert the `1`-Lipschitz estimate of a firmly nonexpansive map into the operator-norm bound.
    have hLip : LipschitzWith 1 L := lipschitzWith_one_of_firmlyNonexpansive hFirm
    rw [ContinuousLinearMap.opNorm_le_iff (show (0 : ℝ) ≤ 1 by positivity)]
    intro x
    simpa [dist_eq_norm] using hLip.dist_le_mul x 0

/-- Helper for Corollary 24.6: a continuous linear map that agrees pointwise with `Prox[f, hf]`
transports the Chapter 24 Gâteaux derivative field from `Prox[f, hf]` to `L`. -/
lemma hasGateauxDerivativeOn_conjugateAddHalfSquaredNorm_toReal_of_eq_proximityOperator
    (L : H →L[ℝ] H) (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hEq : ∀ x : H, L x = Prox[f, hf] x) :
    HasGateauxDerivativeOn
      (fun y : H ↦ (((f + halfSquaredNorm).asEReal∗) y).toReal)
      (fun x ↦ InnerProductSpace.toDual ℝ H (L x))
      Set.univ := by
  have hGateauxProx := hasGateauxDerivativeOn_conjugateAddHalfSquaredNorm_toReal (f := f) hf
  intro x hx
  simpa only [hEq x] using hGateauxProx x hx

/-- Helper for Corollary 24.6: a continuous linear Gâteaux derivative field on the whole space
upgrades to the corresponding pointwise gradient formula. -/
lemma hasGradientAt_of_hasGateauxDerivativeOn_univ_linearMap
    (g : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn g (fun x ↦ InnerProductSpace.toDual ℝ H (L x)) Set.univ)
    (x : H) :
    HasGradientAt g (L x) x := by
  -- Use Fact 2.62 to upgrade the whole-space Gâteaux derivative field to a Fréchet derivative.
  rw [hasGradientAt_iff_hasFDerivAt]
  have hUniv : (Set.univ : Set H) ∈ nhds x := by
    simp
  have hCont :
      ContinuousWithinAt
        (fun y ↦ InnerProductSpace.toDual ℝ H (L y))
        Set.univ x := by
    exact ((InnerProductSpace.toDual ℝ H).continuous.comp L.continuous).continuousWithinAt
  simpa using hasFDerivAt_of_gateauxDerivative_continuousWithinAt hUniv hGateaux hCont

/-- Helper for Corollary 24.6: Example 2.57 gives the gradient of the normalized quadratic model
`y ↦ c + (1 / 2) * ⟪L y, y⟫_ℝ`. -/
lemma halfQuadraticModel_hasGradientAt
    (L : H →L[ℝ] H) (c : ℝ) (x : H) :
    HasGradientAt (fun y : H ↦ c + (1 / 2 : ℝ) * ⟪L y, y⟫_ℝ)
      ((1 / 2 : ℝ) • ((L + L.adjoint) x)) x := by
  -- First differentiate the underlying quadratic-affine model from Example 2.57.
  have hQuadratic :
      HasGradientAt (quadratic_affine_functional L 0) ((L + L.adjoint) x) x := by
    simpa [quadratic_affine_functional] using quadratic_affine_functional_hasGradientAt L 0 x
  -- Then scale by `1 / 2` and add the constant term to match the normalized model.
  have hScaled := hQuadratic.hasFDerivAt.const_smul (1 / 2 : ℝ)
  have hShifted := hScaled.const_add c
  convert hShifted.hasGradientAt using 1
  · ext y
    simp [quadratic_affine_functional]
  · apply (InnerProductSpace.toDual ℝ H).injective
    ext y
    simp

/-- Helper for Corollary 24.6: a proximal point of a `Γ₀(H)` function lies in its effective
domain. -/
lemma isProxPoint_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) {x p : H}
    (hp : IsProxPoint f x p) :
    p ∈ effectiveDomain f := by
  -- Compare the proximal inequality at `p` with one known finite point of `f`.
  rcases hf.2.nonempty with ⟨q, hq⟩
  have hVar := (isProxPoint_iff_forall_inner_add_le f hf.2 x p).mp hp q
  by_contra hpDom
  have hfpTop : (f p : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hpDom))
  have hsumTop : (⟪q - p, x - p⟫_ℝ : EReal) + (f p : EReal) = ⊤ := by
    rw [hfpTop, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
  rw [hsumTop] at hVar
  exact ne_of_lt (mem_effectiveDomain_iff.mp hq) (top_le_iff.mp hVar)

/-- Helper for Corollary 24.6: the variational inequality for a proximal point becomes real-valued
once the comparison point is known to lie in the effective domain. -/
lemma inner_add_toReal_le_toReal_of_isProxPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) {x p y : H}
    (hp : IsProxPoint f x p) (hy : y ∈ effectiveDomain f) :
    ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal := by
  -- First record that both endpoint values are finite so `toReal` is legitimate.
  have hpDom : p ∈ effectiveDomain f :=
    isProxPoint_mem_effectiveDomain f hf hp
  have hVar := (isProxPoint_iff_forall_inner_add_le f hf.2 x p).mp hp y
  have hfpTop : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hpDom)
  have hfpBot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hfyTop : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hfyBot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hCast :
      (((⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal)) ≤
        (((f y : EReal).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hfpTop hfpBot, EReal.coe_toReal hfyTop hfyBot, EReal.coe_add]
      using hVar
  exact_mod_cast hCast

/-- Helper for Corollary 24.6: two proximal values satisfy the pairwise firm inequality. -/
lemma proximityOperator_pairwise_firmInequality_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x y : H) :
    ‖Prox[f, hf] x - Prox[f, hf] y‖ ^ (2 : ℕ) ≤
      inner ℝ (Prox[f, hf] x - Prox[f, hf] y) (x - y) := by
  let p : H := Prox[f, hf] x
  let q : H := Prox[f, hf] y
  have hp : IsProxPoint f x p := by
    simpa [p] using
      proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) x
  have hq : IsProxPoint f y q := by
    simpa [q] using
      proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) y
  -- Combine the two variational inequalities and rewrite the sum into the firm estimate.
  have hpDom : p ∈ effectiveDomain f := isProxPoint_mem_effectiveDomain f hf hp
  have hqDom : q ∈ effectiveDomain f := isProxPoint_mem_effectiveDomain f hf hq
  have hpq :
      ⟪q - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f q : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint f hf hp hqDom
  have hqp :
      ⟪p - q, y - q⟫_ℝ + (f q : EReal).toReal ≤ (f p : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint f hf hq hpDom
  have hSum : ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ ≤ 0 := by
    linarith
  let d : H := p - q
  have hSub : y - q - (x - p) = d - (x - y) := by
    dsimp [d]
    abel_nf
  have hQpD : q - p = -d := by
    dsimp [d]
    abel_nf
  have hRewrite :
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ =
        ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by
    calc
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ
          = inner ℝ (-d) (x - p) + inner ℝ d (y - q) := by rw [hQpD]
      _ = -inner ℝ d (x - p) + inner ℝ d (y - q) := by simp
      _ = inner ℝ d (y - q) - inner ℝ d (x - p) := by ring_nf
      _ = inner ℝ d ((y - q) - (x - p)) := by
            symm
            rw [inner_sub_right]
      _ = inner ℝ d (d - (x - y)) := by rw [hSub]
      _ = inner ℝ d d - inner ℝ d (x - y) := by rw [inner_sub_right]
      _ = ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by rw [real_inner_self_eq_norm_sq]
  rw [hRewrite] at hSum
  have hFinal : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (x - y) := by
    linarith
  simpa [d, p, q] using hFinal

/-- Helper for Corollary 24.6: a continuous linear map that agrees pointwise with `Prox[f, hf]`
inherits self-adjointness from the gradient characterization in Proposition 2.58. -/
lemma isSelfAdjoint_of_eq_proximityOperator
    (L : H →L[ℝ] H) (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hEq : ∀ x : H, L x = Prox[f, hf] x) :
    IsSelfAdjoint L := by
  -- Route correction: avoid the timeout-heavy packaged self-adjoint theorem by comparing the
  -- transported gradient field with the explicit quadratic-model gradient pointwise.
  let g : H → ℝ := fun y : H ↦ (((f + halfSquaredNorm).asEReal∗) y).toReal
  have hGateaux :
      HasGateauxDerivativeOn g (fun x ↦ InnerProductSpace.toDual ℝ H (L x)) Set.univ := by
    simpa [g] using
      hasGateauxDerivativeOn_conjugateAddHalfSquaredNorm_toReal_of_eq_proximityOperator
        L f hf hEq
  have hQuadratic :
      g = fun x : H ↦ g 0 + (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ := by
    simpa [g] using gradient_eq_continuousLinearMap_eq_quadratic_form g L hGateaux
  rw [isSelfAdjoint_iff']
  ext x
  -- Compare the given gradient of `g` with the quadratic-model gradient at the same point.
  have hGradG : HasGradientAt g (L x) x :=
    hasGradientAt_of_hasGateauxDerivativeOn_univ_linearMap g L hGateaux x
  have hGradQuadratic :
      HasGradientAt (fun y : H ↦ g 0 + (1 / 2 : ℝ) * ⟪L y, y⟫_ℝ)
        ((1 / 2 : ℝ) • ((L + L.adjoint) x)) x :=
    halfQuadraticModel_hasGradientAt L (g 0) x
  have hRewritten :
      HasGradientAt g ((1 / 2 : ℝ) • ((L + L.adjoint) x)) x := by
    rw [hQuadratic]
    simpa using hGradQuadratic
  have hx : L x = (1 / 2 : ℝ) • ((L + L.adjoint) x) := hGradG.unique hRewritten
  -- Clear the factor `1 / 2` and isolate the adjoint term pointwise.
  have hSum : L x + L x = L x + L.adjoint x := by
    calc
      L x + L x = (2 : ℝ) • L x := by simp [two_smul]
      _ = (2 : ℝ) • ((1 / 2 : ℝ) • ((L + L.adjoint) x)) := by rw [hx]
      _ = (L + L.adjoint) x := by simp [smul_smul]
      _ = L x + L.adjoint x := by simp [add_apply]
  simpa [star_eq_adjoint] using (add_left_cancel hSum).symm

/-- Helper for Corollary 24.6: a continuous linear map that agrees pointwise with `Prox[f, hf]`
is firmly nonexpansive. -/
lemma firmlyNonexpansive_of_eq_proximityOperator
    (L : H →L[ℝ] H) (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hEq : ∀ x : H, L x = Prox[f, hf] x) :
    FirmlyNonexpansive L := by
  -- Route correction: use the public proximal-point owner directly instead of Proposition 12.28's
  -- private `proximalSelection` notation.
  have hProx : FirmlyNonexpansive (Prox[f, hf]) := by
    rw [firmlyNonexpansive_iff_norm_sq_le_inner]
    intro x y
    simpa using proximityOperator_pairwise_firmInequality_of_mem_gammaZero f hf x y
  simpa [funext hEq] using hProx

/-- Helper for Corollary 24.6: the quadratic functional attached to `L` is
`x ↦ (1 / 2) * ⟪L x, x⟫_ℝ`. -/
noncomputable def quadraticPotentialToReal (L : H →L[ℝ] H) : H → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ

/-- Helper for Corollary 24.6: if `L` is self-adjoint, then the quadratic functional
`x ↦ (1 / 2) * ⟪L x, x⟫_ℝ` has gradient `L x`. -/
lemma hasGradientAt_quadraticPotentialToReal_of_isSelfAdjoint
    (L : H →L[ℝ] H) (hSelf : IsSelfAdjoint L) (x : H) :
    HasGradientAt (quadraticPotentialToReal L) (L x) x := by
  have hfun_eq :
      (fun y : H ↦ (0 : ℝ) + (1 / 2 : ℝ) * quadratic_affine_functional L (0 : H) y) =
        quadraticPotentialToReal L := by
    funext y
    simp [quadraticPotentialToReal, quadratic_affine_functional]
  have hquad :
      HasGradientAt
        (fun y : H ↦ (0 : ℝ) + (1 / 2 : ℝ) * quadratic_affine_functional L (0 : H) y)
        ((1 / 2 : ℝ) • (((L + L.adjoint) x) - (0 : H))) x := by
    have hbase :
        HasGradientAt
          (quadratic_affine_functional L (0 : H))
          (((L + L.adjoint) x) - (0 : H)) x := by
      simpa using quadratic_affine_functional_hasGradientAt L (0 : H) x
    have hscaled := hbase.hasFDerivAt.const_smul (1 / 2 : ℝ)
    simpa using hscaled.const_add (0 : ℝ) |>.hasGradientAt
  have hgrad_eq : ((1 / 2 : ℝ) • (((L + L.adjoint) x) - (0 : H))) = L x := by
    calc
      ((1 / 2 : ℝ) • (((L + L.adjoint) x) - (0 : H)))
          = (1 / 2 : ℝ) • (L x + L x) := by
              simp [hSelf.adjoint_eq]
      _ = (1 / 2 : ℝ) • ((2 : ℝ) • L x) := by rw [two_smul]
      _ = L x := by
            rw [smul_smul]
            norm_num
  -- Rewrite the normalized quadratic-affine model to the target quadratic functional.
  convert hquad using 1
  · exact hfun_eq.symm
  · exact hgrad_eq.symm

/-- Helper for Corollary 24.6: if `L` is monotone, then
`x ↦ (1 / 2) * ⟪L x, x⟫_ℝ` is convex on `H`. -/
lemma quadraticPotentialToReal_convexOn_univ_of_isMonotone
    (L : H →L[ℝ] H) (hMono : L.toLinearMap.IsMonotone) :
    ConvexOn ℝ Set.univ (quadraticPotentialToReal L) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  rw [hb_eq]
  have hgap :
      a * quadraticPotentialToReal L x + (1 - a) * quadraticPotentialToReal L y -
          quadraticPotentialToReal L (a • x + (1 - a) • y) =
        (1 / 2 : ℝ) * (a * (1 - a)) * ⟪L (x - y), x - y⟫_ℝ := by
    simp [quadraticPotentialToReal, ContinuousLinearMap.map_add,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      sub_eq_add_neg]
    ring
  have hab_nonneg : 0 ≤ a * (1 - a) := mul_nonneg ha (sub_nonneg.mpr (by linarith))
  have hmono_nonneg : 0 ≤ ⟪L (x - y), x - y⟫_ℝ := hMono (x - y)
  have hgap_nonneg :
      0 ≤
        a * quadraticPotentialToReal L x + (1 - a) * quadraticPotentialToReal L y -
          quadraticPotentialToReal L (a • x + (1 - a) • y) := by
    rw [hgap]
    exact mul_nonneg (mul_nonneg (by norm_num) hab_nonneg) hmono_nonneg
  exact sub_nonneg.mp hgap_nonneg

/-- Helper for Corollary 24.6: a self-adjoint monotone contraction is the proximity operator of
the shifted conjugate determined by the Moreau-envelope characterization applied to
`x ↦ (1 / 2) * ⟪L x, x⟫_ℝ`. -/
lemma exists_eq_proximityOperator_of_isSelfAdjoint_and_isMonotone_and_norm_le_one_aux
    (L : H →L[ℝ] H) (hSelf : IsSelfAdjoint L) (hMono : L.toLinearMap.IsMonotone)
    (hNorm : ‖L‖ ≤ 1) :
    ∃ (h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)), L = Prox[h, hh] := by
  let β : Set.Ioi (0 : ℝ) := ⟨1, by simp⟩
  let φ : H → ℝ := quadraticPotentialToReal L
  have hgradAt : ∀ x : H, HasGradientAt φ (L x) x := by
    intro x
    simpa [φ] using hasGradientAt_quadraticPotentialToReal_of_isSelfAdjoint L hSelf x
  -- Route correction: avoid the broken `Theorem_18_15` import by using Corollary 18.19's
  -- Moreau-envelope characterization and then recover the prox formula through Proposition 24.4.
  -- The quadratic functional `φ` is the smooth convex input for this Moreau characterization.
  have hdiff : Differentiable ℝ φ := by
    intro x
    exact (hgradAt x).differentiableAt
  have hcont : Continuous φ := hdiff.continuous
  have hconv : ConvexOn ℝ Set.univ φ :=
    quadraticPotentialToReal_convexOn_univ_of_isMonotone L hMono
  have hφGamma : φ.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ φ hcont hconv
  have hgrad : ∇ φ = L := gradient_eq hgradAt
  have hLip : LipschitzWith (Real.toNNReal (β : ℝ)) (∇ φ) := by
    rw [hgrad]
    -- Package `‖L‖ ≤ 1` as a unit Lipschitz estimate for the linear operator.
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hopNorm :
        ‖L (x - y)‖ ≤ 1 * ‖x - y‖ := by
      have hbound :=
        (ContinuousLinearMap.opNorm_le_iff (show (0 : ℝ) ≤ 1 by positivity)).mp hNorm (x - y)
      simpa using hbound
    simpa [β, dist_eq_norm, map_sub] using hopNorm
  have hinner :
      ∀ x y : H, ⟪x - y, ∇ φ x - ∇ φ y⟫_ℝ ≤ (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) := by
    intro x y
    have hgrad_norm :
        ‖∇ φ x - ∇ φ y‖ ≤ (β : ℝ) * ‖x - y‖ := by
      simpa [dist_eq_norm, Real.toNNReal_of_nonneg β.2.le] using hLip.dist_le_mul x y
    calc
      ⟪x - y, ∇ φ x - ∇ φ y⟫_ℝ ≤ ‖x - y‖ * ‖∇ φ x - ∇ φ y‖ := by
        exact real_inner_le_norm _ _
      _ ≤ ‖x - y‖ * ((β : ℝ) * ‖x - y‖) := by
        gcongr
      _ = (β : ℝ) * ‖x - y‖ ^ (2 : ℕ) := by
        ring_nf
  have hgapConv :
      ConvexOn ℝ Set.univ (fun x : H ↦ ((β : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - φ x) :=
    quadratic_gap_convex_of_gradient_upper_bound φ β hdiff hinner
  let h : H → Set.Ioi (⊥ : EReal) := conjugateSubInvHalfSquaredNorm φ β
  have hh : h ∈ Γ₀(H) := by
    simpa [h] using
      conjugateSubInvHalfSquaredNorm_mem_gammaZero_of_halfSquaredNorm_sub_convex
        φ hcont hconv β hgapConv
  have hshifted :
      (h + halfSquaredNorm).asEReal = φ.toEReal.asEReal∗ := by
    ext u
    change ((conjugateSubInvHalfSquaredNorm φ β u : EReal) + (halfSquaredNorm u : EReal)) =
      φ.toEReal.asEReal∗ u
    simpa [β, conjugateSubInvHalfSquaredNorm_apply, halfSquaredNorm_apply] using
      (EReal.sub_add_cancel
        (a := φ.toEReal.asEReal∗ u)
        (b := ((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ))))
  have hbiconj : (φ.toEReal.asEReal∗)∗ = φ.toEReal.asEReal :=
    biconjugate_eq_of_mem_gammaZero hφGamma
  have hEnvelope :
      (fun y : H ↦ (((h + halfSquaredNorm).asEReal∗) y).toReal) = φ := by
    funext x
    have hshifted_conj : (h + halfSquaredNorm).asEReal∗ = (φ.toEReal.asEReal∗)∗ :=
      congrArg (fun g : H → EReal ↦ g∗) hshifted
    have hx :
        ((h + halfSquaredNorm).asEReal∗) x = (φ.toEReal.asEReal) x := by
      calc
        ((h + halfSquaredNorm).asEReal∗) x = ((φ.toEReal.asEReal∗)∗) x := by
          exact congrFun hshifted_conj x
        _ = (φ.toEReal.asEReal) x := by
          exact congrFun hbiconj x
    -- Convert the Moreau-envelope identity back to a real-valued equality.
    simpa [Function.toEReal_apply, Function.asEReal_apply] using congrArg EReal.toReal hx
  have hproxGrad :
      Prox[h, hh] = ∇ (fun y : H ↦ (((h + halfSquaredNorm).asEReal∗) y).toReal) :=
    proximityOperator_eq_gradient_conjugate_add_halfSquaredNorm (f := h) (hf := hh)
  -- Replace the prox envelope by `φ`, whose gradient is already identified with `L`.
  refine ⟨h, hh, ?_⟩
  calc
    L = ∇ φ := by
      simpa using hgrad.symm
    _ = ∇ (fun y : H ↦ (((h + halfSquaredNorm).asEReal∗) y).toReal) := by
      rw [← hEnvelope]
    _ = Prox[h, hh] := by
      simpa using hproxGrad.symm

/-- Corollary 24.6: Moreau's characterization of linear proximity operators. A bounded operator
`L : H →L[ℝ] H` is the proximity operator `Prox[f, hf]` of some `f ∈ Γ₀(H)` if and only if `L`
is self-adjoint, monotone, and satisfies `‖L‖ ≤ 1`. -/
theorem exists_eq_proximityOperator_iff_isSelfAdjoint_and_isMonotone_and_norm_le_one
    (L : H →L[ℝ] H) :
    (∃ (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)), L = Prox[f, hf]) ↔
      IsSelfAdjoint L ∧ L.toLinearMap.IsMonotone ∧ ‖L‖ ≤ 1 := by
  constructor
  · rintro ⟨f, hf, hEq⟩
    have hEqFun : ∀ x : H, L x = Prox[f, hf] x := fun x ↦ congrFun hEq x
    -- First view the proximal operator as a gradient field so Proposition 2.58 yields symmetry.
    have hSelf : IsSelfAdjoint L := isSelfAdjoint_of_eq_proximityOperator L f hf hEqFun
    have hFirm : FirmlyNonexpansive L := firmlyNonexpansive_of_eq_proximityOperator L f hf hEqFun
    -- Then package the firm-nonexpansive consequences into the monotonicity and norm bounds.
    rcases isMonotone_and_norm_le_one_of_firmlyNonexpansive hFirm with ⟨hMono, hNorm⟩
    exact ⟨hSelf, hMono, hNorm⟩
  · rintro ⟨hSelf, hMono, hNorm⟩
    -- The reverse direction follows from the Corollary 18.19 Moreau characterization applied to
    -- the quadratic potential of `L`.
    exact
      exists_eq_proximityOperator_of_isSelfAdjoint_and_isMonotone_and_norm_le_one_aux
        L hSelf hMono hNorm

/-- Pointwise form of Corollary 24.6. -/
theorem exists_eq_proximityOperator_pointwise_iff_isSelfAdjoint_and_isMonotone_and_norm_le_one
    (L : H →L[ℝ] H) :
    (∃ (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)), ∀ x : H, L x = Prox[f, hf] x) ↔
      IsSelfAdjoint L ∧ L.toLinearMap.IsMonotone ∧ ‖L‖ ≤ 1 := by
  constructor
  · rintro ⟨f, hf, hEq⟩
    exact
      (exists_eq_proximityOperator_iff_isSelfAdjoint_and_isMonotone_and_norm_le_one L).1
        ⟨f, hf, funext hEq⟩
  · rintro hL
    rcases
      (exists_eq_proximityOperator_iff_isSelfAdjoint_and_isMonotone_and_norm_le_one L).2 hL with
      ⟨f, hf, hEq⟩
    exact ⟨f, hf, fun x ↦ congrFun hEq x⟩

end Characterizations

end ContinuousLinearMap
