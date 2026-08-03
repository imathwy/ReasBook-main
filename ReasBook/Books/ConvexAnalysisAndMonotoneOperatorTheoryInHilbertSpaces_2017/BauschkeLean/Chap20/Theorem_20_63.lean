import BauschkeLean.Chap14.Corollary_14_8
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_35
import BauschkeLean.Chap20.Definition_20_51
import BauschkeLean.Chap20.Corollary_20_47
import BauschkeLean.Chap20.PairingEqualityOperator
import BauschkeLean.Chap20.Proposition_20_56

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator
open ERealFunction
open WithLp

universe u

namespace SetValuedOperator

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/- Source/core/bridge triage:
- `source-facing`: Theorem 20.63 constructs the proximal-average contact operator attached to a
  monotone operator `A` with nonempty graph.
- `core/canonical`: the owner abstractions are the Fitzpatrick function `F[A]`, the Chapter 9
  bridge `properIoi`, the proximal average `pav`, autoconjugacy, and the pairing-contact owner
  `pairingEqualityOperator`.
- `bridge/view`: the file packages the textbook intermediate function
  `G = pav(F_A, F_A^{*T})` into the canonical `Γ₀(H × H)` and pairing-contact APIs; it should
  therefore reuse those owners directly rather than introduce a parallel contact-set wrapper.

Primitive data: the operator `A`, monotonicity of `A`, and graph nonemptiness.
Derived API: the packaged proximal-average representative, its `Γ₀` membership and
autoconjugacy, and the resulting maximal-monotone extension theorem. -/

-- Semantic recall note: `lean_leansearch` did not return useful Fitzpatrick/proximal-average
-- hits for this item, so the owner/API choice follows the nearby Chapter 20 pairing-contact
-- precedent.

section ProximalAverageBridge

variable (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : (gra A).Nonempty)

/-- Helper fact: the Fitzpatrick representative used in Theorem 20.63 is proper. -/
private theorem fitzpatrickFunctionLocal_isProper_of_graph_nonempty_of_monotone :
    (hA_graph : (gra A).Nonempty) → (hA_mono : A.IsMonotone) →
    IsProper F[A] := by
  -- Reuse Proposition 20.56 directly so the local owner stays identical to the chapter API.
  intro hA_graph hA_mono
  exact fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone A hA_graph hA_mono

/-- Helper fact: the Fitzpatrick representative used in Theorem 20.63 belongs to `Γ₀(H × H)`. -/
private theorem fitzpatrickFunctionLocal_mem_gammaZero :
    (hA_mono : A.IsMonotone) → (hA_graph : (gra A).Nonempty) →
    properIoi (F[A]) (fitzpatrickFunctionLocal_isProper_of_graph_nonempty_of_monotone A hA_graph
      hA_mono) ∈ Γ₀(H × H) := by
  -- Proposition 20.56 already supplies the canonical `Γ₀` package for the Fitzpatrick function.
  intro hA_mono hA_graph
  simpa [fitzpatrickFunctionLocal_isProper_of_graph_nonempty_of_monotone] using
    fitzpatrickFunction_mem_gammaZero A hA_graph hA_mono

/-- The packaged Fitzpatrick representative used in Theorem 20.63. -/
private abbrev fitzpatrickRepresentative (hA_mono : A.IsMonotone) (hA_graph : (gra A).Nonempty) :
    H × H → Set.Ioi (⊥ : EReal) :=
  properIoi (F[A]) (fitzpatrickFunctionLocal_isProper_of_graph_nonempty_of_monotone A hA_graph
    hA_mono)

section HilbertSpace

variable [CompleteSpace H]

attribute [local instance] ERealFunction.prod_completeSpace_l2

/-- Helper fact: the transpose-conjugate of a `Γ₀(H × H)` function again belongs to `Γ₀(H × H)`.
-/
private theorem gammaZeroConjugateTransposeLocal_mem_gammaZero
    {F : H × H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H × H)) :
    F∗ᵀ[hF] ∈ Γ₀(H × H) := by
  -- Proposition 13.38 already packages transpose-conjugates inside `Γ₀(H × H)`.
  exact gammaZeroConjugateTranspose_mem_gammaZero hF

/-- The proximal-average packaged representative attached to the Fitzpatrick function of `A`. -/
private abbrev proximalAverageRepresentative (hA_mono : A.IsMonotone)
    (hA_graph : (gra A).Nonempty) :
    H × H → Set.Ioi (⊥ : EReal) :=
  properIoi
    (pav(fitzpatrickRepresentative A hA_mono hA_graph,
      (fitzpatrickRepresentative A hA_mono hA_graph)∗ᵀ[
        fitzpatrickFunctionLocal_mem_gammaZero A hA_mono hA_graph]))
    (isProper_proximalAverage
      (fitzpatrickRepresentative A hA_mono hA_graph)
      ((fitzpatrickRepresentative A hA_mono hA_graph)∗ᵀ[
        fitzpatrickFunctionLocal_mem_gammaZero A hA_mono hA_graph])
      (fitzpatrickFunctionLocal_mem_gammaZero A hA_mono hA_graph)
      (gammaZeroConjugateTransposeLocal_mem_gammaZero
        (fitzpatrickFunctionLocal_mem_gammaZero A hA_mono hA_graph)))

/-- Helper fact: the proximal-average representative `G` belongs to `Γ₀(H × H)`. -/
private theorem proximalAverage_fitzpatrickFunction_mem_gammaZero :
    proximalAverageRepresentative A hA_mono hA_graph ∈ Γ₀(H × H) := by
  -- Corollary 14.8(1) packages `G = pav(F_A, F_A^{*T})` back into `Γ₀(H × H)`.
  exact proximalAverage_mem_gammaZero
    (fitzpatrickRepresentative A hA_mono hA_graph)
    ((fitzpatrickRepresentative A hA_mono hA_graph)∗ᵀ[
      fitzpatrickFunctionLocal_mem_gammaZero A hA_mono hA_graph])
    (fitzpatrickFunctionLocal_mem_gammaZero A hA_mono hA_graph)
    (gammaZeroConjugateTransposeLocal_mem_gammaZero
      (fitzpatrickFunctionLocal_mem_gammaZero A hA_mono hA_graph))

/-- Helper for Theorem 20.63: the proximal average is symmetric in its two arguments. -/
private theorem proximalAverageKernel_midpoint_swap_local
    (f g : H × H → Set.Ioi (⊥ : EReal)) (x y : H × H) :
    (proximalAverageKernel f g
        ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) =
      (proximalAverageKernel g f (y, (2 : ℝ) • x - y) : EReal) := by
  -- Route correction: use the same midpoint involution as Proposition 14.7, but apply it
  -- directly in the local product space instead of expanding the `ℓ²` norm square by hand.
  have hcompanion : (2 : ℝ) • x - ((2 : ℝ) • x - y) = y := by
    simp
  have hnorm : ‖(2 : ℝ) • x - y - y‖ = ‖y - ((2 : ℝ) • x - y)‖ := by
    have hneg : (2 : ℝ) • x - y - y = -(y - ((2 : ℝ) • x - y)) := by
      simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hnorm_left : ‖(2 : ℝ) • x - y - y‖ = ‖WithLp.toLp 2 ((2 : ℝ) • x - y - y)‖ := by
      simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
        (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := H) (β := H)
          ((2 : ℝ) • x - y - y))
    have hnorm_right : ‖y - ((2 : ℝ) • x - y)‖ = ‖WithLp.toLp 2 (y - ((2 : ℝ) • x - y))‖ := by
      simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
        (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := H) (β := H)
          (y - ((2 : ℝ) • x - y)))
    have hnorm_lp :
        ‖WithLp.toLp 2 ((2 : ℝ) • x - y - y)‖ = ‖WithLp.toLp 2 (y - ((2 : ℝ) • x - y))‖ := by
      calc
        ‖WithLp.toLp 2 ((2 : ℝ) • x - y - y)‖ =
            ‖WithLp.toLp 2 (-(y - ((2 : ℝ) • x - y)))‖ := by rw [hneg]
        _ = ‖-WithLp.toLp 2 (y - ((2 : ℝ) • x - y))‖ := by simp
        _ = ‖WithLp.toLp 2 (y - ((2 : ℝ) • x - y))‖ := by
              simpa using norm_neg (WithLp.toLp 2 (y - ((2 : ℝ) • x - y)))
    calc
      ‖(2 : ℝ) • x - y - y‖ = ‖WithLp.toLp 2 ((2 : ℝ) • x - y - y)‖ := hnorm_left
      _ = ‖WithLp.toLp 2 (y - ((2 : ℝ) • x - y))‖ := hnorm_lp
      _ = ‖y - ((2 : ℝ) • x - y)‖ := hnorm_right.symm
  rw [proximalAverageKernel_apply, proximalAverageKernel_apply]
  simp [hcompanion, hnorm, add_assoc, add_comm]

/-- Helper for Theorem 20.63: the proximal average is symmetric in its two arguments. -/
private theorem proximalAverage_comm_local
    (f g : H × H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H × H)) (hg : g ∈ Γ₀(H × H)) :
    pav(f, g) = pav(g, f) := by
  -- Reindex the defining infimum by the involution `y ↦ (2 : ℝ) • x - y`.
  have hdomf : (effectiveDomain f).Nonempty := hf.2.nonempty
  have hdomg : (effectiveDomain g).Nonempty := hg.2.nonempty
  let _ := hdomf
  let _ := hdomg
  ext x
  rw [proximalAverage_apply_eq_iInf_parameterized (f := f) (g := g) (x := x)]
  rw [proximalAverage_apply_eq_iInf_parameterized (f := g) (g := f) (x := x)]
  apply le_antisymm
  · refine le_iInf fun y ↦ ?_
    have hterm :
        (⨅ z : H × H, (proximalAverageKernel f g (z, (2 : ℝ) • x - z) : EReal)) ≤
          (proximalAverageKernel f g
            ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) :=
      iInf_le
        (fun z : H × H ↦
          (proximalAverageKernel f g (z, (2 : ℝ) • x - z) : EReal))
        ((2 : ℝ) • x - y)
    calc
      (⨅ z : H × H, (proximalAverageKernel f g (z, (2 : ℝ) • x - z) : EReal)) ≤
          (proximalAverageKernel f g
            ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) := hterm
      _ = (proximalAverageKernel g f (y, (2 : ℝ) • x - y) : EReal) :=
        proximalAverageKernel_midpoint_swap_local (f := f) (g := g) (x := x) (y := y)
  · refine le_iInf fun y ↦ ?_
    have hterm :
        (⨅ z : H × H, (proximalAverageKernel g f (z, (2 : ℝ) • x - z) : EReal)) ≤
          (proximalAverageKernel g f
            ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) :=
      iInf_le
        (fun z : H × H ↦
          (proximalAverageKernel g f (z, (2 : ℝ) • x - z) : EReal))
        ((2 : ℝ) • x - y)
    calc
      (⨅ z : H × H, (proximalAverageKernel g f (z, (2 : ℝ) • x - z) : EReal)) ≤
          (proximalAverageKernel g f
            ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) := hterm
      _ = (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal) :=
        proximalAverageKernel_midpoint_swap_local (f := g) (g := f) (x := x) (y := y)

/-- Helper for Theorem 20.63: transpose commutes with the proximal average on `H × H`. -/
private theorem proximalAverage_transpose_local
    (F G : (H × H) → Set.Ioi (⊥ : EReal)) :
    (pav(F, G))ᵀ = pav(Fᵀ, Gᵀ) := by
  -- Unfold transpose and the defining infimum for `pav`, then swap both coordinates.
  ext p
  rcases p with ⟨u, x⟩
  simp only [transpose_apply, proximalAverage_apply]
  congr 1
  exact (Equiv.prodComm H H).iInf_congr fun y ↦ by
    rcases y with ⟨a, b⟩
    simp only [Equiv.prodComm_apply]
    congr 2
    change ‖(u - b, x - a)‖ ^ 2 = ‖(x - a, u - b)‖ ^ 2
    rw [show ‖(u - b, x - a)‖ = ‖toLp 2 (u - b, x - a)‖ by rfl]
    rw [show ‖(x - a, u - b)‖ = ‖toLp 2 (x - a, u - b)‖ by rfl]
    rw [prod_norm_sq_eq_of_L2, prod_norm_sq_eq_of_L2]
    simpa using add_comm (‖u - b‖ ^ 2) (‖x - a‖ ^ 2)

/-- Helper for Theorem 20.63: the proximity operator of `F^{*T}` is the swap-Moreau correction
`p ↦ p - (Prox_F (p.swap)).swap`. -/
private theorem
    proximityOperator_gammaZeroConjugateTransposeLocal_eq_id_sub_swap_proximityOperator_swap
    {F : H × H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H × H)) :
    Prox[(F∗ᵀ[hF]), gammaZeroConjugateTransposeLocal_mem_gammaZero hF] =
      fun p : H × H ↦
        p - (Prox[F, hF] p.swap).swap := by
  funext p
  rcases p with ⟨x, u⟩
  have hswap_prox :
      Prox[(F∗ᵀ[hF]), gammaZeroConjugateTransposeLocal_mem_gammaZero hF] (x, u) =
        (Prox⋆[F, hF] (u, x)).swap := by
    -- Transport proximality for `F^*` across the coordinate swap.
    symm
    apply eq_proximityOperator_of_isProxPoint (F∗ᵀ[hF])
      (hasUniqueProxPoint_of_mem_gammaZero (F∗ᵀ[hF])
        (gammaZeroConjugateTransposeLocal_mem_gammaZero hF))
    rw [isProxPoint_iff_forall_inner_add_le (F∗ᵀ[hF])
      (gammaZeroConjugateTransposeLocal_mem_gammaZero hF).2 (x, u)
      ((Prox⋆[F, hF] (u, x)).swap)]
    intro y
    rcases y with ⟨a, b⟩
    have hproxStar : IsProxPoint (F∗[hF]) (u, x) (Prox⋆[F, hF] (u, x)) :=
      proximityOperator_isProxPoint (F∗[hF])
        (hasUniqueProxPoint_of_mem_gammaZero (F∗[hF]) (gammaZeroConjugate_mem_gammaZero hF))
        (u, x)
    have hineq :=
      (isProxPoint_iff_forall_inner_add_le (F∗[hF])
        (gammaZeroConjugate_mem_gammaZero hF).2 (u, x) (Prox⋆[F, hF] (u, x))).1 hproxStar
    rcases hq : Prox⋆[F, hF] (u, x) with ⟨q₁, q₂⟩
    have hswap_inner :
        ⟪(a, b) - (q₁, q₂).swap, (x, u) - (q₁, q₂).swap⟫_ℝ =
          ⟪(b, a) - (q₁, q₂), (u, x) - (q₁, q₂)⟫_ℝ := by
      rw [show ⟪(a, b) - (q₁, q₂).swap, (x, u) - (q₁, q₂).swap⟫_ℝ =
          ⟪a - q₂, x - q₂⟫_ℝ + ⟪b - q₁, u - q₁⟫_ℝ by rfl]
      rw [show ⟪(b, a) - (q₁, q₂), (u, x) - (q₁, q₂)⟫_ℝ =
          ⟪b - q₁, u - q₁⟫_ℝ + ⟪a - q₂, x - q₂⟫_ℝ by rfl]
      simp [add_comm]
    have hswap_inner_ereal :
        (((⟪(a, b) - (q₁, q₂).swap, (x, u) - (q₁, q₂).swap⟫_ℝ : ℝ) : EReal)) =
          (((⟪(b, a) - (q₁, q₂), (u, x) - (q₁, q₂)⟫_ℝ : ℝ) : EReal)) := by
      exact_mod_cast hswap_inner
    have hineq' := hineq (b, a)
    rw [hswap_inner_ereal]
    simpa [hq, gammaZeroConjugateTranspose_apply, transpose_apply, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using hineq'
  have hmoreau_swap :
      (Prox⋆[F, hF] (u, x)).swap + (Prox[F, hF] (u, x)).swap = (x, u) := by
    -- Apply Moreau's identity at the swapped base point and swap the resulting equality back.
    simpa [add_comm] using congrArg Prod.swap
      (congrFun (proximityOperator_add_conjugateProximityOperator_eq_id_of_mem_gammaZero F hF)
        (u, x))
  calc
    Prox[(F∗ᵀ[hF]), gammaZeroConjugateTransposeLocal_mem_gammaZero hF] (x, u) =
        (Prox⋆[F, hF] (u, x)).swap := hswap_prox
    _ = (x, u) - (Prox[F, hF] (u, x)).swap := by
          exact (eq_sub_iff_add_eq.2 hmoreau_swap)

/-- Helper for Theorem 20.63: for an autoconjugate `Γ₀(H × H)` owner, the proximal fixed-point
identity at `(x + u, x + u)` forces the pairing-contact equality `F(x, u) = ⟪x, u⟫`. -/
private theorem autoconjugate_eq_inner_of_eq_prox_pair
    {F : H × H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H × H))
    (hauto : autoconjugate F.asEReal) {x u : H}
    (hprox : (x, u) = Prox[F, hF] (x + u, x + u)) :
    (F (x, u) : EReal) = pairing (x, u) := by
  have hsub : (u, x) ∈ (∂ F) (x, u) := by
    -- Rewrite the proximal fixed-point identity as the subgradient inequality at `(x, u)`.
    have hproxPoint : IsProxPoint F (x + u, x + u) (x, u) := by
      rw [hprox]
      exact proximityOperator_isProxPoint F (hasUniqueProxPoint_of_mem_gammaZero F hF)
        (x + u, x + u)
    rw [isProxPoint_iff_forall_inner_add_le F hF.2 (x + u, x + u) (x, u)] at hproxPoint
    rw [mem_subdifferential_iff]
    intro y
    have hres : (x + u, x + u) - (x, u) = (u, x) := by
      simp
    have hy := hproxPoint y
    rw [hres] at hy
    exact hy
  have hproper : IsProper F.asEReal := isProper_of_mem_gammaZero hF
  have hpair_le_F : pairing (x, u) ≤ (F (x, u) : EReal) := by
    -- Proposition 13.36 supplies the canonical lower bound for autoconjugate functions.
    simpa [pairing_apply] using pairing_le_autoconjugate hproper hauto x u
  have hsum :
      (u, x) ∈ (∂ F) (x, u) ↔
        (F (x, u) : EReal) + (F (x, u) : EReal) = pairing (x, u) + pairing (x, u) := by
    rw [mem_subdifferential_iff_fenchel_young_eq (f := F) hF.2.nonempty (x, u) (u, x),
      conjugate_swap_eq_of_autoconjugate hauto x u]
    have hpair_prod :
        (((⟪(x, u), (u, x)⟫_ℝ : ℝ) : EReal)) = pairing (x, u) + pairing (x, u) := by
      change (((⟪x, u⟫_ℝ + ⟪u, x⟫_ℝ : ℝ) : EReal)) =
        pairing (x, u) + pairing (x, u)
      simp [pairing_apply, real_inner_comm, EReal.coe_add]
    rw [hpair_prod]
  have hsub_eq :
      (F (x, u) : EReal) + (F (x, u) : EReal) = pairing (x, u) + pairing (x, u) := by
    exact (hsum.mp hsub)
  have hle : (F (x, u) : EReal) ≤ pairing (x, u) := by
    have hle_shift :
        (F (x, u) : EReal) + pairing (x, u) ≤ pairing (x, u) + pairing (x, u) := by
      calc
        (F (x, u) : EReal) + pairing (x, u) ≤ (F (x, u) : EReal) + (F (x, u) : EReal) := by
          simpa [add_comm] using add_le_add_right hpair_le_F (F (x, u) : EReal)
        _ = pairing (x, u) + pairing (x, u) := hsub_eq
    simpa [pairing_apply] using
      (EReal.addLECancellable_coe ⟪x, u⟫_ℝ).add_le_add_iff_right.mp hle_shift
  exact le_antisymm hle hpair_le_F

-- Proof sketch: let `F_A` be `properIoi (F[A]) ...` and let
-- `G := pav(F_A, F_A^{*T})`, viewed through the canonical packaged representative `G`.
-- Proposition 20.56(3) puts `F_A` in `Γ₀(H × H)`, Proposition 16.66 identifies the proximity
-- operator of `F_A^{*T}`, and Corollary 14.8 shows that `G ∈ Γ₀(H × H)` with
-- `G^* = G^T`, hence `G` is autoconjugate. The canonical owner theorem
-- `pairingEqualityOperator_isMaximallyMonotone_of_mem_gammaZero_of_autoconjugate` then yields
-- maximal monotonicity of the pairing-contact operator. For graph inclusion,
-- Proposition 20.56(9), Corollary 14.8(4), Proposition 16.66, and Proposition 16.65 show that
-- every `(x, u) ∈ gra A` is a fixed contact point of `G`, so `(x, u)` lies in the graph of the
-- extension operator.
/-- Helper fact: the proximal-average representative `G` is autoconjugate. -/
private theorem proximalAverage_fitzpatrickFunction_autoconjugate :
    autoconjugate (proximalAverageRepresentative A hA_mono hA_graph).asEReal := by
  let FA := fitzpatrickRepresentative A hA_mono hA_graph
  let hFA := fitzpatrickFunctionLocal_mem_gammaZero A hA_mono hA_graph
  let FAT := FA∗ᵀ[hFA]
  let hFAT := gammaZeroConjugateTransposeLocal_mem_gammaZero hFA
  have hFAT_conj :
      FAT∗[hFAT] = FAᵀ := by
    -- Rewrite the conjugate of `F_A^{*T}` as the transpose of `F_A^{**}` and then collapse the
    -- biconjugate with Fenchel--Moreau.
    funext p
    rcases p with ⟨x, u⟩
    apply Subtype.ext
    calc
      ((FAT∗[hFAT]) (x, u) : EReal) = FAT.asEReal∗ (x, u) := by
        simpa [FAT] using gammaZeroConjugate_apply FAT hFAT (x, u)
      _ = ((FA.asEReal∗)ᵀ)∗ (x, u) := by
        rfl
      _ = (FA.asEReal∗∗)ᵀ (x, u) := by
        rw [← transpose_conjugate (FA.asEReal∗)]
      _ = FA.asERealᵀ (x, u) := by
        rw [biconjugate_eq_of_mem_gammaZero hFA]
      _ = (FAᵀ (x, u) : EReal) := by
        rfl
  have hFAT_transpose :
      FATᵀ = FA∗[hFA] := by
    -- Transposing `F_A^{*T}` removes the final swap and returns the conjugate of `F_A`.
    funext p
    rcases p with ⟨x, u⟩
    apply Subtype.ext
    simp [FAT, gammaZeroConjugateTranspose_apply, transpose_apply]
  have hFATT_gamma : FAᵀ ∈ Γ₀(H × H) := by
    -- Identify `F_Aᵀ` with the packaged conjugate of `F_A^{*T}` to inherit its `Γ₀` witness.
    rw [← hFAT_conj]
    exact gammaZeroConjugate_mem_gammaZero hFAT
  have hpav_comm :
      pav(FA∗[hFA], FAᵀ) = pav(FAᵀ, FA∗[hFA]) := by
    -- Proposition 14.7(i) swaps the two halves of the proximal average.
    exact proximalAverage_comm_local (FA∗[hFA]) (FAᵀ)
      (gammaZeroConjugate_mem_gammaZero hFA) hFATT_gamma
  have hpav_transpose :
      (pav(FA, FAT))ᵀ = pav(FAᵀ, FA∗[hFA]) := by
    -- Push transpose through the proximal average, then simplify the transposed second factor.
    calc
      (pav(FA, FAT))ᵀ = pav(FAᵀ, FATᵀ) := by
        exact proximalAverage_transpose_local FA FAT
      _ = pav(FAᵀ, FA∗[hFA]) := by
        rw [hFAT_transpose]
  have hpav_conj_rewrite :
      pav(FA∗[hFA], FAT∗[hFAT]) = pav(FA∗[hFA], FAᵀ) := by
    rw [hFAT_conj]
  -- Compare `G*` and `Gᵀ` pointwise after rewriting the two proximal-average factors.
  funext p
  rcases p with ⟨x, u⟩
  calc
    (proximalAverageRepresentative A hA_mono hA_graph).asEReal∗ (x, u) =
        pav(FA∗[hFA], FAT∗[hFAT]) (x, u) := by
          simpa [proximalAverageRepresentative, FA, FAT, hFAT] using
            congrFun (gammaZeroConjugate_proximalAverage FA FAT hFA hFAT) (x, u)
    _ = pav(FA∗[hFA], FAᵀ) (x, u) := by
          simpa using congrFun hpav_conj_rewrite (x, u)
    _ = pav(FAᵀ, FA∗[hFA]) (x, u) := by
          simpa using congrFun hpav_comm (x, u)
    _ = (pav(FA, FAT))ᵀ (x, u) := by
          simpa using (congrFun hpav_transpose (x, u)).symm
    _ = (proximalAverageRepresentative A hA_mono hA_graph).asERealᵀ (x, u) := by
          simpa [proximalAverageRepresentative, FA, FAT]

/-- Helper for Theorem 20.63: graph points of `A` are pairing-contact points of the proximal
average representative `G = pav(F_A, F_A^{*T})`. -/
private theorem proximalAverageRepresentative_eq_inner_of_mem_graph
    {x u : H} (hxu : (x, u) ∈ gra A) :
    ((proximalAverageRepresentative A hA_mono hA_graph) (x, u) : EReal) = pairing (x, u) := by
  let FA := fitzpatrickRepresentative A hA_mono hA_graph
  let hFA := fitzpatrickFunctionLocal_mem_gammaZero A hA_mono hA_graph
  let FAT := FA∗ᵀ[hFA]
  let hFAT := gammaZeroConjugateTransposeLocal_mem_gammaZero hFA
  let G := proximalAverageRepresentative A hA_mono hA_graph
  let hG := proximalAverage_fitzpatrickFunction_mem_gammaZero A hA_mono hA_graph
  have hprox_FA : Prox[FA, hFA] (x + u, x + u) = (x, u) := by
    -- Proposition 20.56(9) identifies graph points of `A` with proximal fixed points of `F_A`.
    simpa [FA, hFA] using
      (eq_prox_fitzpatrickFunction_of_mem_graph A hA_graph hA_mono hxu).symm
  have hprox_FAT :
      Prox[FAT, hFAT] (x + u, x + u) =
        (x + u, x + u) - (Prox[FA, hFA] (x + u, x + u)).swap := by
    -- Use the theorem-local swap-Moreau formula for the proximal map of `F_A^{*T}`.
    simpa [FAT, hFAT] using
      congrFun
        (proximityOperator_gammaZeroConjugateTransposeLocal_eq_id_sub_swap_proximityOperator_swap
          hFA)
        (x + u, x + u)
  have hprox_G :
      (x, u) = Prox[G, hG] (x + u, x + u) := by
    -- Corollary 14.8(4) makes `Prox_G` the arithmetic mean of the two proximal maps.
    calc
      (x, u) =
          (1 / 2 : ℝ) • Prox[FA, hFA] (x + u, x + u) +
            (1 / 2 : ℝ) • Prox[FAT, hFAT] (x + u, x + u) := by
              rw [hprox_FAT, hprox_FA]
              have hdiag : (x + u, x + u) - (x, u).swap = (x, u) := by
                simp
              rw [hdiag]
              calc
                (x, u) = (1 : ℝ) • (x, u) := by simp
                _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • (x, u) := by norm_num
                _ = (1 / 2 : ℝ) • (x, u) + (1 / 2 : ℝ) • (x, u) := by
                      rw [add_smul]
      _ = Prox[G, hG] (x + u, x + u) := by
            symm
            simpa [G, hG, FA, hFA, FAT, hFAT] using
              congrFun (proximityOperator_proximalAverage_eq_arithmeticMean FA FAT hFA hFAT)
                (x + u, x + u)
  -- Proposition 16.65 converts the proximal fixed-point identity into the pairing equality.
  simpa [G] using
    autoconjugate_eq_inner_of_eq_prox_pair hG
      (proximalAverage_fitzpatrickFunction_autoconjugate A hA_mono hA_graph) hprox_G

/-- Theorem 20.63 (1): if `A` is monotone and `gra A` is nonempty, set
`G = pav(F_A, F_A^{*T})` and define `B` by
`gra B = {(x, u) | G(x, u) = ⟪x, u⟫}`. Then the canonical pairing-contact operator
`pairingEqualityOperator G` is maximally monotone. -/
theorem pairingEqualityOperator_proximalAverage_fitzpatrickFunction_isMaximallyMonotone :
    Maximal IsMonotone
      (pairingEqualityOperator (proximalAverageRepresentative A hA_mono hA_graph)) := by
  -- Corollary 20.47 is the textbook maximality step once `G ∈ Γ₀` and `G` is autoconjugate.
  exact pairingEqualityOperator_isMaximallyMonotone_of_mem_gammaZero_of_autoconjugate
    (proximalAverageRepresentative A hA_mono hA_graph)
    (proximalAverage_fitzpatrickFunction_mem_gammaZero A hA_mono hA_graph)
    (proximalAverage_fitzpatrickFunction_autoconjugate A hA_mono hA_graph)

/-- Theorem 20.63 (2): with the same proximal-average representative `G`, the canonical
pairing-contact operator `pairingEqualityOperator G` extends `A`. -/
theorem pairingEqualityOperator_proximalAverage_fitzpatrickFunction_extends :
    A ≤ pairingEqualityOperator (proximalAverageRepresentative A hA_mono hA_graph) := by
  intro x u hu
  -- Route correction: use the source contact computation at graph points of `A`.
  rw [mem_pairingEqualityOperator_iff]
  exact proximalAverageRepresentative_eq_inner_of_mem_graph A hA_mono hA_graph hu

/-- Graph-form companion to Theorem 20.63: every graph point of `A` lies in the graph of the
proximal-average pairing-contact operator. This is the graph-containment reformulation of the
canonical extension claim `A ≤ pairingEqualityOperator G`. -/
theorem graph_subset_pairingEqualityOperator_proximalAverage_fitzpatrickFunction :
    gra A ⊆ gra (pairingEqualityOperator (proximalAverageRepresentative A hA_mono hA_graph)) := by
  intro p hp
  rcases p with ⟨x, u⟩
  -- Rewrite graph membership on both sides and invoke the pointwise extension theorem.
  rw [SetValuedOperator.mem_graph] at hp ⊢
  exact (pairingEqualityOperator_proximalAverage_fitzpatrickFunction_extends A hA_mono hA_graph)
    x hp

end HilbertSpace

end ProximalAverageBridge

end

end SetValuedOperator
