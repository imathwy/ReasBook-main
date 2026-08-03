import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap08.Proposition_8_2
import BauschkeLean.Chap08.Proposition_8_4
import BauschkeLean.Chap09.Proposition_9_8
import BauschkeLean.Chap13.Proposition_13_19
import BauschkeLean.Chap13.Proposition_13_45
import BauschkeLean.Chap20.PairingEqualityOperator
import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap20.Proposition_20_58
import BauschkeLean.Chap20.Theorem_20_21

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open ERealFunction
open scoped InnerProductSpace SetValuedOperator

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
- `source-facing`: Proposition 20.61 studies the Fenchel-conjugate contact set attached to the
  Fitzpatrick function of a monotone operator.
- `core/canonical`: the owner abstractions are the Fitzpatrick function `F[A]`, its
  transpose-conjugate `((F[A])∗)ᵀ`, and the pairing-contact operator `pairingEqualityOperator`.
- `bridge/view`: the atomic graph-membership and operator-recovery statements express the source
  contact condition through that owner.

Primitive data: the operator `A`, its Fitzpatrick owner `F[A]`, and maximal monotonicity
`Maximal IsMonotone A`.
Derived API: the domain inclusions and the pairing-contact descriptions recovered from
`((F[A])∗)ᵀ`.
Semantic recall: `lean_leansearch` returned no item-specific hit, so the owner names and
statement surface were verified directly from `Proposition_20_56`, `Proposition_20_58`,
`Theorem_20_46`, and `PairingEqualityOperator`. -/

/-- Helper for Proposition 20.61: the effective domain of the inverse-graph indicator plus the
pairing is exactly `gra A⁻¹`. -/
private theorem inverseGraphIndicatorAddPairing_dom_eq_inverseGraph
    (A : SetValuedOperator H H) :
    ERealFunction.dom (((ι[gra A⁻¹]).asEReal + pairing : H × H → EReal)) = gra A⁻¹ := by
  ext p
  constructor
  · intro hp
    -- Outside `gra A⁻¹`, the indicator term is `⊤`, so the sum cannot lie in the domain.
    by_contra hp_inv
    have htop :
        (((ι[gra A⁻¹]).asEReal + pairing : H × H → EReal) p) = ⊤ := by
      change Function.asEReal (ι[gra A⁻¹]) p + pairing p = ⊤
      rw [Function.asEReal_apply, ERealFunction.indicator_apply]
      simpa [hp_inv, pairing_apply] using
        (EReal.top_add_of_ne_bot (show pairing p ≠ ⊥ by
          exact ne_of_gt (EReal.bot_lt_coe _)))
    exact (ERealFunction.not_mem_dom_iff _ _).2 htop hp
  · intro hp
    -- On `gra A⁻¹`, the indicator vanishes and only the finite pairing remains.
    rw [ERealFunction.mem_dom_iff]
    change Function.asEReal (ι[gra A⁻¹]) p + pairing p < ⊤
    rw [Function.asEReal_apply, ERealFunction.indicator_apply,
      Set.indicator_of_notMem (by simpa using hp), zero_add]
    rw [pairing_apply]
    exact EReal.coe_lt_top _

/-- Helper for Proposition 20.61: enlarging the graph of an operator can only increase its
Fitzpatrick function. -/
private theorem fitzpatrickFunction_mono_of_le
    {A B : SetValuedOperator H H} (hAB : A ≤ B) :
    F[A] ≤ F[B] := by
  rintro ⟨x, u⟩
  -- Reindex each graph supremand for `A` through the graph inclusion into `B`.
  rw [fitzpatrickFunction, fitzpatrickFunction]
  refine iSup_le fun p ↦ ?_
  exact le_iSup_of_le ⟨p.1, hAB p.1.1 p.2⟩ le_rfl

section

variable {H : Type u}

/-- Helper for Proposition 20.61: every inverse-graph point `(u, x)` records `u ∈ range A`
and `x ∈ dom A`. -/
private theorem inverseGraph_subset_range_prod_dom
    (A : SetValuedOperator H H) :
    gra A⁻¹ ⊆ A.range ×ˢ A.dom := by
  intro p hp
  rcases p with ⟨u, x⟩
  -- Swap the inverse-graph coordinates back to a graph point of `A`.
  have hxu : (x, u) ∈ gra A := by
    simpa [SetValuedOperator.mem_inverse_iff] using hp
  have hu_mem : u ∈ A x := by
    simpa [SetValuedOperator.mem_graph] using hxu
  constructor
  · exact (SetValuedOperator.mem_range_iff A u).2 ⟨x, hu_mem⟩
  · exact (SetValuedOperator.mem_dom_iff A x).2 ⟨u, hu_mem⟩

end

/-- Helper for Proposition 20.61: every graph point of a monotone operator is a pairing-contact
point for the transpose-conjugate of its Fitzpatrick function. -/
private theorem le_pairingEqualityOperator_conjugateTranspose_fitzpatrickFunction
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) :
    A ≤ pairingEqualityOperator (((F[A])∗)ᵀ) := by
  intro x u hu
  -- Proposition 20.56 already identifies graph points with transpose-conjugate contact points.
  rw [mem_pairingEqualityOperator_iff]
  exact
    conjugateTranspose_fitzpatrickFunction_eq_inner_of_mem_graph
      A
      hA_mono
      (by simpa [SetValuedOperator.mem_graph] using hu)

/-- Helper for Proposition 20.61: a convex owner whose transpose dominates the pairing has a
monotone transpose-contact operator. -/
private theorem pairingEqualityOperator_transpose_isMonotone_of_isConvex
    {G : H × H → EReal} (hG_conv : IsConvex G)
    (hG_ge : ∀ x u : H, pairing (x, u) ≤ Gᵀ (x, u)) :
    (pairingEqualityOperator Gᵀ).IsMonotone := by
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hx hy
  rw [mem_pairingEqualityOperator_iff] at hx hy
  have hx' : Gᵀ (x, u) = pairing (x, u) := by simpa using hx
  have hy' : Gᵀ (y, v) = pairing (y, v) := by simpa using hy
  have hmid_ge :
      pairing (((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y),
          ((1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v))
        ≤
      Gᵀ (((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y),
          ((1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v)) :=
    hG_ge _ _
  have hmid_le :
      Gᵀ (((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y),
          ((1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v))
        ≤
      ((1 / 2 : ℝ) : EReal) * Gᵀ (x, u) +
        (1 - ((1 / 2 : ℝ) : EReal)) * Gᵀ (y, v) := by
    -- Apply convexity to the swapped points `(u, x)` and `(v, y)`.
    simpa [transpose_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hG_conv (x := (u, x)) (y := (v, y)) (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hpair_ineq :
      pairing (((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y),
          ((1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v))
        ≤
      ((1 / 2 : ℝ) : EReal) * pairing (x, u) +
        (1 - ((1 / 2 : ℝ) : EReal)) * pairing (y, v) := by
    -- The midpoint contact values are bounded above by the convex combination of the endpoint
    -- contact values.
    calc
      pairing (((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y),
            ((1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v))
          ≤
        Gᵀ (((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y),
            ((1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v)) := hmid_ge
      _ ≤ ((1 / 2 : ℝ) : EReal) * Gᵀ (x, u) +
            (1 - ((1 / 2 : ℝ) : EReal)) * Gᵀ (y, v) := hmid_le
      _ = ((1 / 2 : ℝ) : EReal) * pairing (x, u) +
            (1 - ((1 / 2 : ℝ) : EReal)) * pairing (y, v) := by rw [hx', hy']
  have hpair_ineq' :
      (((⟪((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y),
            ((1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v)⟫_ℝ : ℝ) : EReal))
        ≤
      (((1 / 2 : ℝ) * ⟪x, u⟫_ℝ + (1 - 1 / 2 : ℝ) * ⟪y, v⟫_ℝ : ℝ) : EReal) := by
    simpa [pairing_apply, EReal.coe_add, EReal.coe_mul] using hpair_ineq
  have hreal_ineq :
      ⟪((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y),
          ((1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v)⟫_ℝ
        ≤
      (1 / 2 : ℝ) * ⟪x, u⟫_ℝ + (1 - 1 / 2 : ℝ) * ⟪y, v⟫_ℝ := by
    exact_mod_cast hpair_ineq'
  have hmid_expand :
      ⟪((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y),
          ((1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • v)⟫_ℝ
        =
      (1 / 4 : ℝ) * (⟪x, u⟫_ℝ + ⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ + ⟪y, v⟫_ℝ) := by
    rw [inner_add_left, inner_add_right, inner_add_right]
    repeat rw [inner_smul_left, inner_smul_right]
    have hstarHalf : (starRingEnd ℝ) (1 / 2 : ℝ) = (1 / 2 : ℝ) := by simp
    have hstarOther :
        (starRingEnd ℝ) (1 - (1 / 2 : ℝ)) = (1 - (1 / 2 : ℝ)) := by
      simp
    repeat rw [hstarHalf, hstarOther]
    ring_nf
  have hcross :
      ⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ + ⟪y, v⟫_ℝ := by
    rw [hmid_expand] at hreal_ineq
    nlinarith
  have hmono_eq :
      ⟪x - y, u - v⟫_ℝ =
        ⟪x, u⟫_ℝ + ⟪y, v⟫_ℝ - (⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  -- The cross-term inequality is exactly the monotonicity inequality in expanded form.
  nlinarith [hcross, hmono_eq]

-- Proof sketch: Proposition 20.56 (2) identifies `F[A]` with the conjugate of the canonical
-- inverse-graph indicator owner `(ι[gra A⁻¹]).asEReal` plus the pairing on `H × H`; applying
-- Fenchel conjugation once more gives the biconjugate of that sum.
/-- Clause (i) of Proposition 20.61. The Fenchel conjugate of the Fitzpatrick function is the
Fenchel biconjugate of the inverse-graph indicator plus the pairing on `H × H`. -/
theorem conjugate_fitzpatrickFunction_eq_biconjugate_inverseGraphIndicator_add_pairing
    (A : SetValuedOperator H H) (_hA_graph : (gra A).Nonempty) (_hA_mono : A.IsMonotone) :
    (F[A])∗ = (((ι[gra A⁻¹]).asEReal + pairing)∗∗) := by
  -- Conjugate the owner identity from Proposition 20.56 once more.
  simpa using
    congrArg ERealFunction.conjugate
      (fitzpatrickFunction_eq_conjugate_inverseGraphIndicator_add_pairing (A := A))

-- Proof sketch: combine clause (1) with the lower-semicontinuous-convex-envelope domain inclusion
-- from Proposition 9.8 (iv), applied to the inverse-graph indicator plus pairing.
/-- First inclusion in clause (ii) of Proposition 20.61. The convex hull of `gra A⁻¹` lies in the
effective domain of `(F[A])∗`. -/
theorem convexHull_inverseGraph_subset_dom_conjugate_fitzpatrickFunction
    (A : SetValuedOperator H H) (hA_graph : (gra A).Nonempty) (hA_mono : A.IsMonotone) :
    convexHull ℝ (gra A⁻¹) ⊆ ERealFunction.dom ((F[A])∗) := by
  let G : H × H → EReal := (ι[gra A⁻¹]).asEReal + pairing
  have hdom_subset : ERealFunction.dom G ⊆ ERealFunction.dom (G∗∗) := by
    intro p hp
    -- Biconjugation is pointwise below the original owner, so finite points stay finite.
    exact
      (ERealFunction.mem_dom_iff _ _).2 <|
        lt_of_le_of_lt
          (biconjugate_le G p)
          ((ERealFunction.mem_dom_iff _ _).1 hp)
  have hdom_convex : Convex ℝ (ERealFunction.dom (G∗∗)) := by
    have hbiconj_gamma : G∗∗ ∈ gamma (H × H) := conjugate_mem_gamma (f := G∗)
    have hbiconj_conv : IsConvex (G∗∗) := (mem_gamma_iff _).1 hbiconj_gamma |>.1
    have hbiconj_epi_conv : Convex ℝ (epigraph (G∗∗)) := by
      refine (convex_epigraph_iff_jensen_on_dom (G∗∗)).2 ?_
      intro x y hx hy a ha0 ha1
      exact hbiconj_conv ha0.le ha1.le
    -- Convexity of the epigraph propagates to convexity of the effective domain.
    exact convex_dom_of_convex_epigraph (G∗∗) hbiconj_epi_conv
  -- Normalize the domain to `gra A⁻¹`, then use convexity of the biconjugate domain.
  calc
    convexHull ℝ (gra A⁻¹) = convexHull ℝ (ERealFunction.dom G) := by
      rw [inverseGraphIndicatorAddPairing_dom_eq_inverseGraph (A := A)]
    _ ⊆ ERealFunction.dom (G∗∗) := convexHull_min hdom_subset hdom_convex
    _ = ERealFunction.dom ((F[A])∗) := by
      rw [conjugate_fitzpatrickFunction_eq_biconjugate_inverseGraphIndicator_add_pairing
        (A := A) hA_graph hA_mono]

-- Proof sketch: use clause (1) and the complementary domain inclusion from Proposition 9.8 (iv)
-- for the lower-semicontinuous convex envelope, together with the Hilbert-space biconjugation
-- bridge from Proposition 13.45 / 13.46 for the inverse-graph indicator plus pairing.
/-- Second inclusion in clause (ii) of Proposition 20.61. The effective domain of `(F[A])∗` is
contained in the closure of the convex hull of `gra A⁻¹`. -/
theorem dom_conjugate_fitzpatrickFunction_subset_closure_convexHull_inverseGraph
    [CompleteSpace H] (A : SetValuedOperator H H)
    (hA_graph : (gra A).Nonempty) (hA_mono : A.IsMonotone) :
    ERealFunction.dom ((F[A])∗) ⊆ closure (convexHull ℝ (gra A⁻¹)) := by
  let G : H × H → EReal := (ι[gra A⁻¹]).asEReal + pairing
  letI : CompleteSpace (H × H) := ERealFunction.prod_completeSpace_l2
  have hdom_conj : (ERealFunction.dom (G∗)).Nonempty := by
    rcases (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
      (A := A) hA_graph hA_mono).2 with ⟨p, hp⟩
    -- Transport the Fitzpatrick properness witness across the conjugate identity from
    -- Proposition 20.56.
    refine ⟨p, ?_⟩
    simpa [G, fitzpatrickFunction_eq_conjugate_inverseGraphIndicator_add_pairing (A := A)] using hp
  -- Rewrite `dom ((F[A])∗)` as the domain of the biconjugate owner and apply Proposition 9.8.
  calc
    ERealFunction.dom ((F[A])∗) = ERealFunction.dom (G∗∗) := by
      rw [conjugate_fitzpatrickFunction_eq_biconjugate_inverseGraphIndicator_add_pairing
        (A := A) hA_graph hA_mono]
    _ = ERealFunction.dom (lowerSemicontinuousConvexEnvelope G) := by
      rw [biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty G hdom_conj]
    _ ⊆ closure (convexHull ℝ (ERealFunction.dom G)) :=
      dom_lowerSemicontinuousConvexEnvelope_subset_closure_convexHull_dom G
    _ = closure (convexHull ℝ (gra A⁻¹)) := by
      rw [inverseGraphIndicatorAddPairing_dom_eq_inverseGraph (A := A)]

-- Proof sketch: every point of `gra A⁻¹` has first coordinate in `range A` and second coordinate
-- in `dom A`; pass to convex hulls and then take closures in the product space.
/-- Third inclusion in clause (ii) of Proposition 20.61. The closed convex hull of `gra A⁻¹`
lies in the product of the closed convex hulls of `range A` and `dom A`. -/
theorem closure_convexHull_inverseGraph_subset_closure_convexHull_range_prod_closure_convexHull_dom
    (A : SetValuedOperator H H) (_hA_graph : (gra A).Nonempty) (_hA_mono : A.IsMonotone) :
    closure (convexHull ℝ (gra A⁻¹)) ⊆
      closure (convexHull ℝ A.range) ×ˢ closure (convexHull ℝ A.dom) := by
  have hgraph_subset :
      gra A⁻¹ ⊆ closure (convexHull ℝ A.range) ×ˢ closure (convexHull ℝ A.dom) := by
    intro p hp
    rcases inverseGraph_subset_range_prod_dom (A := A) hp with ⟨hp_range, hp_dom⟩
    constructor
    · exact subset_closure (subset_convexHull ℝ A.range hp_range)
    · exact subset_closure (subset_convexHull ℝ A.dom hp_dom)
  have htarget_convex :
      Convex ℝ
        (closure (convexHull ℝ A.range) ×ˢ closure (convexHull ℝ A.dom) : Set (H × H)) := by
    exact (convex_convexHull ℝ A.range).closure.prod (convex_convexHull ℝ A.dom).closure
  have htarget_closed :
      IsClosed
        (closure (convexHull ℝ A.range) ×ˢ closure (convexHull ℝ A.dom) : Set (H × H)) := by
    exact isClosed_closure.prod isClosed_closure
  -- First place the inverse graph in the product target, then pass through hull and closure.
  exact closure_minimal (convexHull_min hgraph_subset htarget_convex) htarget_closed

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: extend `A` to a maximally monotone operator and compare Fitzpatrick functions via
-- the order-reversal property of Fenchel conjugation; Proposition 20.58 then yields the lower
-- bound by the pairing. This is the canonical owner form of the source inequality
-- `pairing (x, u) ≤ ((F[A])∗)ᵀ (x, u)`.
/-- Clause (iii) of Proposition 20.61. For a monotone operator, the transpose-conjugate owner
of its Fitzpatrick function dominates the pairing. -/
theorem inner_le_conjugateTranspose_fitzpatrickFunction
    (A : SetValuedOperator H H) (_hA_graph : (gra A).Nonempty) (hA_mono : A.IsMonotone)
    (x u : H) :
    pairing (x, u) ≤ ((F[A])∗)ᵀ (x, u) := by
  obtain ⟨Amax, hA_le, hAmax⟩ :=
    exists_isMaximallyMonotone_extension A hA_mono
  have hfitz_le : F[A] ≤ F[Amax] := fitzpatrickFunction_mono_of_le hA_le
  have hconj_le : (F[Amax])∗ ≤ (F[A])∗ := ERealFunction.conjugate_antitone hfitz_le
  -- Compare `A` with a maximally monotone extension and then use Proposition 20.58.
  calc
    pairing (x, u) ≤ F[Amax] (x, u) := Maximal.inner_le_fitzpatrickFunction hAmax x u
    _ ≤ ((F[Amax])∗)ᵀ (x, u) :=
      fitzpatrickFunction_le_conjugate_transpose Amax (Maximal.isMonotone hAmax) (x, u)
    _ = (F[Amax])∗ (u, x) := by rw [transpose_apply]
    _ ≤ (F[A])∗ (u, x) := hconj_le (u, x)
    _ = ((F[A])∗)ᵀ (x, u) := by rw [transpose_apply]

-- Proof sketch: Proposition 20.56 (6) shows that every graph point of `A` lies in the
-- transpose-conjugate pairing-contact operator. Theorem 20.46 identifies that owner as maximally
-- monotone once clause (5) supplies the lower bound
-- `pairing (x, u) ≤ ((F[A])∗)ᵀ (x, u)`. Maximality of `A`
-- then forces equality of the two operators.
/-- Proposition 20.61: clause (iv). A maximally monotone operator is the pairing-contact
operator of the transpose-conjugate Fenchel conjugate of its Fitzpatrick function. -/
theorem Maximal.eq_pairingEqualityOperator_conjugateTranspose_fitzpatrickFunction
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A = pairingEqualityOperator (((F[A])∗)ᵀ) := by
  have hA_graph : (gra A).Nonempty := by
    by_contra hA_graph
    let B : SetValuedOperator H H := fun _ ↦ ({0} : Set H)
    have hB_mono : B.IsMonotone := by
      rw [SetValuedOperator.isMonotone_iff]
      intro x u y v hu hv
      simp [B] at hu hv
      subst u
      subst v
      simp
    have hAB : A ≤ B := by
      intro x u hu
      exfalso
      exact hA_graph ⟨(x, u), by simpa [SetValuedOperator.mem_graph] using hu⟩
    have hzero_mem : 0 ∈ A 0 := (hA.2 hB_mono hAB 0) (by simp [B])
    exact hA_graph ⟨(0, 0), by simpa [SetValuedOperator.mem_graph] using hzero_mem⟩
  have hAle :
      A ≤ pairingEqualityOperator (((F[A])∗)ᵀ) :=
    le_pairingEqualityOperator_conjugateTranspose_fitzpatrickFunction
      (A := A) (Maximal.isMonotone hA)
  have hcontact_mono :
      (pairingEqualityOperator (((F[A])∗)ᵀ)).IsMonotone := by
    have hFAstar_conv : IsConvex ((F[A])∗) :=
      (mem_gamma_iff _).1 (conjugate_mem_gamma (f := F[A])) |>.1
    exact pairingEqualityOperator_transpose_isMonotone_of_isConvex hFAstar_conv
      (fun x u ↦
        inner_le_conjugateTranspose_fitzpatrickFunction
          (A := A)
          hA_graph
          (Maximal.isMonotone hA)
          x
          u)
  have hcontact_le_A :
      pairingEqualityOperator (((F[A])∗)ᵀ) ≤ A :=
    hA.2 hcontact_mono hAle
  -- Maximality upgrades the contact inclusion to equality of operators.
  ext x u
  constructor
  · exact fun hu ↦ hAle x hu
  · exact fun hu ↦ hcontact_le_A x hu

/-- Source-facing graph form for clause (6): the graph of a maximally monotone operator
is exactly the transpose-conjugate Fitzpatrick contact set
`{p | ((F[A])∗)ᵀ p = pairing p}`. -/
theorem Maximal.graph_eq_setOf_conjugateTranspose_fitzpatrickFunction_eq_inner
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A.graph = {p | ((F[A])∗)ᵀ p = pairing p} := by
  have hgraph_eq :
      A.graph = (pairingEqualityOperator (((F[A])∗)ᵀ)).graph := by
    exact congrArg SetValuedOperator.graph
      (Maximal.eq_pairingEqualityOperator_conjugateTranspose_fitzpatrickFunction hA)
  -- Rewrite the operator first, then expose the primitive graph description of the contact owner.
  calc
    A.graph = (pairingEqualityOperator (((F[A])∗)ᵀ)).graph := hgraph_eq
    _ = {p | ((F[A])∗)ᵀ p = pairing p} := by
      simpa using graph_pairingEqualityOperator_eq (F := (((F[A])∗)ᵀ))

-- Proof sketch: rewrite `A` by the recovered pairing-contact owner from clause (6), then unfold
-- graph membership with the primitive owner lemma `mem_graph_pairingEqualityOperator_iff`.
/-- Atomic contact-set form for clause (6): a point belongs to the graph of a maximally
monotone operator exactly when the Fenchel conjugate of its Fitzpatrick function attains the
pairing in transpose-conjugate form. -/
theorem Maximal.mem_graph_iff_conjugateTranspose_fitzpatrickFunction_eq_inner
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x u : H) :
    (x, u) ∈ A.graph ↔ ((F[A])∗)ᵀ (x, u) = pairing (x, u) := by
  -- The graph equality from the previous theorem is already the desired contact-set statement.
  simpa using congrArg (fun s : Set (H × H) ↦ (x, u) ∈ s)
    (Maximal.graph_eq_setOf_conjugateTranspose_fitzpatrickFunction_eq_inner hA)

end

end SetValuedOperator
