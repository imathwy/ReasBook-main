import Mathlib
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

noncomputable section

namespace ERealFunction

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_innerProductSpace_l2

section SubdifferentialAndEpigraphNormalCone

/-- Helper for Proposition 16.16: the support inequality on `C - {p}` is equivalent to the
pointwise variational inequalities against all points of `C`. -/
private lemma innerSupremumOn_sub_singleton_le_zero_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {u p : E} :
    innerSupremumOn (C - ({p} : Set E)) u ≤ 0 ↔ ∀ y ∈ C, ⟪y - p, u⟫_ℝ ≤ 0 := by
  constructor
  · intro hsup y hy
    -- Compare the translated set against `{0}` to recover the pointwise inequalities.
    have hsep :
        innerSupremumOn (C - ({p} : Set E)) u ≤ innerInfimumOn ({0} : Set E) u := by
      simpa using hsup
    have hinner :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set E)) ({0} : Set E) u).1 hsep
    have hy_sub : y - p ∈ C - ({p} : Set E) := by
      exact ⟨y, hy, p, by simp, rfl⟩
    simpa using hinner (y - p) hy_sub 0 (by simp)
  · intro hinner
    -- Expand each translated point as `y - p` and push the family back to the support inequality.
    have hsep :
        innerSupremumOn (C - ({p} : Set E)) u ≤ innerInfimumOn ({0} : Set E) u :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set E)) ({0} : Set E) u).2
        (fun v hv z hz ↦ by
          have hz' : z = 0 := by simpa using hz
          subst hz'
          rcases hv with ⟨y, hy, w, hw, hv⟩
          have hw' : w = p := by simpa using hw
          have hv' : v = y - p := by
            simpa [hw'] using hv.symm
          simpa [hv'] using hinner y hy)
    simpa using hsep

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16.16: an effective-domain point gives a canonical real-height point of
the epigraph. -/
private lemma mem_epigraph_toReal_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∈ effectiveDomain f) :
    (y, (f y : EReal).toReal) ∈ epigraph f.asEReal := by
  -- Finiteness of `f y` says that the canonical real height lies on the epigraph.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hy))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16.16: every real-height epigraph point has base point in the
effective domain, and its height dominates the finite value `(f y).toReal`. -/
private lemma effectiveDomain_and_toReal_le_of_mem_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} {η : ℝ}
    (hyη : (y, η) ∈ epigraph f.asEReal) :
    y ∈ effectiveDomain f ∧ (f y : EReal).toReal ≤ η := by
  -- Epigraph membership gives a finite upper bound on `f y`, hence both finiteness and the
  -- height comparison after applying `toReal`.
  have hfy_le : (f y : EReal) ≤ (η : EReal) := (mem_epigraph_iff _ _ _).mp hyη
  have hy_dom : y ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hfy_le (EReal.coe_lt_top η)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hη_top : ((η : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top η
  have htoReal : (f y : EReal).toReal ≤ ((η : EReal)).toReal := by
    simpa using EReal.toReal_le_toReal hfy_le hfy_bot hη_top
  exact ⟨hy_dom, htoReal⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16.16: the real inner product is ordinary multiplication. -/
private lemma real_inner_eq_mul (a b : ℝ) :
    ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Proposition 16.16: the product Hilbert inner product against `(u, -1)` separates
into the `H`-component minus the height difference. -/
private lemma inner_pair_sub_right_neg_one
    {x y u : H} {ξ η : ℝ} :
    ⟪(y, η) - (x, ξ), (u, (-1 : ℝ))⟫_ℝ = ⟪y - x, u⟫_ℝ - (η - ξ) := by
  -- Under the canonical `ℓ²` product structure, the horizontal and vertical parts decouple.
  change ⟪(y - x, η - ξ), (u, (-1 : ℝ))⟫_ℝ = ⟪y - x, u⟫_ℝ - (η - ξ)
  change ⟪y - x, u⟫_ℝ + ⟪η - ξ, (-1 : ℝ)⟫_ℝ = ⟪y - x, u⟫_ℝ - (η - ξ)
  rw [real_inner_eq_mul]
  ring

/-- Helper for Proposition 16.16: epigraph normal-cone membership at the real-height graph point
is equivalent to the translated pointwise inner-product inequalities against all epigraph
points. -/
private lemma mem_normalCone_epigraph_iff_forall_inner_pair_nonpos
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) {u : H} {a : ℝ} :
    (u, a) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔
      ∀ y η, (y, η) ∈ epigraph f.asEReal →
        ⟪(y, η) - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
  have hx_epi : (x, (f x : EReal).toReal) ∈ epigraph f.asEReal :=
    mem_epigraph_toReal_of_mem_effectiveDomain (f := f) hx
  -- Unfold the normal cone at a point of the epigraph and rewrite the translated support
  -- inequality pointwise.
  rw [Set.normalCone_of_mem hx_epi]
  have hnormal_iff :
      innerSupremumOn
          (epigraph f.asEReal - ({(x, (f x : EReal).toReal)} : Set (H × ℝ))) (u, a) ≤ 0 ↔
        ∀ z ∈ epigraph f.asEReal,
          ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
    exact
      (innerSupremumOn_sub_singleton_le_zero_iff :
        innerSupremumOn
            (epigraph f.asEReal - ({(x, (f x : EReal).toReal)} : Set (H × ℝ))) (u, a) ≤ 0 ↔
          ∀ z ∈ epigraph f.asEReal,
            ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0)
  constructor
  · intro hu
    have hpointwise := hnormal_iff.1 hu
    intro y η hyη
    exact hpointwise (y, η) hyη
  · intro hu
    have hpointwise :
        ∀ z ∈ epigraph f.asEReal,
          ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
      intro z hz
      rcases z with ⟨y, η⟩
      exact hu y η hz
    exact hnormal_iff.2 hpointwise

/-- Helper for Proposition 16.16: at a point of the effective domain, subgradients are exactly
the normals of the real-height epigraph slice with vertical component `-1`. -/
private lemma mem_subdifferential_iff_mem_normalCone_epigraph_at_effectiveDomain_point
    (f : H → Set.Ioi (⊥ : EReal)) {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔
      (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
  constructor
  · intro hu
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂] at hu
    -- Lift the canonical domain inequalities to arbitrary epigraph points by monotonicity in the
    -- height coordinate.
    refine (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos (f := f) hx).2 ?_
    intro y η hyη
    rcases effectiveDomain_and_toReal_le_of_mem_epigraph (f := f) hyη with ⟨hy, hη⟩
    have hxy : ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := hu y hy
    have hminor : ⟪y - x, u⟫_ℝ + (f x : EReal).toReal ≤ η := by
      linarith
    have hpair :
        ⟪y - x, u⟫_ℝ - (η - (f x : EReal).toReal) ≤ 0 := by
      linarith
    have hpair' :
        ⟪(y, η) - (x, (f x : EReal).toReal), (u, (-1 : ℝ))⟫_ℝ ≤ 0 := by
      rw [inner_pair_sub_right_neg_one]
      exact hpair
    exact hpair'
  · intro hu
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂]
    intro y hy
    have hy_epi : (y, (f y : EReal).toReal) ∈ epigraph f.asEReal :=
      mem_epigraph_toReal_of_mem_effectiveDomain (f := f) hy
    have hineq :=
      (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos (f := f) hx).1 hu
        y ((f y : EReal).toReal) hy_epi
    rw [inner_pair_sub_right_neg_one] at hineq
    change ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal
    linarith

-- Proof sketch: the epigraph normal-cone computation gives `(i) ↔ (ii)`, and convexity of `f`
-- identifies that criterion with equality in the Fenchel--Young identity `(iii)`. The
-- proper-conjugate clause `(iv)` is the downstream bridge owned by Proposition 16.10, so it is
-- recorded separately below only in the source direction `(iii) → (iv)`.
/-- Proposition 16.16 (1): for an effective-domain point `x`, clauses `(i)`, `(ii)`, and `(iii)`
say that the following are equivalent: `u ∈ ∂ f x`, `(u, -1)` lies in the normal cone to the
real-height epigraph of `f` at `(x, (f x : EReal).toReal)`, and equality holds in the
Fenchel--Young identity `f(x) + f^*(u) = ⟪x, u⟫`. -/
theorem subdifferential_normalCone_fenchelYoung_tfae
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) (hdom : (effectiveDomain f).Nonempty)
    (x u : H) (hx : x ∈ effectiveDomain f) :
    List.TFAE
      [u ∈ (∂ f) x,
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal),
        (f x : EReal) + f.asEReal∗ u =
          ((⟪x, u⟫_ℝ : ℝ) : EReal)] := by
  let _ := hconv
  -- Clause `(i) ↔ (ii)` is the epigraph-normal characterization at the real-height graph point.
  tfae_have 1 ↔ 2 := by
    change u ∈ (∂ f) x ↔
      (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal)
    exact mem_subdifferential_iff_mem_normalCone_epigraph_at_effectiveDomain_point f hx
  -- Clause `(i) ↔ (iii)` is exactly Proposition 16.10.
  tfae_have 1 ↔ 3 := by
    change u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)
    exact mem_subdifferential_iff_fenchel_young_eq (f := f) hdom x u
  tfae_finish

/-- Proposition 16.16 (2): if `f` is convex and proper, then the Fenchel--Young equality
clause `(iii)` implies the conjugate subdifferential clause `x ∈ ∂ f*(u)`. On the implementation
surface this is stated for the packaged conjugate `properConjugateIoi f hdom`. -/
theorem mem_subdifferential_properConjugateIoi_of_fenchel_young_eq_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) (hdom : (effectiveDomain f).Nonempty) (x u : H)
    (hfy : (f x : EReal) + f.asEReal∗ u =
      ((⟪x, u⟫_ℝ : ℝ) : EReal)) :
    x ∈ (∂ (properConjugateIoi f hdom)) u := by
  let _ := hconv
  -- First convert the contact equality into primal subgradient membership.
  have hsub : u ∈ (∂ f) x :=
    (mem_subdifferential_iff_fenchel_young_eq (f := f) hdom x u).2 hfy
  -- Then Proposition 16.10 transports that subgradient to the packaged conjugate.
  exact mem_subdifferential_properConjugateIoi_of_mem_subdifferential (f := f) hdom x u hsub

/-- Companion to Proposition 16.16: for a proper convex function and an effective-domain point
`x`, the subdifferential criterion is equivalent to the epigraph normal-cone criterion at the
real-height point `(x, (f x : EReal).toReal)`, which is the textbook point `(x, f(x))`. -/
theorem mem_subdifferential_iff_mem_normalCone_epigraph
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) (hdom : (effectiveDomain f).Nonempty)
    {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔
      (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
  let _ := hconv
  let _ := hdom
  -- This is exactly the geometric core lemma specialized to the effective-domain point `x`.
  exact mem_subdifferential_iff_mem_normalCone_epigraph_at_effectiveDomain_point f hx

end SubdifferentialAndEpigraphNormalCone

end ERealFunction
