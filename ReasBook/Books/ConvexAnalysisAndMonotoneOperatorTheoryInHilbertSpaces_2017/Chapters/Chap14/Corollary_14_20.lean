import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Text_1_0_28
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_10
import BauschkeLean.Chap13.Proposition_13_23

open scoped InnerProductSpace

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section Conjugation

attribute [local instance] Classical.propDecidable

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 14 20: the global infimum of an `EReal`-valued function is the infimum of
its image over the finite-above domain. -/
lemma iInf_eq_sInf_image_dom
    {X : Type*} (f : X → EReal) :
    (⨅ x : X, f x) = sInf (f '' dom f) := by
  rw [← sInf_range]
  refine le_antisymm ?_ ?_
  · -- Restrict the lower-bound property of `sInf (range f)` to the finite-above image.
    exact (isGLB_sInf (f '' dom f)).2 <| by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact (isGLB_sInf (Set.range f)).1 ⟨x, rfl⟩
  · -- Outside `dom f`, the only omitted value is `⊤`, which does not affect lower bounds.
    exact (isGLB_sInf (Set.range f)).2 <| by
      intro z hz
      rcases hz with ⟨x, rfl⟩
      by_cases hx : x ∈ dom f
      · exact (isGLB_sInf (f '' dom f)).1 ⟨x, hx, rfl⟩
      · rw [not_mem_dom_iff] at hx
        simp [hx]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 14 20: adding a real constant commutes with subtype-indexed suprema in
`EReal`. -/
lemma ereal_add_iSup_subtype_of_real_shift
    {S : Set H} (r : ℝ) (φ : S → EReal) :
    ((r : EReal) + ⨆ x : S, φ x) =
      ⨆ x : S, (r : EReal) + φ x := by
  simpa [add_comm] using
    (ereal_iSup_add_of_real_shift r (fun x : S ↦ φ x)).symm

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 14 20: outside the effective domain, the coerced value is `⊤`. -/
lemma asEReal_eq_top_of_not_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} (hx : x ∉ effectiveDomain f) :
    f.asEReal x = ⊤ := by
  exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 14 20: if a family is `⊥` outside a set, then its full supremum agrees
with the supremum over the corresponding subtype. -/
lemma iSup_eq_iSup_subtype_of_eq_bot_outside
    {S : Set H} (φ : H → EReal) (hbot : ∀ x, x ∉ S → φ x = ⊥) :
    (⨆ x : H, φ x) = ⨆ x : S, φ x := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x ↦ ?_
    by_cases hx : x ∈ S
    · simpa using le_iSup (fun y : S ↦ φ y) ⟨x, hx⟩
    · rw [hbot x hx]
      exact bot_le
  · refine iSup_le fun x ↦ ?_
    simpa using le_iSup φ (x : H)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 14 20: the piecewise owner equal to `g - h` on `effectiveDomain g` and
`+∞` outside it has domain exactly `effectiveDomain g`. -/
lemma dom_piecewise_sub_on_effectiveDomain
    (g h : H → Set.Ioi (⊥ : EReal)) :
    dom (fun x ↦ if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤) =
      effectiveDomain g := by
  ext x
  constructor
  · intro hx
    by_cases hxg : x ∈ effectiveDomain g
    · exact hxg
    · have hφ_top :
        (if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤) = ⊤ := by
          simp [hxg]
      exact False.elim ((mem_dom_iff_ne_top _ _).1 hx hφ_top)
  · intro hx
    rw [mem_dom_iff_ne_top]
    have hg_top : g.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hsum_top :
        g.asEReal x + -h.asEReal x ≠ ⊤ := by
      refine EReal.add_ne_top hg_top ?_
      simpa using (EReal.neg_eq_top_iff.not.mpr (ne_of_gt (h x).2))
    simpa [hx, sub_eq_add_neg] using hsum_top

/-- Helper for Corollary 14 20: evaluating the Fenchel biconjugate of a `Γ₀(H)` function at a
fixed primal point yields the domain-restricted supremum over its conjugate. -/
lemma biconjugate_value_eq_iSup_dom_conjugate
    (h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) (x : H) :
    h.asEReal x =
      ⨆ v : dom (h.asEReal∗), (((⟪x, (v : H)⟫_ℝ : ℝ) : EReal) - h.asEReal∗ v) := by
  have hbiconj : h.asEReal∗∗ x = h.asEReal x :=
    congrFun (biconjugate_eq_of_mem_gammaZero hh) x
  calc
    h.asEReal x = h.asEReal∗∗ x := hbiconj.symm
    _ = ⨆ v : H, (((⟪v, x⟫_ℝ : ℝ) : EReal) - h.asEReal∗ v) := by
      rw [conjugate_apply]
    _ = ⨆ v : H, (((⟪x, v⟫_ℝ : ℝ) : EReal) - h.asEReal∗ v) := by
      refine iSup_congr fun v ↦ ?_
      rw [real_inner_comm]
    _ =
        ⨆ v : dom (h.asEReal∗), (((⟪x, (v : H)⟫_ℝ : ℝ) : EReal) - h.asEReal∗ v) := by
      rw [iSup_eq_iSup_subtype_of_eq_bot_outside
        (φ := fun v : H ↦ (((⟪x, v⟫_ℝ : ℝ) : EReal) - h.asEReal∗ v))]
      intro v hv
      have hv_top : h.asEReal∗ v = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [dom] using hv))
      rw [hv_top]
      simp

/-- Helper for Corollary 14 20: at a domain point of `g`, negating `g - h` expands through the
Fenchel--Moreau formula for `h`. -/
lemma neg_sub_eq_iSup_shifted_dual_defect
    (g h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) (x : effectiveDomain g) :
    -(g.asEReal x - h.asEReal x) =
      ⨆ v : dom (h.asEReal∗),
        (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v) := by
  have hg_top : g.asEReal x ≠ ⊤ := ne_of_lt x.2
  have hg_bot : g.asEReal x ≠ ⊥ := ne_of_gt (g x).2
  let r : ℝ := -(g.asEReal x).toReal
  have hr : ((r : ℝ) : EReal) = -g.asEReal x := by
    dsimp [r]
    simpa using congrArg Neg.neg (EReal.coe_toReal hg_top hg_bot)
  calc
    -(g.asEReal x - h.asEReal x) = -g.asEReal x + h.asEReal x := by
      simpa [sub_eq_add_neg] using
        (EReal.neg_sub
          (x := g.asEReal x)
          (y := h.asEReal x)
          (Or.inl hg_bot)
          (Or.inl hg_top))
    _ = ((r : ℝ) : EReal) + h.asEReal x := by rw [hr]
    _ =
        ((r : ℝ) : EReal) +
          ⨆ v : dom (h.asEReal∗), (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - h.asEReal∗ v) := by
      rw [biconjugate_value_eq_iSup_dom_conjugate h hh (x : H)]
    _ =
        ⨆ v : dom (h.asEReal∗),
          ((r : ℝ) : EReal) +
            ((((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - h.asEReal∗ v)) := by
      rw [ereal_add_iSup_subtype_of_real_shift
        (r := r)
        (φ := fun v : dom (h.asEReal∗) ↦
          (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - h.asEReal∗ v))]
    _ =
        ⨆ v : dom (h.asEReal∗),
          (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v) := by
      refine iSup_congr fun v ↦ ?_
      rw [hr]
      rw [sub_eq_add_neg, sub_eq_add_neg]
      let a : EReal := (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal))
      change -g.asEReal x + (a + -(h.asEReal∗ v)) = a + -g.asEReal x + -(h.asEReal∗ v)
      rw [add_left_comm, ← add_assoc]

omit [CompleteSpace H] in
/-- Helper for Corollary 14 20: for a dual point in `dom (h*)`, the inner supremum over
`effectiveDomain g` is the shifted conjugate defect of `g`. -/
lemma iSup_effectiveDomain_affine_shift_eq_conjugate_sub
    (g h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) (v : dom (h.asEReal∗)) :
    (⨆ x : effectiveDomain g,
      (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v)) =
      g.asEReal∗ (v : H) - h.asEReal∗ v := by
  have hv_top : h.asEReal∗ (v : H) ≠ ⊤ := (mem_dom_iff_ne_top _ _).1 v.2
  have hv_bot : h.asEReal∗ (v : H) ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hh.2.nonempty (v : H)
  let r : ℝ := -(h.asEReal∗ (v : H)).toReal
  have hr : ((r : ℝ) : EReal) = -h.asEReal∗ (v : H) := by
    dsimp [r]
    simpa using congrArg Neg.neg (EReal.coe_toReal hv_top hv_bot)
  have hrestrict :
      (⨆ x : effectiveDomain g, (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x)) =
        ⨆ x : H, (((⟪x, (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x) := by
    symm
    exact iSup_eq_iSup_subtype_of_eq_bot_outside
      (φ := fun x : H ↦ (((⟪x, (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x))
      (hbot := fun x hx ↦ by
        change (((⟪x, (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x) = ⊥
        rw [asEReal_eq_top_of_not_mem_effectiveDomain g hx]
        simp)
  calc
    (⨆ x : effectiveDomain g,
      (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v)) =
        ⨆ x : effectiveDomain g,
          ((((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x) + (r : EReal)) := by
      refine iSup_congr fun x ↦ ?_
      rw [sub_eq_add_neg, hr]
    _ =
        (⨆ x : effectiveDomain g,
          (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x)) + (r : EReal) := by
      simpa using
        ereal_iSup_add_of_real_shift
          r
          (fun x : effectiveDomain g ↦
            (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x))
    _ = (⨆ x : H, (((⟪x, (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x)) + (r : EReal) := by
      rw [hrestrict]
    _ = g.asEReal∗ (v : H) + (r : EReal) := by
      rw [conjugate_apply]
    _ = g.asEReal∗ (v : H) - h.asEReal∗ v := by
      rw [hr]
      simp [sub_eq_add_neg]

omit [CompleteSpace H] in
/-- Helper for Corollary 14 20: the subtype-indexed dual range agrees with the displayed image over
`dom (h*)`. -/
lemma dual_range_eq_image_dom
    (g h : H → Set.Ioi (⊥ : EReal)) :
    Set.range (fun v : dom (h.asEReal∗) ↦ g.asEReal∗ (v : H) - h.asEReal∗ v) =
      ((fun v : H ↦ g.asEReal∗ v - h.asEReal∗ v) '' dom (h.asEReal∗)) := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, v.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

omit [CompleteSpace H] in
/-- Helper for Corollary 14 20: the conjugate at the origin of the piecewise owner from
Proposition 14.19 is the negative infimum of the primal image. -/
lemma piecewise_sub_conjugate_zero_eq_neg_sInf_primal_image
    (g h : H → Set.Ioi (⊥ : EReal)) :
    (fun x ↦ if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤)∗ 0 =
      -sInf ((fun x ↦ g.asEReal x - h.asEReal x) '' effectiveDomain g) := by
  let φ : H → EReal := fun x ↦
    if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤
  have himage :
      φ '' effectiveDomain g =
        (fun x ↦ g.asEReal x - h.asEReal x) '' effectiveDomain g := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [φ, hx]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [φ, hx]⟩
  -- Rewrite the origin conjugate as the negative infimum of the finite-above domain image.
  calc
    φ∗ 0 = -(⨅ x : H, φ x) := by
      exact conjugate_zero_eq_neg_iInf φ
    _ = -sInf (φ '' dom φ) := by
      rw [iInf_eq_sInf_image_dom]
    _ = -sInf (φ '' effectiveDomain g) := by
      rw [dom_piecewise_sub_on_effectiveDomain (g := g) (h := h)]
    _ = -sInf ((fun x ↦ g.asEReal x - h.asEReal x) '' effectiveDomain g) := by
      rw [himage]

/-- Helper for Corollary 14 20: the origin conjugate of the piecewise owner is the displayed
dual supremum. -/
lemma piecewise_sub_conjugate_zero_eq_sSup_conjugate_sub_image
    (g h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) :
    (fun x ↦ if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤)∗ 0 =
      sSup ((fun v ↦ g.asEReal∗ v - h.asEReal∗ v) '' dom (h.asEReal∗)) := by
  let φ : H → EReal := fun x ↦
    if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤
  have hrestrict :
      (⨆ x : H, -φ x) = ⨆ x : effectiveDomain g, -φ x := by
    exact iSup_eq_iSup_subtype_of_eq_bot_outside
      (φ := fun x : H ↦ -φ x)
      (hbot := fun x hx ↦ by
        simp [φ, hx])
  calc
    φ∗ 0 = ⨆ x : H, -φ x := by
      rw [conjugate_apply]
      refine iSup_congr fun x ↦ ?_
      simp [φ]
    _ = ⨆ x : effectiveDomain g, -φ x := hrestrict
    _ = ⨆ x : effectiveDomain g, -(g.asEReal x - h.asEReal x) := by
      refine iSup_congr fun x ↦ ?_
      simp [φ, x.2]
    _ =
        ⨆ x : effectiveDomain g,
          ⨆ v : dom (h.asEReal∗),
            (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v) := by
      refine iSup_congr fun x ↦ ?_
      exact neg_sub_eq_iSup_shifted_dual_defect g h hh x
    _ =
        ⨆ v : dom (h.asEReal∗),
          ⨆ x : effectiveDomain g,
            (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v) := by
      rw [iSup_comm]
    _ = ⨆ v : dom (h.asEReal∗), g.asEReal∗ (v : H) - h.asEReal∗ v := by
      refine iSup_congr fun v ↦ ?_
      exact iSup_effectiveDomain_affine_shift_eq_conjugate_sub g h hh v
    _ = sSup ((fun v ↦ g.asEReal∗ v - h.asEReal∗ v) '' dom (h.asEReal∗)) := by
      rw [← sSup_range, dual_range_eq_image_dom g h]

omit [CompleteSpace H] in
/-- Helper for Corollary 14 20: at any dual point in `dom (h*)`, negating `g* - h*` swaps the two
conjugates. -/
lemma neg_conjugate_sub_eq_swap_sub
    (g h : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) {v : H}
    (hv : v ∈ dom (h.asEReal∗)) :
    -(g.asEReal∗ v - h.asEReal∗ v) = h.asEReal∗ v - g.asEReal∗ v := by
  have hh_top : h.asEReal∗ v ≠ ⊤ := (mem_dom_iff_ne_top _ _).1 hv
  have hg_bot : g.asEReal∗ v ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hg.2.nonempty v
  -- The domain condition on `h∗` and properness of `g` rule out the exceptional `EReal` cases.
  simpa [sub_eq_add_neg, add_comm] using
    (EReal.neg_sub
      (x := g.asEReal∗ v)
      (y := h.asEReal∗ v)
      (.inl hg_bot)
      (.inr hh_top))

omit [CompleteSpace H] in
/-- Helper for Corollary 14 20: negating the dual image from Proposition 14.19 swaps the order of
the two conjugates. -/
lemma neg_image_conjugate_sub_eq_swap_sub_image
    (g h : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) :
    (-·) '' ((fun v ↦ g.asEReal∗ v - h.asEReal∗ v) '' dom (h.asEReal∗)) =
      ((fun v ↦ h.asEReal∗ v - g.asEReal∗ v) '' dom (h.asEReal∗)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    -- Reduce the image statement to the pointwise dual negation identity.
    simpa using (neg_conjugate_sub_eq_swap_sub g h hg hv).symm
  · rintro ⟨v, hv, rfl⟩
    refine ⟨g.asEReal∗ v - h.asEReal∗ v, ⟨v, hv, rfl⟩, ?_⟩
    -- Reuse the same pointwise identity in the reverse image inclusion.
    simpa using neg_conjugate_sub_eq_swap_sub g h hg hv

omit [CompleteSpace H] in
/-- Helper for Corollary 14 20: the dual supremum from Proposition 14.19 is the negative infimum
of the swapped dual image. -/
lemma sSup_conjugate_sub_image_eq_neg_sInf_swap_sub_image
    (g h : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) :
    sSup ((fun v ↦ g.asEReal∗ v - h.asEReal∗ v) '' dom (h.asEReal∗)) =
      -sInf ((fun v ↦ h.asEReal∗ v - g.asEReal∗ v) '' dom (h.asEReal∗)) := by
  -- Convert the dual supremum to a negative infimum and identify the negated image explicitly.
  rw [EReal.sSup_eq_neg_sInf_image_neg]
  rw [neg_image_conjugate_sub_eq_swap_sub_image g h hg]

-- Proof sketch: apply the preceding conjugation identity for the piecewise function equal to
-- `g - h` on `effectiveDomain g` and `+∞` outside it at `u = 0`, then use the canonical origin
-- formula for Fenchel conjugates to rewrite both sides as negative infima. Finally unfold that
-- piecewise expression on the primal side and `dom` on the dual side to recover the displayed
-- source-facing infima.
/-- Corollary 14 20: if `g, h ∈ Γ₀(H)`, then the infimum of `g - h` over `dom g` equals the
infimum of `h* - g*` over `dom h*`. -/
theorem toland_singer_inf_sub_eq_inf_conjugate_sub
    (g h : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (hh : h ∈ Γ₀(H)) :
    sInf ((fun x ↦ g.asEReal x - h.asEReal x) '' effectiveDomain g) =
      sInf
        ((fun v ↦ h.asEReal∗ v - g.asEReal∗ v) '' dom (h.asEReal∗)) := by
  have hconj :
      (fun x ↦ if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤)∗ 0 =
        sSup ((fun v ↦ g.asEReal∗ v - h.asEReal∗ v) '' dom (h.asEReal∗)) := by
    exact piecewise_sub_conjugate_zero_eq_sSup_conjugate_sub_image g h hh
  have hdual :
      sSup ((fun v ↦ g.asEReal∗ v - h.asEReal∗ v) '' dom (h.asEReal∗)) =
        -sInf ((fun v ↦ h.asEReal∗ v - g.asEReal∗ v) '' dom (h.asEReal∗)) := by
    -- Use the dedicated dual-image normalization helper introduced above.
    exact sSup_conjugate_sub_image_eq_neg_sInf_swap_sub_image g h hg
  -- Compare the two negative infima and then cancel the outer negation.
  exact neg_injective <| by
    calc
      -sInf ((fun x ↦ g.asEReal x - h.asEReal x) '' effectiveDomain g) =
          (fun x ↦ if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤)∗ 0 := by
        exact (piecewise_sub_conjugate_zero_eq_neg_sInf_primal_image g h).symm
      _ =
          sSup ((fun v ↦ g.asEReal∗ v - h.asEReal∗ v) '' dom (h.asEReal∗)) := hconj
      _ =
          -sInf ((fun v ↦ h.asEReal∗ v - g.asEReal∗ v) '' dom (h.asEReal∗)) := hdual

end Conjugation

end ERealFunction
