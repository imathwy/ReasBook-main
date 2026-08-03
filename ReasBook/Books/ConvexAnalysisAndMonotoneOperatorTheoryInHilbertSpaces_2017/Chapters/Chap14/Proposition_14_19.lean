import Mathlib
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool unavailable in this session; notation and owner were checked against local
-- Chapter 14 conjugation files.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

attribute [local instance] Classical.propDecidable

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The function equal to `g - h` on `effectiveDomain g` and `+∞` outside `effectiveDomain g`. -/
noncomputable def subOnEffectiveDomain
    (g h : H → Set.Ioi (⊥ : EReal)) : H → EReal :=
  fun x ↦ if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤

/-- Helper for Proposition 14.19: if an `EReal`-valued family is `⊥` outside a set, then its full
supremum agrees with the supremum over the corresponding subtype. -/
private lemma iSup_eq_iSup_subtype_of_eq_bot_outside
    {S : Set H} (φ : H → EReal) (hbot : ∀ x, x ∉ S → φ x = ⊥) :
    (⨆ x : H, φ x) = ⨆ x : S, φ x := by
  -- Compare the unrestricted supremum with the restricted one pointwise.
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x ↦ ?_
    by_cases hx : x ∈ S
    · simpa using le_iSup (fun y : S ↦ φ y) ⟨x, hx⟩
    · rw [hbot x hx]
      exact bot_le
  · refine iSup_le fun x ↦ ?_
    simpa using le_iSup φ (x : H)

/-- Helper for Proposition 14.19: outside `effectiveDomain f`, the coerced value `f.asEReal` is
`⊤`. -/
private lemma asEReal_eq_top_of_not_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} (hx : x ∉ effectiveDomain f) :
    f.asEReal x = ⊤ := by
  -- The effective domain is exactly the set where the value is strictly below `⊤`.
  exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))

/-- Helper for Proposition 14.19: evaluating the Fenchel biconjugate of a `Γ₀(H)` function at a
fixed primal point yields the domain-restricted supremum over its conjugate. -/
private lemma biconjugate_value_eq_iSup_dom_conjugate
    (h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) (x : H) :
    h.asEReal x =
      ⨆ v : dom (h.asEReal∗), (((⟪x, (v : H)⟫_ℝ : ℝ) : EReal) - h.asEReal∗ v) := by
  have hbiconj : h.asEReal∗∗ x = h.asEReal x :=
    congrFun (biconjugate_eq_of_mem_gammaZero hh) x
  -- Expand the biconjugate and then restrict the dual supremum to `dom (h*)`.
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

/-- Helper for Proposition 14.19: adding a finite real constant commutes with subtype-indexed
suprema in `EReal`. -/
private lemma ereal_add_iSup_subtype_of_real_shift
    {S : Set H} (r : ℝ) (φ : S → EReal) :
    ((r : EReal) + ⨆ x : S, φ x) =
      ⨆ x : S, (r : EReal) + φ x := by
  -- Commute the finite shift with the supremum using the Chapter 13 shift lemma.
  simpa [add_comm] using
    (ereal_iSup_add_of_real_shift r (fun x : S ↦ φ x)).symm

/-- Helper for Proposition 14.19: at a domain point of `g`, negating `g - h` expands through the
Fenchel--Moreau formula for `h`. -/
private lemma neg_sub_eq_iSup_shifted_dual_defect
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
  -- Rewrite `h` via Fenchel--Moreau and then push the finite shift `-g(x)` through the supremum.
  calc
    -(g.asEReal x - h.asEReal x) = -g.asEReal x + h.asEReal x := by
      simpa [sub_eq_add_neg] using
        (EReal.neg_sub
          (x := g.asEReal x)
          (y := h.asEReal x)
          (Or.inl hg_bot)
          (Or.inl hg_top))
    _ = ((r : ℝ) : EReal) + h.asEReal x := by
      rw [hr]
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

/-- Helper for Proposition 14.19: at a domain point of `g`, the affine defect of `g - h` splits
into the shifted dual defects indexed by `dom (h*)`. -/
private lemma affine_defect_sub_eq_iSup_shifted_dual_defect
    (g h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) (u : H) (x : effectiveDomain g) :
    (((⟪(x : H), u⟫_ℝ : ℝ) : EReal) - (g.asEReal x - h.asEReal x)) =
      ⨆ v : dom (h.asEReal∗),
        (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v) := by
  -- Add the finite pairing `⟪x,u⟫` after expanding the negative defect from the previous helper.
  calc
    (((⟪(x : H), u⟫_ℝ : ℝ) : EReal) - (g.asEReal x - h.asEReal x)) =
        (((⟪(x : H), u⟫_ℝ : ℝ) : EReal) + (-(g.asEReal x - h.asEReal x))) := by
      rw [sub_eq_add_neg]
    _ =
        (((⟪(x : H), u⟫_ℝ : ℝ) : EReal) +
          ⨆ v : dom (h.asEReal∗),
            (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v)) := by
      rw [neg_sub_eq_iSup_shifted_dual_defect g h hh x]
    _ =
        ⨆ v : dom (h.asEReal∗),
          (((⟪(x : H), u⟫_ℝ : ℝ) : EReal) +
            ((((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v))) := by
      rw [ereal_add_iSup_subtype_of_real_shift
        (r := ⟪(x : H), u⟫_ℝ)
        (φ := fun v : dom (h.asEReal∗) ↦
          (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v))]
    _ =
        ⨆ v : dom (h.asEReal∗),
          (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v) := by
      refine iSup_congr fun v ↦ ?_
      let au : EReal := (((⟪(x : H), u⟫_ℝ : ℝ) : EReal))
      let av : EReal := (((⟪(x : H), (v : H)⟫_ℝ : ℝ) : EReal))
      have hsum : au + av = (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal)) := by
        dsimp [au, av]
        rw [← EReal.coe_add, ← inner_add_right]
      calc
        au + (av - g.asEReal x - h.asEReal∗ v) =
            (au + av) - g.asEReal x - h.asEReal∗ v := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ =
            (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v) := by
              rw [hsum]

/-- Helper for Proposition 14.19: for a dual point in `dom (h*)`, the inner supremum over
`effectiveDomain g` is the shifted conjugate defect of `g`. -/
private lemma iSup_effectiveDomain_affine_shift_add_eq_conjugate_sub
    (g h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) (u : H) (v : dom (h.asEReal∗)) :
    (⨆ x : effectiveDomain g,
      (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v)) =
      g.asEReal∗ (u + (v : H)) - h.asEReal∗ v := by
  have hv_top : h.asEReal∗ (v : H) ≠ ⊤ := (mem_dom_iff_ne_top _ _).1 v.2
  have hv_bot : h.asEReal∗ (v : H) ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hh.2.nonempty (v : H)
  let r : ℝ := -(h.asEReal∗ (v : H)).toReal
  have hr : ((r : ℝ) : EReal) = -h.asEReal∗ (v : H) := by
    dsimp [r]
    simpa using congrArg Neg.neg (EReal.coe_toReal hv_top hv_bot)
  have hrestrict :
      (⨆ x : effectiveDomain g, (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x)) =
        ⨆ x : H, (((⟪x, u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x) := by
    symm
    exact iSup_eq_iSup_subtype_of_eq_bot_outside
      (φ := fun x : H ↦ (((⟪x, u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x))
      (hbot := fun x hx ↦ by
        change (((⟪x, u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x) = ⊥
        rw [asEReal_eq_top_of_not_mem_effectiveDomain g hx]
        simp)
  -- Extend the primal supremum back to all of `H`, then recognize the conjugate of `g`.
  calc
    (⨆ x : effectiveDomain g,
      (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v)) =
        ⨆ x : effectiveDomain g,
          ((((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x) + (r : EReal)) := by
      refine iSup_congr fun x ↦ ?_
      rw [sub_eq_add_neg, hr]
    _ =
        (⨆ x : effectiveDomain g,
          (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x)) + (r : EReal) := by
      simpa using
        ereal_iSup_add_of_real_shift
          r
          (fun x : effectiveDomain g ↦
            (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x))
    _ = (⨆ x : H, (((⟪x, u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x)) + (r : EReal) := by
      rw [hrestrict]
    _ = g.asEReal∗ (u + (v : H)) + (r : EReal) := by
      rw [conjugate_apply]
    _ = g.asEReal∗ (u + (v : H)) - h.asEReal∗ v := by
      rw [hr]
      simp [sub_eq_add_neg]

/-- Proposition 14.19: if `g` is proper, if `h ∈ Γ₀(H)`, and if
`f = subOnEffectiveDomain g h`, then for every `u ∈ H`,
`f∗ u = sup_{v ∈ dom h*} (g* (u + v) - h* v)`. -/
theorem conjugate_subOnEffectiveDomain_eq_iSup_dom_conjugate_add_sub_conjugate
    (g h : H → Set.Ioi (⊥ : EReal)) (hg : IsProper g.asEReal) (hh : h ∈ Γ₀(H)) (u : H) :
    (subOnEffectiveDomain g h)∗ u =
      ⨆ v : dom (h.asEReal∗), (g.asEReal∗ (u + (v : H)) - h.asEReal∗ v) := by
  let _ := hg
  -- Route correction: prove the identity directly by restricting the primal supremum to
  -- `effectiveDomain g`, inserting the Fenchel--Moreau formula for `h`, and swapping suprema.
  rw [conjugate_apply]
  calc
    (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - subOnEffectiveDomain g h x)) =
        ⨆ x : effectiveDomain g, (((⟪(x : H), u⟫_ℝ : ℝ) : EReal) - subOnEffectiveDomain g h x) := by
      rw [iSup_eq_iSup_subtype_of_eq_bot_outside
        (φ := fun x : H ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - subOnEffectiveDomain g h x))]
      intro x hx
      -- Outside `effectiveDomain g`, the piecewise value is `⊤`, so the affine defect is `⊥`.
      simp [subOnEffectiveDomain, hx]
    _ = ⨆ x : effectiveDomain g, (((⟪(x : H), u⟫_ℝ : ℝ) : EReal) - (g.asEReal x - h.asEReal x)) := by
      refine iSup_congr fun x ↦ ?_
      simp [subOnEffectiveDomain, x.2]
    _ =
        ⨆ x : effectiveDomain g,
          ⨆ v : dom (h.asEReal∗),
            (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v) := by
      refine iSup_congr fun x ↦ ?_
      exact affine_defect_sub_eq_iSup_shifted_dual_defect g h hh u x
    _ =
        ⨆ v : dom (h.asEReal∗),
          ⨆ x : effectiveDomain g,
            (((⟪(x : H), u + (v : H)⟫_ℝ : ℝ) : EReal) - g.asEReal x - h.asEReal∗ v) := by
      rw [iSup_comm]
    _ = ⨆ v : dom (h.asEReal∗), (g.asEReal∗ (u + (v : H)) - h.asEReal∗ v) := by
      refine iSup_congr fun v ↦ ?_
      exact iSup_effectiveDomain_affine_shift_add_eq_conjugate_sub g h hh u v

end Conjugation

end ERealFunction
