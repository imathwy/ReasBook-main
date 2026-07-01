/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part1

section Chap03
section Section12

/-- Defn 12.2: The conjugate `f*` of a function `f` on `ℝ^n` is the function on `ℝ^n` defined by
`f*(x*) = sup_x (⟪x, x*⟫ - f x) = - inf_x (f x - ⟪x, x*⟫)`. -/
noncomputable def fenchelConjugate (n : Nat) (f : (Fin n → Real) → EReal) :
    (Fin n → Real) → EReal :=
  fun xStar =>
    sSup (Set.range (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x))

/-- Text 12.2.1: If `f₁` and `f₂` are functions on `ℝ^n` satisfying `f₁ x ≤ f₂ x` for every `x`,
then their conjugates satisfy the reverse inequality: `f₁*(x*) ≥ f₂*(x*)` for every `x*`. -/
theorem fenchelConjugate_antitone (n : Nat) :
    Antitone (fun f : (Fin n → Real) → EReal => fenchelConjugate n f) := by
  intro f₁ f₂ hf xStar
  unfold fenchelConjugate
  refine sSup_le ?_
  rintro y ⟨x, rfl⟩
  have hx :
      ((x ⬝ᵥ xStar : Real) : EReal) - f₂ x ≤ ((x ⬝ᵥ xStar : Real) : EReal) - f₁ x :=
    EReal.sub_le_sub le_rfl (hf x)
  exact le_trans hx (le_sSup ⟨x, rfl⟩)

/-- `fenchelConjugate` rewritten as a pointwise `iSup` (over `Set.range`). -/
lemma fenchelConjugate_eq_iSup (n : Nat) (f : (Fin n → Real) → EReal) (xStar : Fin n → Real) :
    fenchelConjugate n f xStar =
      iSup (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x) := by
  simp [fenchelConjugate, sSup_range]

/-- The dot product with a fixed vector is continuous. -/
lemma continuous_dotProduct_const {n : Nat} (x : Fin n → Real) :
    Continuous (fun xStar : Fin n → Real => x ⬝ᵥ xStar) := by
  classical
  -- `dotProduct x xStar = ∑ i, x i * xStar i`.
  simpa [dotProduct] using
    (continuous_finset_sum (s := Finset.univ)
      (f := fun i : Fin n => fun xStar : Fin n → Real => x i * xStar i)
      (fun i _hi => continuous_const.mul (continuous_apply i)))

/-- Lower semicontinuity of the affine pieces `xStar ↦ ⟪x, xStar⟫ - c` used in `fenchelConjugate`. -/
lemma lowerSemicontinuous_dotProduct_sub_const {n : Nat} (x : Fin n → Real) (c : EReal) :
    LowerSemicontinuous (fun xStar : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - c) := by
  have hcont_real : Continuous (fun xStar : Fin n → Real => x ⬝ᵥ xStar) :=
    continuous_dotProduct_const (x := x)
  have hcont_ereal : Continuous (fun xStar : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) := by
    simpa using (EReal.continuous_coe_iff (f := fun xStar : Fin n → Real => x ⬝ᵥ xStar)).2 hcont_real
  have hpair :
      Continuous (fun xStar : Fin n → Real => (((x ⬝ᵥ xStar : Real) : EReal), -c)) :=
    hcont_ereal.prodMk continuous_const
  have hlsc :
      LowerSemicontinuous
        (fun xStar : Fin n → Real =>
          (fun p : EReal × EReal => p.1 + p.2) (((x ⬝ᵥ xStar : Real) : EReal), -c)) := by
    exact EReal.lowerSemicontinuous_add.comp_continuous hpair
  simpa [sub_eq_add_neg] using hlsc

/-- `f*(b) ≤ μ` iff the affine function `x ↦ ⟪x,b⟫ - μ` is pointwise below `f`. -/
lemma fenchelConjugate_le_coe_iff_affine_le (n : Nat) (f : (Fin n → Real) → EReal)
    (b : Fin n → Real) (μ : Real) :
    fenchelConjugate n f b ≤ (μ : EReal) ↔
      ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ f x := by
  constructor
  · intro h x
    have hx' :
        ((x ⬝ᵥ b : Real) : EReal) - f x ≤ (μ : EReal) := by
      have hxle : ((x ⬝ᵥ b : Real) : EReal) - f x ≤ fenchelConjugate n f b := by
        unfold fenchelConjugate
        exact le_sSup ⟨x, rfl⟩
      exact le_trans hxle h
    have h1 : f x ≠ (⊥ : EReal) ∨ (μ : EReal) ≠ ⊤ := Or.inr (by simp)
    have h2 : f x ≠ (⊤ : EReal) ∨ (μ : EReal) ≠ ⊥ := Or.inr (by simp)
    have hx'' : ((x ⬝ᵥ b : Real) : EReal) ≤ (μ : EReal) + f x :=
      (EReal.sub_le_iff_le_add h1 h2).1 hx'
    have hx''' : ((x ⬝ᵥ b : Real) : EReal) ≤ f x + (μ : EReal) := by
      simpa [add_comm, add_left_comm, add_assoc] using hx''
    have h3 : (μ : EReal) ≠ ⊥ ∨ f x ≠ (⊤ : EReal) := Or.inl (by simp)
    have h4 : (μ : EReal) ≠ ⊤ ∨ f x ≠ (⊥ : EReal) := Or.inl (by simp)
    have : ((x ⬝ᵥ b : Real) : EReal) - (μ : EReal) ≤ f x :=
      (EReal.sub_le_iff_le_add h3 h4).2 hx'''
    simpa using this
  · intro h
    unfold fenchelConjugate
    refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    have hx : ((x ⬝ᵥ b : Real) : EReal) - (μ : EReal) ≤ f x := by
      simpa using h x
    have h3 : (μ : EReal) ≠ ⊥ ∨ f x ≠ (⊤ : EReal) := Or.inl (by simp)
    have h4 : (μ : EReal) ≠ ⊤ ∨ f x ≠ (⊥ : EReal) := Or.inl (by simp)
    have hx' : ((x ⬝ᵥ b : Real) : EReal) ≤ f x + (μ : EReal) :=
      (EReal.sub_le_iff_le_add h3 h4).1 hx
    have hx'' : ((x ⬝ᵥ b : Real) : EReal) ≤ (μ : EReal) + f x := by
      simpa [add_comm, add_left_comm, add_assoc] using hx'
    have h1 : f x ≠ (⊥ : EReal) ∨ (μ : EReal) ≠ ⊤ := Or.inr (by simp)
    have h2 : f x ≠ (⊤ : EReal) ∨ (μ : EReal) ≠ ⊥ := Or.inr (by simp)
    exact (EReal.sub_le_iff_le_add h1 h2).2 hx''

/-- Any affine map `h : ℝ^n → ℝ` can be written as `x ↦ ⟪x,b⟫ - β`. -/
lemma affineMap_exists_dotProduct_sub {n : Nat} (h : AffineMap ℝ (Fin n → Real) Real) :
    ∃ (b : Fin n → Real) (β : Real), ∀ x : Fin n → Real, h x = x ⬝ᵥ b - β := by
  classical
  rcases linearMap_exists_dotProduct_representation (φ := h.linear) with ⟨b, hb⟩
  refine ⟨b, -(h 0), ?_⟩
  intro x
  have hdecomp : h x = h.linear x + h 0 := by
    have := congrArg (fun f : (Fin n → Real) → Real => f x) (AffineMap.decomp (f := h))
    simpa using this
  -- `h x = ⟪x,b⟫ + h 0 = ⟪x,b⟫ - (-(h 0))`.
  simp [hdecomp, hb, sub_eq_add_neg]

/-- `clConv n f` is pointwise bounded above by `f`. -/
lemma clConv_le (n : Nat) (f : (Fin n → Real) → EReal) : clConv n f ≤ f := by
  classical
  intro x
  refine sSup_le ?_
  rintro y ⟨h, hh, rfl⟩
  exact hh x

/-- Any affine minorant of `f` is pointwise below `clConv n f`. -/
lemma affine_le_clConv (n : Nat) (f : (Fin n → Real) → EReal) (h : AffineMap ℝ (Fin n → Real) Real)
    (hh : ∀ y : Fin n → Real, (h y : EReal) ≤ f y) :
    ∀ x : Fin n → Real, (h x : EReal) ≤ clConv n f x := by
  classical
  intro x
  unfold clConv
  refine le_sSup ?_
  exact ⟨h, hh, rfl⟩

/-- Two `EReal` values are equal if they have the same real upper bounds. -/
lemma EReal.eq_of_forall_le_coe_iff {a b : EReal}
    (h : ∀ μ : Real, a ≤ (μ : EReal) ↔ b ≤ (μ : EReal)) : a = b := by
  classical
  by_cases hbtop : b = ⊤
  · -- If `b = ⊤`, then `b ≤ μ` is false for every real `μ`, hence so is `a ≤ μ`,
    -- and therefore `a = ⊤`.
    subst hbtop
    have ha_lt : ∀ μ : Real, (μ : EReal) < a := by
      intro μ
      have hbμ : ¬ (⊤ : EReal) ≤ (μ : EReal) := not_top_le_coe μ
      have haμ : ¬ a ≤ (μ : EReal) := by
        intro haμ
        exact hbμ ((h μ).1 haμ)
      have : ¬ (μ : EReal) ≥ a := by simpa [ge_iff_le] using haμ
      exact lt_of_not_ge this
    have ha_top : a = ⊤ := (EReal.eq_top_iff_forall_lt a).2 ha_lt
    exact ha_top
  by_cases hbbot : b = ⊥
  · -- If `b = ⊥`, then `b ≤ μ` is true for every real `μ`, hence so is `a ≤ μ`.
    -- This forces `a = ⊥`.
    subst hbbot
    have ha_le : ∀ μ : Real, a ≤ (μ : EReal) := by
      intro μ
      exact (h μ).2 (bot_le : (⊥ : EReal) ≤ (μ : EReal))
    have ha_ne_top : a ≠ ⊤ := by
      intro hatop
      have : (⊤ : EReal) ≤ (0 : EReal) := by simpa [hatop] using ha_le 0
      exact (not_top_le_coe 0) this
    by_cases ha_bot : a = ⊥
    · exact ha_bot
    · set s : Real := a.toReal
      have has : a = (s : EReal) := by
        simpa [s] using (EReal.coe_toReal (x := a) ha_ne_top ha_bot).symm
      have : ¬ a ≤ ((s - 1 : Real) : EReal) := by
        intro hle
        have hle' : (s : EReal) ≤ ((s - 1 : Real) : EReal) := by simpa [has] using hle
        have : s ≤ s - 1 := (EReal.coe_le_coe_iff).1 hle'
        linarith
      exact (this (ha_le (s - 1))).elim
  -- `b` is finite real.
  have hb_ne_top : b ≠ ⊤ := hbtop
  have hb_ne_bot : b ≠ ⊥ := hbbot
  set r : Real := b.toReal
  have hbr : b = (r : EReal) := by
    simpa [r] using (EReal.coe_toReal (x := b) hb_ne_top hb_ne_bot).symm
  have har : a ≤ (r : EReal) := by
    have : b ≤ (r : EReal) := by simp [hbr]
    exact (h r).2 this
  have ha_ne_top : a ≠ ⊤ := by
    intro hatop
    have har' := har
    simp [hatop] at har'
  have ha_ne_bot : a ≠ ⊥ := by
    intro habot
    have hb_lt : ¬ b ≤ ((r - 1 : Real) : EReal) := by
      intro hb
      have hb' : (r : EReal) ≤ ((r - 1 : Real) : EReal) := by
        simpa [hbr] using hb
      have : r ≤ r - 1 := (EReal.coe_le_coe_iff).1 hb'
      linarith
    have : a ≤ ((r - 1 : Real) : EReal) := by
      simp [habot]
    exact hb_lt ((h (r - 1)).1 this)
  set s : Real := a.toReal
  have has : a = (s : EReal) := by
    simpa [s] using (EReal.coe_toReal (x := a) ha_ne_top ha_ne_bot).symm
  have hrs : r ≤ s := by
    have : a ≤ (s : EReal) := by simp [has]
    have : b ≤ (s : EReal) := (h s).1 this
    simpa [hbr, EReal.coe_le_coe_iff] using this
  have hsr : s ≤ r := by
    have har' := har
    simp [has] at har'
    simpa [EReal.coe_le_coe_iff] using har'
  have hs : s = r := le_antisymm hsr hrs
  simp [has, hbr, hs]

/-- The Fenchel conjugate is always closed and convex. -/
lemma fenchelConjugate_closedConvex (n : Nat) (f : (Fin n → Real) → EReal) :
    LowerSemicontinuous (fenchelConjugate n f) ∧ ConvexFunction (fenchelConjugate n f) := by
  classical
  -- View `fenchelConjugate` as an `iSup` of closed convex functions.
  let g : (Fin n → Real) → (Fin n → Real) → EReal :=
    fun x xStar => ((x ⬝ᵥ xStar : Real) : EReal) - f x
  have hg_closed : ∀ x : Fin n → Real, ClosedConvexFunction (g x) := by
    intro x
    have hlsc : LowerSemicontinuous (g x) := by
      simpa [g] using lowerSemicontinuous_dotProduct_sub_const (x := x) (c := f x)
    -- Convexity: either the function is constant `⊤`/`⊥`, or it is a finite affine function.
    by_cases htop : f x = ⊤
    · have hconst : g x = fun _ : Fin n → Real => (⊥ : EReal) := by
        funext xStar
        simp [g, htop]
      have hconv : ConvexFunction (g x) := by
        -- epigraph of `⊥` is `univ`
        unfold ConvexFunction ConvexFunctionOn
        have hep :
            epigraph (Set.univ : Set (Fin n → Real)) (g x) =
              (Set.univ : Set ((Fin n → Real) × Real)) := by
          ext p
          constructor
          · intro _hp
            exact Set.mem_univ _
          · intro _hp
            refine ⟨trivial, ?_⟩
            simp [hconst]
        simpa [hep] using (convex_univ : Convex ℝ (Set.univ : Set ((Fin n → Real) × Real)))
      exact ⟨hconv, hlsc⟩
    by_cases hbot : f x = ⊥
    · have hconst : g x = fun _ : Fin n → Real => (⊤ : EReal) := by
        funext xStar
        simp [g, hbot]
      have hconv : ConvexFunction (g x) := by
        -- epigraph of `⊤` is `∅`
        unfold ConvexFunction ConvexFunctionOn
        have hep :
            epigraph (Set.univ : Set (Fin n → Real)) (g x) = (∅ : Set ((Fin n → Real) × Real)) := by
          ext p
          constructor
          · intro hp
            have hle : (g x) p.1 ≤ (p.2 : EReal) := hp.2
            have hle' := hle
            simp [hconst] at hle'
          · intro hp
            cases hp
        simpa [hep] using (convex_empty : Convex ℝ (∅ : Set ((Fin n → Real) × Real)))
      exact ⟨hconv, hlsc⟩
    · -- Finite case: `f x` is a real, so `g x` is affine hence convex.
      have hx_ne_top : f x ≠ ⊤ := htop
      have hx_ne_bot : f x ≠ ⊥ := hbot
      set r : Real := (f x).toReal
      have hr : f x = (r : EReal) := by
        simpa [r] using (EReal.coe_toReal (x := f x) hx_ne_top hx_ne_bot).symm
      have haff :
          AffineFunctionOn (Set.univ : Set (Fin n → Real))
            (fun xStar : Fin n → Real =>
              ((Finset.univ.sum (fun i => xStar i * x i) + (-r) : Real) : EReal)) := by
        simpa using affineFunctionOn_univ_inner_add_const (a := x) (α := -r)
      have hconvOn :
          ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (g x) := by
        -- Rewrite `g x` into the standard affine normal form.
        have hg :
            g x =
              (fun xStar : Fin n → Real =>
                ((Finset.univ.sum (fun i => xStar i * x i) + (-r) : Real) : EReal)) := by
          funext xStar
          have hdot : x ⬝ᵥ xStar = Finset.univ.sum (fun i : Fin n => xStar i * x i) := by
            classical
            simp [dotProduct, mul_comm]
          -- Convert to `EReal` and subtract the real constant.
          simp [g, hr, hdot, sub_eq_add_neg, add_comm]
        simpa [hg] using haff.2.1
      have hconv : ConvexFunction (g x) := by
        simpa [ConvexFunction] using hconvOn
      exact ⟨hconv, hlsc⟩
  have hSup : ClosedConvexFunction (fun xStar : Fin n → Real => iSup (fun x : Fin n → Real => g x xStar)) :=
    closedConvexFunction_iSup_of_closed (f := g) hg_closed
  have hEq :
      (fun xStar : Fin n → Real => iSup (fun x : Fin n → Real => g x xStar)) =
        fenchelConjugate n f := by
    funext xStar
    simp [g, fenchelConjugate_eq_iSup]
  have hClosed : ClosedConvexFunction (fenchelConjugate n f) := by
    simpa [hEq] using hSup
  exact ⟨hClosed.2, hClosed.1⟩

/-- For a real `x` and `a : EReal`, `x - a` is the supremum of `x - β` over real `β` with `a ≤ β`. -/
lemma sub_eq_sSup_image_sub_of_le (x : Real) (a : EReal) :
    (x : EReal) - a =
      sSup ((fun β : Real => ((x - β : Real) : EReal)) '' {β : Real | a ≤ (β : EReal)}) := by
  classical
  by_cases ha_top : a = ⊤
  · simp [ha_top]
  by_cases ha_bot : a = ⊥
  · -- Unbounded above, so the supremum is `⊤`.
    have htop :
        sSup ((fun β : Real => ((x - β : Real) : EReal)) '' {β : Real | a ≤ (β : EReal)}) =
          (⊤ : EReal) := by
      refine (EReal.eq_top_iff_forall_lt _).2 ?_
      intro y
      have hy : y < y + 1 := by linarith
      let β : Real := x - (y + 1)
      have hβmem : β ∈ ({β : Real | a ≤ (β : EReal)} : Set Real) := by
        simp [ha_bot]
      have himg :
          ((x - β : Real) : EReal) ∈
            (fun β : Real => ((x - β : Real) : EReal)) '' {β : Real | a ≤ (β : EReal)} := by
        exact ⟨β, hβmem, rfl⟩
      have hle :
          ((x - β : Real) : EReal) ≤
            sSup
              ((fun β : Real => ((x - β : Real) : EReal)) '' {β : Real | a ≤ (β : EReal)}) :=
        le_sSup himg
      have hxβ : (x - β : Real) = y + 1 := by
        dsimp [β]
        ring
      have hy' : (y : EReal) < ((x - β : Real) : EReal) := by
        simpa [hxβ] using (EReal.coe_lt_coe_iff.2 hy)
      exact lt_of_lt_of_le hy' hle
    calc
      (x : EReal) - a = (⊤ : EReal) := by simp [ha_bot]
      _ = sSup ((fun β : Real => ((x - β : Real) : EReal)) '' {β : Real | a ≤ (β : EReal)}) := by
        simpa using htop.symm
  -- Finite case: `a = r`.
  set r : Real := a.toReal
  have har : a = (r : EReal) := by
    have ha_ne_top : a ≠ ⊤ := ha_top
    have ha_ne_bot : a ≠ ⊥ := ha_bot
    simpa [r] using (EReal.coe_toReal (x := a) ha_ne_top ha_ne_bot).symm
  apply le_antisymm
  · -- `x - a ≤ sSup …` (use `β = r`).
    have hmem : r ∈ ({β : Real | a ≤ (β : EReal)} : Set Real) := by
      simp [har]
    have himg :
        ((x - r : Real) : EReal) ∈
          (fun β : Real => ((x - β : Real) : EReal)) '' {β : Real | a ≤ (β : EReal)} := by
      exact ⟨r, hmem, rfl⟩
    have hxle :
        ((x - r : Real) : EReal) ≤
          sSup ((fun β : Real => ((x - β : Real) : EReal)) '' {β : Real | a ≤ (β : EReal)}) :=
      le_sSup himg
    simpa [har] using hxle
  · -- `sSup … ≤ x - a`.
    refine sSup_le ?_
    rintro z ⟨β, hβ, rfl⟩
    have hβ' : r ≤ β := by
      simpa [har, EReal.coe_le_coe_iff] using hβ
    have : (x - β : Real) ≤ x - r := by linarith
    simpa [har] using (EReal.coe_le_coe_iff.2 this)

/-- The Fenchel biconjugate coincides with `clConv`. -/
lemma fenchelConjugate_biconjugate_eq_clConv (n : Nat) (f : (Fin n → Real) → EReal) :
    fenchelConjugate n (fenchelConjugate n f) = clConv n f := by
  classical
  funext x
  let fStar : (Fin n → Real) → EReal := fenchelConjugate n f
  apply le_antisymm
  · -- `f** ≤ clConv`.
    unfold fenchelConjugate
    refine sSup_le ?_
    rintro y ⟨b, rfl⟩
    -- Rewrite `⟪x,b⟫ - f*(b)` as a supremum over `β ≥ f*(b)`.
    have hrewrite :
        (((b ⬝ᵥ x : Real) : EReal) - fStar b) =
          sSup ((fun β : Real => ((x ⬝ᵥ b - β : Real) : EReal)) '' {β : Real | fStar b ≤ (β : EReal)}) := by
      -- Use commutativity of the dot product to match the `x ⬝ᵥ b` form.
      have : ((b ⬝ᵥ x : Real) : EReal) - fStar b = ((x ⬝ᵥ b : Real) : EReal) - fStar b := by
        simp [dotProduct_comm]
      simpa [this] using (sub_eq_sSup_image_sub_of_le (x := (x ⬝ᵥ b)) (a := fStar b))
    -- Every `β` satisfying `f*(b) ≤ β` yields an affine minorant of `f`, hence contributes to `clConv`.
    have hle : sSup ((fun β : Real => ((x ⬝ᵥ b - β : Real) : EReal)) '' {β : Real | fStar b ≤ (β : EReal)})
        ≤ clConv n f x := by
      refine sSup_le ?_
      rintro z ⟨β, hβ, rfl⟩
      have hminorant : ∀ y : Fin n → Real, ((y ⬝ᵥ b - β : Real) : EReal) ≤ f y := by
        exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := b) (μ := β)).1 hβ
      -- Build the corresponding affine map `y ↦ ⟪y,b⟫ - β`.
      let φ : (Fin n → Real) →ₗ[ℝ] Real :=
        { toFun := fun y => y ⬝ᵥ b
          map_add' := by
            intro y z
            -- linearity in the first argument via commutativity + `dotProduct_add`
            simp [dotProduct_comm, dotProduct_add]
          map_smul' := by
            intro c y
            -- scalar in the first argument via commutativity + `dotProduct_smul`
            simp [dotProduct_comm, dotProduct_smul, smul_eq_mul] }
      let hAff : AffineMap ℝ (Fin n → Real) Real :=
        { toFun := fun y => y ⬝ᵥ b - β
          linear := φ
          map_vadd' := by
            intro p v
            -- `v +ᵥ p = v + p` in a vector space
            simp [φ, dotProduct_comm, dotProduct_add, sub_eq_add_neg, add_assoc, add_left_comm,
              add_comm] }
      have hhAff : ∀ y : Fin n → Real, (hAff y : EReal) ≤ f y := by
        intro y
        simpa [hAff] using hminorant y
      have hxle : (hAff x : EReal) ≤ clConv n f x := affine_le_clConv (n := n) (f := f) hAff hhAff x
      simpa [hAff] using hxle
    have hmain : ((↑(b ⬝ᵥ x) : EReal) - fStar b) ≤ clConv n f x := by
      simpa [hrewrite] using hle
    simpa [fStar, fenchelConjugate] using hmain
  · -- `clConv ≤ f**`.
    unfold clConv
    refine sSup_le ?_
    rintro y ⟨h, hh, rfl⟩
    -- Put `h` in normal form `x ↦ ⟪x,b⟫ - β`.
    rcases affineMap_exists_dotProduct_sub (h := h) with ⟨b, β, hb⟩
    have hβ : fStar b ≤ (β : EReal) := by
      -- Use the characterization of upper bounds of `f*`.
      have : ∀ x : Fin n → Real, ((x ⬝ᵥ b - β : Real) : EReal) ≤ f x := by
        intro x
        -- `hh x` is `h x ≤ f x`; rewrite `h x` using `hb`.
        simpa [hb x] using hh x
      exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := b) (μ := β)).2 this
    have hx_le : (h x : EReal) ≤ ((x ⬝ᵥ b : Real) : EReal) - fStar b := by
      -- `β` is an upper bound on `f*(b)`, so subtracting `β` is below subtracting `f*(b)`.
      have hsub :
          ((x ⬝ᵥ b : Real) : EReal) - (β : EReal) ≤ ((x ⬝ᵥ b : Real) : EReal) - fStar b := by
        -- `sub_le_sub` is antitone in the second argument.
        have := EReal.sub_le_sub (x := ((x ⬝ᵥ b : Real) : EReal)) (y := ((x ⬝ᵥ b : Real) : EReal))
          (z := (β : EReal)) (t := fStar b) le_rfl hβ
        simpa using this
      -- Rewrite `h x` as `⟪x,b⟫ - β`.
      simpa [hb x] using hsub
    -- This is one term in the supremum defining `f** x`.
    have hx_term : ((x ⬝ᵥ b : Real) : EReal) - fStar b ≤ fenchelConjugate n fStar x := by
      unfold fenchelConjugate
      refine le_sSup ?_
      exact ⟨b, by simp [dotProduct_comm]⟩
    exact le_trans hx_le hx_term

/-- The conjugate of `clConv` agrees with the conjugate. -/
lemma fenchelConjugate_clConv_eq (n : Nat) (f : (Fin n → Real) → EReal) :
    fenchelConjugate n (clConv n f) = fenchelConjugate n f := by
  classical
  funext b
  refine EReal.eq_of_forall_le_coe_iff (a := fenchelConjugate n (clConv n f) b)
    (b := fenchelConjugate n f b) ?_
  intro μ
  -- Use the affine-minorant characterization for both sides.
  constructor
  · intro hμ
    -- `(clConv f)*(b) ≤ μ` gives the affine inequality against `clConv f`,
    -- and `clConv f ≤ f` transfers it to `f`.
    have hAff :
        ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ clConv n f x :=
      (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := clConv n f) (b := b) (μ := μ)).1 hμ
    have hAff' : ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ f x := by
      intro x
      exact le_trans (hAff x) (clConv_le (n := n) (f := f) x)
    exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := b) (μ := μ)).2 hAff'
  · intro hμ
    -- Conversely, an affine minorant of `f` is an affine minorant of `clConv f`.
    have hAff :
        ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ f x :=
      (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := b) (μ := μ)).1 hμ
    -- Build the affine map `x ↦ ⟪x,b⟫ - μ` and use `affine_le_clConv`.
    let φ : (Fin n → Real) →ₗ[ℝ] Real :=
      { toFun := fun y => y ⬝ᵥ b
        map_add' := by
          intro y z
          simp [dotProduct_comm, dotProduct_add]
        map_smul' := by
          intro c y
          simp [dotProduct_comm, dotProduct_smul, smul_eq_mul] }
    let hAffMap : AffineMap ℝ (Fin n → Real) Real :=
      { toFun := fun y => y ⬝ᵥ b - μ
        linear := φ
        map_vadd' := by
          intro p v
          simp [φ, dotProduct_comm, dotProduct_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] }
    have hhAffMap : ∀ y : Fin n → Real, (hAffMap y : EReal) ≤ f y := by
      intro y
      simpa [hAffMap] using hAff y
    have hle_cl : ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ clConv n f x := by
      intro x
      have := affine_le_clConv (n := n) (f := f) hAffMap hhAffMap x
      simpa [hAffMap] using this
    exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := clConv n f) (b := b) (μ := μ)).2 hle_cl

/-- If `f` is identically `⊤`, then `clConv n f` is identically `⊤`. -/
lemma clConv_eq_const_top_of_forall_eq_top {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ∀ x : Fin n → Real, f x = ⊤) :
    clConv n f = fun _ : Fin n → Real => (⊤ : EReal) := by
  classical
  funext x
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro y
  -- Use the constant affine function with value `y+1`.
  let hConst : AffineMap ℝ (Fin n → Real) Real :=
    { toFun := fun _ => y + 1
      linear := 0
      map_vadd' := by
        intro p v
        simp }
  have hhConst : ∀ z : Fin n → Real, (hConst z : EReal) ≤ f z := by
    intro z
    simp [hConst, hf z]
  have hx : (hConst x : EReal) ≤ clConv n f x := affine_le_clConv (n := n) (f := f) hConst hhConst x
  have hy : (y : EReal) < (hConst x : EReal) := by
    have : y < y + 1 := by linarith
    simpa [hConst] using (EReal.coe_lt_coe_iff.2 this)
  exact lt_of_lt_of_le hy hx

/-- A proper convex function has a proper Fenchel conjugate. -/
lemma proper_fenchelConjugate_of_proper (n : Nat) {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) := by
  classical
  have hclosed := fenchelConjugate_closedConvex (n := n) (f := f)
  have hconv : ConvexFunction (fenchelConjugate n f) := hclosed.2
  have hconvOn : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) := by
    simpa [ConvexFunction] using hconv
  -- A linear lower bound on `f` gives a finite point for `f*`.
  obtain ⟨b, β, hb⟩ := properConvexFunctionOn_exists_linear_lowerBound (n := n) (f := f) hf
  have hb' : ∀ x : Fin n → Real, ((x ⬝ᵥ b - β : Real) : EReal) ≤ f x := by
    intro x
    simpa [ge_iff_le] using hb x
  have hbstar : fenchelConjugate n f b ≤ (β : EReal) :=
    (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := b) (μ := β)).2 hb'
  have hne_epi : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) := by
    refine ⟨(b, β), ?_⟩
    exact (mem_epigraph_univ_iff (f := fenchelConjugate n f)).2 (by simpa using hbstar)
  -- `f*` never takes the value `⊥` if `f` is finite somewhere.
  obtain ⟨x0, r0, hx0⟩ := properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf
  have hnotbot : ∀ xStar : Fin n → Real, fenchelConjugate n f xStar ≠ (⊥ : EReal) := by
    intro xStar hbot
    have hterm_le : ((x0 ⬝ᵥ xStar : Real) : EReal) - f x0 ≤ fenchelConjugate n f xStar := by
      unfold fenchelConjugate
      exact le_sSup ⟨x0, rfl⟩
    have hterm_ne : ((x0 ⬝ᵥ xStar : Real) : EReal) - f x0 ≠ (⊥ : EReal) := by
      simpa [hx0] using (EReal.coe_ne_bot (x0 ⬝ᵥ xStar - r0))
    have hterm_le_bot : ((x0 ⬝ᵥ xStar : Real) : EReal) - f x0 ≤ (⊥ : EReal) := by
      simpa [hbot] using hterm_le
    have : ((x0 ⬝ᵥ xStar : Real) : EReal) - f x0 = (⊥ : EReal) :=
      le_antisymm hterm_le_bot bot_le
    exact hterm_ne this
  refine ⟨hconvOn, hne_epi, ?_⟩
  intro x hx
  exact hnotbot x

/-- Properness is preserved by Fenchel conjugation (for convex functions). -/
lemma fenchelConjugate_proper_iff (n : Nat) (f : (Fin n → Real) → EReal) (hf : ConvexFunction f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) ↔
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
  classical
  constructor
  · intro hfStar
    -- `f*` proper implies `f**` proper.
    have hproper_bi :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
          (fenchelConjugate n (fenchelConjugate n f)) :=
      proper_fenchelConjugate_of_proper (n := n) (f := fenchelConjugate n f) hfStar
    -- Rewrite `f**` as `clConv f`.
    have hbiconj : fenchelConjugate n (fenchelConjugate n f) = clConv n f :=
      fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f)
    have hclProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (clConv n f) := by
      simpa [hbiconj] using hproper_bi
    -- From properness of `clConv f`, deduce `f` is proper (using convexity of `f`).
    have hnotbot_f : ∀ x : Fin n → Real, f x ≠ (⊥ : EReal) := by
      intro x hx
      have hle : clConv n f x ≤ f x := (clConv_le (n := n) (f := f) x)
      have hbot : clConv n f x = (⊥ : EReal) := by
        exact le_antisymm (by simpa [hx] using hle) bot_le
      exact (hclProper.2.2 x (by simp)) hbot
    have hnot_all_top : ¬ (∀ x : Fin n → Real, f x = ⊤) := by
      intro hall
      have hcltop : clConv n f = (fun _ : Fin n → Real => (⊤ : EReal)) :=
        clConv_eq_const_top_of_forall_eq_top (n := n) (f := f) hall
      rcases hclProper.2.1 with ⟨p, hp⟩
      -- But the epigraph of a constant `⊤` function is empty.
      have : p ∈ (epigraph (Set.univ : Set (Fin n → Real)) (fun _ : Fin n → Real => (⊤ : EReal))) := by
        simpa [hcltop] using hp
      simp [epigraph] at this
    obtain ⟨x0, hx0_top⟩ := not_forall.1 hnot_all_top
    have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := hnotbot_f x0
    -- Build a point in the epigraph using the finite value at `x0`.
    set r0 : Real := (f x0).toReal
    have hr0 : f x0 = (r0 : EReal) := by
      have hx0_ne_top : f x0 ≠ (⊤ : EReal) := by
        intro htop
        exact hx0_top (by simp [htop])
      simpa [r0] using (EReal.coe_toReal (x := f x0) hx0_ne_top hx0_ne_bot).symm
    have hne_epi : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f) := by
      refine ⟨(x0, r0), ?_⟩
      exact (mem_epigraph_univ_iff (f := f)).2 (by simp [hr0])
    refine ⟨?_, hne_epi, ?_⟩
    · simpa [ConvexFunction] using hf
    · intro x hx
      exact hnotbot_f x
  · intro hfProper
    exact proper_fenchelConjugate_of_proper (n := n) (f := f) hfProper

/-- Theorem 12.2. Let `f` be a convex function. Then its conjugate `f*` (here represented by
`fenchelConjugate n f`) is a closed convex function, and it is proper if and only if `f` is
proper. Moreover, the conjugate of the closure equals the conjugate, and the biconjugate equals
the closure: `(cl f)^* = f^*` and `f^{**} = cl f` (here `cl f` is represented by `clConv n f`). -/
theorem fenchelConjugate_closedConvex_proper_iff_and_biconjugate (n : Nat)
    (f : (Fin n → Real) → EReal) (hf : ConvexFunction f) :
    (LowerSemicontinuous (fenchelConjugate n f) ∧ ConvexFunction (fenchelConjugate n f)) ∧
      (ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) ↔
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) ∧
        fenchelConjugate n (clConv n f) = fenchelConjugate n f ∧
          fenchelConjugate n (fenchelConjugate n f) = clConv n f := by
  have hclosed : LowerSemicontinuous (fenchelConjugate n f) ∧ ConvexFunction (fenchelConjugate n f) :=
    fenchelConjugate_closedConvex (n := n) (f := f)
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) ↔
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    fenchelConjugate_proper_iff (n := n) (f := f) hf
  have hcl : fenchelConjugate n (clConv n f) = fenchelConjugate n f :=
    fenchelConjugate_clConv_eq (n := n) (f := f)
  have hbiconj : fenchelConjugate n (fenchelConjugate n f) = clConv n f :=
    fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f)
  exact ⟨hclosed, hproper, hcl, hbiconj⟩

/-- Lower semicontinuity implies closedness of the book's epigraph `epigraph univ f`. -/
lemma isClosed_epigraph_univ_of_lowerSemicontinuous {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : LowerSemicontinuous f) :
    IsClosed (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
  -- Compare with the standard epigraph `{p : E × EReal | f p.1 ≤ p.2}` via the continuous map
  -- `(x, μ) ↦ (x, (μ : EReal))`.
  have hclosed :
      IsClosed {p : (Fin n → Real) × EReal | f p.1 ≤ p.2} :=
    hf.isClosed_epigraph
  have hcont : Continuous (fun p : (Fin n → Real) × Real => (p.1, (p.2 : EReal))) := by
    refine Continuous.prodMk continuous_fst ?_
    exact continuous_coe_real_ereal.comp continuous_snd
  have hpre :
      (fun p : (Fin n → Real) × Real => (p.1, (p.2 : EReal))) ⁻¹'
          {p : (Fin n → Real) × EReal | f p.1 ≤ p.2} =
        epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
    ext p
    constructor
    · intro hp
      refine ⟨by trivial, ?_⟩
      simpa using hp
    · intro hp
      exact hp.2
  simpa [hpre] using hclosed.preimage hcont

/-- Supporting affine minorant for a closed proper convex `EReal`-valued function:
if `(μ0 : EReal) < f x0`, then there is an affine `h` with `h ≤ f` and `μ0 < h x0`. -/
lemma exists_affineMap_strictly_above_below_point_ereal {n : Nat} {f : (Fin n → Real) → EReal}
    (hf_closed : LowerSemicontinuous f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∀ (x0 : Fin n → Real) (μ0 : Real), ((μ0 : EReal) < f x0) →
      ∃ h : AffineMap ℝ (Fin n → Real) Real,
        (∀ y : Fin n → Real, (h y : EReal) ≤ f y) ∧ μ0 < h x0 := by
  classical
  intro x0 μ0 hμ0
  let C : Set ((Fin n → Real) × Real) := epigraph (S := (Set.univ : Set (Fin n → Real))) f
  have hC_conv : Convex ℝ C := hf_proper.1
  have hC_closed : IsClosed C := isClosed_epigraph_univ_of_lowerSemicontinuous (hf := hf_closed)
  have hx0 : ((x0, μ0) : (Fin n → Real) × Real) ∉ C := by
    intro hx0
    have : f x0 ≤ (μ0 : EReal) := (mem_epigraph_univ_iff (f := f)).1 hx0
    exact (not_le_of_gt hμ0) this
  obtain ⟨l, u, hl, hu⟩ :=
    geometric_hahn_banach_closed_point (E := (Fin n → Real) × ℝ) (s := C) (x := (x0, μ0))
      hC_conv hC_closed hx0
  let H : Set ((Fin n → Real) × Real) := {p : (Fin n → Real) × Real | l p ≤ u}
  have hC_sub_H : C ⊆ H := by
    intro p hp
    have hp' : l p < u := hl p hp
    exact le_of_lt hp'
  have hx0_not_H : ((x0, μ0) : (Fin n → Real) × Real) ∉ H := by
    intro hxH
    exact (lt_irrefl u) (lt_of_lt_of_le hu hxH)
  -- Represent `l` as `p ↦ ⟪p.1, b⟫ + p.2 * t`.
  let t : Real := l ((0 : Fin n → Real), (1 : Real))
  let φ : (Fin n → Real) →ₗ[ℝ] Real := l.toLinearMap.comp (LinearMap.inl ℝ (Fin n → Real) ℝ)
  rcases linearMap_exists_dotProduct_representation (φ := φ) with ⟨b, hb⟩
  have hl_repr : ∀ p : (Fin n → Real) × Real, l p = p.1 ⬝ᵥ b + p.2 * t := by
    rintro ⟨x, μ⟩
    have hprod := strongDual_apply_prod (l := l) (x := x) (μ := μ)
    have hx0 : l (x, (0 : Real)) = φ x := by
      -- `φ x = l (x, 0)`.
      simp [φ]
    -- `l (x, μ) = l (x, 0) + μ * t`.
    simpa [t, hx0, hb x, add_comm, add_left_comm, add_assoc] using hprod
  have hH_repr :
      ∃ (bH : Fin n → Real) (tH βH : Real),
        (bH ≠ 0 ∨ tH ≠ 0) ∧
          H = {p : (Fin n → Real) × Real | p.1 ⬝ᵥ bH + p.2 * tH ≤ βH} := by
    refine ⟨b, t, u, ?_, ?_⟩
    · by_contra hzero
      push_neg at hzero
      rcases hzero with ⟨hb0, ht0⟩
      -- If `b = 0` and `t = 0`, then `l = 0`, so `H` is either empty or all of space.
      have hl0 : ∀ p : (Fin n → Real) × Real, l p = 0 := by
        intro p
        simp [hl_repr p, hb0, ht0]
      have hu0 : u < 0 := by simpa [hl0 ((x0, μ0) : (Fin n → Real) × Real)] using hu
      have hempty : H = (∅ : Set ((Fin n → Real) × Real)) := by
        ext p
        constructor
        · intro hp
          have : (0 : Real) ≤ u := by simpa [H, hl0 p] using hp
          exact (not_lt_of_ge this) hu0
        · intro hp
          cases hp
      have : (C : Set ((Fin n → Real) × Real)).Nonempty := hf_proper.2.1
      rcases this with ⟨p, hp⟩
      have : p ∈ H := hC_sub_H hp
      simp [hempty] at this
    · ext p
      simp [H, hl_repr p]
  have htricho :=
    (closedHalfSpace_trichotomy (n := n) (H := H) hH_repr)
  have hH_types : IsVerticalHalfSpace n H ∨ IsUpperHalfSpace n H ∨ IsLowerHalfSpace n H :=
    htricho.1
  -- Rule out the lower half-space case using the upward-closedness of the epigraph.
  cases hH_types with
  | inl hV =>
      rcases hV with ⟨bV, βV, hbV, hHV⟩
      -- Use a global affine lower bound for `f` and tilt it using the strict inequality at `x0`.
      obtain ⟨b0, β0, hb0⟩ :=
        properConvexFunctionOn_exists_linear_lowerBound (n := n) (f := f) hf_proper
      -- The affine map `g(x) = ⟪x,b0⟫ - β0` is a global minorant of `f`.
      let φ0 : (Fin n → Real) →ₗ[ℝ] Real :=
        { toFun := fun y => y ⬝ᵥ b0
          map_add' := by
            intro y z
            simp [dotProduct_comm, dotProduct_add]
          map_smul' := by
            intro c y
            simp [dotProduct_comm, dotProduct_smul, smul_eq_mul] }
      let g : AffineMap ℝ (Fin n → Real) Real :=
        φ0.toAffineMap + AffineMap.const ℝ (Fin n → Real) (-β0)
      have hg_le : ∀ y : Fin n → Real, (g y : EReal) ≤ f y := by
        intro y
        have : f y ≥ ((y ⬝ᵥ b0 - β0 : Real) : EReal) := hb0 y
        simpa [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      -- From `x0 ∉ H` we get the strict inequality `βV < ⟪x0,bV⟫`.
      have hx0_gt : βV < x0 ⬝ᵥ bV := by
        have : ((x0, μ0) : (Fin n → Real) × Real) ∉ {p : (Fin n → Real) × Real | p.1 ⬝ᵥ bV ≤ βV} := by
          simpa [H, hHV] using hx0_not_H
        have : ¬ x0 ⬝ᵥ bV ≤ βV := by
          simpa [Set.mem_setOf_eq] using this
        exact lt_of_not_ge this
      have hδpos : 0 < x0 ⬝ᵥ bV - βV := sub_pos.2 hx0_gt
      let s : Real := (|μ0 - g x0| + 1) / (x0 ⬝ᵥ bV - βV)
      -- The affine map `v(x) = ⟪x,bV⟫ - βV`.
      let φV : (Fin n → Real) →ₗ[ℝ] Real :=
        { toFun := fun y => y ⬝ᵥ bV
          map_add' := by
            intro y z
            simp [dotProduct_comm, dotProduct_add]
          map_smul' := by
            intro c y
            simp [dotProduct_comm, dotProduct_smul, smul_eq_mul] }
      let v : AffineMap ℝ (Fin n → Real) Real :=
        φV.toAffineMap + AffineMap.const ℝ (Fin n → Real) (-βV)
      let h : AffineMap ℝ (Fin n → Real) Real := g + s • v
      have hv_le : ∀ y : Fin n → Real, f y ≠ (⊤ : EReal) → y ⬝ᵥ bV ≤ βV := by
        intro y hy_top
        have hy_bot : f y ≠ (⊥ : EReal) := hf_proper.2.2 y (by simp)
        set r : Real := (f y).toReal
        have hr : f y = (r : EReal) := by
          simpa [r] using (EReal.coe_toReal (x := f y) hy_top hy_bot).symm
        have hyC : ((y, r) : (Fin n → Real) × Real) ∈ C :=
          (mem_epigraph_univ_iff (f := f)).2 (by simp [hr])
        have hyH : ((y, r) : (Fin n → Real) × Real) ∈ H := hC_sub_H hyC
        have : ((y, r) : (Fin n → Real) × Real) ∈ {p : (Fin n → Real) × Real | p.1 ⬝ᵥ bV ≤ βV} := by
          simpa [H, hHV] using hyH
        simpa [Set.mem_setOf_eq] using this
      have hh_le : ∀ y : Fin n → Real, (h y : EReal) ≤ f y := by
        intro y
        by_cases hy_top : f y = ⊤
        · simp [hy_top]
        · have hyineq : y ⬝ᵥ bV - βV ≤ 0 := by
            have : y ⬝ᵥ bV ≤ βV := hv_le (y := y) hy_top
            linarith
          have hs_nonneg : 0 ≤ s := by
            have : 0 ≤ |μ0 - g x0| + 1 := by
              have : 0 ≤ |μ0 - g x0| := abs_nonneg _
              linarith
            exact div_nonneg this (le_of_lt hδpos)
          have haux : h y ≤ g y := by
            have hvy : v y = y ⬝ᵥ bV - βV := by
              -- Reduce by definitional unfolding; avoid `simp` timeouts.
              rw [sub_eq_add_neg]
              dsimp [v, φV]
            have hhy : h y = g y + s * (y ⬝ᵥ bV - βV) := by
              -- `h = g + s • v`, so evaluate pointwise and use `hvy`.
              dsimp [h]
              change g y + s * v y = g y + s * (y ⬝ᵥ bV - βV)
              simp [hvy]
            -- Since `y ⬝ᵥ bV - βV ≤ 0` and `0 ≤ s`, the extra term is nonpositive.
            have hmul : s * (y ⬝ᵥ bV - βV) ≤ 0 := by
              have : s * (y ⬝ᵥ bV - βV) ≤ s * 0 :=
                mul_le_mul_of_nonneg_left hyineq hs_nonneg
              simpa using this
            have h' : g y + s * (y ⬝ᵥ bV - βV) ≤ g y + 0 := add_le_add_right hmul (g y)
            have : g y + s * (y ⬝ᵥ bV - βV) ≤ g y := by simpa using h'
            simpa [hhy] using this
          -- Convert `h y ≤ g y` to `EReal` and use `g ≤ f`.
          have : (h y : EReal) ≤ (g y : EReal) := by
            exact (EReal.coe_le_coe_iff.2 haux)
          exact le_trans this (hg_le y)
      have hμ0 : μ0 < h x0 := by
        have hδne : x0 ⬝ᵥ bV - βV ≠ 0 := ne_of_gt hδpos
        have hsδ :
            s * (x0 ⬝ᵥ bV - βV) = |μ0 - g x0| + 1 := by
          -- `s = (|μ0 - g x0| + 1) / (x0 ⬝ᵥ bV - βV)`.
          dsimp [s]
          -- `(A / δ) * δ = A` for `δ ≠ 0`.
          calc
            (|μ0 - g x0| + 1) / (x0 ⬝ᵥ bV - βV) * (x0 ⬝ᵥ bV - βV) =
                (|μ0 - g x0| + 1) * (x0 ⬝ᵥ bV - βV) / (x0 ⬝ᵥ bV - βV) := by
                  simpa using
                    (div_mul_eq_mul_div (|μ0 - g x0| + 1) (x0 ⬝ᵥ bV - βV) (x0 ⬝ᵥ bV - βV))
            _ = |μ0 - g x0| + 1 := by
                  simpa using (mul_div_cancel_right₀ (|μ0 - g x0| + 1) hδne)
        have hle_abs : μ0 - g x0 ≤ |μ0 - g x0| := le_abs_self _
        have hle : μ0 ≤ g x0 + |μ0 - g x0| := by linarith
        have hlt : μ0 < g x0 + (|μ0 - g x0| + 1) := by linarith
        -- Expand `h x0` as `g x0 + s * (x0 ⬝ᵥ bV - βV)`.
        have hvx0 : v x0 = x0 ⬝ᵥ bV - βV := by
          rw [sub_eq_add_neg]
          dsimp [v, φV]
        have hx0 :
            h x0 = g x0 + (|μ0 - g x0| + 1) := by
          -- Expand `h x0 = g x0 + s * v x0` and then rewrite using `hvx0` and `hsδ`.
          have hx0' : h x0 = g x0 + s * v x0 := by
            dsimp [h]
          calc
            h x0 = g x0 + s * v x0 := hx0'
            _ = g x0 + s * (x0 ⬝ᵥ bV - βV) := by simp [hvx0]
            _ = g x0 + (|μ0 - g x0| + 1) := by simp [hsδ]
        -- Now `μ0 < h x0`.
        simpa [hx0] using hlt
      refine ⟨h, hh_le, hμ0⟩
  | inr hUorL =>
      cases hUorL with
      | inl hU =>
          rcases hU with ⟨bU, βU, hHU⟩
          -- The affine map `h(x) = ⟪x,bU⟫ - βU` comes from the upper half-space.
          let φU : (Fin n → Real) →ₗ[ℝ] Real :=
            { toFun := fun y => y ⬝ᵥ bU
              map_add' := by
                intro y z
                simp [dotProduct_comm, dotProduct_add]
              map_smul' := by
                intro c y
                simp [dotProduct_comm, dotProduct_smul, smul_eq_mul] }
          let h : AffineMap ℝ (Fin n → Real) Real :=
            φU.toAffineMap + AffineMap.const ℝ (Fin n → Real) (-βU)
          have hμ0' : μ0 < h x0 := by
            have : ((x0, μ0) : (Fin n → Real) × Real) ∉ {p : (Fin n → Real) × Real | p.2 ≥ p.1 ⬝ᵥ bU - βU} := by
              simpa [H, hHU] using hx0_not_H
            have : ¬ (μ0 ≥ x0 ⬝ᵥ bU - βU) := by
              simpa [Set.mem_setOf_eq] using this
            have : μ0 < x0 ⬝ᵥ bU - βU := lt_of_not_ge this
            have hx0 : h x0 = x0 ⬝ᵥ bU - βU := by
              rw [sub_eq_add_neg]
              dsimp [h, φU]
            simpa [hx0] using this
          have hh : ∀ y : Fin n → Real, (h y : EReal) ≤ f y := by
            intro y
            by_cases hy_top : f y = ⊤
            · simp [hy_top]
            · have hy_bot : f y ≠ (⊥ : EReal) := hf_proper.2.2 y (by simp)
              set r : Real := (f y).toReal
              have hr : f y = (r : EReal) := by
                simpa [r] using (EReal.coe_toReal (x := f y) hy_top hy_bot).symm
              have hyC : ((y, r) : (Fin n → Real) × Real) ∈ C :=
                (mem_epigraph_univ_iff (f := f)).2 (by simp [hr])
              have hyH : ((y, r) : (Fin n → Real) × Real) ∈ H := hC_sub_H hyC
              have : ((y, r) : (Fin n → Real) × Real) ∈ {p : (Fin n → Real) × Real | p.2 ≥ p.1 ⬝ᵥ bU - βU} := by
                simpa [H, hHU] using hyH
              have hyr : r ≥ y ⬝ᵥ bU - βU := by
                simpa [Set.mem_setOf_eq] using this
              have : (h y : EReal) ≤ (r : EReal) := by
                exact (EReal.coe_le_coe_iff.2 hyr)
              simpa [hr] using this
          refine ⟨h, hh, hμ0'⟩
      | inr hL =>
          rcases hL with ⟨bL, βL, hHL⟩
          -- Lower half-spaces cannot contain a nonempty epigraph (which is upward closed).
          rcases properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf_proper with
            ⟨x1, r1, hr1⟩
          have hx1C : ((x1, r1) : (Fin n → Real) × Real) ∈ C :=
            (mem_epigraph_univ_iff (f := f)).2 (by simp [hr1])
          have hx1H : ((x1, r1) : (Fin n → Real) × Real) ∈ H := hC_sub_H hx1C
          let μ : Real := max r1 (x1 ⬝ᵥ bL - βL + 1)
          have hx1C' : ((x1, μ) : (Fin n → Real) × Real) ∈ C := by
            have : f x1 ≤ (μ : EReal) := by
              have hle : r1 ≤ μ := le_max_left r1 (x1 ⬝ᵥ bL - βL + 1)
              have : (r1 : EReal) ≤ (μ : EReal) := (EReal.coe_le_coe_iff.2 hle)
              simpa [hr1] using this
            exact (mem_epigraph_univ_iff (f := f)).2 this
          have hx1H' : ((x1, μ) : (Fin n → Real) × Real) ∈ H := hC_sub_H hx1C'
          have : ((x1, μ) : (Fin n → Real) × Real) ∈ {p : (Fin n → Real) × Real | p.2 ≤ p.1 ⬝ᵥ bL - βL} := by
            simpa [H, hHL] using hx1H'
          have hle : μ ≤ x1 ⬝ᵥ bL - βL := by
            simpa [Set.mem_setOf_eq] using this
          have hge : x1 ⬝ᵥ bL - βL + 1 ≤ μ := by
            dsimp [μ]
            exact le_max_right _ _
          have : x1 ⬝ᵥ bL - βL + 1 ≤ x1 ⬝ᵥ bL - βL := le_trans hge hle
          linarith

/-- A closed proper convex function agrees with its `clConv` envelope. -/
lemma clConv_eq_of_closedProperConvex {n : Nat} {f : (Fin n → Real) → EReal}
    (hf_closed : LowerSemicontinuous f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    clConv n f = f := by
  classical
  funext x
  apply le_antisymm
  · exact clConv_le (n := n) (f := f) x
  · -- Show `f x ≤ clConv n f x` using supporting affine minorants.
    by_cases hx_top : f x = ⊤
    · -- If `f x = ⊤`, show `clConv n f x = ⊤`.
      have htop : clConv n f x = (⊤ : EReal) := by
        refine (EReal.eq_top_iff_forall_lt _).2 ?_
        intro μ
        obtain ⟨h, hh, hμx⟩ :=
          exists_affineMap_strictly_above_below_point_ereal (f := f) hf_closed hf_proper x μ
            (by simp [hx_top])
        have hxle : (h x : EReal) ≤ clConv n f x := affine_le_clConv (n := n) (f := f) h hh x
        have hμx' : (μ : EReal) < (h x : EReal) := (EReal.coe_lt_coe_iff.2 hμx)
        exact lt_of_lt_of_le hμx' hxle
      simp [hx_top, htop]
    · have hx_bot : f x ≠ (⊥ : EReal) := hf_proper.2.2 x (by simp)
      set r : Real := (f x).toReal
      have hr : f x = (r : EReal) := by
        simpa [r] using (EReal.coe_toReal (x := f x) hx_top hx_bot).symm
      -- `⊥ < clConv n f x` since `f` has an affine minorant (properness).
      obtain ⟨b0, β0, hb0⟩ :=
        properConvexFunctionOn_exists_linear_lowerBound (n := n) (f := f) hf_proper
      let φ0 : (Fin n → Real) →ₗ[ℝ] Real :=
        { toFun := fun y => y ⬝ᵥ b0
          map_add' := by
            intro y z
            simp [dotProduct_comm, dotProduct_add]
          map_smul' := by
            intro c y
            simp [dotProduct_comm, dotProduct_smul, smul_eq_mul] }
      let g : AffineMap ℝ (Fin n → Real) Real :=
        φ0.toAffineMap + AffineMap.const ℝ (Fin n → Real) (-β0)
      have hg : ∀ y : Fin n → Real, (g y : EReal) ≤ f y := by
        intro y
        have : f y ≥ ((y ⬝ᵥ b0 - β0 : Real) : EReal) := hb0 y
        simpa [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hbot_lt : (⊥ : EReal) < clConv n f x := by
        have hxg : (g x : EReal) ≤ clConv n f x := affine_le_clConv (n := n) (f := f) g hg x
        have hbotg : (⊥ : EReal) < (g x : EReal) := by simp
        exact lt_of_lt_of_le hbotg hxg
      -- Now use `le_of_forall_lt` on `EReal`.
      refine le_of_forall_lt ?_
      intro y hy
      cases y using EReal.rec with
      | bot =>
          simpa using hbot_lt
      | top =>
          -- `⊤ < f x` is impossible.
          simp [hr] at hy
      | coe μ =>
          have hμ : (μ : EReal) < f x := by simpa using hy
          obtain ⟨h, hh, hμx⟩ :=
            exists_affineMap_strictly_above_below_point_ereal (f := f) hf_closed hf_proper x μ hμ
          have hxle : (h x : EReal) ≤ clConv n f x := affine_le_clConv (n := n) (f := f) h hh x
          have hμx' : (μ : EReal) < (h x : EReal) := (EReal.coe_lt_coe_iff.2 hμx)
          exact lt_of_lt_of_le hμx' hxle

end Section12
end Chap03
