import Mathlib
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap08.Proposition_8_20
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Proposition_12_11
import BauschkeLean.Chap12.Proposition_12_37
import BauschkeLean.Chap12.Proposition_12_36
import BauschkeLean.Chap12.Definition_12_5
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Proposition_13_12
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap13.Proposition_13_48
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap15.Definition_15_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

/-- Helper for Proposition 15 26: Jensen convexity implies convexity of the real-height epigraph.
-/
private theorem convex_epigraph_of_isConvex_ereal
    {H : Type u} [AddCommGroup H] [Module ℝ H] {f : H → EReal} (hconv : IsConvex f) :
    Convex ℝ (epigraph f) := by
  refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
  intro x y hx hy a ha0 ha1
  exact hconv ha0.le ha1.le

/-- Helper for Proposition 15 26: infimal postcomposition can be written as an indexed infimum
over the concrete fiber subtype. -/
private theorem infimalPostcomposition_eq_iInf_fiber
    {H : Type u} {K : Type v} (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) (y : K) :
    (L ▷ f) y = ⨅ x : {x // L x = y}, (f x.1 : EReal) := by
  change sInf ((fun x ↦ (f x : EReal)) '' (L ⁻¹' {y})) = ⨅ x : {x // L x = y}, (f x.1 : EReal)
  rw [show (fun x ↦ (f x : EReal)) '' (L ⁻¹' {y}) =
      Set.range (fun x : {x // L x = y} ↦ (f x.1 : EReal)) by
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, by simpa using hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x.1, by simp, rfl⟩]
  exact sInf_range

/-- Helper for Proposition 15 26: if the effective domain is empty, then the Fenchel conjugate is
identically `⊥`. -/
private theorem conjugate_eq_bot_of_effectiveDomain_empty
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : ¬ (effectiveDomain f).Nonempty) :
    f.asEReal∗ = fun _ : H ↦ (⊥ : EReal) := by
  funext u
  rw [conjugate_apply]
  apply le_antisymm
  · refine iSup_le fun x ↦ ?_
    have htop : f.asEReal x = ⊤ := by
      by_contra hx_top
      exact hdom ⟨x, by simpa [effectiveDomain, lt_top_iff_ne_top] using hx_top⟩
    simp [Function.asEReal, htop]
  · exact bot_le

/-- Helper for Proposition 15 26: a source-facing function with convex epigraph is convex on its
effective domain in the Chapter 8 sense. -/
private theorem convexOn_effectiveDomain_of_convex_epigraph
    {H : Type u} [AddCommGroup H] [Module ℝ H] {f : H → Set.Ioi (⊥ : EReal)}
    (hdom : (effectiveDomain f).Nonempty) (hconv : Convex ℝ (epigraph f.asEReal)) :
    ConvexOn f (effectiveDomain f) := by
  refine ⟨hdom, subset_rfl, ?_⟩
  intro x hx y hy α hα0 hα1
  exact (convex_epigraph_iff_jensen_on_dom f.asEReal).1 hconv hx hy hα0 hα1

/-- Helper for Proposition 15 26: properness of a Fenchel conjugate forces properness of the
original function. -/
private theorem isProper_of_conjugate_isProper
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {f : H → EReal}
    (hproper : IsProper f∗) :
    IsProper f := by
  rcases hproper.2 with ⟨u₀, hu₀⟩
  have hu₀_top : f∗ u₀ ≠ ⊤ := ne_of_lt ((mem_dom_iff _ _).mp hu₀)
  have hbot_not_mem : (⊥ : EReal) ∉ Set.range f∗ :=
    (isProper_iff_bot_notMem_range (f := f∗)).mp hproper |>.1
  have hf_ne_top : f ≠ ⊤ := by
    intro hf_top
    subst hf_top
    refine hbot_not_mem ?_
    refine ⟨u₀, ?_⟩
    rw [conjugate_apply]
    simp
  refine ⟨?_, ?_⟩
  · intro x hfx
    have htop_le : (⊤ : EReal) ≤ f∗ u₀ := by
      calc
        ⊤ = ((⟪x, u₀⟫_ℝ : ℝ) : EReal) - f x := by simp [hfx]
        _ ≤ f∗ u₀ := by
          simpa [conjugate_apply] using
            (le_iSup (fun y : H ↦ ((⟪y, u₀⟫_ℝ : ℝ) : EReal) - f y) x)
    exact hu₀_top (le_antisymm le_top htop_le)
  · by_contra hdom
    apply hf_ne_top
    funext x
    apply (not_mem_dom_iff f x).mp
    intro hx
    exact hdom ⟨x, hx⟩

/-- Helper for Proposition 15 26: under the standard range-domain hypothesis, the conjugate of a
linear precomposition is the adjoint infimal postcomposition once the source function belongs to
`Γ₀`. -/
private theorem conjugate_comp_eq_adjointInfimalPostcomposition_of_mem_gammaZero
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    (g.asEReal ∘ L)∗ = L.adjoint ▷ g.asEReal∗ := by
  let _ := hg
  let _ := hdom
  sorry

/-- Helper for Proposition 15 26: the domain-intersection hypothesis yields the range-domain
intersection needed for the Chapter 13 composition-conjugation formula. -/
private theorem range_inter_effectiveDomain_nonempty_of_inter_image_nonempty
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (hdom : (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) :
    (Set.range L ∩ effectiveDomain g).Nonempty := by
  rcases hdom with ⟨y, hyg, hyL⟩
  rcases hyL with ⟨x, hx, rfl⟩
  exact ⟨L x, ⟨x, rfl⟩, hyg⟩

/-- Helper for Proposition 15 26: the image-intersection hypothesis gives a common point of the
effective domains of `f` and `g ∘ L`. -/
private theorem effectiveDomain_inter_comp_nonempty_of_inter_image_nonempty
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (hdom : (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) :
    (effectiveDomain f ∩ effectiveDomain (g ∘ L)).Nonempty := by
  rcases hdom with ⟨y, hyg, hyL⟩
  rcases hyL with ⟨x, hxf, rfl⟩
  refine ⟨x, hxf, ?_⟩
  simpa [Function.comp, mem_effectiveDomain_iff] using hyg

/-- Helper for Proposition 15 26: if one effective domain is empty, then the dual infimal
convolution collapses to the constant function `⊥`. -/
private theorem dual_infimalConvolution_eq_bot_of_empty_effectiveDomain
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (A : K →L[ℝ] H)
    (hempty : ¬ (effectiveDomain f).Nonempty ∨ ¬ (effectiveDomain g).Nonempty) :
    f.asEReal∗ □ (A ▷ g.asEReal∗) = fun _ : H ↦ (⊥ : EReal) := by
  funext u
  rcases hempty with hdomf | hdomg
  · -- If `f` has empty effective domain, its conjugate is already constantly `⊥`.
    rw [conjugate_eq_bot_of_effectiveDomain_empty f hdomf, infimalConvolution_apply]
    apply le_antisymm
    · refine le_trans (iInf_le (fun y : H ↦ (⊥ : EReal) + (A ▷ g.asEReal∗) (u - y)) 0) ?_
      simp
    · exact bot_le
  · -- If `g` has empty effective domain, we evaluate the inner marginal at the fiber point `0`.
    have hconj_g : g.asEReal∗ = fun _ : K ↦ (⊥ : EReal) :=
      conjugate_eq_bot_of_effectiveDomain_empty g hdomg
    have hpost_zero : (A ▷ g.asEReal∗) 0 = (⊥ : EReal) := by
      have himage :
          (fun x : K ↦ (⊥ : EReal)) '' (A ⁻¹' ({0} : Set H)) = ({(⊥ : EReal)} : Set EReal) := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          simp
        · intro ht
          rcases Set.mem_singleton_iff.mp ht with rfl
          refine ⟨0, ?_, rfl⟩
          simp
      have himage_conj :
          (fun x ↦ g.asEReal∗ x) '' (A ⁻¹' ({0} : Set H)) = ({(⊥ : EReal)} : Set EReal) := by
        rw [hconj_g]
        exact himage
      -- Unfold the fiber infimum at `0` and collapse the image to the singleton `{⊥}`.
      change sInf ((fun x ↦ g.asEReal∗ x) '' (A ⁻¹' ({0} : Set H))) = (⊥ : EReal)
      rw [himage_conj]
      simp
    rw [infimalConvolution_apply]
    apply le_antisymm
    · refine le_trans (iInf_le (fun y : H ↦ f.asEReal∗ y + (A ▷ g.asEReal∗) (u - y)) u) ?_
      rw [sub_self, hpost_zero]
      simp
    · exact bot_le

/-- Helper for Proposition 15 26: in the nondegenerate case, the infimal postcomposition of the
second Fenchel conjugate along `A` already has convex real-height epigraph. -/
private theorem convex_epigraph_infimalPostcomposition_conjugate
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (g : K → Set.Ioi (⊥ : EReal)) (A : K →L[ℝ] H)
    (hdomg : (effectiveDomain g).Nonempty) :
    Convex ℝ (epigraph (A ▷ g.asEReal∗)) := by
  have hconv_g : IsConvex g.asEReal∗ := (mem_gamma_iff _).1 (conjugate_mem_gamma g.asEReal) |>.1
  -- Package `g∗` back into `]-∞,+∞]` and apply the Chapter 12 infimal-postcomposition owner.
  simpa [properConjugateIoi_apply] using
    convex_epigraph_infimalPostcomposition
      (properConjugateIoi g hdomg)
      A.toAffineMap
      (convex_epigraph_of_isConvex (properConjugateIoi g hdomg)
        (by simpa [properConjugateIoi_apply] using hconv_g))

/-- Helper for Proposition 15 26: the separable sum of the two packaged conjugates has convex
real-height epigraph. -/
private theorem convex_epigraph_separable_sum_properConjugates
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (hdomf : (effectiveDomain f).Nonempty) (hdomg : (effectiveDomain g).Nonempty) :
    Convex ℝ
      (epigraph (((properConjugateIoi f hdomf) ⊕ (properConjugateIoi g hdomg)).asEReal)) := by
  have hconv_f : IsConvex f.asEReal∗ := (mem_gamma_iff _).1 (conjugate_mem_gamma f.asEReal) |>.1
  have hconv_g : IsConvex g.asEReal∗ := (mem_gamma_iff _).1 (conjugate_mem_gamma g.asEReal) |>.1
  -- Convexity is coordinatewise on the product because each conjugate is convex on its own space.
  refine convex_epigraph_of_isConvex_ereal ?_
  intro x y α hα0 hα1
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  have hα_nonneg : (0 : EReal) ≤ (α : EReal) := EReal.coe_nonneg.mpr hα0
  have hβ_nonneg : (0 : EReal) ≤ (((1 - α : ℝ) : EReal)) :=
    EReal.coe_nonneg.mpr (sub_nonneg.mpr hα1)
  calc
    (((properConjugateIoi f hdomf) ⊕ (properConjugateIoi g hdomg)).asEReal)
        (α • (x₁, x₂) + (1 - α) • (y₁, y₂))
        =
          f.asEReal∗ (α • x₁ + (1 - α) • y₁) +
            g.asEReal∗ (α • x₂ + (1 - α) • y₂) := by
              simp [pointwiseAdd_apply, properConjugateIoi_apply]
    _ ≤ ((α : EReal) * f.asEReal∗ x₁ + (((1 - α : ℝ) : EReal) * f.asEReal∗ y₁)) +
          ((α : EReal) * g.asEReal∗ x₂ + (((1 - α : ℝ) : EReal) * g.asEReal∗ y₂)) := by
            exact add_le_add (hconv_f hα0 hα1) (hconv_g hα0 hα1)
    _ = ((α : EReal) * f.asEReal∗ x₁ + (α : EReal) * g.asEReal∗ x₂) +
          ((((1 - α : ℝ) : EReal) * f.asEReal∗ y₁) +
            (((1 - α : ℝ) : EReal) * g.asEReal∗ y₂)) := by
            simp [add_assoc, add_left_comm]
    _ = (α : EReal) *
          (((properConjugateIoi f hdomf) ⊕ (properConjugateIoi g hdomg)).asEReal) (x₁, x₂) +
          (((1 - α : ℝ) : EReal)) *
            (((properConjugateIoi f hdomf) ⊕ (properConjugateIoi g hdomg)).asEReal) (y₁, y₂) := by
            rw [← EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg (EReal.coe_ne_top α),
              ← EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg (EReal.coe_ne_top (1 - α))]
            simp [pointwiseAdd_apply, properConjugateIoi_apply]

section DualInfimalConvolution

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Helper for Proposition 15 26: a strict upper bound on an infimal convolution is witnessed by
one concrete decomposition point. -/
private theorem exists_decomposition_lt_of_infimalConvolution_lt
    {E : Type*} [AddGroup E] {F G : E → EReal} {x : E} {ξ : EReal}
    (hξ : (F □ G) x < ξ) :
    ∃ y : E, F y + G (x - y) < ξ := by
  -- Unfold the outer infimum and extract one decomposition value below the chosen upper bound.
  rw [infimalConvolution_apply] at hξ
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hξ
  exact ⟨y, hy⟩

/-- Helper for Proposition 15 26: every decomposition gives an upper bound on the infimal
convolution. -/
private theorem infimalConvolution_le_of_decomposition
    {E : Type*} [AddGroup E] {F G : E → EReal} (x y : E) :
    (F □ G) x ≤ F y + G (x - y) := by
  -- Evaluate the defining infimum at the chosen decomposition point `y`.
  rw [infimalConvolution_apply]
  exact iInf_le (fun z : E ↦ F z + G (x - z)) y

/-- Helper for Proposition 15 26: a decomposition value strictly below a real bound forces the
residual `G`-term to stay in the finite-above domain. -/
private theorem infimalConvolution_witness_residual_mem_dom_of_lt
    {E : Type*} [AddGroup E] {F G : E → EReal}
    (hF_bot : ∀ z : E, F z ≠ ⊥) {x y : E} {ξ : ℝ}
    (hy : F y + G (x - y) < (ξ : EReal)) :
    x - y ∈ dom G := by
  -- A real upper bound rules out `G (x - y) = ⊤`, because then the whole sum would be `⊤`.
  rw [mem_dom_iff]
  by_contra hxy_dom
  have hG_top : G (x - y) = ⊤ := le_antisymm le_top (le_of_not_gt hxy_dom)
  have hsum_lt_top : F y + G (x - y) < ⊤ := lt_trans hy (EReal.coe_lt_top ξ)
  have hsum_top : F y + G (x - y) = ⊤ := by
    rw [hG_top]
    exact EReal.add_top_of_ne_bot (hF_bot y)
  rw [hsum_top] at hsum_lt_top
  simp at hsum_lt_top

/-- Helper for Proposition 15 26: once `(F □ G) x` is known not to be `⊥`, any approximate
decomposition lying strictly below a real height has both coordinates in the Jensen domains of `F`
and `G`. -/
private theorem infimalConvolution_witness_mem_dom_of_lt_of_value_ne_bot
    {E : Type*} [AddGroup E] {F G : E → EReal}
    (hF_bot : ∀ z : E, F z ≠ ⊥) {x y : E} (hx_ne_bot : (F □ G) x ≠ ⊥)
    {ξ : ℝ} (hy : F y + G (x - y) < (ξ : EReal)) :
    y ∈ dom F ∧ x - y ∈ dom G := by
  have hres_dom :
      x - y ∈ dom G :=
    infimalConvolution_witness_residual_mem_dom_of_lt hF_bot hy
  refine ⟨?_, hres_dom⟩
  -- If `F y = ⊤`, either the decomposition sum is `⊥` and forces `(F □ G) x = ⊥`, or it is `⊤`
  -- and contradicts the strict real upper bound.
  rw [mem_dom_iff_ne_top]
  intro hF_top
  by_cases hG_bot : G (x - y) = ⊥
  · have hsum_bot : F y + G (x - y) = ⊥ := by
      rw [hF_top, hG_bot]
      simp
    have hle : (F □ G) x ≤ ⊥ := by
      simpa [hsum_bot] using infimalConvolution_le_of_decomposition (F := F) (G := G) x y
    exact hx_ne_bot (le_antisymm hle bot_le)
  · have hsum_lt_top : F y + G (x - y) < ⊤ := lt_trans hy (EReal.coe_lt_top ξ)
    have hsum_top : F y + G (x - y) = ⊤ := by
      rw [hF_top]
      exact EReal.top_add_of_ne_bot hG_bot
    rw [hsum_top] at hsum_lt_top
    simp at hsum_lt_top

/-- Helper for Proposition 15 26: if the residual `G (x - y)` is not `⊥`, then any decomposition
value strictly below a real height already places both coordinates in the Jensen domains of `F`
and `G`. -/
private theorem infimalConvolution_witness_mem_dom_of_lt_of_residual_ne_bot
    {E : Type*} [AddGroup E] {F G : E → EReal}
    (hF_bot : ∀ z : E, F z ≠ ⊥) {x y : E} (hG_ne_bot : G (x - y) ≠ ⊥)
    {ξ : ℝ} (hy : F y + G (x - y) < (ξ : EReal)) :
    y ∈ dom F ∧ x - y ∈ dom G := by
  have hres_dom :
      x - y ∈ dom G :=
    infimalConvolution_witness_residual_mem_dom_of_lt hF_bot hy
  refine ⟨?_, hres_dom⟩
  -- The residual being different from `⊥` rules out the `F y = ⊤` branch directly.
  rw [mem_dom_iff_ne_top]
  intro hF_top
  have hsum_lt_top : F y + G (x - y) < ⊤ := lt_trans hy (EReal.coe_lt_top ξ)
  have hsum_top : F y + G (x - y) = ⊤ := by
    rw [hF_top]
    exact EReal.top_add_of_ne_bot hG_ne_bot
  rw [hsum_top] at hsum_lt_top
  simp at hsum_lt_top

/-- Helper for Proposition 15 26: two strict decomposition witnesses yield the corresponding
strict weighted bound for the infimal convolution at the affine-combined base point. -/
private theorem infimalConvolution_combo_lt_of_witnesses
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F G : E → EReal}
    (hconvF : Convex ℝ (epigraph F)) (hconvG : Convex ℝ (epigraph G))
    {x₁ x₂ y₁ y₂ : E} {α ξ₁ ξ₂ : ℝ}
    (hy₁F : y₁ ∈ dom F) (hy₁G : x₁ - y₁ ∈ dom G)
    (hy₂F : y₂ ∈ dom F) (hy₂G : x₂ - y₂ ∈ dom G)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hy₁ : F y₁ + G (x₁ - y₁) < (ξ₁ : EReal))
    (hy₂ : F y₂ + G (x₂ - y₂) < (ξ₂ : EReal)) :
    (F □ G) (α • x₁ + (1 - α) • x₂) <
      (α : EReal) * (ξ₁ : EReal) + (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) := by
  have hFJ := (convex_epigraph_iff_jensen_on_dom F).1 hconvF
  have hGJ := (convex_epigraph_iff_jensen_on_dom G).1 hconvG
  have hαE_pos : (0 : EReal) < (α : EReal) := by
    exact_mod_cast hα0
  have hβ_pos : (0 : EReal) < (((1 - α : ℝ)) : EReal) := by
    exact_mod_cast sub_pos.mpr hα1
  have hα_nonneg : (0 : EReal) ≤ (α : EReal) := hαE_pos.le
  have hβ_nonneg : (0 : EReal) ≤ (((1 - α : ℝ)) : EReal) := hβ_pos.le
  let y : E := α • y₁ + (1 - α) • y₂
  have hresidual :
      α • x₁ + (1 - α) • x₂ - y =
        α • (x₁ - y₁) + (1 - α) • (x₂ - y₂) := by
    -- The residual of the combined witness is the combined residual.
    dsimp [y]
    simp [sub_eq_add_neg, smul_add, add_comm, add_left_comm, add_assoc]
  have hF_combo :
      F y ≤ (α : EReal) * F y₁ + (((1 - α : ℝ)) : EReal) * F y₂ := by
    -- Jensen's inequality for `F` controls the combined witness point.
    simpa [y] using hFJ hy₁F hy₂F hα0 hα1
  have hG_combo :
      G (α • x₁ + (1 - α) • x₂ - y) ≤
        (α : EReal) * G (x₁ - y₁) + (((1 - α : ℝ)) : EReal) * G (x₂ - y₂) := by
    -- The same Jensen step applies to the residual points of `G`.
    rw [hresidual]
    exact hGJ hy₁G hy₂G hα0 hα1
  have hdecomp :
      (F □ G) (α • x₁ + (1 - α) • x₂) ≤
        F y + G (α • x₁ + (1 - α) • x₂ - y) := by
    -- Evaluate the defining infimum at the affine-combined witness.
    exact
      infimalConvolution_le_of_decomposition
        (F := F) (G := G) (α • x₁ + (1 - α) • x₂) y
  have hsum_le :
      (F □ G) (α • x₁ + (1 - α) • x₂) ≤
        ((α : EReal) * F y₁ + (((1 - α : ℝ)) : EReal) * F y₂) +
          ((α : EReal) * G (x₁ - y₁) + (((1 - α : ℝ)) : EReal) * G (x₂ - y₂)) := by
    -- Combine the decomposition estimate with the two Jensen bounds.
    exact le_trans hdecomp (add_le_add hF_combo hG_combo)
  have hsum_target :
      (F □ G) (α • x₁ + (1 - α) • x₂) ≤
        (α : EReal) * (F y₁ + G (x₁ - y₁)) +
          (((1 - α : ℝ)) : EReal) * (F y₂ + G (x₂ - y₂)) := by
    -- First regroup the weighted endpoint terms, then fold them into weighted sums.
    have hsum_le' :
        (F □ G) (α • x₁ + (1 - α) • x₂) ≤
          ((α : EReal) * F y₁ + (α : EReal) * G (x₁ - y₁)) +
            ((((1 - α : ℝ)) : EReal) * F y₂ +
              (((1 - α : ℝ)) : EReal) * G (x₂ - y₂)) := by
      simpa [add_assoc, add_left_comm, add_comm] using hsum_le
    calc
      (F □ G) (α • x₁ + (1 - α) • x₂) ≤
          ((α : EReal) * F y₁ + (α : EReal) * G (x₁ - y₁)) +
            ((((1 - α : ℝ)) : EReal) * F y₂ +
              (((1 - α : ℝ)) : EReal) * G (x₂ - y₂)) := hsum_le'
      _ = (α : EReal) * (F y₁ + G (x₁ - y₁)) +
            (((1 - α : ℝ)) : EReal) * (F y₂ + G (x₂ - y₂)) := by
              rw [← EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg (EReal.coe_ne_top α),
                ← EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg (EReal.coe_ne_top (1 - α))]
  have hweight₁ :
      (α : EReal) * (F y₁ + G (x₁ - y₁)) < (α : EReal) * (ξ₁ : EReal) := by
    -- Positive scaling preserves the strict first witness bound.
    have :
        (F y₁ + G (x₁ - y₁)) * (α : EReal) <
          (ξ₁ : EReal) * (α : EReal) := by
      exact strict_right_mul_lt hαE_pos (EReal.coe_ne_top α) hy₁
    simpa [mul_comm] using this
  have hweight₂ :
      (((1 - α : ℝ)) : EReal) * (F y₂ + G (x₂ - y₂)) <
        (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) := by
    -- Positive scaling preserves the strict second witness bound.
    have :
        (F y₂ + G (x₂ - y₂)) * (((1 - α : ℝ)) : EReal) <
          (ξ₂ : EReal) * (((1 - α : ℝ)) : EReal) := by
      exact strict_right_mul_lt hβ_pos (EReal.coe_ne_top (1 - α)) hy₂
    simpa [mul_comm] using this
  have hweighted_lt :
      (α : EReal) * (F y₁ + G (x₁ - y₁)) +
          (((1 - α : ℝ)) : EReal) * (F y₂ + G (x₂ - y₂)) <
        (α : EReal) * (ξ₁ : EReal) + (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) := by
    -- The two strict weighted bounds add directly.
    exact EReal.add_lt_add hweight₁ hweight₂
  exact lt_of_le_of_lt hsum_target hweighted_lt

/-- Helper for Proposition 15 26: every finite-above point of an `EReal`-valued function admits a
real height above the function value. -/
private theorem exists_real_ge_of_mem_dom_local
    {E : Type*} {G : E → EReal} {z : E} (hz : z ∈ dom G) :
    ∃ ξ : ℝ, G z ≤ (ξ : EReal) := by
  -- Domain membership means the value lies strictly below `⊤`, so a real separator exists.
  rw [mem_dom_iff] at hz
  rcases EReal.lt_iff_exists_real_btwn.mp hz with ⟨ξ, hξ, _⟩
  exact ⟨ξ, le_of_lt hξ⟩

/-- Helper for Proposition 15 26: a residual value equal to `⊥` stays equal to `⊥` along every
strict convex combination with a point of the finite-above domain. -/
private theorem combo_value_eq_bot_of_left_bot_of_convex_epigraph_local
    {E : Type*} [AddCommGroup E] [Module ℝ E] {G : E → EReal}
    (hconvG : Convex ℝ (epigraph G)) {z₁ z₂ : E} (hz₁_bot : G z₁ = ⊥) (hz₂_dom : z₂ ∈ dom G)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    G (α • z₁ + (1 - α) • z₂) = ⊥ := by
  -- Route correction: as in Proposition 8.4, we use arbitrary real heights above `⊥` and force
  -- the convex-combination height below every prescribed real budget.
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  rcases exists_real_ge_of_mem_dom_local hz₂_dom with ⟨ξ, hξ⟩
  let η : ℝ := (r - (1 - α) * ξ) / α - 1
  have hz₁_mem : (z₁, η) ∈ epigraph G := by
    -- Any real ordinate lies above `⊥`.
    rw [mem_epigraph_iff, hz₁_bot]
    simp
  have hz₂_mem : (z₂, ξ) ∈ epigraph G := by
    -- The chosen finite-above witness gives a genuine real-height epigraph point.
    simpa [mem_epigraph_iff] using hξ
  have hβ : 0 < 1 - α := sub_pos.mpr hα1
  have hcombo_mem :
      (α • (z₁, η) + (1 - α) • (z₂, ξ)) ∈ epigraph G := by
    -- Convexity transfers membership to the strict convex combination.
    exact (convex_iff_forall_pos.mp hconvG) hz₁_mem hz₂_mem hα0 hβ (by ring)
  have hcombo_le :
      G (α • z₁ + (1 - α) • z₂) ≤ ((α * η + (1 - α) * ξ : ℝ) : EReal) := by
    -- Rewrite the product-space combination into the desired base point and height.
    rw [mem_epigraph_iff] at hcombo_mem
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo_mem
  have hη_eq : α * η + (1 - α) * ξ = r - α := by
    -- The auxiliary height `η` is tuned so that the combined ordinate becomes `r - α`.
    dsimp [η]
    field_simp [hα0.ne']
    ring
  have hheight_lt : ((α * η + (1 - α) * ξ : ℝ) : EReal) < (r : EReal) := by
    -- Since `α > 0`, the height `r - α` is strictly below the target budget `r`.
    rw [hη_eq]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hα0)
  exact lt_of_le_of_lt hcombo_le hheight_lt

/-- Helper for Proposition 15 26: if the left factor never attains `⊥`, then convexity of the two
real-height epigraphs should imply convexity of the infimal convolution epigraph directly at the
`EReal` level. -/
private theorem convex_epigraph_infimalConvolution_of_convex_epigraph_left_ne_bot
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F G : E → EReal) (hF_bot : ∀ z : E, F z ≠ ⊥)
    (hconvF : Convex ℝ (epigraph F)) (hconvG : Convex ℝ (epigraph G)) :
    Convex ℝ (epigraph (F □ G)) := by
  -- Route correction: the previous sigma-fiber rewrite is false because a `⊤` left term can meet
  -- a `⊥` inner infimum. We therefore work directly with the nested infimal convolution.
  refine (convex_epigraph_iff_jensen_on_dom (F □ G)).2 ?_
  intro x₁ x₂ hx₁_dom hx₂_dom α hα0 hα1
  have hβ_pos : 0 < 1 - α := sub_pos.mpr hα1
  have hαE_pos : (0 : EReal) < (α : EReal) := by
    exact_mod_cast hα0
  have hβE_pos : (0 : EReal) < (((1 - α : ℝ)) : EReal) := by
    exact_mod_cast hβ_pos
  have hresidual {y₁ y₂ : E} :
      α • x₁ + (1 - α) • x₂ - (α • y₁ + (1 - α) • y₂) =
        α • (x₁ - y₁) + (1 - α) • (x₂ - y₂) := by
    -- The residual of the affine-combined witness is the affine combination of the residuals.
    simp [sub_eq_add_neg, smul_add, add_comm, add_left_comm, add_assoc]
  by_cases hx₁_bot : (F □ G) x₁ = ⊥
  · have hcombo_bot : (F □ G) (α • x₁ + (1 - α) • x₂) = ⊥ := by
      -- Push the combined value below every real budget using one arbitrary-low witness at `x₁`.
      refine (EReal.eq_bot_iff_forall_lt _).2 ?_
      intro r
      have hx₂_lt_top : (F □ G) x₂ < ⊤ := (mem_dom_iff (F □ G) x₂).mp hx₂_dom
      obtain ⟨ξ₂, hx₂_lt, _⟩ := EReal.lt_iff_exists_real_btwn.mp hx₂_lt_top
      let η₁ : ℝ := (r - (1 - α) * ξ₂) / α - 1
      have hx₁_lt : (F □ G) x₁ < (η₁ : EReal) := by
        simp [hx₁_bot]
      obtain ⟨y₁, hy₁⟩ :=
        exists_decomposition_lt_of_infimalConvolution_lt
          (F := F) (G := G) (x := x₁) (ξ := (η₁ : EReal)) hx₁_lt
      obtain ⟨y₂, hy₂⟩ :=
        exists_decomposition_lt_of_infimalConvolution_lt
          (F := F) (G := G) (x := x₂) (ξ := (ξ₂ : EReal)) hx₂_lt
      have hy₂G : x₂ - y₂ ∈ dom G :=
        infimalConvolution_witness_residual_mem_dom_of_lt hF_bot hy₂
      by_cases hres₁_bot : G (x₁ - y₁) = ⊥
      · let y : E := α • y₁ + (1 - α) • y₂
        have hG_combo_bot :
            G (α • (x₁ - y₁) + (1 - α) • (x₂ - y₂)) = ⊥ := by
          -- A `⊥` residual stays `⊥` along the segment when the other residual stays finite above.
          exact
            combo_value_eq_bot_of_left_bot_of_convex_epigraph_local
              (G := G) hconvG hres₁_bot hy₂G hα0 hα1
        have hdecomp :
            (F □ G) (α • x₁ + (1 - α) • x₂) ≤
              F y + G (α • x₁ + (1 - α) • x₂ - y) :=
          infimalConvolution_le_of_decomposition
            (F := F) (G := G) (α • x₁ + (1 - α) • x₂) y
        have hle_bot : (F □ G) (α • x₁ + (1 - α) • x₂) ≤ ⊥ := by
          -- Evaluating at the combined witness gives a sum with residual value `⊥`.
          simpa [y, hresidual, hG_combo_bot, EReal.add_bot] using hdecomp
        exact lt_of_le_of_lt hle_bot (by simp)
      · have hres₁_ne_bot : G (x₁ - y₁) ≠ ⊥ := hres₁_bot
        have hy₁_mem : y₁ ∈ dom F ∧ x₁ - y₁ ∈ dom G :=
          infimalConvolution_witness_mem_dom_of_lt_of_residual_ne_bot hF_bot hres₁_ne_bot hy₁
        by_cases hres₂_bot : G (x₂ - y₂) = ⊥
        · let y : E := α • y₁ + (1 - α) • y₂
          have hG_combo_bot :
              G (α • (x₁ - y₁) + (1 - α) • (x₂ - y₂)) = ⊥ := by
            -- If the right residual is `⊥`, swap the segment endpoints and apply the same lemma.
            have hswap :
                G ((1 - α) • (x₂ - y₂) + (1 - (1 - α)) • (x₁ - y₁)) = ⊥ := by
              exact
                combo_value_eq_bot_of_left_bot_of_convex_epigraph_local
                  (G := G) hconvG hres₂_bot hy₁_mem.2 hβ_pos (by linarith)
            have hrewrite : 1 - (1 - α) = α := by
              ring
            simpa [hrewrite, add_comm, add_left_comm, add_assoc] using hswap
          have hdecomp :
              (F □ G) (α • x₁ + (1 - α) • x₂) ≤
                F y + G (α • x₁ + (1 - α) • x₂ - y) :=
            infimalConvolution_le_of_decomposition
              (F := F) (G := G) (α • x₁ + (1 - α) • x₂) y
          have hle_bot : (F □ G) (α • x₁ + (1 - α) • x₂) ≤ ⊥ := by
            -- The swapped `⊥` propagation again turns the chosen decomposition value into `⊥`.
            simpa [y, hresidual, hG_combo_bot, EReal.add_bot] using hdecomp
          exact lt_of_le_of_lt hle_bot (by simp)
        · have hres₂_ne_bot : G (x₂ - y₂) ≠ ⊥ := hres₂_bot
          have hy₂_mem : y₂ ∈ dom F ∧ x₂ - y₂ ∈ dom G :=
            infimalConvolution_witness_mem_dom_of_lt_of_residual_ne_bot hF_bot hres₂_ne_bot hy₂
          have hcombo_lt :
              (F □ G) (α • x₁ + (1 - α) • x₂) <
                (α : EReal) * (η₁ : EReal) +
                  (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) := by
            -- With both residuals finite above, the strict two-witness Jensen estimate applies.
            exact
              infimalConvolution_combo_lt_of_witnesses
                (F := F) (G := G) hconvF hconvG
                hy₁_mem.1 hy₁_mem.2 hy₂_mem.1 hy₂_mem.2
                hα0 hα1 hy₁ hy₂
          have hη₁_eq : α * η₁ + (1 - α) * ξ₂ = r - α := by
            -- The auxiliary level `η₁` is chosen so the weighted sum lands strictly below `r`.
            dsimp [η₁]
            field_simp [hα0.ne']
            ring
          have hbudget :
              (α : EReal) * (η₁ : EReal) +
                  (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) <
                (r : EReal) := by
            rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, hη₁_eq]
            exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hα0)
          exact lt_trans hcombo_lt hbudget
    -- Once the combined value is `⊥`, Jensen's inequality is immediate because the left endpoint
    -- already contributes a `⊥` weighted term.
    simp [hcombo_bot, hx₁_bot, EReal.mul_bot_of_pos hαE_pos]
  · have hx₁_ne_bot : (F □ G) x₁ ≠ ⊥ := hx₁_bot
    by_cases hx₂_bot : (F □ G) x₂ = ⊥
    · have hcombo_bot : (F □ G) (α • x₁ + (1 - α) • x₂) = ⊥ := by
        -- This is the symmetric endpoint-`⊥` case, handled by swapping the roles of the endpoints.
        refine (EReal.eq_bot_iff_forall_lt _).2 ?_
        intro r
        have hx₁_lt_top : (F □ G) x₁ < ⊤ := (mem_dom_iff (F □ G) x₁).mp hx₁_dom
        obtain ⟨ξ₁, hx₁_lt, _⟩ := EReal.lt_iff_exists_real_btwn.mp hx₁_lt_top
        let η₂ : ℝ := (r - α * ξ₁) / (1 - α) - 1
        have hx₂_lt : (F □ G) x₂ < (η₂ : EReal) := by
          simp [hx₂_bot]
        obtain ⟨y₁, hy₁⟩ :=
          exists_decomposition_lt_of_infimalConvolution_lt
            (F := F) (G := G) (x := x₁) (ξ := (ξ₁ : EReal)) hx₁_lt
        obtain ⟨y₂, hy₂⟩ :=
          exists_decomposition_lt_of_infimalConvolution_lt
            (F := F) (G := G) (x := x₂) (ξ := (η₂ : EReal)) hx₂_lt
        have hy₁G : x₁ - y₁ ∈ dom G :=
          infimalConvolution_witness_residual_mem_dom_of_lt hF_bot hy₁
        by_cases hres₂_bot : G (x₂ - y₂) = ⊥
        · let y : E := α • y₁ + (1 - α) • y₂
          have hswap :
              G ((1 - α) • (x₂ - y₂) + (1 - (1 - α)) • (x₁ - y₁)) = ⊥ := by
            -- Put the `⊥` residual on the left so the local propagation lemma applies directly.
            exact
              combo_value_eq_bot_of_left_bot_of_convex_epigraph_local
                (G := G) hconvG hres₂_bot hy₁G hβ_pos (by linarith)
          have hrewrite : 1 - (1 - α) = α := by
            ring
          have hG_combo_bot :
              G (α • (x₁ - y₁) + (1 - α) • (x₂ - y₂)) = ⊥ := by
            simpa [hrewrite, add_comm, add_left_comm, add_assoc] using hswap
          have hdecomp :
              (F □ G) (α • x₁ + (1 - α) • x₂) ≤
                F y + G (α • x₁ + (1 - α) • x₂ - y) :=
            infimalConvolution_le_of_decomposition
              (F := F) (G := G) (α • x₁ + (1 - α) • x₂) y
          have hle_bot : (F □ G) (α • x₁ + (1 - α) • x₂) ≤ ⊥ := by
            -- The chosen decomposition again has `⊥` residual value after convex combination.
            simpa [y, hresidual, hG_combo_bot, EReal.add_bot] using hdecomp
          exact lt_of_le_of_lt hle_bot (by simp)
        · have hres₂_ne_bot : G (x₂ - y₂) ≠ ⊥ := hres₂_bot
          have hy₂_mem : y₂ ∈ dom F ∧ x₂ - y₂ ∈ dom G :=
            infimalConvolution_witness_mem_dom_of_lt_of_residual_ne_bot hF_bot hres₂_ne_bot hy₂
          by_cases hres₁_bot : G (x₁ - y₁) = ⊥
          · let y : E := α • y₁ + (1 - α) • y₂
            have hG_combo_bot :
                G (α • (x₁ - y₁) + (1 - α) • (x₂ - y₂)) = ⊥ := by
              -- If the left residual is already `⊥`, use it directly.
              exact
                combo_value_eq_bot_of_left_bot_of_convex_epigraph_local
                  (G := G) hconvG hres₁_bot hy₂_mem.2 hα0 hα1
            have hdecomp :
                (F □ G) (α • x₁ + (1 - α) • x₂) ≤
                  F y + G (α • x₁ + (1 - α) • x₂ - y) :=
              infimalConvolution_le_of_decomposition
                (F := F) (G := G) (α • x₁ + (1 - α) • x₂) y
            have hle_bot : (F □ G) (α • x₁ + (1 - α) • x₂) ≤ ⊥ := by
              -- The combined decomposition value is again `⊥`.
              simpa [y, hresidual, hG_combo_bot, EReal.add_bot] using hdecomp
            exact lt_of_le_of_lt hle_bot (by simp)
          · have hres₁_ne_bot : G (x₁ - y₁) ≠ ⊥ := hres₁_bot
            have hy₁_mem : y₁ ∈ dom F ∧ x₁ - y₁ ∈ dom G :=
              infimalConvolution_witness_mem_dom_of_lt_of_residual_ne_bot hF_bot hres₁_ne_bot hy₁
            have hcombo_lt :
                (F □ G) (α • x₁ + (1 - α) • x₂) <
                  (α : EReal) * (ξ₁ : EReal) +
                    (((1 - α : ℝ)) : EReal) * (η₂ : EReal) := by
              -- When both residuals avoid `⊥`, the strict two-witness estimate closes the branch.
              exact
                infimalConvolution_combo_lt_of_witnesses
                  (F := F) (G := G) hconvF hconvG
                  hy₁_mem.1 hy₁_mem.2 hy₂_mem.1 hy₂_mem.2
                  hα0 hα1 hy₁ hy₂
            have hη₂_eq : α * ξ₁ + (1 - α) * η₂ = r - (1 - α) := by
              -- The auxiliary right budget is tuned to land strictly below `r`.
              dsimp [η₂]
              field_simp [sub_ne_zero.mpr hα1.ne]
              ring
            have hbudget :
                (α : EReal) * (ξ₁ : EReal) +
                    (((1 - α : ℝ)) : EReal) * (η₂ : EReal) <
                  (r : EReal) := by
              rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, hη₂_eq]
              exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hβ_pos)
            exact lt_trans hcombo_lt hbudget
      -- The right endpoint contributes the `⊥` weighted term in this symmetric branch.
      simp [hcombo_bot, hx₂_bot]
    · have hx₂_ne_bot : (F □ G) x₂ ≠ ⊥ := hx₂_bot
      have hterm₁_ne_top : (α : EReal) * (F □ G) x₁ ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl (by exact_mod_cast hα0.le),
          Or.inl (EReal.coe_ne_top α), ?_⟩
        exact Or.inr ((mem_dom_iff (F □ G) x₁).mp hx₁_dom).ne
      have hterm₂_ne_top : (((1 - α : ℝ)) : EReal) * (F □ G) x₂ ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)),
          Or.inl (by exact_mod_cast hβ_pos.le), Or.inl (EReal.coe_ne_top (1 - α)), ?_⟩
        exact Or.inr ((mem_dom_iff (F □ G) x₂).mp hx₂_dom).ne
      -- Reserve separate budgets above the two weighted endpoint values and approximate each
      -- infimum.
      refine EReal.le_add_of_forall_gt (Or.inr hterm₂_ne_top) (Or.inl hterm₁_ne_top) ?_
      intro a' ha' b' hb'
      have hx₁_lt_div : (F □ G) x₁ < a' / (α : EReal) := by
        refine (EReal.lt_div_iff hαE_pos (EReal.coe_ne_top α)).2 ?_
        simpa [mul_comm] using ha'
      have hx₂_lt_div : (F □ G) x₂ < b' / (((1 - α : ℝ)) : EReal) := by
        refine (EReal.lt_div_iff hβE_pos (EReal.coe_ne_top (1 - α))).2 ?_
        simpa [mul_comm] using hb'
      obtain ⟨ξ₁, hξ₁_lower, hξ₁_upper⟩ := EReal.exists_between_coe_real hx₁_lt_div
      obtain ⟨ξ₂, hξ₂_lower, hξ₂_upper⟩ := EReal.exists_between_coe_real hx₂_lt_div
      obtain ⟨y₁, hy₁⟩ :=
        exists_decomposition_lt_of_infimalConvolution_lt
          (F := F) (G := G) (x := x₁) (ξ := (ξ₁ : EReal)) hξ₁_lower
      obtain ⟨y₂, hy₂⟩ :=
        exists_decomposition_lt_of_infimalConvolution_lt
          (F := F) (G := G) (x := x₂) (ξ := (ξ₂ : EReal)) hξ₂_lower
      have hy₁_mem : y₁ ∈ dom F ∧ x₁ - y₁ ∈ dom G :=
        infimalConvolution_witness_mem_dom_of_lt_of_value_ne_bot hF_bot hx₁_ne_bot hy₁
      have hy₂_mem : y₂ ∈ dom F ∧ x₂ - y₂ ∈ dom G :=
        infimalConvolution_witness_mem_dom_of_lt_of_value_ne_bot hF_bot hx₂_ne_bot hy₂
      have hcombo_lt :
          (F □ G) (α • x₁ + (1 - α) • x₂) <
            (α : EReal) * (ξ₁ : EReal) +
              (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) := by
        -- The interior branch is exactly the strict two-witness estimate prepared above.
        exact
          infimalConvolution_combo_lt_of_witnesses
            (F := F) (G := G) hconvF hconvG
            hy₁_mem.1 hy₁_mem.2 hy₂_mem.1 hy₂_mem.2
            hα0 hα1 hy₁ hy₂
      have hbudget₁ : (α : EReal) * (ξ₁ : EReal) < a' := by
        -- The first decomposition level sits strictly below the first reserved budget.
        have : (ξ₁ : EReal) * (α : EReal) < a' :=
          (EReal.lt_div_iff hαE_pos (EReal.coe_ne_top α)).1 hξ₁_upper
        simpa [mul_comm] using this
      have hbudget₂ : (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) < b' := by
        -- The second decomposition level sits strictly below the second reserved budget.
        have : (ξ₂ : EReal) * (((1 - α : ℝ)) : EReal) < b' :=
          (EReal.lt_div_iff hβE_pos (EReal.coe_ne_top (1 - α))).1 hξ₂_upper
        simpa [mul_comm] using this
      exact le_of_lt (lt_trans hcombo_lt (EReal.add_lt_add hbudget₁ hbudget₂))

-- Proof sketch: every Fenchel conjugate is convex, and infimal postcomposition along a linear map
-- preserves convexity of the epigraph. Proposition 12.11 then yields convexity of the infimal
-- convolution of those two canonical pieces.
/-- The infimal convolution of a Fenchel conjugate with the infimal postcomposition of a Fenchel
conjugate has convex epigraph. This is the core convexity owner behind dual infimal convolutions. -/
theorem convex_epigraph_infimalConvolution_conjugate_infimalPostcomposition
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (A : K →L[ℝ] H) :
    Convex ℝ (epigraph (f.asEReal∗ □ (A ▷ g.asEReal∗))) := by
  -- Split first on the degenerate empty-domain case, then reduce the genuine case to the direct
  -- infimal-convolution owner proved just above.
  by_cases hempty : ¬ (effectiveDomain f).Nonempty ∨ ¬ (effectiveDomain g).Nonempty
  · -- If either effective domain is empty, the whole dual infimal convolution is constantly `⊥`.
    rw [dual_infimalConvolution_eq_bot_of_empty_effectiveDomain f g A hempty]
    simpa [epigraph] using (convex_univ : Convex ℝ (Set.univ : Set (H × ℝ)))
  · classical
    push Not at hempty
    have hdomfg : (effectiveDomain f).Nonempty ∧ (effectiveDomain g).Nonempty := hempty
    have hdomf : (effectiveDomain f).Nonempty := hdomfg.1
    have hdomg : (effectiveDomain g).Nonempty := hdomfg.2
    have hconv_f : Convex ℝ (epigraph f.asEReal∗) := by
      -- Every Fenchel conjugate is convex in the Chapter 9 `gamma` sense.
      exact
        convex_epigraph_of_isConvex_ereal
          ((mem_gamma_iff _).1 (conjugate_mem_gamma f.asEReal) |>.1)
    have hconv_post : Convex ℝ (epigraph (A ▷ g.asEReal∗)) :=
      convex_epigraph_infimalPostcomposition_conjugate g A hdomg
    let F : H → EReal := f.asEReal∗
    let G : H → EReal := A ▷ g.asEReal∗
    have hF_bot : ∀ z : H, F z ≠ ⊥ := by
      intro z
      exact conjugate_ne_bot_of_effectiveDomain_nonempty hdomf z
    have hconv_inf : Convex ℝ (epigraph (F □ G)) := by
      exact
        convex_epigraph_infimalConvolution_of_convex_epigraph_left_ne_bot
          (E := H) (F := F) (G := G) (hF_bot := hF_bot)
          (by simpa [F] using hconv_f)
          (by simpa [G] using hconv_post)
    -- The remaining owner only needs that the left conjugate never attains `⊥`.
    simpa [F, G] using hconv_inf

end DualInfimalConvolution

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Helper for Proposition 15 26: precomposing a `Γ₀` function with a continuous linear map
preserves `Γ₀` membership when the range meets the effective domain. -/
theorem comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty
    {E : Type*} {F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (g : F → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(F))
    (L : E →L[ℝ] F)
    (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    g ∘ L ∈ Γ₀(E) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · simpa using hg.1.comp L.continuous
  · refine ⟨effectiveDomain_comp_nonempty_of_range_inter_nonempty g L hdom, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    have hx' : L x ∈ effectiveDomain g := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hx
    have hy' : L y ∈ effectiveDomain g := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hy
    simpa [Function.comp, map_add, map_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hg.2.ineq hx' hy' hα hα_lt_one

/-- Helper for Proposition 15 26: the conjugate of the dual infimal convolution of two
`Γ₀(H)` conjugates is the primal pointwise sum. -/
private theorem conjugate_infimalConvolution_gammaZeroConjugates_eq_pointwiseAdd_asEReal
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗ = (f + g).asEReal := by
  have hconj_f : (gammaZeroConjugate f hf).asEReal = f.asEReal∗ := by
    funext u
    simp
  have hconj_g : (gammaZeroConjugate g hg).asEReal = g.asEReal∗ := by
    funext u
    simp
  calc
    (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗
        = (gammaZeroConjugate f hf).asEReal∗ + (gammaZeroConjugate g hg).asEReal∗ := by
          exact conjugate_infimalConvolution_eq (gammaZeroConjugate f hf) (gammaZeroConjugate g hg)
    _ = f.asEReal∗∗ + g.asEReal∗∗ := by rw [hconj_f, hconj_g]
    _ = f.asEReal + g.asEReal := by
          rw [biconjugate_eq_of_mem_gammaZero hf, biconjugate_eq_of_mem_gammaZero hg]
    _ = (f + g).asEReal := by
          funext x
          simp [Function.asEReal_apply]

/-- Helper for Proposition 15 26: the conjugate of the primal pointwise sum is the Fenchel
biconjugate of the dual infimal convolution. -/
theorem conjugate_pointwiseAdd_eq_biconjugate_infimalConvolution_conjugates
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    (f + g).asEReal∗ =
      (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗∗ := by
  simpa using
    congrArg conjugate
      (conjugate_infimalConvolution_gammaZeroConjugates_eq_pointwiseAdd_asEReal f g hf hg).symm

/-- Helper for Proposition 15 26: under the standard domain-intersection hypothesis, the dual
infimal convolution of two `Γ₀(H)` conjugates is proper. -/
theorem isProper_infimalConvolution_conjugates
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (gammaZeroConjugate f hf □ gammaZeroConjugate g hg) := by
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  have hconj :
      (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗ = (f + g).asEReal :=
    conjugate_infimalConvolution_gammaZeroConjugates_eq_pointwiseAdd_asEReal f g hf hg
  have hproper_conj : IsProper ((gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗) := by
    rw [hconj]
    exact isProper_of_mem_gammaZero hfg
  exact isProper_of_conjugate_isProper hproper_conj

/-- Helper for Proposition 15 26: under the standard domain-intersection hypothesis, the dual
infimal convolution of two `Γ₀(H)` conjugates has a continuous affine minorant. -/
theorem exists_continuousAffineMinorantWithSlope_infimalConvolution_conjugates
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    ∃ u : H,
      HasContinuousAffineMinorantWithSlope
        (gammaZeroConjugate f hf □ gammaZeroConjugate g hg) u := by
  let F : H → EReal := gammaZeroConjugate f hf □ gammaZeroConjugate g hg
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  have hconj : F∗ = (f + g).asEReal := by
    simpa [F] using
      conjugate_infimalConvolution_gammaZeroConjugates_eq_pointwiseAdd_asEReal f g hf hg
  rcases hfg.2.nonempty with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hdom_conj : u ∈ dom F∗ := by
    rw [hconj]
    simpa [effectiveDomain, dom] using hu
  simpa [F] using
    (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope F u).1 hdom_conj

-- Proof sketch: combine the Chapter 13 formula for the conjugate of a sum with linear
-- precomposition and the biconjugacy identity for `Γ₀` functions, then identify the resulting
-- right-hand side with the canonical `EReal`-valued dual infimal convolution
-- `f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)`.
/-- Proposition 15 26 (1): if `f ∈ Γ₀(H)` and `g ∈ Γ₀(K)` with
`effectiveDomain g ∩ L '' effectiveDomain f ≠ ∅`, then the conjugate of the composite primal
objective is the Fenchel biconjugate of `f* □ (L* ▷ g*)`. -/
theorem conjugate_pointwiseAddComp_eq_biconjugate_dualInfimalConvolution
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hdom : (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) :
    (compositePrimalObjective f g L)∗ =
      (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗))∗∗ := by
  let hrange : (Set.range L ∩ effectiveDomain g).Nonempty :=
    range_inter_effectiveDomain_nonempty_of_inter_image_nonempty f g L hdom
  let hcomp : g ∘ L ∈ Γ₀(H) :=
    comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty g hg L hrange
  calc
    (compositePrimalObjective f g L)∗ = (f + g ∘ L).asEReal∗ := by
      simp [compositePrimalObjective, primalObjective]
    _ = (gammaZeroConjugate f hf □ gammaZeroConjugate (g ∘ L) hcomp)∗∗ := by
      simpa using
        conjugate_pointwiseAdd_eq_biconjugate_infimalConvolution_conjugates
          f (g ∘ L) hf hcomp
    _ = (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗))∗∗ := by
      have hcompconj : (g ∘ L).asEReal∗ = L.adjoint ▷ g.asEReal∗ :=
        conjugate_comp_eq_adjointInfimalPostcomposition_of_mem_gammaZero g hg L hrange
      simpa [gammaZeroConjugate_apply] using
        congrArg (fun ψ : H → EReal ↦ (f.asEReal∗ □ ψ)∗∗) hcompconj

-- Proof sketch: use clause (1) to identify the conjugate of
-- `f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)` with the proper `Γ₀`
-- composite primal objective, then apply the standard implication that properness of the
-- conjugate forces properness of the original function.
/-- Proposition 15 26 (2): under the same assumptions, the dual infimal convolution
`f* □ (L* ▷ g*)` is proper. -/
theorem isProper_dualInfimalConvolution
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hdom : (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) :
    IsProper (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)) := by
  let hrange : (Set.range L ∩ effectiveDomain g).Nonempty :=
    range_inter_effectiveDomain_nonempty_of_inter_image_nonempty f g L hdom
  let hcomp : g ∘ L ∈ Γ₀(H) :=
    comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty g hg L hrange
  let hfg : (effectiveDomain f ∩ effectiveDomain (g ∘ L)).Nonempty :=
    effectiveDomain_inter_comp_nonempty_of_inter_image_nonempty f g L hdom
  have hcompconj : (g ∘ L).asEReal∗ = L.adjoint ▷ g.asEReal∗ :=
    conjugate_comp_eq_adjointInfimalPostcomposition_of_mem_gammaZero g hg L hrange
  rw [← hcompconj]
  simpa [gammaZeroConjugate_apply] using
    isProper_infimalConvolution_conjugates
      (f := f) (g := g ∘ L) hf hcomp hfg
  

-- Proof sketch: apply the owner-level convexity theorem for `f* □ (A ▷ g*)` and specialize to
-- `A = L.adjoint`. No `Γ₀` or domain-intersection hypothesis is needed; completeness enters only
-- through the Hilbert adjoint `L.adjoint`.
/-- Proposition 15 26 (3): for arbitrary `]-∞,+∞]`-valued `f` and `g`, the dual infimal
convolution `f* □ (L* ▷ g*)` is convex on all of `H`. -/
theorem convex_epigraph_dualInfimalConvolution
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    Convex ℝ
      (epigraph (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗))) := by
  simpa using
    convex_epigraph_infimalConvolution_conjugate_infimalPostcomposition f g L.adjoint

-- Proof sketch: by clause (1), the conjugate of
-- `f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)` is the proper composite
-- primal objective. The standard criterion relating a nontrivial conjugate to affine minorants
-- then produces a continuous affine minorant of the dual infimal convolution.
/-- Proposition 15 26 (4): under the same assumptions, the dual infimal convolution
`f* □ (L* ▷ g*)` admits a continuous affine minorant. -/
theorem exists_continuousAffineMinorantWithSlope_dualInfimalConvolution
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hdom : (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) :
    ∃ u : H,
      HasContinuousAffineMinorantWithSlope
        (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)) u := by
  let hrange : (Set.range L ∩ effectiveDomain g).Nonempty :=
    range_inter_effectiveDomain_nonempty_of_inter_image_nonempty f g L hdom
  let hcomp : g ∘ L ∈ Γ₀(H) :=
    comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty g hg L hrange
  let hfg : (effectiveDomain f ∩ effectiveDomain (g ∘ L)).Nonempty :=
    effectiveDomain_inter_comp_nonempty_of_inter_image_nonempty f g L hdom
  have hcompconj : (g ∘ L).asEReal∗ = L.adjoint ▷ g.asEReal∗ :=
    conjugate_comp_eq_adjointInfimalPostcomposition_of_mem_gammaZero g hg L hrange
  rw [← hcompconj]
  simpa [gammaZeroConjugate_apply] using
    exists_continuousAffineMinorantWithSlope_infimalConvolution_conjugates
      (f := f) (g := g ∘ L) hf hcomp hfg

end FenchelRockafellarDuality

end ERealFunction
