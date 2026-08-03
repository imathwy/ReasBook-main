import Mathlib
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap13.Definition_13_34
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Theorem_13_37

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Corollary 13 38: an `]-∞,+∞]`-valued function with nonempty effective domain has
Fenchel conjugate nowhere equal to `-∞`. -/
theorem conjugate_ne_bot_of_effectiveDomain_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) (u : H) :
    f.asEReal∗ u ≠ ⊥ := by
  -- The raw conjugate of a proper extended-real function never takes the value `-∞`.
  have hproper : IsProper f.asEReal := by
    refine ⟨fun x ↦ ne_of_gt (f x).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  exact conjugate_ne_bot_of_isProper hproper u

/-- Helper for Corollary 13 38: every `Γ₀(H)` function has Fenchel conjugate with nonempty
domain. -/
theorem dom_conjugate_nonempty_of_mem_gammaZero
    [CompleteSpace H] {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    (dom f.asEReal∗).Nonempty := by
  have hproper_f : IsProper f.asEReal := isProper_of_mem_gammaZero hf
  have hgamma_f : f.asEReal ∈ gamma H := asEReal_mem_gamma_of_mem_gammaZero hf
  exact (conjugate_is_proper_of_mem_gamma hproper_f hgamma_f).2

/-- The Fenchel conjugate of an `]-∞,+∞]`-valued function with nonempty effective domain, packaged
again as `]-∞,+∞]`-valued. -/
noncomputable abbrev properConjugateIoi (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) :
    H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨f.asEReal∗ u,
      bot_lt_iff_ne_bot.mpr (conjugate_ne_bot_of_effectiveDomain_nonempty hdom u)⟩

/-- Coercing `properConjugateIoi f hdom` back to `EReal` recovers the canonical Fenchel
conjugate `f.asEReal∗`. -/
@[simp] theorem properConjugateIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) (u : H) :
    (properConjugateIoi f hdom u : EReal) = f.asEReal∗ u :=
  rfl

/-- The `Γ₀(H)` specialization of `properConjugateIoi`. -/
noncomputable abbrev gammaZeroConjugate (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  properConjugateIoi f hf.2.nonempty

/- Lean cannot infer the `Γ₀(H)` witness from `f` alone, so the packaged source-facing conjugate
keeps that witness explicit and writes the canonical `Γ₀(H)` Fenchel conjugate as `f∗[hf]`. -/
scoped notation:max f "∗[" hf "]" => gammaZeroConjugate f hf

/-- Coercing `gammaZeroConjugate f hf` back to `EReal` recovers the canonical Fenchel conjugate
`f.asEReal∗`. -/
@[simp] theorem gammaZeroConjugate_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    (f∗[hf] u : EReal) = f.asEReal∗ u :=
  rfl

/-- The Fenchel conjugate of a `Γ₀(H)` function again belongs to `Γ₀(H)`. -/
theorem gammaZeroConjugate_mem_gammaZero
    [CompleteSpace H] {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f∗[hf] ∈ Γ₀(H) := by
  have hproper_conj : IsProper f.asEReal∗ := by
    refine ⟨conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty,
      dom_conjugate_nonempty_of_mem_gammaZero hf⟩
  have hgamma_conj : f.asEReal∗ ∈ gamma H := conjugate_mem_gamma f.asEReal
  have hrepr : f∗[hf] = properIoi (f.asEReal∗) hproper_conj := by
    -- Both packaged owners have the same `EReal` value pointwise; only the proof fields differ.
    funext u
    apply Subtype.ext
    rfl
  rw [hrepr]
  exact properIoi_mem_gammaZero_of_mem_gamma hproper_conj hgamma_conj

end Conjugation

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 13 38: a `Γ₀(H)` function agrees with the Fenchel biconjugate of its
canonical `EReal`-valued coercion. -/
theorem biconjugate_eq_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f.asEReal∗∗ = f.asEReal := by
  have hproper_f : IsProper f.asEReal := isProper_of_mem_gammaZero hf
  have hgamma_f : f.asEReal ∈ gamma H := asEReal_mem_gamma_of_mem_gammaZero hf
  -- Apply Fenchel--Moreau to the canonical `EReal`-valued representative of `f`.
  exact (mem_gamma_iff_eq_biconjugate_of_is_proper hproper_f).mp hgamma_f

/-- Corollary 13 38: if `f ∈ Γ₀(H)`, then its canonical `Γ₀(H)`-valued Fenchel conjugate again
belongs to `Γ₀(H)`, and the Fenchel biconjugate of the `EReal`-valued coercion of `f` is `f`
itself. -/
theorem conjugate_mem_gammaZero_and_biconjugate_eq
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f∗[hf] ∈ Γ₀(H) ∧ f.asEReal∗∗ = f.asEReal := by
  exact ⟨gammaZeroConjugate_mem_gammaZero hf, biconjugate_eq_of_mem_gammaZero hf⟩

end FenchelMoreau

section Transpose

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- The canonical `Γ₀(H × H)` representative of the transpose-conjugate `F^{*T}`. -/
noncomputable abbrev gammaZeroConjugateTranspose
    (F : H × H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × H)) :
    H × H → Set.Ioi (⊥ : EReal) :=
  (F∗[hF])ᵀ

/- Lean cannot infer the `Γ₀(H × H)` witness from `F` alone, so the packaged source-facing
transpose-conjugate keeps that witness explicit and writes `F^{*T}` as `F∗ᵀ[hF]`. -/
scoped notation:max F "∗ᵀ[" hF "]" => gammaZeroConjugateTranspose F hF

@[simp] theorem gammaZeroConjugateTranspose_apply
    (F : H × H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × H)) (u x : H) :
    F∗ᵀ[hF] (u, x) = F∗[hF] (x, u) :=
  rfl

/-- The transpose-conjugate `F^{*T}` of a `Γ₀(H × H)` function again belongs to `Γ₀(H × H)`. -/
theorem gammaZeroConjugateTranspose_mem_gammaZero
    [CompleteSpace H] {F : H × H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H × H)) :
    F∗ᵀ[hF] ∈ Γ₀(H × H) := by
  simpa [gammaZeroConjugateTranspose] using
    mem_gammaZero_comp_continuousLinearEquiv
      (f := F∗[hF]) (gammaZeroConjugate_mem_gammaZero hF)
      (ContinuousLinearEquiv.prodComm ℝ H H)

end Transpose

section ProximityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 13 38: a source-facing owner for the proximity operator of a
`Γ₀(H)`-valued function. -/
noncomputable def gammaZero_proximity_operator
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) : H → H :=
  proximityOperator f (hasUniqueProxPoint_of_mem_gammaZero f hf)

/-- Helper for Corollary 13 38: a source-facing owner for the scaled proximity operator of a
`Γ₀(H)`-valued function. -/
noncomputable def scaled_gammaZero_proximity_operator
    (γ : PosReal) (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) : H → H :=
  scaledProximityOperator f hf γ

/- Source-facing notation for the proximity operator of the Fenchel conjugate `f*`,
represented by the canonical `Γ₀(H)`-valued owner `f∗[hf]`. -/
notation "Prox⋆[" f ", " hf "]" =>
  gammaZero_proximity_operator (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf)

/- Source-facing notation for the scaled proximity operator `Prox_{γ f*}`,
represented by the canonical `Γ₀(H)`-valued owner `f∗[hf]`. -/
notation "Prox⋆[" γ ", " f ", " hf "]" =>
  scaled_gammaZero_proximity_operator γ (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf)

end ProximityOperator

section TransposeProximityOperator

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/- Source-facing notation for the proximity operator of the transpose-conjugate `F^{*T}`,
represented by the canonical `Γ₀(H × H)`-valued owner `F∗ᵀ[hF]`. -/
notation "Prox⋆ᵀ[" F ", " hF "]" =>
  gammaZero_proximity_operator (F∗ᵀ[hF]) (gammaZeroConjugateTranspose_mem_gammaZero hF)

end TransposeProximityOperator

end ERealFunction
