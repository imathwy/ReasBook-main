import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_1_WithBotTopBridge
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.2 identifies the chapter concave-closure fixed-point equation
  `concaveClosure g = g` with upper semicontinuity of `g` and closedness of every real upper
  level set of `g`, and it asserts convexity of those upper level sets under concavity.
- `core/canonical`: the Chapter 6 owner `concaveClosure`, mathlib's `UpperSemicontinuous`, the
  Chapter 6 owner `Function.IsConcave`, and the Chapter 1 owner `Function.IsConvex`.
- `bridge/view`: negation turns upper level sets of `g` into sublevel sets of `-g`; the
  convex-side fixed-point equation `cl(-g) = -g` is used only as a proof bridge, matching the
  companion source-facing bridge isolated in Theorem 6.30.1.

Primary mathematical domain:
- upper semicontinuity and upper level sets of `WithBotTop α`-valued concave functions, with the
  textbook `EReal` / `ℝ` surface recovered by specialization.

Domain-style sampling used here:
- `concaveClosure`;
- `lowerSemicontinuousHull` / the notation `cl(·)`;
- `upperSemicontinuous_iff_isClosed_preimage`;
- `lowerSemicontinuous_iff_isClosed_sublevel`;
- `Function.IsConcave` and `Function.IsConcave.convex_neg`;
- `Function.IsConvex.convex_le`.

Primitive data vs. derived API:
- primitive owners for part (1): `concaveClosure g` and `UpperSemicontinuous g` on the canonical
  codomain layer `WithBotTop α`;
- source hypothesis used only for part (2): `g.IsConcave 𝕜`;
- derived API: the closed-scalar-upper-level-set characterization, the convex-side bridge
  `LowerSemicontinuous (-g)`, and the convexity of those upper level sets; the convexity of `-g`
  is used only internally via `hg.convex_neg`.

Layer target:
- part (1): `source-facing` on the textbook `EReal` specialization, obtained from a
  `bridge/view` theorem at the generic `WithBotTop α` owner layer;
- part (2): `bridge/view`, via the chapter owner `Function.IsConcave`.
-/

section

variable {α : Type*} [LinearOrder α]
variable {E : Type u} [TopologicalSpace E]

/-- Companion owner form: a `WithBotTop α`-valued function is upper semicontinuous exactly when
all of its scalar upper level sets are closed. -/
theorem upperSemicontinuous_iff_isClosed_upperLevelSets
    [NoMaxOrder α] [Nonempty α] (g : E → WithBotTop α) :
    UpperSemicontinuous g ↔ ∀ a : α, IsClosed (g ⁻¹' Set.Ici (a : WithBotTop α)) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  constructor
  · intro hg a
    simpa using hg (a : WithBotTop α)
  · intro h y
    change WithBot (WithTop α) at y
    induction y using WithBot.recBotCoe with
    | bot => simp
    | coe y =>
        induction y using WithTop.recTopCoe with
        | top =>
            have hpreimage_eq :
                g ⁻¹' Set.Ici (⊤ : WithBotTop α) = ⋂ a : α, g ⁻¹' Set.Ici (a : WithBotTop α) := by
              ext x
              simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_Ici]
              constructor
              · intro hx a
                exact le_trans (by simp) hx
              · intro hx
                by_cases htop : g x = ⊤
                · simp [htop]
                · cases hgx : g x using WithBotTop.rec with
                  | bot =>
                      exfalso
                      let a : α := Classical.choice ‹Nonempty α›
                      have hxa : (a : WithBotTop α) ≤ g x := hx a
                      simp [hgx] at hxa
                  | coe b =>
                      exfalso
                      rcases exists_gt b with ⟨a, hba⟩
                      have hxa : (a : WithBotTop α) ≤ g x := hx a
                      rw [hgx] at hxa
                      exact (not_le_of_gt hba) (WithBotTop.coe_le_coe.mp hxa)
                  | top => exact (htop hgx).elim
            rw [show ((⊤ : WithTop α) : WithBot (WithTop α)) = (⊤ : WithBotTop α) by rfl]
            rw [hpreimage_eq]
            exact isClosed_iInter h
        | coe a =>
            simpa using h a

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddCommGroup 𝕜]
variable {E : Type u} [TopologicalSpace E]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
variable [DenselyOrdered 𝕜] [NoMaxOrder 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜]
variable [NoBotOrder 𝕜] [IsOrderedAddMonoid 𝕜]

/-- Companion bridge: on the canonical `WithBotTop 𝕜` codomain layer, the Chapter 6
concave-closure fixed-point equation is equivalent to upper semicontinuity. -/
theorem concaveClosure_eq_self_iff_upperSemicontinuous
    (g : E → WithBotTop 𝕜) :
    concaveClosure g = g ↔ UpperSemicontinuous g := by
  rw [concaveClosure_eq_self_iff_lowerSemicontinuous_neg]
  rw [lowerSemicontinuous_iff_isClosed_sublevel_withBotTop,
    upperSemicontinuous_iff_isClosed_upperLevelSets]
  constructor
  · intro h a
    have hs :
        {x : E | (-g) x ≤ (((-a : 𝕜) : WithBotTop 𝕜))} =
          g ⁻¹' Set.Ici (a : WithBotTop 𝕜) := by
      ext x
      simpa [Set.mem_preimage] using
        (show -g x ≤ (((-a : 𝕜) : WithBotTop 𝕜)) ↔ (a : WithBotTop 𝕜) ≤ g x from
          WithBotTop.neg_le)
    simpa [hs] using h (-a)
  · intro h a
    have hs :
        {x : E | (-g) x ≤ (a : WithBotTop 𝕜)} =
          g ⁻¹' Set.Ici (-((a : 𝕜) : WithBotTop 𝕜)) := by
      ext x
      simpa [Set.mem_preimage] using
        (show -g x ≤ (a : WithBotTop 𝕜) ↔ (-((a : 𝕜) : WithBotTop 𝕜)) ≤ g x from
          WithBotTop.neg_le)
    simpa using hs.symm ▸ h (-a)

/-- Theorem 6.30.2 (1): the chapter concave-closure fixed-point equation,
upper semicontinuity, and closedness of all scalar upper level sets are equivalent.
Specializing `𝕜 = ℝ` recovers the textbook `EReal` statement. -/
theorem concaveClosure_eq_self_tfae_upperSemicontinuous_isClosed_upperLevelSets
    {g : E → WithBotTop 𝕜} :
    List.TFAE
      [concaveClosure g = g,
        UpperSemicontinuous g,
        ∀ a : 𝕜, IsClosed (g ⁻¹' Set.Ici (a : WithBotTop 𝕜))] := by
  tfae_have 1 ↔ 2 := by
    exact concaveClosure_eq_self_iff_upperSemicontinuous g
  tfae_have 2 ↔ 3 := by
    exact upperSemicontinuous_iff_isClosed_upperLevelSets g
  tfae_finish

end

section

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

namespace Function.IsConcave

/-- Owner form of Theorem 6.30.2 (2): every scalar upper level set of a concave
`WithBotTop α`-valued function is convex. The textbook `EReal` / `ℝ` statement is the
specialization `α = ℝ`. -/
theorem convex_upperLevelSet
    {g : E → WithBotTop α} (hg : g.IsConcave 𝕜) (a : α) :
    Convex 𝕜 (g ⁻¹' Set.Ici (a : WithBotTop α)) := by
  have hset :
      g ⁻¹' Set.Ici (a : WithBotTop α) =
        {x : E | (-g) x ≤ (((-a : α) : WithBotTop α))} := by
    ext x
    simpa [Set.mem_preimage] using
      (show (a : WithBotTop α) ≤ g x ↔ -g x ≤ (((-a : α) : WithBotTop α)) from
        WithBotTop.neg_le.symm)
  rw [hset]
  simpa using hg.convex_neg.convex_le (((-a : α) : WithBotTop α))

end Function.IsConcave

end
