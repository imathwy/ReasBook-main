import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

attribute [local instance] Classical.propDecidable

open scoped Rockafellar

section PointIndicatorNotation

/-- Point-indicator notation surface specialized from the set-indicator owner. -/
scoped[Rockafellar] notation:70 "δp" "(" x " | " a ")" =>
  δ(x | ({a} : Set _))

end PointIndicatorNotation

section

variable {E : Type u} {𝕜 : Type v}
variable [AddGroup E]
variable [ConditionallyCompleteLattice 𝕜] [AddZeroClass 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.1.1 identifies the infimal convolution of `f` with the singleton
  indicator at `a` as the translate `x ↦ f (x - a)`.
- `core/canonical`: the owner abstractions are the chapter binary infimal convolution `□` from
  `Text_5_4_0`, specifically its additive-group bridge `infimal_convolution_apply_neg_add`, and
  the chapter indicator `δ(· | C)` from `Defintion_4_8_1`.
- `bridge/view`: the textbook point-indicator is exposed as notation `δp(· | a)`, a thin view of
  the singleton-set indicator owner `δ(· | ({a} : Set E))`.
- Primitive data vs derived API: the primitive data are `f` and `a`; the point `x` appears only
  when evaluating the owner-level identity at a point.
- Ambient minimization: the statement only uses additive-group structure on the domain and the
  additive conditional-completeness required by `□`. Because the project codomain is
  `WithBotTop 𝕜`, the textbook extended-real condition that `f` never takes `-∞` becomes the
  explicit guard `∀ y, f y ≠ ⊥`, which is used through the canonical additive rule
  `WithBotTop.add_top_of_ne_bot`.
-/

-- Proof sketch: expand `(f □ δp(· | a)) x` with
-- `infimal_convolution_apply_neg_add`. The singleton indicator is `0` exactly when `-y + x = a`,
-- i.e. `y = x - a`, and is `⊤` otherwise.
-- The non-`⊥` guard on `f` turns every off-singleton summand into `⊤`, so the infimum reduces to
-- the unique admissible value `f (x - a)`.
/-- Text 5.4.1.1: infimal convolution with the singleton indicator at `a` translates `f` by `a`;
in the chapter codomain `WithBotTop 𝕜`, this requires the source-faithful exclusion of `⊥`
values from `f`. The canonical owner-level surface is a function equality. -/
theorem infimal_convolution_indicator_singleton_eq_sub
    (f : E → WithBotTop 𝕜) (a : E) (hf_ne_bot : ∀ y : E, f y ≠ ⊥) :
    (f □ (δp(· | a))) = fun x ↦ f (x - a) := by
  classical
  funext x
  rw [infimal_convolution_apply_neg_add]
  calc
    (⨅ y : E, f y + δp(-y + x | a)) =
        ⨅ y : E, if -y + x = a then f y else ⊤ := by
          refine iInf_congr fun y ↦ ?_
          by_cases hy : -y + x = a
          · simp [hy]
          · have hy' : -y + x ∉ ({a} : Set E) := by
                simpa [Set.mem_singleton_iff] using hy
            simp [hy, hy', WithBotTop.add_top_of_ne_bot (hf_ne_bot y)]
    _ = ⨅ y : E, ⨅ (_ : -y + x = a), f y := by
          refine iInf_congr fun y ↦ ?_
          by_cases hy : -y + x = a
          · simp [hy]
          · simp [hy]
    _ = ⨅ y : {y : E // -y + x = a}, f (y : E) := by
          rw [iInf_subtype']
    _ = f (x - a) := by
          let y0 : {y : E // -y + x = a} := ⟨x - a, by
            simp [sub_eq_add_neg, add_assoc]⟩
          have hsub : Subsingleton {y : E // -y + x = a} := by
            constructor
            intro y₁ y₂
            apply Subtype.ext
            have hy₁ : (y₁ : E) = x - a := by
              rw [eq_sub_iff_add_eq]
              simpa [add_assoc] using congrArg (fun t ↦ (y₁ : E) + t) y₁.property.symm
            have hy₂ : (y₂ : E) = x - a := by
              rw [eq_sub_iff_add_eq]
              simpa [add_assoc] using congrArg (fun t ↦ (y₂ : E) + t) y₂.property.symm
            exact hy₁.trans hy₂.symm
          letI : Unique {y : E // -y + x = a} := ⟨⟨y0⟩, fun y ↦ hsub.elim y y0⟩
          have hdefault : ((default : {y : E // -y + x = a}) : E) = x - a := by
            exact congrArg Subtype.val (hsub.elim default y0)
          simpa using congrArg f hdefault

end
