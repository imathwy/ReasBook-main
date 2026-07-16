import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

attribute [local instance] Classical.propDecidable

open scoped Rockafellar

section

variable {E : Type u} {𝕜 : Type v}
variable [AddGroup E]
variable [ConditionallyCompleteLattice 𝕜] [AddZeroClass 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.1.2 rewrites the binary infimal convolution `(f □ g) x` by
  reflecting `f` to `y ↦ f (-y)` and inserting the singleton indicator at `x`.
- `core/canonical`: the owner abstractions are the chapter binary infimal convolution
  `infimal_convolution` / `□` from `Text_5_4_0` and the indicator owner `indicator` from
  `Defintion_4_8_1`.
- `bridge/view`: the singleton indicator `δ[𝕜](· | ({x} : Set E))` isolates the affine constraint
  hidden in the textbook's iterated-infimum formula, and the reflection is kept directly as the
  explicit function `fun y ↦ f (-y)` rather than as a second owner wrapper.
- Primitive data vs derived API: the primitive data are the functions `f`, `g`, and the point
  `x`; the reflected inner convolution is the source-facing bridge used to restate `(f □ g) x`.
- Ambient minimization: the statement uses only additive-group structure on the domain and the
  ordered additive structure already used by `infimal_convolution`. In the project's
  `WithBotTop 𝕜` codomain, if `f` attains `⊥` then both sides of the displayed identity collapse
  to `⊥`, so no extra owner-level guard is needed. The outer and inner rewrites both use the
  noncommutative owner bridge `infimal_convolution_apply_neg_add`, so no domain or codomain
  commutativity assumption remains.
- Reuse check: the singleton-indicator collapse is already owned by
  `infimal_convolution_indicator_singleton_eq_sub` from `Text_5_4_1_1`, so the reflected-inner
  step below should reuse that theorem rather than duplicating its subtype argument.
-/

-- Proof sketch: first split on whether `f` attains `⊥`. If it does, then both outer infima are
-- already `⊥` by evaluating at that witness through `infimal_convolution_apply_neg_add`.
-- Otherwise expand the outer and inner convolutions by the same owner theorem. For the inner
-- term, the singleton indicator forces the unique decomposition `-y + z = x`, i.e.
-- `y = z + -x`, so the reflected summand becomes `f (x + -z)`.
/-- Text 5.4.1.2: if `h y = f (-y)`, then the binary infimal convolution `(f □ g) x` can be
rewritten as the infimum over `z` of `(h □ δ[𝕜](· | ({x} : Set E))) z + g z`. In the project's
`WithBotTop 𝕜` codomain this remains valid without extra hypotheses: if `f` takes the value `⊥`,
then both sides collapse to `⊥`. -/
theorem infimal_convolution_eq_iInf_add_reflection_infimal_convolution_singleton_indicator
    (f g : E → WithTopBot 𝕜) (hf_ne_bot : ∀ y, f y ≠ ⊥) (x : E) :
    (f □ g) x =
      ⨅ z : E, (((fun y ↦ f (-y)) □ (δ[𝕜](· | ({x} : Set E)))) z) + g z := by
  classical
  have hinner : ∀ z : E,
      (((fun y ↦ f (-y)) □ (δ[𝕜](· | ({x} : Set E)))) z) = f (x + -z) := by
    intro z
    simpa [sub_eq_add_neg, neg_add_rev] using
      congrArg (fun h : E → WithTopBot 𝕜 ↦ h z)
        (infimal_convolution_indicator_singleton_eq_sub
          (f := fun y ↦ f (-y)) (a := x) (hf_ne_bot := fun y ↦ hf_ne_bot (-y)))
  calc
    (f □ g) x = ⨅ y : E, f y + g (-y + x) := infimal_convolution_apply_neg_add f g x
    _ = ⨅ z : E, f (x + -z) + g z := by
          let e : E ≃ E :=
            { toFun := fun y ↦ -y + x
              invFun := fun z ↦ x + -z
              left_inv := fun y ↦ by simp [neg_add_rev]
              right_inv := fun z ↦ by simp [neg_add_rev] }
          exact Equiv.iInf_congr e fun y ↦ by simp [e, neg_add_rev]
    _ = ⨅ z : E, (((fun y ↦ f (-y)) □ (δ[𝕜](· | ({x} : Set E)))) z) + g z := by
          refine iInf_congr fun z ↦ ?_
          rw [hinner z]

end
