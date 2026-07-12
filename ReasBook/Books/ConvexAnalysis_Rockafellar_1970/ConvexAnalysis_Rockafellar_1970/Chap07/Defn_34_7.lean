import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_18
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3

section

universe u v

open scoped Rockafellar

namespace SaddleFunction

section

variable {𝕜 : Type*} [Ring 𝕜]
variable {U : Type u} {V : Type v}
variable {EU EV : Type*}
variable {α : Type*} [LT α]
variable [TopologicalSpace U] [AddCommGroup EU] [Module 𝕜 EU] [AddTorsor EU U]
variable [TopologicalSpace V] [AddCommGroup EV] [Module 𝕜 EV] [AddTorsor EV V]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 34.7 names the kernel of a saddle-function `K` as the finite
  bifunction obtained by restricting `K` to the relative interior of its product domain `dom K`.
- `core/canonical`: the chapter already owns the coordinate effective-domain operators `dom₁` and
  `dom₂` together with the product owner `dom K`, while the project
  already owns the scalar-generic product relative-interior theorem `ri_prod_eq`.
- `bridge/view`: the ambient `WithTopBot α`-valued restriction is only the coercion view of that
  finite kernel back into the chapter saddle-function codomain.

Domain-style sampling used here:
- `SaddleFunction.dom₁`, `SaddleFunction.dom₂`, and the Chapter 34 notation `dom K` from
  `Chap07.Defn_34_3` on the codomain layer `WithTopBot α`;
- `ri_prod_eq` from `Chap02.Text_6_18`, already stated for arbitrary scalar rings
  and topological modules;
- `Bifunction.toWithTopBot` from `Chap01.EOrder.Basic`, which is the canonical codomain bridge from
  a finite bifunction back to the ambient extended-value layer;
- `WithTopBot.mem_range_coe_iff` / `WithBot.unbot` / `WithTop.untop`, which provide the canonical
  finite-value extraction on the relative-interior domain.

Primitive data vs derived API:
- primitive data already present upstream: the saddle-function `K` and its coordinate effective
  domains `dom₁ K`, `dom₂ K`, and their product domain `dom K`;
- derived API introduced here: the relative-interior description of that existing owner, the
  source-facing finite kernel on the intrinsic coordinate-domain owners
  `ri[𝕜](dom₁ K)` and `ri[𝕜](dom₂ K)`, and the coercion bridge back to `WithTopBot α`.

Layer target: `source-facing`. The source genuinely introduces the kernel, but no new wrapper is
 needed: the public owner is the finite restriction on the intrinsic coordinate-domain owners
 already owned by the chapter, not a parallel `WithTopBot`-valued wrapper.
- Ambient-layer refinement: the full item lives on topological affine spaces (`AddTorsor`) rather
  than additive groups for points, since `ri[𝕜](·)` and `ri_prod_eq` only require the intrinsic
  affine structure.
-/

variable (𝕜) in
@[simp] theorem intrinsicInterior_dom (K : U → V → WithTopBot α) :
    ri[𝕜](dom K) = ri[𝕜](dom₁ K) ×ˢ ri[𝕜](dom₂ K) := by
  change ri[𝕜](dom₁ K ×ˢ dom₂ K) = ri[𝕜](dom₁ K) ×ˢ ri[𝕜](dom₂ K)
  exact ri_prod_eq (𝕜 := 𝕜) (s := dom₁ K) (t := dom₂ K)

variable (𝕜) in
@[simp] theorem mem_intrinsicInterior_dom {K : U → V → WithTopBot α} {p : U × V} :
    p ∈ ri[𝕜](dom K) ↔ p.1 ∈ ri[𝕜](dom₁ K) ∧ p.2 ∈ ri[𝕜](dom₂ K) := by
  rw [intrinsicInterior_dom, Set.mem_prod]

variable (𝕜) in
/-- Defn 34.7: the kernel of a saddle-function `K` is the restriction of `K` to the relative
interior of its product domain `dom K`, equivalently (by `intrinsicInterior_dom`) as a finite
bifunction on the coordinate relative interiors `ri[𝕜](dom₁ K)` and `ri[𝕜](dom₂ K)`. On this
intrinsic domain all values are finite, so the source-facing owner lives in `α`; the ambient
`WithTopBot α` restriction is only the coercion bridge back to the saddle-function codomain. -/
def kernel (K : U → V → WithTopBot α) :
    ri[𝕜](dom₁ K) → ri[𝕜](dom₂ K) → α :=
  fun u v ↦
    let hri : (u.1, v.1) ∈ ri[𝕜](dom K) := by
      rw [intrinsicInterior_dom]
      exact ⟨u.2, v.2⟩
    let hdom : (u.1, v.1) ∈ dom K := intrinsicInterior_subset hri
    let htop : K u.1 v.1 ≠ ⊤ :=
      WithTop.lt_top_iff_ne_top.mp ((mem_dom.mp hdom).2 u.1)
    let y : WithBot α := (K u.1 v.1).untop htop
    let hbot : y ≠ ⊥ := by
      have hbot' : (⊥ : WithBot α) < y :=
        (WithTop.lt_untop_iff htop).2 ((mem_dom.mp hdom).1 v.1)
      exact WithBot.bot_lt_iff_ne_bot.mp hbot'
    y.unbot hbot

variable (𝕜) in
@[simp] theorem kernel_apply (K : U → V → WithTopBot α)
    (u : ri[𝕜](dom₁ K)) (v : ri[𝕜](dom₂ K)) :
    Bifunction.toWithTopBot (kernel 𝕜 K) u v = K u.1 v.1 := by
  let hri : (u.1, v.1) ∈ ri[𝕜](dom K) := by
    rw [intrinsicInterior_dom]
    exact ⟨u.2, v.2⟩
  let hdom : (u.1, v.1) ∈ dom K := intrinsicInterior_subset hri
  let htop : K u.1 v.1 ≠ ⊤ :=
    WithTop.lt_top_iff_ne_top.mp ((mem_dom.mp hdom).2 u.1)
  let y : WithBot α := (K u.1 v.1).untop htop
  let hbot : y ≠ ⊥ := by
    have hbot' : (⊥ : WithBot α) < y :=
      (WithTop.lt_untop_iff htop).2 ((mem_dom.mp hdom).1 v.1)
    exact WithBot.bot_lt_iff_ne_bot.mp hbot'
  change (((kernel 𝕜 K u v : α) : WithBot α) : WithTopBot α) = K u.1 v.1
  change (((y.unbot hbot : α) : WithBot α) : WithTopBot α) = K u.1 v.1
  rw [WithBot.coe_unbot]
  simp [y]

end

end SaddleFunction

end
