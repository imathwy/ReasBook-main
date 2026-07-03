import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_23_5_1 (from Chap05) -/
noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function.IsClosedProperConvex

variable {f : E → EReal} {x xStar : E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.5.1 states that, for a closed proper convex function, the
  subdifferential of the Fenchel conjugate is the inverse set-valued mapping of the
  subdifferential of the original function.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.subdifferentialAt`, the Fenchel conjugate notation `f⋆`, and the bundled hypothesis
  `f.IsClosedProperConvex`.
- `bridge/view`: this corollary is a one-step specialization of Theorem 23.5 from the
  closure-normalized equivalence to the closed case, using the canonical
  closed/proper/convex owner instead of carrying a separate hypothesis `cl(f) x = f x`.

Domain-style sampling used here:
- `Function.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `Function.IsClosedProperConvex` from `Chap03/Text_12_3_6`;
- `lowerSemicontinuousHull_eq_self` on lower-semicontinuous functions;
- `Function.subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_
  conjugate_subdifferentialAt_of_closure_eq` from `Chap05/Theorem_23_5`.

Primitive data vs derived API:
- primitive inputs: the function `f`, the primal point `x`, the dual point `xStar`, and the owner
  hypothesis `hf : f.IsClosedProperConvex`;
- derived surface: the inverse-graph equivalence
  `x ∈ subdifferentialAt (f⋆) xStar ↔ xStar ∈ subdifferentialAt f x`.

Layer target: `source-facing`, stated directly on the canonical Chapter 23 owners
`Function.subdifferentialAt` and `Function.IsClosedProperConvex`, with no surrogate
inverse-relation package.
-/

-- Proof sketch: Theorem 23.5 already places the two membership clauses
-- `xStar ∈ subdifferentialAt f x` and `x ∈ subdifferentialAt (f⋆) xStar` in the same TFAE class
-- once the closure normalization `cl(f) x = f x` is available. For a closed proper convex
-- function, lower semicontinuity identifies `cl(f) = f`, so that normalization is automatic, and
-- the two clauses become equivalent.
/-- Corollary 23.5.1: if `f` is closed proper convex, then the subdifferential of the Fenchel
conjugate is the inverse of the subdifferential of `f` as a set-valued mapping; equivalently,
`x ∈ ∂f⋆(xStar)` if and only if `xStar ∈ ∂f(x)`. -/
theorem mem_subdifferentialAt_convexConjugate_iff
    (hf : f.IsClosedProperConvex) :
    x ∈ subdifferentialAt (f⋆) xStar ↔ xStar ∈ subdifferentialAt f x := by
  have hclx : cl(f) x = f x := by
    simpa using congrFun (lowerSemicontinuousHull_eq_self hf.closed) x
  exact
    (subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_conjugate_subdifferentialAt_of_closure_eq
      hf.convex hf.proper hclx).out 4 0

end Function.IsClosedProperConvex

end

/-! ### Corollary_23_5_2 (from Chap05) -/
noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.5.2 says that if a proper convex function is subdifferentiable at
  `x`, then `cl(f)` agrees with `f` at `x`, and the subdifferential at `x` is unchanged by
  passing from `f` to `cl(f)`.
- `core/canonical`: the relevant project owners are `Function.subdifferentialAt`,
  `Function.IsConvex`, `Function.IsProper`, and Rockafellar's closure notation `cl(·)`.
- `bridge/view`: the source phrase “subdifferentiable at `x`” is rendered directly by
  `(subdifferentialAt f x).Nonempty`, so no auxiliary predicate or wrapper is introduced.

Domain-style sampling used here:
- `Function.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- the closure-normalized TFAE theorem
  `Function.subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_`
  `conjugate_subdifferentialAt_of_closure_eq` from `Chap05/Theorem_23_5`;
- Rockafellar's closure notation `cl(·)` already used throughout the Chapter 23 development.

Primitive data vs derived API:
- primitive inputs: the convexity and properness hypotheses on `f`, the base point `x`, and the
  nonemptiness of `subdifferentialAt f x`;
- derived API: the pointwise closure normalization `cl(f) x = f x`, the pointwise membership
  equivalence for `subdifferentialAt (cl(f)) x`, and the resulting set equality.

Layer target: `source-facing`, stated directly on the canonical Euclidean subdifferential owner.
-/

variable {f : E → EReal} {x : E}

-- Proof sketch: choose `xStar ∈ subdifferentialAt f x`. Theorem 23.5 places that membership in
-- the same Fenchel-Young equivalence class as equality at `(x, xStar)`. Combining the resulting
-- equality with the general inequalities `f x ≥ cl(f) x = f⋆⋆ x` forces the value normalization
-- `cl(f) x = f x`. The closure-normalized form of Theorem 23.5 then identifies the original and
-- closure-side subgradient clauses for every `xStar`, yielding equality of the two
-- subdifferentials.
/-- Corollary 23.5.2: if `f` is a proper convex function and is subdifferentiable at `x`, then
`cl(f)` agrees with `f` at `x`, and the subdifferential at `x` is unchanged by passing from `f`
to `cl(f)`. -/
theorem lowerSemicontinuousHull_apply_eq_and_subdifferentialAt_eq_of_subdifferentialAt_nonempty
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hsub : (subdifferentialAt f x).Nonempty) :
    cl(f) x = f x ∧ subdifferentialAt (cl(f)) x = subdifferentialAt f x := sorry

-- Proof sketch: use the first clause of the corollary above, obtained from a witness
-- `xStar ∈ subdifferentialAt f x` and the Fenchel-Young equality criterion in Theorem 23.5.
/-- At any point where a proper convex function has a nonempty Chapter 23 subdifferential, its
lower-semicontinuous hull has the same value. -/
theorem lowerSemicontinuousHull_apply_eq_of_subdifferentialAt_nonempty
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hsub : (subdifferentialAt f x).Nonempty) :
    cl(f) x = f x :=
  (lowerSemicontinuousHull_apply_eq_and_subdifferentialAt_eq_of_subdifferentialAt_nonempty
    hf_convex hf_proper hsub).1

-- Proof sketch: the preceding set-equality clause already lives on the canonical owner
-- `subdifferentialAt`, so the owner-friendly pointwise form is obtained by rewriting membership
-- across that equality.
/-- At a point where `subdifferentialAt f x` is nonempty, passing to `cl(f)` preserves the Chapter
23 subgradient condition pointwise. -/
theorem mem_subdifferentialAt_lowerSemicontinuousHull_iff_of_subdifferentialAt_nonempty
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hsub : (subdifferentialAt f x).Nonempty)
    {xStar : E} :
    xStar ∈ subdifferentialAt (cl(f)) x ↔ xStar ∈ subdifferentialAt f x := by
  rw [(lowerSemicontinuousHull_apply_eq_and_subdifferentialAt_eq_of_subdifferentialAt_nonempty
    hf_convex hf_proper hsub).2]

-- Proof sketch: first obtain `cl(f) x = f x` from the preceding companion theorem. Then apply the
-- closure-normalized equivalence theorem
-- `subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_conjugate_subdifferentialAt_of_closure_eq`
-- from Theorem 23.5 to identify the original and closure-side subgradient clauses pointwise.
/-- Passing from a proper convex function to its lower-semicontinuous hull does not change the
Chapter 23 subdifferential at a point where the original subdifferential is nonempty. -/
theorem subdifferentialAt_lowerSemicontinuousHull_eq_of_subdifferentialAt_nonempty
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hsub : (subdifferentialAt f x).Nonempty) :
    subdifferentialAt (cl(f)) x = subdifferentialAt f x :=
  (lowerSemicontinuousHull_apply_eq_and_subdifferentialAt_eq_of_subdifferentialAt_nonempty
    hf_convex hf_proper hsub).2

end Function

end

/-! ### Corollary_23_5_3 (from Chap05) -/
noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

variable {C : Set E} {x xStar : E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.5.3 identifies subgradients of the support function of a nonempty
  closed convex set with the points of the set where the corresponding linear functional attains
  its maximum.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.subdifferentialAt` and the support-function owner
  `(δᵛ[WithBotTop ℝ](· | C) : E → WithBotTop ℝ)`.
- `bridge/view`: the proof reuses the existing chapter bridge chain
  `supportFunction = (indicatorFunction C)⋆`,
  `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff`,
  and `Function.mem_subdifferentialAt_indicatorFunction_iff`.

Domain-style sampling used here:
- `supportFunction` / `δᵛ(· | C)` from `Chap01/Defintion_4_8_2`;
- `indicatorFunction_isClosedProperConvex_of_nonempty` from `Chap03/Text_12_3_6`;
- `convexConjugate_indicatorFunction_eq_supportFunction` from `Chap03/Text_13_1_4`;
- `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff` and
  `Function.mem_subdifferentialAt_indicatorFunction_iff` from Chapter 23.

Primitive data vs derived API:
- primitive inputs: the set `C`, the primal point `x`, the dual point `xStar`, and the
  nonempty/closed/convex hypotheses on `C`;
- derived API: the equivalence between support-function subgradient membership and the primal
  maximizer condition on `C`.

Layer target: `source-facing`. The public theorem remains the textbook set-level statement on the
owner `(δᵛ[WithBotTop ℝ](· | C) : E → WithBotTop ℝ)`, while the proof is routed through the
canonical indicator owner instead of a second local Fenchel-Young unpacking.
-/

-- Proof sketch: the indicator of a nonempty closed convex set is a closed proper convex function,
-- so Corollary 23.5.1 applies to `δ(· | C)`. Rewrite its conjugate as `supportFunction C`, then
-- rewrite the remaining indicator-subgradient clause by the existing source-facing owner theorem
-- `Function.mem_subdifferentialAt_indicatorFunction_iff`. The resulting sign inequality is exactly
-- the pointwise `IsMaxOn` condition for `z ↦ ⟪z, xStar⟫` on `C`.
/-- Corollary 23.5.3: for a nonempty closed convex set `C`, a point `x` belongs to the
subdifferential of the support function `δᵛ[WithBotTop ℝ](· | C)` at `xStar` exactly when `x ∈ C`
and the linear functional `z ↦ ⟪z, xStar⟫` attains its maximum over `C` at `x`. In the source
notation, this is the subdifferential of `δᵛ(· | C)`. -/
theorem mem_subdifferentialAt_supportFunction_iff_mem_and_isMaxOn
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    x ∈ subdifferentialAt (δᵛ[WithBotTop ℝ](· | C)) xStar ↔
      x ∈ C ∧ IsMaxOn (fun z : E ↦ ⟪z, xStar⟫) C x := by
  have h_indicator : (δ(· | C) : E → EReal).IsClosedProperConvex :=
    indicatorFunction_isClosedProperConvex_of_nonempty hC_nonempty hC_closed hC_convex
  rw [← convexConjugate_indicatorFunction_eq_supportFunction C]
  rw [h_indicator.mem_subdifferentialAt_convexConjugate_iff]
  rw [mem_subdifferentialAt_indicatorFunction_iff]
  constructor
  · rintro ⟨hxC, hxStar⟩
    refine ⟨hxC, isMaxOn_iff.2 ?_⟩
    intro z hzC
    exact sub_nonpos.mp <| by
      simpa [real_inner_comm, inner_sub_right] using hxStar z hzC
  · rintro ⟨hxC, hmax⟩
    refine ⟨hxC, ?_⟩
    intro z hzC
    have hz : (⟪z, xStar⟫ : ℝ) ≤ ⟪x, xStar⟫ :=
      (isMaxOn_iff.mp hmax) z hzC
    simpa [real_inner_comm, inner_sub_right] using sub_nonpos.mpr hz

end Function

end

/-! ### Corollary_23_5_4 (from Chap05) -/
noncomputable section

open scoped PolarCone RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

variable {K : Set E} {x xStar : E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.5.4 compares the subdifferential of the indicator of a nonempty
  closed convex cone `K` with the subdifferential of the indicator of its polar cone `Kᵒ`, and
  identifies both with the complementary-slackness conditions `x ∈ K`, `xStar ∈ Kᵒ`,
  `⟪x, xStar⟫ = 0`.
- `core/canonical`: the relevant project owners are the Chapter 23 Euclidean subdifferential
  `Function.subdifferentialAt`, the Chapter 1 indicator notation `δ[ℝ](· | K)`, the Chapter 3
  polar-cone notation `Kᵒ`, and the cone hypothesis owner `Set.IsConvexCone ℝ K`.
- `bridge/view`: the normal-cone identification for indicator subdifferentials from
  `Example_23_0_7` and the polar/normal-cone relation at the origin from Chapter 14 guide the
  intended proof, but the public theorem surface remains directly on the source-facing
  subdifferential owners rather than switching the statement to a normal-cone wrapper.

Domain-style sampling used here:
- `Function.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `Function.subdifferentialAt_indicatorFunction_eq_normalCone` from `Chap05/Example_23_0_7`;
- `polarCone` / `Kᵒ` from `Chap03/Text_14_0_1`;
- `Set.IsConvexCone` from `Chap01/Definition_2_5_10`.

Primitive data vs derived API:
- primitive inputs: the cone `K`, points `x`, `xStar`, and the hypotheses that `K` is nonempty,
  closed, and convex-cone-valued;
- derived API: the mutual equivalence of the primal indicator-subgradient condition, the dual
  indicator-subgradient condition over the polar cone, and the direct complementary-slackness
  conjunction.

Layer target: `source-facing`, using the Chapter 23 indicator-subgradient owner surface and the
project's standard `List.TFAE` shape for multi-clause equivalence statements.
-/

-- Proof sketch: rewrite each indicator-function subdifferential by
-- `subdifferentialAt_indicatorFunction_eq_normalCone`. For a nonempty closed convex cone,
-- Chapter 14 identifies `Kᵒ` with `normalCone K 0` and `normalCone Kᵒ 0` with `K`; transporting
-- the base point from `0` to `x` turns the two normal-cone memberships into the complementary
-- conditions `x ∈ K`, `xStar ∈ Kᵒ`, `⟪x, xStar⟫ = 0`. These three clauses are therefore in one
-- TFAE class.
/-- Corollary 23.5.4: for a nonempty closed convex cone `K`, the following are equivalent:
`xStar ∈ ∂δ(· | K)(x)`, `x ∈ ∂δ(· | Kᵒ)(xStar)`, and the complementary-slackness conditions
`x ∈ K`, `xStar ∈ Kᵒ`, `⟪x, xStar⟫ = 0`. -/
theorem subdifferentialAt_indicatorFunction_polarCone_tfae
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone ℝ K) :
    List.TFAE
      [ xStar ∈ subdifferentialAt (δ[ℝ](· | K)) x,
        x ∈ subdifferentialAt (δ[ℝ](· | ((Kᵒ[ℝ] : PointedCone ℝ E) : Set E))) xStar,
        x ∈ K ∧ xStar ∈ (((Kᵒ[ℝ] : PointedCone ℝ E) : Set E)) ∧ ⟪x, xStar⟫ = (0 : ℝ) ] := sorry

end Function

end

/-! ### Theorem_23_5 (from Chap05) -/
noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → EReal} {x : E} {xStar : StrongDual ℝ E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 23.5 is the Fenchel-Young equality criterion for a proper convex
  function, stated in terms of subgradients, attainment of the primal and dual conjugate suprema,
  and equality in the Fenchel-Young inequality.
- `core/canonical`: the intrinsic owner for the unstarred four-clause theorem is the dual-valued
  `_root_.subdifferentialAt`, together with the Fenchel conjugate `f⋆`, the chapter pairing
  notation `⟪·, ·⟫ₚ`, and `List.TFAE`.
- `bridge/view`: the Euclidean vector-valued subdifferential `Function.subdifferentialAt` and the
  starred dual-side clause `x ∈ subdifferentialAt (f⋆) xStar` are Fréchet-Riesz bridge surfaces on
  top of that intrinsic owner, so they belong only to the second theorem below.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and the Euclidean bridge `Function.subdifferentialAt` from
  `Chap05/Definition_23_0_6`;
- `convexConjugate` / `f⋆` from `Chap03/Defn_12_2`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` and
  `Function.IsClosedProperConvex.biconjugate_eq` from `Chap03/Theorem_12_2`;
- `List.TFAE` as the canonical owner for “the following conditions are mutually equivalent”.

Primitive data vs derived API:
- primitive inputs: the proper convex function `f`, the primal point `x`, and the dual point
  `xStar`;
- primitive owner surface: `xStar ∈ subdifferentialAt f x` and the Fenchel conjugate evaluations
  `f x`, `f⋆ xStar`;
- derived surface: the attainment clauses, the Fenchel-Young inequality/equality clauses, and in
  the Euclidean bridge theorem below the extra dual-side and closure-side subgradient clauses.

Layer target:
- the first theorem is `core/canonical`: it keeps only the intrinsic unstarred Fenchel-Young
  equivalence and removes the unnecessary Euclidean self-duality assumptions;
- the second theorem is `bridge/view`: it adds back the vector-valued dual-side and closure-side
  clauses under the explicit Euclidean self-duality hypothesis `cl(f) x = f x`.
-/

-- Proof sketch: clause `(a)` is the supporting-hyperplane inequality at `x`, so it rewrites
-- directly to the statement that `z ↦ ⟪z, xStar⟫ₚ - f z` is maximized at `z = x`, giving
-- `(a) ↔ (b)`.
-- The defining supremum formula for `f⋆ xStar` identifies the maximum value in `(b)` with
-- `f⋆ xStar`, so `(b)` is equivalent to the reverse Fenchel-Young inequality `(c)`. The general
-- Fenchel-Young inequality always gives the opposite inequality, hence `(c)` is equivalent to the
-- equality clause `(d)`.
/-- Theorem 23.5, intrinsic owner form: for a proper convex function, the following are
equivalent: `xStar` is a subgradient of `f` at `x`, the Fenchel supremum
`z ↦ ⟪z, xStar⟫ₚ - f z` is attained at `x`, and the Fenchel-Young inequality at `(x, xStar)` holds
with inequality or equality. -/
theorem subdifferentialAt_tfae_isMaxOn_fenchelYoung
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) :
    List.TFAE
      [ xStar ∈ subdifferentialAt f x,
        IsMaxOn (fun z : E ↦ ⟪z, xStar⟫ₚ - f z) Set.univ x,
        f x + f⋆ xStar ≤ ⟪x, xStar⟫ₚ,
        f x + f⋆ xStar = ⟪x, xStar⟫ₚ ] := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

variable {f : E → EReal} {x xStar : E}

-- Proof sketch: combine the four-way equivalence above for `f` with the same argument applied to
-- the conjugate `f⋆`. Biconjugacy identifies `f⋆⋆` with `cl(f)`, and the normalization
-- hypothesis `cl(f) x = f x` turns equality in the Fenchel-Young formula for `(f, x, xStar)` into
-- the same equality for `(f⋆, xStar, x)` and for `cl(f)` at `x`. This yields a single seven-way
-- TFAE covering the unstarred, starred, and closure-side subgradient clauses.
/-- Theorem 23.5, Euclidean bridge form: under the pointwise closure normalization
`cl(f) x = f x`, the dual-side subgradient and attainment conditions for `f⋆`, together with the
subgradient condition for `cl(f)`, join the same Fenchel-Young equivalence class as the intrinsic
four clauses from Theorem 23.5. -/
theorem subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_conjugate_subdifferentialAt_of_closure_eq
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hclx : cl(f) x = f x) :
    List.TFAE
      [ xStar ∈ subdifferentialAt f x,
        IsMaxOn (fun z : E ↦ ⟪z, xStar⟫ₚ - f z) Set.univ x,
        f x + f⋆ xStar ≤ ⟪x, xStar⟫ₚ,
        f x + f⋆ xStar = ⟪x, xStar⟫ₚ,
        x ∈ subdifferentialAt (f⋆) xStar,
        IsMaxOn (fun zStar : E ↦ ⟪x, zStar⟫ₚ - f⋆ zStar) Set.univ xStar,
        xStar ∈ subdifferentialAt (cl(f)) x ] := sorry

end Function

end
