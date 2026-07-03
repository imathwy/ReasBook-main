import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_38_4_1 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 38.4.1 upgrades Theorem 38.4 under closedness of the bifunction `F`
  and the function `f`, concluding that `image F f` is closed, that its defining infimum is
  attained pointwise, and that its conjugate is the closure of the adjoint-side image `F⋆ f⋆`.
- `core/canonical`: the owner declarations already present in the chapter are `Bifunction.image`,
  `Bifunction.adjoint`, `Bifunction.dom`, `Function.IsClosedProperConvex`, `riDom(·)`, and
  `lowerSemicontinuousHull`, written `cl(·)`.
- `bridge/view`: the source expressions `F⋆ f⋆` and `ri (dom F⋆)` use the same adjoint owner
  after the canonical operational view `Function.swap (F⋆)`, which matches the input order
  expected by `image` and `dom`.

Domain-style sampling used here:
- `Bifunction.image` and `Bifunction.image_apply` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Lemma_31_0_8`;
- `Bifunction.dom` and `Bifunction.IsProper` from `Theorem_38_1`;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`;
- `Function.IsClosedProperConvex.biconjugate_eq`, together with the chapter notations `riDom(·)`
  and `cl(·)`.

Primitive data vs derived API:
- primitive inputs: a bifunction `F : U → X → EReal` and a function `f : U → EReal`;
- primitive owner hypotheses: `IsClosedConvex F`, the Chapter 38 properness owner `IsProper F`,
  closed proper convexity of `f`, and the common-relative-interior hypothesis on `f⋆` and
  `Function.swap (F⋆)`;
- derived API: lower semicontinuity of `image F f`, the pointwise attainment formula, and the
  conjugacy identity with `cl(image (Function.swap (F⋆)) (f⋆))`.

Layer target: `source-facing`, stated directly in the established owner language with no extra
wrapper for “closed image data” or “attainment data”.
-/

variable (F : U → X → EReal) (f : U → EReal)
variable (hF : IsClosedConvex F) (hF_proper : IsProper F)
variable (hf : f.IsClosedProperConvex)

local notation "ri(" C ")" => intrinsicInterior ℝ C

variable
    (hri :
      (riDom(f⋆) ∩ ri(dom (Function.swap (F⋆ : X → U → EReal)))).Nonempty)

-- Proof sketch: apply the closed-case upgrade of Theorem 38.4 to the source-facing owner
-- `image F f`. Closedness is recorded canonically as lower semicontinuity of the resulting
-- function, not by introducing a second owner for “closed images”.
/-- Corollary 38.4.1, closedness clause: if `F` is a closed proper convex bifunction, `f` is
closed proper convex, and `riDom(f⋆)` meets `ri (dom (Function.swap (F⋆)))`, then the image
`image F f` is closed. -/
theorem lowerSemicontinuous_image_of_common_riDom
    :
    LowerSemicontinuous (image F f) := by
  sorry

-- Proof sketch: the same closed-case regularity hypothesis yields attainment of the source
-- infimum `inf_u (f u + F u x)` for every `x`. The theorem keeps that source-facing equality
-- surface instead of repackaging attainment in an auxiliary structure.
/-- Corollary 38.4.1, attainment clause: under the same hypotheses, the infimum in the definition
of `image F f` is attained at every `x`. -/
theorem exists_eq_image_of_common_riDom
    (x : X) :
    ∃ u : U, image F f x = f u + F u x := by
  sorry

-- Proof sketch: the dual identity from Theorem 38.4 is applied on the conjugate side and then
-- converted back to the original side with closed proper convex biconjugacy. The resulting outer
-- closure is the chapter owner `cl(·)`.
/-- Corollary 38.4.1, conjugacy clause:
`(image F f)⋆ = cl(image (Function.swap (F⋆)) (f⋆))`. -/
theorem
    convexConjugate_image_eq_cl_image_adjoint_conjugate_of_common_riDom
    :
    (image F f)⋆ = cl(image (Function.swap (F⋆ : X → U → EReal)) (f⋆)) := by
  sorry

end

end Bifunction

/-! ### Definition_38_4_1 (from Chap08) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: despite the legacy file name, this item is Rockafellar's Corollary 38.4.1 on
  the image `image F f`, asserting closedness, pointwise attainment of the defining infimum, and
  the adjoint-side conjugacy formula.
- `core/canonical`: the owner abstractions already live in the chapter as `Bifunction.image`,
  `Bifunction.adjoint`, `Bifunction.dom`, and the function-side closed/proper/convex owner
  `Function.IsClosedProperConvex`.
- `bridge/view`: this file contributes no new mathematics beyond the canonical Chapter 8
  formulation already present in `Items/Chap08/Corollary_38_4_1.lean`, so it should reuse that
  source-facing theorem family directly.

Primary mathematical domain:
- infimal images of convex bifunctions and their adjoint-side conjugacy/attainment properties.

Domain-style sampling used here:
- `Bifunction.image` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Lemma_31_0_8`;
- `Bifunction.dom` from `Theorem_38_1`;
- the canonical Corollary 38.4.1 theorem family in `Corollary_38_4_1`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → EReal` and a function `f : U → EReal`;
- primitive owner layer: the existing chapter owners `image F f` and `F⋆`, with the operational
  bifunction view `Function.swap (F⋆)` where needed;
- derived API: lower semicontinuity of `image F f`, pointwise attainment of the infimum defining
  `image F f`, and the conjugacy identity with `cl(image (Function.swap (F⋆)) (f⋆))`.

Layer target: `bridge/view`. This file now reuses the existing source-facing owner theorems
directly instead of maintaining a parallel local API.
-/

/- Corollary 38.4.1, closedness clause: the canonical owner theorem for closedness of `image F f`
under the common-relative-interior hypothesis is already
`lowerSemicontinuous_image_of_common_riDom`. -/
recall Bifunction.lowerSemicontinuous_image_of_common_riDom

/- Corollary 38.4.1, attainment clause: the canonical owner theorem for attainment of the defining
infimum of `image F f` is already
`exists_eq_image_of_common_riDom`. -/
recall Bifunction.exists_eq_image_of_common_riDom

/- Corollary 38.4.1, conjugacy clause: the canonical owner theorem is already
`Bifunction.convexConjugate_image_eq_cl_image_adjoint_conjugate_of_common_riDom`.
-/
recall
  Bifunction.convexConjugate_image_eq_cl_image_adjoint_conjugate_of_common_riDom

/-! ### Proposition_38_4_2 (from Chap08) -/
noncomputable section

universe u v w r

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {Y : Type w}
variable {α : Type r}
variable [ConditionallyCompleteLinearOrder α] [AddCommGroup α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.4.2 states that the inverse bifunction of the product `GF`
  agrees with the source concave-side product `F_* G_*`.
- `core/canonical`: the chapter owner abstractions already present are `Bifunction.comp` for the
  source product `GF`, `Bifunction.image` for the underlying one-step elimination, and
  `Bifunction.inverse` for `F_*`.
- `bridge/view`: the right-hand side still has no separate concave-side product owner in the
  chapter, so the source `F_* G_*` is rendered by its explicit supremum formula. The left-hand
  side should nevertheless use the established owner `comp G F` rather than repeating its
  implementation.

Primary mathematical domain:
- product and inversion operations for convex/concave bifunctions in the Chapter 38 algebra.

Domain-style sampling used here:
- `Bifunction.comp` and `Bifunction.comp_apply_eq_iInf` from `Theorem_38_5`;
- `Bifunction.image` and `Bifunction.image_apply` from `Definition_38_0_4`;
- `Bifunction.inverse` and `Bifunction.inverse_apply` from `Definition_36_4_1`;
- the Chapter 6/7 pattern of keeping concave-side source formulas explicit when no canonical owner
  has been introduced yet.

Primitive data vs derived API:
- primitive source data: bifunctions `F : U → X → WithBotTop α` and
  `G : X → Y → WithBotTop α`;
- primitive owner expression: `(comp G F) _*`;
- derived source formula: `fun y u ↦ ⨆ x, G _* y x + F _* x u`;
- derived API: no extra structure beyond the owner equality itself.

Layer target: `bridge/view`.

Redundant-source-assumption check:
- the textbook mentions proper convexity, but the displayed identity is algebraic in the product
  and inverse operations, so those hypotheses are removed from the public Lean statement.
-/

-- Proof sketch: unfold `inverse` and `image`. The left-hand side becomes
-- `- (⨅ x, F u x + G x y)`, which is the supremum of the negated summands on `WithBotTop α`.
-- Rewrite those negated slice values with `inverse_apply` to obtain
-- `⨆ x, G _* y x + F _* x u`.
/-- Proposition 38.4.2: the inverse of the source product `GF`, owned here by `comp G F`, is the
source supremum-side product `F_* G_*`, rendered explicitly because the chapter has no separate
owner for that concave-side product. -/
theorem inverse_comp_eq_iSup_inverse_add_inverse
    (F : U → X → WithBotTop α) (G : X → Y → WithBotTop α) :
    (comp G F) _* = fun y u ↦ ⨆ x : X, G _* y x + F _* x u := sorry

end

end Bifunction

/-! ### Proposition_38_4_3 (from Chap08) -/
noncomputable section

universe u v w r

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.4.3 identifies the Chapter 38 product of two singleton-graph
  indicator bifunctions with the singleton-graph indicator of the composite map.
- `core/canonical`: the owner abstractions already present upstream are `Bifunction.comp` for the
  Chapter 38 product, `Bifunction.graphIndicator` for singleton-graph indicators, and
  `Function.comp` for composition of maps.
- `bridge/view`: this item is therefore a direct equality between existing owners, while the
  indexed-infimum formula is kept only as a companion derived from `comp_apply_eq_iInf`.

Primary mathematical domain:
- composition of singleton-indicator bifunctions attached to maps.

Domain-style sampling used here:
- `Bifunction.graphIndicator` from `Chap06.Definition_6_29_9`;
- `Bifunction.comp` and `Bifunction.comp_apply_eq_iInf` from `Chap08.Theorem_38_5`;
- `Function.comp` from core Lean.

Primitive data vs derived API:
- primitive source data: maps `A : U → X` and `B : X → Y`;
- primitive source-facing owner expression: `comp (graphIndicator 𝕜 B) (graphIndicator 𝕜 A)`;
- derived API: the owner equality with `graphIndicator 𝕜 (B ∘ A)` and its explicit pointwise
  `iInf` formula, from which the textbook linear-map case follows by specialization.

Layer target: `bridge/view`.
-/

section

variable {𝕜 : Type r} {U : Type u} {X : Type v} {Y : Type w}
variable [AddMonoid 𝕜] [ConditionallyCompleteLattice 𝕜]

-- Proof sketch: evaluate the Chapter 38 owner `comp` with `comp_apply_eq_iInf`. If
-- `y = B (A u)`, the summand at `x = A u` is `0`, and every other summand is `⊤`; if
-- `y ≠ B (A u)`, then every summand is already `⊤`. This is exactly the singleton-indicator
-- bifunction of `B ∘ A`.
/-- Proposition 38.4.3, owner form: the Chapter 38 product of the singleton-indicator
bifunctions of maps `A` and `B` is the singleton-indicator bifunction of the composite
`B ∘ A`. The textbook linear-map statement is its direct specialization. -/
theorem comp_graphIndicator_eq_graphIndicator_comp
    (A : U → X) (B : X → Y) :
    comp (graphIndicator 𝕜 B) (graphIndicator 𝕜 A) =
      graphIndicator 𝕜 (B ∘ A) := by
  classical
  funext u y
  rw [comp_apply_eq_iInf]
  by_cases hy : y = B (A u)
  · have hle :
        (⨅ x : X, graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y) ≤
          (0 : WithBotTop 𝕜) := by
      simpa [graphIndicator_cases, hy] using
        (iInf_le (fun x : X ↦ graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y) (A u))
    have hge :
        (0 : WithBotTop 𝕜) ≤
          ⨅ x : X, graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y := by
      refine le_iInf fun x ↦ ?_
      by_cases hx : x = A u
      · subst hx
        simp [graphIndicator_cases, hy]
      · have hbranch : (if B (A u) = B x then (0 : WithBotTop 𝕜) else ⊤) ≠ ⊥ := by
          by_cases hBx : B (A u) = B x <;> simp [hBx]
        simp [graphIndicator_cases, hx, hy, hbranch] at *
    simpa [graphIndicator_cases, hy] using le_antisymm hle hge
  · have htop :
        (⊤ : WithBotTop 𝕜) ≤
          ⨅ x : X, graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y := by
      refine le_iInf fun x ↦ ?_
      by_cases hx : x = A u
      · subst hx
        simp [graphIndicator_cases, hy]
      · have hbranch : (if y = B x then (0 : WithBotTop 𝕜) else ⊤) ≠ ⊥ := by
          by_cases hBx : y = B x <;> simp [hBx]
        simp [graphIndicator_cases, hx, hbranch] at *
    simpa [graphIndicator_cases, hy] using le_antisymm le_top htop

/-- Pointwise owner form of Proposition 38.4.3. -/
@[simp] theorem comp_graphIndicator_apply
    (A : U → X) (B : X → Y) (u : U) (y : Y) :
    comp (graphIndicator 𝕜 B) (graphIndicator 𝕜 A) u y =
      graphIndicator 𝕜 (B ∘ A) u y := by
  simpa using congrFun (congrFun (comp_graphIndicator_eq_graphIndicator_comp A B) u) y

/-- Pointwise `iInf` companion form of Proposition 38.4.3, obtained by expanding the Chapter 38
owner `comp`. -/
theorem iInf_add_graphIndicator_eq_graphIndicator_comp
    (A : U → X) (B : X → Y) (u : U) (y : Y) :
    (⨅ x : X, graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y) =
      graphIndicator 𝕜 (B ∘ A) u y := by
  simpa [comp_apply_eq_iInf] using comp_graphIndicator_apply A B u y

end

end Bifunction

/-! ### Theorem_38_4 (from Chap08) -/
noncomputable section

universe u v u' v' w

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 38.4 introduces the image `Ff` of a convex function `f` under a convex
  bifunction `F`, given by the infimum formula `x ↦ inf_u (f u + F u x)`.
- `core/canonical`: the existing chapter owners are `Bifunction.image` from
  `Definition_38_0_4`, `Bifunction.dom` from `Definition_6_29_8` / `Theorem_38_1`, and the
  Chapter 1 linear-image
  owner `Function.linearImage`.
- `bridge/view`: proof-level bridges pass through the Chapter 1 linear-image owner and through the
  adjoint-side owners `adjoint` and the image-side operational view `Function.swap (F⋆)`,
  but the public theorem surface should stay on `Bifunction.image` and `Bifunction.dom`.

Primary mathematical domain:
- convex bifunctions, infimal images, Fenchel conjugates, and relative-interior qualification.

Domain-style sampling used here:
- `Bifunction.image` and `Bifunction.image_apply` from `Chap08.Definition_38_0_4`;
- `Bifunction.dom` from `Chap06.Definition_6_29_8`, reused in `Chap08.Theorem_38_1`;
- `Bifunction.image_eq_linearImage_fst` from `Chap08.Definition_38_3_1`;
- `Function.isConvex_linearImage` from `Chap01.Theorem_5_7`;
- `adjoint` from `Chap06.Definition_6_30_14`;
- `inverse` from `Chap07.Definition_36_4_1`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop 𝕜` and a function
  `f : U → WithBotTop 𝕜`;
- primitive source-facing owners already present upstream: `image F f`, `dom F`, the adjoint
  notation `F⋆ : XStar → UStar → WithBotTop ℝ`, and its canonical image-side operational view
  `Function.swap (F⋆)`;
- derived API here: convexity of `image F f`, the conjugacy identity for
  `convexConjugate (image F f)`, and the attainment statement for the adjoint-side infimum over
  `Function.swap (F⋆)`.

Layer target: `source-facing`, stated directly through the established chapter owners rather than
through a parallel wrapper for “image data” or “dual attainment data”.
-/

section Convexity

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: pass from the source-facing owner `image F f` to the Chapter 1 owner
-- `Function.partialInfimum` via `image_eq_linearImage_fst`, then apply the intrinsic
-- partial-infimum convexity theorem to the convex graph kernel `(x, u) ↦ f u + F u x`.
/-- Theorem 38.4 (1): if `F` is a convex bifunction and `f` is convex, then the image `image F f`
is convex. -/
theorem isConvex_image
    (F : U → X → WithBotTop 𝕜) (f : U → WithBotTop 𝕜)
    (hF_convex : Function.IsConvex 𝕜 (Function.uncurry F))
    (hf_convex : Function.IsConvex 𝕜 f) :
    (image F f).IsConvex 𝕜 := sorry

end Convexity

section Conjugacy

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [Neg UStar]
variable [HasPairing U UStar ℝ] [HasPairing X XStar ℝ]
variable (F : U → X → WithBotTop ℝ) (f : U → WithBotTop ℝ)

local notation "ri(" C ")" => intrinsicInterior ℝ C
local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop ℝ)
local notation "f⋆" => (convexConjugate f : UStar → WithBotTop ℝ)

-- Proof sketch: rewrite `(image F f)⋆` using the same perturbation-function representation of
-- `image F f` that underlies Theorem 5.7, then apply the Chapter 31 Fenchel-duality argument to
-- the concave slice `u ↦ ⟪F u, x⋆⟫`. The qualification hypothesis is exactly the common
-- relative-interior condition `ri(dom f) ∩ ri(dom F) ≠ ∅`.
/-- Conjugacy clause of Theorem 38.4: if `ri (dom f)` and `ri (dom F)` have a point in common,
then for each `x⋆`, the Fenchel conjugate of `image F f` at `x⋆` equals the value at `x⋆` of the
image of `f⋆` under the canonical image-side view `Function.swap (F⋆)` of the adjoint
bifunction. -/
theorem convexConjugate_image_eq_image_adjoint_conjugate_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F))
    (hf_convex : Function.IsConvex ℝ f)
    (hf_proper : f.IsProper)
    (hri : (riDom(f) ∩ ri(dom F)).Nonempty)
    (xStar : XStar) :
    (image F f)⋆ xStar = image (Function.swap F⋆) (f⋆) xStar := sorry

-- Proof sketch: the same duality argument that gives the equality in clause (2) also yields, for
-- each `x⋆`, a minimizing dual point `u⋆` in the infimum formula defining the adjoint-side image.
/-- Attainment clause of Theorem 38.4: under the same relative-interior hypothesis, the infimum in
the definition of `(image (Function.swap (F⋆)) (f⋆)) x⋆` is attained for every `x⋆`. -/
theorem exists_eq_image_adjoint_conjugate_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F))
    (hf_convex : Function.IsConvex ℝ f)
    (hf_proper : f.IsProper)
    (hri : (riDom(f) ∩ ri(dom F)).Nonempty)
    (xStar : XStar) :
    ∃ uStar : UStar,
      image (Function.swap F⋆) (f⋆) xStar =
        f⋆ uStar + F⋆ xStar uStar := sorry

end Conjugacy

end Bifunction
