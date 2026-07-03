import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_7_4_1 (from Chap02) -/
section

open scoped Rockafellar

namespace Function

section GenericCodomain

variable {X : Type*} [TopologicalSpace X]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Nonempty 𝕜]

/-- For a `WithBotTop 𝕜`-valued function with a nonempty finite codomain layer, passing to the
Chapter 7 closure `cl(·)` can only enlarge the effective domain. This owner-level inclusion is
independent of convexity and properness. -/
theorem subset_dom_lowerSemicontinuousHull (f : X → WithBotTop 𝕜) :
    dom(f) ⊆ dom(cl(f)) := by
  rw [lowerSemicontinuousHull, effectiveDomain_verticalInfimum_eq_image_fst]
  rw [effectiveDomain_eq_image_fst_epi]
  rintro x ⟨p, hp, rfl⟩
  exact ⟨p, subset_closure hp, rfl⟩

end GenericCodomain

end Function

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

-- This finite-dimensional ordered-normed layer is exactly the upstream owner layer used by
-- Theorem 7.4 (`cl(·)` off-frontier `EqOn`) and Theorem 6.3 (intrinsic-interior/closure
-- invariance for convex sets), which this corollary chains without adding stronger assumptions.

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.4.1 says that for a proper convex function, passing from `f` to its
  closure `cl(f)` can only enlarge the effective domain by adding relative-boundary points, and
  therefore does not change the closure, relative interior, or dimension of the effective domain.
- `core/canonical`: the owner abstractions already fixed in the chapter are `Function.IsConvex 𝕜`,
  `Function.IsProper`, Rockafellar's closure owner `cl(·)`, the effective-domain owners `dom(·)`,
  `rb(·)`, and `riDom(·)`, and the set-dimension owner `Set.affineDim`.
- `bridge/view`: the textbook relative boundary is rendered directly by the chapter notation
  `rb[𝕜](dom(f))`, while the relative interior and dimension claims are expressed on
  `riDom[𝕜](·)` and
  `Set.affineDim`.

Domain-style sampling used here:
- `Function.subset_dom_lowerSemicontinuousHull` for the basic inclusion
  `dom(f) ⊆ dom(cl(f))`;
- `Function.IsConvex.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper` from
  Theorem 7.4 for the boundary-localization clause;
- `Convex.closure_intrinsicInterior_eq_closure` and
  `Convex.intrinsicInterior_closure_eq_intrinsicInterior` from Theorem 6.3 for the relative-
  interior invariance under closure;
- `Set.affineDim` from Definition 2.4.10 for the dimension clause.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop 𝕜`, together with convexity and properness;
- derived outputs: the domain inclusion, the relative-boundary localization of the new domain
  points of `cl(f)`, and the resulting closure, relative-interior, and affine-dimension
  equalities.

Layer target: `source-facing`, split into atomic owner-level consequences rather than packaged as
one large conjunction.
-/

namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

/- Corollary 7.4.1 (1): the domain inclusion `dom(f) ⊆ dom(cl(f))` is exactly the owner theorem
`Function.subset_dom_lowerSemicontinuousHull`; it does not use convexity or properness. -/
recall Function.subset_dom_lowerSemicontinuousHull

-- Proof sketch: if `x ∈ dom(cl(f)) \ dom(f)` and `x` were not on the relative frontier of
-- `dom(f)`, then Theorem 7.4 would give `cl(f) x = f x`. Since `x ∉ dom(f)`, this would force
-- `cl(f) x = ⊤`, contradicting `x ∈ dom(cl(f))`. So every new point of `dom(cl(f))` lies in the
-- relative frontier of `dom(f)`.
/-- Corollary 7.4.1 (2): any point added to the effective domain by passing from `f` to `cl(f)`
lies in the relative frontier of `dom(f)`. -/
theorem diff_dom_lowerSemicontinuousHull_subset_intrinsicFrontier_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    dom(cl(f)) \ dom(f) ⊆ rb[𝕜](dom(f)) := by
  intro x hx
  by_contra hx_not_frontier
  have hx_off_frontier : x ∈ (rb[𝕜](dom(f)))ᶜ := by
    simpa [Set.mem_compl] using hx_not_frontier
  have hEqOn :
      Set.EqOn (cl(f)) f (rb[𝕜](dom(f)))ᶜ :=
    hf.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper hf_proper
  have hcl_eq_f : cl(f) x = f x := hEqOn hx_off_frontier
  have hx_not_dom : x ∉ dom(f) := hx.2
  have hf_top : f x = (⊤ : WithBotTop 𝕜) := by
    by_contra hfx_ne_top
    exact hx_not_dom (mem_effectiveDomain.mpr (lt_of_le_of_ne le_top hfx_ne_top))
  have hcl_top : cl(f) x = (⊤ : WithBotTop 𝕜) := by
    simpa [hcl_eq_f] using hf_top
  have hcl_lt_top : cl(f) x < (⊤ : WithBotTop 𝕜) := mem_effectiveDomain.mp hx.1
  have htop_lt_top : (⊤ : WithBotTop 𝕜) < ⊤ := by
    rw [hcl_top] at hcl_lt_top
    exact hcl_lt_top
  exact (lt_irrefl (⊤ : WithBotTop 𝕜)) htop_lt_top

-- Proof sketch (intrinsic owner form): clause (2) localizes the new points in `dom(cl(f))` to the
-- relative frontier of `dom(f)`, hence to `intrinsicClosure 𝕜 (dom(f))`; together with
-- `dom(f) ⊆ dom(cl(f))`, this yields equality of intrinsic closures.
/-- Corollary 7.4.1 (3), intrinsic owner form: `dom(cl(f))` and `dom(f)` have the same intrinsic
closure. -/
theorem intrinsicClosure_dom_lowerSemicontinuousHull_eq_intrinsicClosure_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    intrinsicClosure 𝕜 (dom(cl(f))) = intrinsicClosure 𝕜 (dom(f)) := by
  refine subset_antisymm ?_ ?_
  · have hdom_subset : dom(cl(f)) ⊆ intrinsicClosure 𝕜 dom(f) := by
      intro x hx
      by_cases hx_dom : x ∈ dom(f)
      · exact subset_intrinsicClosure hx_dom
      · have hx_frontier : x ∈ rb[𝕜](dom(f)) :=
          (diff_dom_lowerSemicontinuousHull_subset_intrinsicFrontier_of_isProper
            (f := f) hf hf_proper) ⟨hx, hx_dom⟩
        exact intrinsicFrontier_subset_intrinsicClosure hx_frontier
    exact (intrinsicClosure_mono hdom_subset).trans (by
      simp)
  · exact intrinsicClosure_mono (Function.subset_dom_lowerSemicontinuousHull (f := f))

/-- Corollary 7.4.1 (3), ambient-closure bridge: `dom(cl(f))` and `dom(f)` have the same closure.
-/
theorem closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    closure (dom(cl(f))) = closure (dom(f)) := by
  simpa [intrinsicClosure_eq_closure 𝕜 (dom(cl(f))), intrinsicClosure_eq_closure 𝕜 (dom(f))]
    using
      intrinsicClosure_dom_lowerSemicontinuousHull_eq_intrinsicClosure_dom_of_isProper
        (f := f) hf hf_proper

-- Proof sketch: both `dom(f)` and `dom(cl(f))` are convex sets. For convex sets, taking closure
-- does not change the relative interior. Applying this to the common closure from clause (3)
-- gives the same relative interior for the two effective domains.
/-- Corollary 7.4.1 (4): `dom(cl(f))` and `dom(f)` have the same relative interior, written here
as equality of `riDom(cl(f))` and `riDom(f)`. -/
theorem riDom_lowerSemicontinuousHull_eq_riDom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    riDom[𝕜](cl(f)) = riDom[𝕜](f) := by
  have hconv_dom_f : Convex 𝕜 dom(f) := hf.convex_dom
  have hconv_dom_cl : Convex 𝕜 dom(cl(f)) := by
    exact (hf.lowerSemicontinuousHull_isClosedProperConvex_of_isProper hf_proper).convex.convex_dom
  calc
    riDom[𝕜](cl(f))
        = ri[𝕜](closure (dom(cl(f)))) := by
            simpa [riDom_eq_intrinsicInterior_dom] using
              (hconv_dom_cl.intrinsicInterior_closure_eq_intrinsicInterior).symm
    _ = ri[𝕜](closure (dom(f))) := by
          rw [closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper
            (f := f) hf hf_proper]
    _ = riDom[𝕜](f) := by
          simpa [riDom_eq_intrinsicInterior_dom] using
            hconv_dom_f.intrinsicInterior_closure_eq_intrinsicInterior

-- Proof sketch (primitive affine owner form): equal closures imply equal affine spans by
-- `Set.affineSpan_closure`.
/-- Corollary 7.4.1 (5), primitive affine owner form: `dom(cl(f))` and `dom(f)` have the same
affine span. -/
theorem affineSpan_dom_lowerSemicontinuousHull_eq_affineSpan_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    affineSpan 𝕜 (dom(cl(f))) = affineSpan 𝕜 (dom(f)) := by
  calc
    affineSpan 𝕜 (dom(cl(f)))
        = affineSpan 𝕜 (closure (dom(cl(f)))) := by
            simpa using (Set.affineSpan_closure (𝕜 := 𝕜) (C := dom(cl(f)))).symm
    _ = affineSpan 𝕜 (closure (dom(f))) := by
          rw [closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper
            (f := f) hf hf_proper]
    _ = affineSpan 𝕜 (dom(f)) := by
          simpa using (Set.affineSpan_closure (𝕜 := 𝕜) (C := dom(f)))

/-- Corollary 7.4.1 (5), affine-dimension bridge: `dom(cl(f))` and `dom(f)` have the same affine
dimension. -/
theorem affineDim_dom_lowerSemicontinuousHull_eq_affineDim_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    dim[𝕜](dom(cl(f))) = dim[𝕜](dom(f)) := by
  simpa [Set.affineDim] using
    congrArg (fun A : AffineSubspace 𝕜 E => A.affineDim)
      (affineSpan_dom_lowerSemicontinuousHull_eq_affineSpan_dom_of_isProper
        (f := f) hf hf_proper)

end Function.IsConvex

end

/-! ### Corollary_7_4_2 (from Chap02) -/
section

open scoped Rockafellar

universe u

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

variable {f : E → WithBotTop 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.4.2 says that a proper convex function is closed whenever its
  effective domain is an affine set.
- `core/canonical`: the owner abstractions already fixed in the chapter are `Function.IsConvex 𝕜`,
  `Function.IsProper`, the effective-domain owner `dom(·)`, the affine-set owner
  `Set.IsAffine 𝕜`, and the bundled closed/proper/convex predicate
  `Function.IsClosedProperConvex`.
- `bridge/view`: the textbook phrase "`dom f` is an affine set" is rendered by the canonical
  set-level affine owner predicate `Set.IsAffine 𝕜 dom(f)`.

Domain-style sampling used here:
- `Function.IsConvex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper` from Theorem 7.4;
- `Function.IsConvex.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper` from
  Theorem 7.4;
- the affine-set owner `Set.IsAffine 𝕜` (equivalently, affine-subspace carrier form);
- the chapter closed/proper/convex owner `Function.IsClosedProperConvex`.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop 𝕜`, together with convexity, properness, and
  the affine-domain hypothesis;
- derived output: the canonical closed/proper/convex owner for `f`, which packages the source
  conclusion "`f` is closed" together with the original convexity and properness assumptions.

Layer target: `source-facing`, stated directly on the canonical chapter owners rather than through
an auxiliary wrapper for affine domains.
-/

-- Proof sketch: Theorem 7.4 gives `Set.EqOn (cl(f)) f (intrinsicFrontier 𝕜 dom(f))ᶜ`. If
-- `dom(f)` is affine, then its intrinsic interior is all of `dom(f)`, so its intrinsic frontier
-- is empty. Hence `cl(f) = f`, and the closed/proper/convex conclusion for `cl(f)` from
-- Theorem 7.4 transfers directly to `f`.
/-- Corollary 7.4.2: if a proper convex function has affine effective domain, written here as
`Set.IsAffine 𝕜 dom(f)`, then it is closed; equivalently, together with the
original hypotheses, it is a closed proper convex function. In particular, this applies when `f`
is finite throughout a finite-dimensional ambient space, so that `dom(f) = Set.univ`. -/
  theorem isClosedProperConvex_of_affine_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hdom_affine : Set.IsAffine 𝕜 dom(f)) :
    IsClosedProperConvex[𝕜] f := by
  have hspan : affineSpan 𝕜 dom(f) = dom(f) :=
    (Set.isAffine_iff_affineSpan_eq_self (k := 𝕜) (dom(f))).1 hdom_affine
  have hpre : ((↑) : affineSpan 𝕜 dom(f) → E) ⁻¹' dom(f) = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hx : (x : E) ∈ (affineSpan 𝕜 dom(f) : Set E) := x.2
      rw [hspan] at hx
      exact hx
  have hfrontier : intrinsicFrontier 𝕜 dom(f) = ∅ := by
    rw [intrinsicFrontier, hpre, frontier_univ, Set.image_empty]
  have hcl : cl(f) = f := by
    ext x
    have hEqOn : Set.EqOn (cl(f)) f (rb[𝕜](dom(f)))ᶜ :=
      hf.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper hf_proper
    have hx : x ∈ (rb[𝕜](dom(f)))ᶜ := by
      simp [hfrontier]
    exact hEqOn hx
  rw [← hcl]
  exact hf.lowerSemicontinuousHull_isClosedProperConvex_of_isProper hf_proper

end Function.IsConvex

end

/-! ### Theorem_7_4 (from Chap02) -/
section

open scoped Rockafellar

variable {𝕜 E α : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable [TopologicalSpace (WithBotTop α)] [AddCommMonoid α] [SMul 𝕜 α]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 7.4 says that for a proper convex function, the Chapter 7 closure
  `cl(f)` is a closed proper convex function and agrees with `f` away from the relative boundary
  of `dom(f)`.
- `core/canonical`: the owner abstractions already fixed in the project are
  `Function.IsConvex 𝕜`, `Function.IsProper`, Rockafellar's closure owner `cl(·)`, the effective
  domain owner `dom(·)`, mathlib's `intrinsicFrontier 𝕜` with chapter notation `rb[𝕜](·)`, and the
  chapter core predicate `Function.IsClosedProperConvex`.
- `bridge/view`: the textbook phrase "except perhaps at relative boundary points of `dom f`" is
  rendered by a `Set.EqOn` statement on the complement of `rb[𝕜](dom(f))`.

Domain-style sampling used here:
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.IsProper` and `dom(·)` from `Chap01.Definition_4_6` and `Chap01.Definition_4_4`;
- the relative-boundary notation `rb[𝕜](·)` from `Chap02.Text_6_10`;
- Rockafellar's closure owner `cl(·)` from `Chap02.Text_7_0_4`;
- the bundled closed/proper/convex predicate `Function.IsClosedProperConvex` from
  `Chap03.Text_12_3_6`.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop α` on the chapter scalar/ambient layer,
  together with convexity and properness;
- derived outputs: the bundled closed/proper/convex status of `cl(f)` and the pointwise agreement
  of `cl(f)` with `f` off the relative boundary `rb[𝕜](dom(f))` of the effective domain.

Layer target: `source-facing`, stated directly on the canonical owners `cl(·)`,
`Function.IsClosedProperConvex`, and `intrinsicFrontier 𝕜`, with the chapter theorem surface
written using `rb[𝕜](·)`.

Remaining scalar/ambient strength rationale:
- the codomain layer is decoupled from the scalar: `f` is `WithBotTop α`-valued, with `α` carrying
  only the order/topology/module data needed by the imported owner APIs;
- the scalar layer is generalized from `ℝ` to `𝕜`, following the upstream owner surfaces used by
  `Function.IsConvex`, `cl(·)`, `rb[𝕜](·)`, and `Function.IsClosedProperConvex`;
- finite-dimensional normed ambient hypotheses are retained because this theorem is the
  finite-dimensional closure theorem in the chapter's current upstream dependency chain.
-/

namespace Function.IsConvex

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

variable {f : E → WithBotTop α}

-- Proof sketch: `hf_proper` rules out the `-∞` branch, so the closure operator stays the
-- lower-semicontinuous hull `cl(f)`. Convexity of `cl(f)` comes from closure of the convex
-- epigraph, lower semicontinuity is built into `cl(·)`, and the second clause of the theorem
-- shows that `cl(f)` is finite on `dom(f)`, which yields properness.
/-- Theorem 7.4: if `f` is a proper convex function on a finite-dimensional normed space,
then its Chapter 7 closure `cl(f)` is a closed proper convex function. -/
theorem lowerSemicontinuousHull_isClosedProperConvex_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    IsClosedProperConvex[𝕜] (cl(f)) := sorry

-- Proof sketch: on `ri(dom f)`, the epigraph argument from Lemma 7.3 and the line-intersection
-- closure theorem identify `cl(f)` with `f`. If `x ∉ closure dom(f)`, then both functions take
-- the value `⊤`. The only points not covered by these two cases are the relative-boundary points
-- of `dom(f)`.
/-- For a proper convex function, `cl(f)` agrees with `f` away from the relative boundary of its
effective domain. -/
theorem lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    Set.EqOn (cl(f)) f (rb[𝕜](dom(f)))ᶜ := sorry

end Function.IsConvex

end
