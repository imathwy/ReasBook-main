import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 4.4.1 states that the effective domain of a
  globally defined convex `WithTopBot`-valued function is convex.
- `core/canonical`: the intrinsic owner layer is `ConvexOn 𝕜 S f`, with the
  relative conclusion `Convex 𝕜 (S ∩ dom(f))` and the global proposition as
  the specialization `S = Set.univ`.
- `bridge/view`: `ConvexOn.convex_lt` gives convexity of `{x | x ∈ S ∧ f x < ⊤}`,
  which is definitionally `S ∩ dom(f)`; `effectiveDomain_inter_eq_image_fst_epi`
  then provides the projection view.

Domain-style sampling used here:
- `ConvexOn` and `ConvexOn.convex_lt`;
- `effectiveDomain` and the notation `dom(f)` from `Definition 4.4`;
- `effectiveDomain_inter_eq_image_fst_epi`;
- `epi[S] f` as projection-view bridge data.

Primitive data vs derived API:
- primitive input: a subset `S` and function `f : E → WithTopBot α`;
- owner hypothesis: convexity of `f` on `S` as `ConvexOn 𝕜 S f`;
- derived conclusion: convexity of the owner set `S ∩ dom(f)`, and then `dom(f)` as a
  specialization.

Layer target: `core/canonical` first (relative owner theorem), then `source-facing`
specialization (`S = Set.univ`).
-/

section

variable {𝕜 : Type w} {E : Type u} {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [PartialOrder α]
variable [AddCommMonoid (WithTopBot α)]
variable [IsOrderedCancelAddMonoid (WithTopBot α)]
variable [Module 𝕜 (WithTopBot α)] [PosSMulStrictMono 𝕜 (WithTopBot α)]

namespace ConvexOn

/-- Helper for Prop 4.4.1: if `f` is convex on `S`, then the finite-value slice
`S ∩ dom(f)` is convex. -/
theorem convex_inter_dom {S : Set E} {f : E → WithTopBot α}
    (hf : ConvexOn 𝕜 S f) :
    Convex 𝕜 (S ∩ dom(f)) := by
  -- Reinterpret the effective domain as the strict sublevel set below `⊤`.
  simpa [effectiveDomain] using (hf.convex_lt (r := (⊤ : WithTopBot α)))

/-- Helper for Prop 4.4.1: `S ∩ dom(f)` is convex, hence so is its epigraph projection
description `Prod.fst '' (epi[S] f)`. -/
theorem convex_image_fst_epi {S : Set E} {f : E → WithTopBot α} [Nonempty α]
    (hf : ConvexOn 𝕜 S f) :
    Convex 𝕜 (Prod.fst '' (epi[S] f)) := by
  -- Replace the projection description by the relative effective domain.
  simpa [effectiveDomain_inter_eq_image_fst_epi (f := f) (S := S)] using
    (hf.convex_inter_dom : Convex 𝕜 (S ∩ dom(f)))

/-- Prop 4.4.1: if `f` is convex on all of `E`, then `dom(f)` is convex. -/
theorem convex_dom {f : E → WithTopBot α}
    (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    Convex 𝕜 dom(f) := by
  -- Specialize the relative-domain theorem to the global set `Set.univ`.
  simpa [Set.univ_inter] using
    (hf.convex_inter_dom : Convex 𝕜 ((Set.univ : Set E) ∩ dom(f)))

end ConvexOn
end
