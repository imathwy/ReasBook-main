import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

section

variable {E k : Type*}
variable [Semiring k] [Sub k] [PartialOrder k] [AddCommMonoid E] [SMul k E]

/-- Source-facing bridge: if every ambient fixed-`x` umbra slice over `S` is convex, then the
corresponding umbra is convex. -/
theorem convex_umbra_of_convex_slices_mem {C S : Set E}
    (hSlice : ∀ x ∈ S, Convex k (umbraSlice[k | C, x])) :
    Convex k (umbra[k | C, S]) := by
  simpa [umbra] using convex_iInter (fun x : S ↦ hSlice x x.2)

end

section

variable {E k : Type*}
variable [Field k] [PartialOrder k] [IsOrderedRing k] [PosMulReflectLT k]
  [AddCommMonoid E] [Module k E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.8.3 states that the umbra of a convex set `C` is convex.
- `core/canonical`: the owner abstraction is the standard convexity predicate `Convex k` on
  subsets of a `k`-module.
- `bridge/view`: the set under discussion is the source-facing set `umbra C S`, so the theorem
  should be stated directly for that canonical source-facing set.
- Primitive data vs derived API: the sets `C` and `S` and the convexity of `C` are primitive; the
  convexity of `umbra C S` is the sole derived conclusion.
- Domain-style sampling: this item aligns with the chapter's closure results for convexity under
  arbitrary intersections. Concretely, the relevant owner-level API is the predicate `Convex k`,
  together with mathlib's subtype-indexed `convex_iInter` and the owner-side derived theorem
  `Convex.umbraSlice` for the fixed-`x` slices from `Text_3_8_1`. The more special theorem
  `Convex.affinity` was also checked during sampling as the canonical affine-image owner for each
  individual slice parameter, but the reusable owner theorem is already packaged at the chapter
  level as `Convex.umbraSlice`.
- Layer target: `bridge/view`; the source-facing theorem about `umbra` is preserved, with the
  outer convexity step delegated to subtype-indexed `convex_iInter` and the inner slice convexity
  delegated to
  the owner theorem `Convex.umbraSlice`.
-/

/-- If `C` is convex, then its umbra with respect to any subset `S` is convex. -/
theorem Convex.umbra {C S : Set E} (hC : Convex k C) :
    Convex k (umbra[k | C, S]) := by
  exact convex_umbra_of_convex_slices_mem (S := S) fun x _hx ↦ hC.umbraSlice (x := x)

/-- Text 3.8.3: if `C` is convex, then its umbra with respect to any subset `S` is convex. -/
theorem convex_umbra {C S : Set E} (hC : Convex k C) :
    Convex k (umbra[k | C, S]) :=
  hC.umbra

end
