import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {𝕜 : Type v}
variable {E : Type u}

/-
Source/core/bridge triage:
- `source-facing`: Theorem 2.5 states that an arbitrary intersection of convex cones is again a
  convex cone, where Definition 2.5.10 provides the short source-facing owner
  `Set.IsConvexCone 𝕜 K`.
- `core/canonical`: the closure proofs use the owner-side intersection theorems
  `Set.IsCone.sInter` / `Set.IsCone.iInter` and `convex_sInter` / `convex_iInter` through the
  fields of `Set.IsConvexCone`; the source-facing closure API is exposed both at `sInter` and at
  the indexed-family surface `Set.IsConvexCone.iInter`.
- `bridge/view`: mathlib's bundled theorem `ConvexCone.coe_sInf` is only a companion bridge. The
  numbered item itself should stay at the textbook subset layer and reuse the owner-side
  intersection theorems directly.
- Primitive data vs derived API: the primitive datum is the family `S : Set (Set E)`. Closure of
  the source owner `Set.IsConvexCone` under arbitrary intersections is derived API.
- Domain-style sampling: this refinement is guided by the chapter owner `Set.IsCone` from
  Definition 2.5.9, the short source-facing owner `Set.IsConvexCone` from Definition 2.5.10,
  `Set.IsCone.sInter`, `Set.IsCone.iInter`, `convex_sInter`, `convex_iInter`, and the bundled
  bridge `ConvexCone.coe_sInf`.
- Layer target: `source-facing`.
-/

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

namespace Set.IsConvexCone

/-- Primitive constructor form of Theorem 2.5: if each member of a family is both a cone and
convex, then the intersection is a convex cone. -/
theorem sInter_mk {S : Set (Set E)}
    (hCone : ∀ s ∈ S, Set.IsCone 𝕜 s)
    (hConvex : ∀ s ∈ S, Convex 𝕜 s) :
    IsConvexCone 𝕜 (⋂₀ S) := by
  exact ⟨Set.IsCone.sInter hCone, convex_sInter hConvex⟩

/-- Theorem 2.5: an arbitrary intersection of convex cones is again a convex cone, expressed in the
chapter's source-facing owner form `Set.IsConvexCone 𝕜 _`. -/
theorem sInter {S : Set (Set E)}
    (hS : ∀ s ∈ S, IsConvexCone 𝕜 s) : IsConvexCone 𝕜 (⋂₀ S) := by
  exact sInter_mk (fun s hs ↦ (hS s hs).isCone) (fun s hs ↦ (hS s hs).convex)

/-- Primitive constructor form of indexed intersection closure for convex cones. -/
theorem iInter_mk {ι : Sort*} {s : ι → Set E}
    (hCone : ∀ i, Set.IsCone 𝕜 (s i))
    (hConvex : ∀ i, Convex 𝕜 (s i)) :
    IsConvexCone 𝕜 (⋂ i, s i) := by
  exact ⟨Set.IsCone.iInter hCone, convex_iInter hConvex⟩

/-- Indexed-family form of Theorem 2.5: intersections written as `iInter` are convex cones when
every fiber is a convex cone. -/
theorem iInter {ι : Sort*} {s : ι → Set E}
    (hs : ∀ i, IsConvexCone 𝕜 (s i)) : IsConvexCone 𝕜 (⋂ i, s i) := by
  exact iInter_mk (fun i ↦ (hs i).isCone) (fun i ↦ (hs i).convex)

end Set.IsConvexCone
