import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

variable {I : Sort w}

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 8.3.3 states that the recession cone of a nonempty intersection of
  closed convex sets in a topological module over an ordered topological semifield is the
  intersection of their recession cones.
- `core/canonical`: the chapter owner object for this source notion is `recessionCone`.
- `bridge/view`: Theorem 8.2 separately identifies `recessionCone` with `asymptoticCone 𝕜` for
  closed convex nonempty sets, so this file should keep only the owner-level intersection formula.
  Binary intersections are a derived specialization via `Set.inter_eq_iInter`, not a second public
  owner theorem.
- Domain-style sampling:
  - primitive owner-side API: `recessionCone`, `Set.mem_recessionCone_iff`
  - upstream bridge API: `Convex.mem_recessionCone_of_nonneg_ray` and
    `Convex.mem_recessionCone_of_exists_pos_ray`.
- Primitive data vs derived API:
  - primitive direction `⋂₀ (recessionCone '' S) ⊆ 0⁺[𝕜] (⋂₀ S)` uses only the owner definition;
  - the reverse inclusion is exactly where the closed-convex bridge theorem is needed.
  - indexed `iInter` statements are derived from the intrinsic `sInter` owner layer via
    `Set.sInter_range`.
- Upstream-first minimality check:
  the stronger ordered-topological-semifield stack appears first in
  Theorem 8.3's bridge API (which is itself aligned with mathlib's
  asymptotic-cone layer), so this file keeps those assumptions only on the
  reverse inclusion and leaves the primitive inclusion at the weak owner layer.
- Layer target: `source-facing`, with the owner-only inclusion in `Set` (owner namespace) and the
  closed-convex bridge statements in `Convex`.
-/

namespace Set

section

variable {𝕜 : Type v} {P E : Type u} [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P]
variable {C : I → Set P}
variable {S : Set (Set P)}

/-- Intrinsic primitive inclusion for recession cones of arbitrary set-families:
membership in every recession cone of members of `S` implies membership in the recession cone of
their intersection `⋂₀ S`. This owner-level statement is ambient-intrinsic:
the family lives in an ambient point type `P`, while recession directions lie in `E`. -/
theorem sInter_recessionCone_subset_recessionCone_sInter :
    (⋂₀ ((fun t : Set P ↦ t.recessionCone 𝕜) '' S)) ⊆ (0⁺[𝕜] (⋂₀ S) : Set E) := by
  intro y hy
  rw [Set.mem_recessionCone_iff]
  intro x hx a ha
  refine Set.mem_sInter.mpr fun t ht ↦ ?_
  have hy_t : y ∈ t.recessionCone 𝕜 :=
    (Set.mem_sInter.mp hy) (t.recessionCone 𝕜) ⟨t, ht, rfl⟩
  exact (Set.mem_recessionCone_iff.mp hy_t) x ((Set.mem_sInter.mp hx) t ht) a ha

/-- The primitive owner-level inclusion for recession cones of indexed intersections:
membership in every `0⁺[𝕜] (C i)` implies membership in `0⁺[𝕜] (⋂ i, C i)`.
As above, this is stated on the intrinsic ambient/direction split `P`/`E`. -/
theorem iInter_recessionCone_subset_recessionCone_iInter :
    (⋂ i, (0⁺[𝕜] (C i) : Set E)) ⊆ (0⁺[𝕜] (⋂ i, C i) : Set E) := by
  simpa [Set.sInter_range] using
    (sInter_recessionCone_subset_recessionCone_sInter (S := Set.range C))

/-- Primitive bridge-layer reverse inclusion for arbitrary set-families:
if `⋂₀ S` is nonempty and each member `t ∈ S` has the owner-side bridge property that one
base-point nonnegative ray in direction `y` implies `y ∈ 0⁺[𝕜] t`, then every recession direction
of the intersection belongs to every member recession cone. -/
theorem recessionCone_sInter_subset_sInter_recessionCone_of_nonneg_ray
    (hS_nonempty : (⋂₀ S).Nonempty)
    (hRayToRecession :
      ∀ t ∈ S, ∀ {x : P} {y : E}, x ∈ t →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ t) → y ∈ (0⁺[𝕜] t : Set E)) :
    (0⁺[𝕜] (⋂₀ S) : Set E) ⊆ ⋂₀ ((fun t : Set P ↦ t.recessionCone 𝕜) '' S) := by
  intro y hy
  rcases hS_nonempty with ⟨x, hx⟩
  refine Set.mem_sInter.mpr fun t ht ↦ ?_
  rcases ht with ⟨t, htS, rfl⟩
  exact hRayToRecession t htS ((Set.mem_sInter.mp hx) t htS) fun a ha ↦
    (Set.mem_sInter.mp <| (Set.mem_recessionCone_iff.mp hy) x hx a ha) t htS

/-- Primitive bridge-layer equality for arbitrary set-families:
if `⋂₀ S` is nonempty and each member `t ∈ S` has the owner-side bridge property that one
base-point nonnegative ray in direction `y` implies `y ∈ 0⁺[𝕜] t`, then the recession cone of the
intersection is the intersection of the member recession cones. -/
theorem recessionCone_sInter_eq_sInter_recessionCone_of_nonneg_ray
    (hS_nonempty : (⋂₀ S).Nonempty)
    (hRayToRecession :
      ∀ t ∈ S, ∀ {x : P} {y : E}, x ∈ t →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ t) → y ∈ (0⁺[𝕜] t : Set E)) :
    (0⁺[𝕜] (⋂₀ S) : Set E) = ⋂₀ ((fun t : Set P ↦ t.recessionCone 𝕜) '' S) := by
  exact Set.Subset.antisymm
    (recessionCone_sInter_subset_sInter_recessionCone_of_nonneg_ray
      (S := S) hS_nonempty hRayToRecession)
    (sInter_recessionCone_subset_recessionCone_sInter (S := S))

/-- Primitive bridge-layer reverse inclusion for indexed intersections:
if `⋂ i, C i` is nonempty and each member `C i` has the owner-side bridge property that one
base-point nonnegative ray in direction `y` implies `y ∈ 0⁺[𝕜] (C i)`, then every recession
direction of the intersection belongs to each member recession cone. -/
theorem recessionCone_iInter_subset_iInter_recessionCone_of_nonneg_ray
    (hC_nonempty : (⋂ i, C i).Nonempty)
    (hRayToRecession :
      ∀ i, ∀ {x : P} {y : E}, x ∈ C i →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C i) → y ∈ (0⁺[𝕜] (C i) : Set E)) :
    (0⁺[𝕜] (⋂ i, C i) : Set E) ⊆ ⋂ i, (0⁺[𝕜] (C i) : Set E) := by
  simpa [Set.sInter_range] using
    (recessionCone_sInter_subset_sInter_recessionCone_of_nonneg_ray
      (S := Set.range C)
      (by simpa [Set.sInter_range] using hC_nonempty)
      (fun t ht {x} {y} hx hRay ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hRayToRecession i hx hRay))

/-- Primitive bridge-layer equality for indexed intersections:
if `⋂ i, C i` is nonempty and each member `C i` has the owner-side bridge property that one
base-point nonnegative ray in direction `y` implies `y ∈ 0⁺[𝕜] (C i)`, then the recession cone of
the intersection is the intersection of the member recession cones. -/
theorem recessionCone_iInter_eq_iInter_recessionCone_of_nonneg_ray
    (hC_nonempty : (⋂ i, C i).Nonempty)
    (hRayToRecession :
      ∀ i, ∀ {x : P} {y : E}, x ∈ C i →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C i) → y ∈ (0⁺[𝕜] (C i) : Set E)) :
    (0⁺[𝕜] (⋂ i, C i) : Set E) = ⋂ i, (0⁺[𝕜] (C i) : Set E) := by
  simpa [Set.sInter_range] using
    (recessionCone_sInter_eq_sInter_recessionCone_of_nonneg_ray
      (S := Set.range C)
      (by simpa [Set.sInter_range] using hC_nonempty)
      (fun t ht {x} {y} hx hRay ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hRayToRecession i hx hRay))

end

end Set

namespace Convex

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {C : I → Set E}
variable {S : Set (Set E)}

/-- The nontrivial inclusion in Corollary 8.3.3 at the intrinsic set-family layer:
for closed convex members of `S` with nonempty intersection, every direction in
`0⁺[𝕜] (⋂₀ S)` lies in each member recession cone. -/
theorem recessionCone_sInter_subset_sInter_recessionCone
    (hS_convex : ∀ t ∈ S, Convex 𝕜 t) (hS_closed : ∀ t ∈ S, IsClosed t)
    (hS_nonempty : (⋂₀ S).Nonempty) :
    0⁺[𝕜] (⋂₀ S) ⊆ ⋂₀ ((fun t : Set E ↦ 0⁺[𝕜] t) '' S) := by
  exact Set.recessionCone_sInter_subset_sInter_recessionCone_of_nonneg_ray
    (S := S) hS_nonempty
    (fun t ht {x} {y} hx hRay ↦
      (hS_convex t ht).mem_recessionCone_of_nonneg_ray (x := x) (y := y) (hS_closed t ht) hRay)

/-- Corollary 8.3.3 at the intrinsic set-family layer:
for closed convex members of `S` with nonempty intersection, the recession cone of `⋂₀ S` is the
intersection of the member recession cones. -/
theorem recessionCone_sInter_eq_sInter_recessionCone
    (hS_convex : ∀ t ∈ S, Convex 𝕜 t) (hS_closed : ∀ t ∈ S, IsClosed t)
    (hS_nonempty : (⋂₀ S).Nonempty) :
    0⁺[𝕜] (⋂₀ S) = ⋂₀ ((fun t : Set E ↦ 0⁺[𝕜] t) '' S) := by
  exact Set.recessionCone_sInter_eq_sInter_recessionCone_of_nonneg_ray
    (S := S) hS_nonempty
    (fun t ht {x} {y} hx hRay ↦
      (hS_convex t ht).mem_recessionCone_of_nonneg_ray (x := x) (y := y) (hS_closed t ht) hRay)

/-- The nontrivial inclusion in Corollary 8.3.3: for closed convex families with nonempty
intersection, every direction in `0⁺[𝕜] (⋂ i, C i)` lies in each `0⁺[𝕜] (C i)`. -/
theorem recessionCone_iInter_subset_iInter_recessionCone
    (hC_convex : ∀ i, Convex 𝕜 (C i)) (hC_closed : ∀ i, IsClosed (C i))
    (hC_nonempty : (⋂ i, C i).Nonempty) :
    0⁺[𝕜] (⋂ i, C i) ⊆ ⋂ i, 0⁺[𝕜] (C i) := by
  simpa [Set.sInter_range] using
    (recessionCone_sInter_subset_sInter_recessionCone (S := Set.range C)
      (fun t ht ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hC_convex i)
      (fun t ht ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hC_closed i)
      (by simpa [Set.sInter_range] using hC_nonempty))

/-- Corollary 8.3.3: if `(C i)_{i ∈ I}` is a family of closed convex subsets of a topological
module over `𝕜` whose intersection is nonempty, then the recession cone
`0⁺[𝕜] (⋂ i, C i)` is the intersection of the recession cones `0⁺[𝕜] (C i)`.
-/
-- Proof sketch: for `y ∈ 0⁺[𝕜] (⋂ i, C i)`, choose `x ∈ ⋂ i, C i`; then the whole ray
-- `x + a • y` stays in every `C i`, so Theorem 8.3 applied to each closed convex `C i` shows
-- `y ∈ 0⁺[𝕜] (C i)`. Conversely, if `y` lies in every `0⁺[𝕜] (C i)`, then every
-- nonnegative translate of every `x ∈ ⋂ i, C i` stays in each `C i`, hence in their intersection.
theorem recessionCone_iInter_eq_iInter_recessionCone
    (hC_convex : ∀ i, Convex 𝕜 (C i)) (hC_closed : ∀ i, IsClosed (C i))
    (hC_nonempty : (⋂ i, C i).Nonempty) :
    0⁺[𝕜] (⋂ i, C i) = ⋂ i, 0⁺[𝕜] (C i) := by
  simpa [Set.sInter_range] using
    (recessionCone_sInter_eq_sInter_recessionCone (S := Set.range C)
      (fun t ht ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hC_convex i)
      (fun t ht ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hC_closed i)
      (by simpa [Set.sInter_range] using hC_nonempty))

end

end Convex

end
