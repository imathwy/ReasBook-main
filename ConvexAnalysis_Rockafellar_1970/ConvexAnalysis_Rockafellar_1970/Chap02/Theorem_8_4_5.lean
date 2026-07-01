import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

variable {𝕜 : Type v} [Zero 𝕜] [LE 𝕜]
variable {E : Type u} [AddGroup E] [SMul 𝕜 E]
variable {P : Type w} [AddAction E P] [HAdd P E P]

open scoped Pointwise
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 8.4.5 identifies the lineality set of a set `C` with the set
  of translation vectors that leave `C` invariant under the intrinsic translation owner
  `Set.vaddSet`, i.e. `y +ᵥ C = C`. The public owner in this file is `Set.lineal 𝕜 C`,
  rendered as `lin[𝕜](C)`.
- `bridge/view`: the chapter recession theorem is stated in singleton-addition form
  `C + {y} ⊆ C`. The core theorems here are parameterized by the primitive bridge hypothesis
  `hrec : ∀ z, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C`; this keeps Theorem 8.4.5 at the weakest owner layer.
  The convex specializations are downstream bridge corollaries using
  `Convex.mem_recessionCone_iff_vadd_subset_self`.
- Primitive data vs derived API: the owner data remains the set `Set.lineal 𝕜 C`; the
  translation-invariance criteria are derived API, with the `vadd` theorem as source-facing and
  the singleton-addition theorem as its bridge view.
- Domain-style sampling used here: `Set.lineal`,
  `Set.lineal_eq_neg_recessionCone_inter_recessionCone`, `Set.mem_lineal_iff`, and
  `Convex.mem_recessionCone_iff_vadd_subset_self`.
- Layer target: this remains a direct source-facing set equality, not a bundled cone statement.
- Scalar-strength note: the stronger assumptions
  `[Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]` are needed only for the
  convex bridge theorem from Theorem 8.1 (its converse direction uses floor/interpolation over
  scalar intervals), not for the lineality-via-bridge argument itself.
--/

namespace Set

/-- Core owner-layer form of Theorem 8.4.5: if recession membership is characterized by
translation inclusion (`hrec`), then `y ∈ lin[𝕜](C)` exactly when translation by `y` fixes `C`. -/
-- Proof sketch: rewrite `y ∈ lin[𝕜](C)` by `Set.mem_lineal_iff` into recession conditions for `y`
-- and `-y`, then use the bridge hypothesis `hrec` in each direction.
theorem mem_lineal_iff_vadd_eq_self {C : Set P}
    (hrec : ∀ z : E, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C) {y : E} :
    y ∈ lin[𝕜](C) ↔ y +ᵥ C = C := by
  rw [mem_lineal_iff]
  constructor
  · rintro ⟨hypos, hyneg⟩
    have hypos' : y +ᵥ C ⊆ C := (hrec y).1 hypos
    have hyneg' : (-y) +ᵥ C ⊆ C := (hrec (-y)).1 hyneg
    refine Set.Subset.antisymm hypos' ?_
    intro x hx
    have hxneg : (-y) +ᵥ x ∈ C :=
      hyneg' <| Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩
    exact Set.mem_vadd_set.mpr ⟨(-y) +ᵥ x, hxneg, by
      simp [vadd_neg_vadd]⟩
  · intro hy
    have hypos : y ∈ 0⁺[𝕜] C := (hrec y).2 hy.le
    have hyneg : (-y) +ᵥ C ⊆ C := by
      intro x hx
      rcases Set.mem_vadd_set.mp hx with ⟨z, hz, rfl⟩
      have hz' : z ∈ y +ᵥ C := hy.ge hz
      rcases Set.mem_vadd_set.mp hz' with ⟨w, hw, hwz⟩
      have hcancel : (-y) +ᵥ z = w := by
        rw [← hwz]
        simp [neg_vadd_vadd]
      exact hcancel ▸ hw
    exact ⟨hypos, (hrec (-y)).2 hyneg⟩

/-- Theorem 8.4.5 (source-facing form): under the recession/translation bridge hypothesis `hrec`,
`lin[𝕜](C)` is exactly the set of vectors `y` such that translating `C` by `y` leaves `C`
unchanged. -/
theorem lineal_eq_setOf_vadd_eq_self {C : Set P}
    (hrec : ∀ z : E, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C) :
    lin[𝕜](C) = {y : E | y +ᵥ C = C} := by
  ext y
  rw [Set.mem_setOf_eq, mem_lineal_iff_vadd_eq_self hrec]

end Set

end

section

universe u v

variable {𝕜 : Type v} [Zero 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [SMul 𝕜 E]

open scoped Pointwise
open scoped Rockafellar

private theorem add_singleton_eq_vaddSet (a : E) (A : Set E) :
    A + {a} = a +ᵥ A := by
  rw [Set.add_singleton, ← Set.image_vadd]
  ext x
  simp [vadd_eq_add, add_comm]

namespace Set

/-- Bridge view in singleton-addition form. -/
theorem mem_lineal_iff_add_singleton_eq_self {C : Set E}
    (hrec : ∀ z : E, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C) {y : E} :
    y ∈ lin[𝕜](C) ↔ C + {y} = C := by
  rw [mem_lineal_iff_vadd_eq_self hrec]
  constructor <;> intro hy
  · calc
      C + {y} = y +ᵥ C := add_singleton_eq_vaddSet y C
      _ = C := hy
  · calc
      y +ᵥ C = C + {y} := (add_singleton_eq_vaddSet y C).symm
      _ = C := hy

/-- Singleton-addition bridge view of Theorem 8.4.5 under the same bridge hypothesis `hrec`. -/
theorem lineal_eq_setOf_add_singleton_eq_self {C : Set E}
    (hrec : ∀ z : E, z ∈ 0⁺[𝕜] C ↔ z +ᵥ C ⊆ C) :
    lin[𝕜](C) = {y : E | C + {y} = C} := by
  ext y
  rw [Set.mem_setOf_eq, mem_lineal_iff_add_singleton_eq_self hrec]

end Set

end

section

universe u v

variable {𝕜 : Type v} [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

open scoped Pointwise
open scoped Rockafellar

namespace Convex

/-- Convex owner-prefix specialization of `Set.mem_lineal_iff_vadd_eq_self`, instantiated with
Theorem 8.1's recession/translation bridge. -/
theorem mem_lineal_iff_vadd_eq_self {C : Set E} (hC : Convex 𝕜 C) {y : E} :
    y ∈ lin[𝕜](C) ↔ y +ᵥ C = C := by
  exact Set.mem_lineal_iff_vadd_eq_self
    (hrec := hC.mem_recessionCone_iff_vadd_subset_self)

/-- Convex singleton-addition specialization. -/
theorem mem_lineal_iff_add_singleton_eq_self {C : Set E} (hC : Convex 𝕜 C) {y : E} :
    y ∈ lin[𝕜](C) ↔ C + {y} = C := by
  exact Set.mem_lineal_iff_add_singleton_eq_self
    (hrec := hC.mem_recessionCone_iff_vadd_subset_self)

/-- Convex set-equality specialization of Theorem 8.4.5 in intrinsic translation form. -/
theorem lineal_eq_setOf_vadd_eq_self {C : Set E} (hC : Convex 𝕜 C) :
    lin[𝕜](C) = {y : E | y +ᵥ C = C} := by
  exact Set.lineal_eq_setOf_vadd_eq_self
    (hrec := hC.mem_recessionCone_iff_vadd_subset_self)

/-- Convex set-equality specialization in singleton-addition form. -/
theorem lineal_eq_setOf_add_singleton_eq_self {C : Set E} (hC : Convex 𝕜 C) :
    lin[𝕜](C) = {y : E | C + {y} = C} := by
  exact Set.lineal_eq_setOf_add_singleton_eq_self
    (hrec := hC.mem_recessionCone_iff_vadd_subset_self)

end Convex

end
