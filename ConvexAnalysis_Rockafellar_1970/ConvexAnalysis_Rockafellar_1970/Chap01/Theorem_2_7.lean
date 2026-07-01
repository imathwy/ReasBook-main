import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open scoped Pointwise

section SpanAffineBridge

variable {R : Type v} [Ring R]
variable {E : Type u} [AddCommGroup E] [Module R E]

namespace Set

/-- If `0 ∈ s`, then the linear span of `s` (viewed as an affine subspace) coincides with its
affine span. -/
theorem span_toAffineSubspace_eq_affineSpan_of_zero_mem {s : Set E} (h0 : 0 ∈ s) :
    (Submodule.span R s).toAffineSubspace = affineSpan R s := by
  ext x
  change x ∈ (Submodule.span R s : Set E) ↔ x ∈ (affineSpan R s : Set E)
  simpa [insert_eq_of_mem h0] using
    (congrArg (fun t : Set E ↦ x ∈ t) (affineSpan_insert_zero (k := R) s).symm)

/-- If `0 ∈ s`, the carriers of the linear span and affine span of `s` coincide. -/
theorem span_eq_affineSpan_of_zero_mem {s : Set E} (h0 : 0 ∈ s) :
    (Submodule.span R s : Set E) = (affineSpan R s : Set E) := by
  exact congrArg (fun t : AffineSubspace R E ↦ (t : Set E))
    (span_toAffineSubspace_eq_affineSpan_of_zero_mem (R := R) (s := s) h0)

end Set
end SpanAffineBridge

section PointedConeTheorem

/-
Source/core/bridge triage:
- `source-facing`: Theorem 2.7 identifies, for a convex cone `K ⊆ ℝ^n` containing `0`, the least
  linear subspace containing `K` with `K - K`, identifies that same set with the affine hull
  `aff K`, and identifies the greatest linear subspace contained in `K` with `(-K) ∩ K`.
- `core/canonical`: the source is stated in `ℝ^n`, but the owner-side constructions only use the
  `PointedCone` owner plus the ambient linear objects `Submodule.span R (K : Set E)`,
  `affineSpan R (K : Set E)`, and `K.lineal`. The item is split at the weakest natural layer:
  affine-span bridge statements at `[PartialOrder R]`, while difference-set and lineality bridges
  remain at `[LinearOrder R]`.
- `bridge/view`: this file now keeps short owner-level equalities first
  (`span_eq_sup_neg`, `span_toAffineSubspace_eq_affineSpan`, `lineal_eq_inf_neg`) and
  derives the textbook set equalities as source-facing bridge theorems.
- Primitive data vs derived API: the pointed cone `K` is primitive owner data. The set-level
  formulas `(K : Set E) - (K : Set E)` and `(- (K : Set E)) ∩ (K : Set E)` are source-facing
  bridge surfaces derived from owner theorems.
- Domain-style sampling: the relevant owner declarations are `PointedCone R E`,
  `Submodule.span` with `Submodule.subset_span` and `Submodule.span_le`,
  `affineSpan_insert_zero`, `Submodule.coe_sup`, `Submodule.coe_inf`, and
  `PointedCone.gc_ofSubmodule_lineal`/`PointedCone.ofSubmodule_lineal`/`PointedCone.mem_lineal`.
- Layer target: mixed. Owner-level abstraction is primary; set-theoretic textbook equalities are
  retained as explicit bridge/view surfaces.
-/

/- Theorem 2.7 (1): the source's least-subspace statement for a pointed convex cone `K ⊆ R^n` is
the canonical owner construction `Submodule.span` together with its containment and minimality
lemmas `Submodule.subset_span` and `Submodule.span_le`. -/
recall Submodule.span
recall Submodule.subset_span
recall Submodule.span_le

namespace PointedCone

open Set

section SpanDiff

variable {R : Type v} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

/-- Owner form of Theorem 2.7 (1): the least subspace containing a pointed cone is the supremum
of the cone and its opposite. -/
theorem span_eq_sup_neg (K : PointedCone R E) :
    (Submodule.span R (K : Set E) : PointedCone R E) = K ⊔ -K := by
  ext x
  constructor
  · intro hx
    change x ∈ (Submodule.span R (K : Set E) : Set E) at hx
    have hxadd : x ∈ (K : Set E) + (- (K : Set E)) := by
      refine Submodule.closure_induction ?_ ?_ ?_ hx
      · refine Set.mem_add.2 ⟨0, K.zero_mem, 0, ?_, by simp⟩
        exact by simp [Set.mem_neg, K.zero_mem]
      · intro y z _ _ hy hz
        rcases Set.mem_add.1 hy with ⟨u, hu, v, hv, rfl⟩
        rcases Set.mem_add.1 hz with ⟨u', hu', v', hv', rfl⟩
        refine Set.mem_add.2 ⟨u + u', K.add_mem hu hu', v + v', ?_, ?_⟩
        · exact Set.mem_neg.2 <| by
            simpa [neg_add, add_comm] using K.add_mem (Set.mem_neg.1 hv') (Set.mem_neg.1 hv)
        · simp [add_left_comm, add_comm]
      · intro a y hy
        by_cases ha : 0 ≤ a
        · refine Set.mem_add.2 ⟨a • y, K.smul_mem ha hy, 0, ?_, by simp⟩
          exact by simp [Set.mem_neg, K.zero_mem]
        · have hna : 0 ≤ -a := by
            exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge ha))
          have hayneg : a • y ∈ - (K : Set E) := by
            refine Set.mem_neg.2 ?_
            simpa [neg_smul] using K.smul_mem hna hy
          exact Set.mem_add.2 ⟨0, K.zero_mem, a • y, hayneg, by simp⟩
    change x ∈ ((K ⊔ -K : PointedCone R E) : Set E)
    simpa [Submodule.coe_sup] using hxadd
  · intro hx
    change x ∈ (Submodule.span R (K : Set E) : Set E)
    change x ∈ ((K ⊔ -K : PointedCone R E) : Set E) at hx
    have hxadd : x ∈ (K : Set E) + (- (K : Set E)) := by
      simpa [Submodule.coe_sup] using hx
    rcases Set.mem_add.1 hxadd with ⟨u, hu, w, hw, huw⟩
    have huSpan : u ∈ (Submodule.span R (K : Set E) : Set E) := Submodule.subset_span hu
    have hwSpan : w ∈ (Submodule.span R (K : Set E) : Set E) := by
      have hnegwSpan : -w ∈ (Submodule.span R (K : Set E) : Set E) :=
        Submodule.subset_span (Set.mem_neg.1 hw)
      simpa using Submodule.neg_mem (Submodule.span R (K : Set E)) hnegwSpan
    simpa [huw] using Submodule.add_mem (Submodule.span R (K : Set E)) huSpan hwSpan

/-- Theorem 2.7 (1), set form: the underlying set of the least containing subspace of a
pointed convex cone is the difference set `K - K`. -/
theorem span_eq_sub (K : PointedCone R E) :
    (Submodule.span R (K : Set E) : Set E) = (K : Set E) - (K : Set E) := by
  simpa [sub_eq_add_neg, Submodule.coe_sup] using
    congrArg (fun C : PointedCone R E ↦ (C : Set E)) K.span_eq_sup_neg

end SpanDiff

section Affine

variable {R : Type v} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

/-- Owner form of Theorem 2.7 (2): for a pointed cone, the linear span (viewed as an affine
subspace) is exactly the affine span. -/
theorem span_toAffineSubspace_eq_affineSpan (K : PointedCone R E) :
    (Submodule.span R (K : Set E)).toAffineSubspace = affineSpan R (K : Set E) := by
  simpa using
    (Set.span_toAffineSubspace_eq_affineSpan_of_zero_mem
      (R := R) (s := (K : Set E)) K.zero_mem)

/-- Set-level bridge for Theorem 2.7 (2): linear span and affine span have the same carrier. -/
theorem span_eq_affineSpan (K : PointedCone R E) :
    (Submodule.span R (K : Set E) : Set E) = (affineSpan R (K : Set E) : Set E) := by
  simpa using Set.span_eq_affineSpan_of_zero_mem (R := R) (s := (K : Set E)) K.zero_mem

end Affine

section SpanDiff

variable {R : Type v} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

/-- Theorem 2.7 (2): the difference set of a pointed convex cone coincides with its affine hull. -/
-- Proof sketch: combine `span_eq_sub` with `span_eq_affineSpan`.
theorem sub_eq_affineSpan (K : PointedCone R E) :
    (K : Set E) - (K : Set E) = (affineSpan R (K : Set E) : Set E) := by
  calc
    (K : Set E) - (K : Set E) = (Submodule.span R (K : Set E) : Set E) := K.span_eq_sub.symm
    _ = (affineSpan R (K : Set E) : Set E) := K.span_eq_affineSpan

end SpanDiff

section Lineal

variable {R : Type v} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

/- Theorem 2.7 (3): the source's greatest-subspace statement for a pointed convex cone `K ⊆ R^n`
is that a submodule lies in `K` exactly when it lies in `K ∩ (-K)`, i.e. in the pointed-cone
infimum `K ⊓ -K`. -/
recall PointedCone.ofSubmodule
recall PointedCone.gc_ofSubmodule_lineal
recall PointedCone.ofSubmodule_lineal
recall PointedCone.mem_lineal

/-- Owner equality for Theorem 2.7 (3): lineality is the infimum of a cone and its opposite. -/
theorem lineal_eq_inf_neg (K : PointedCone R E) :
    (K.lineal : PointedCone R E) = K ⊓ -K := by
  simp [PointedCone.ofSubmodule_lineal]

/-- Owner form of Theorem 2.7 (3): a submodule is contained in `K` iff it is contained in
`K.lineal`. This is the greatest-submodule characterization at the canonical lineality owner. -/
theorem submodule_le_iff_le_lineal (K : PointedCone R E) (S : Submodule R E) :
    (S : PointedCone R E) ≤ K ↔ S ≤ K.lineal := by
  simpa using (PointedCone.gc_ofSubmodule_lineal (R := R) (E := E) S K)

/-- Bridge form of Theorem 2.7 (3): a submodule lies in `K` iff it lies in `K ⊓ -K`. -/
theorem submodule_le_iff_le_inf_neg (K : PointedCone R E) (S : Submodule R E) :
    (S : PointedCone R E) ≤ K ↔ (S : PointedCone R E) ≤ K ⊓ -K := by
  constructor
  · intro hSK x hx
    refine ⟨hSK hx, ?_⟩
    exact Set.mem_neg.2 (hSK (S.neg_mem hx))
  · intro hSinf x hx
    exact (hSinf hx).1

/-- Theorem 2.7 (3), set form at the lineality owner: the carrier of `K.lineal` is
`(-K) ∩ K`. -/
theorem lineal_eq_neg_inter (K : PointedCone R E) :
    (K.lineal : Set E) = (- (K : Set E)) ∩ (K : Set E) := by
  ext x
  simp [and_comm]

/-- Bridge set form of Theorem 2.7 (3): the carrier of `K ⊓ -K` is `(-K) ∩ K`. -/
theorem inf_neg_eq_neg_inter (K : PointedCone R E) :
    ((K ⊓ -K : PointedCone R E) : Set E) = (- (K : Set E)) ∩ (K : Set E) := by
  simpa [K.lineal_eq_inf_neg] using K.lineal_eq_neg_inter

end Lineal

end PointedCone

end PointedConeTheorem

end
