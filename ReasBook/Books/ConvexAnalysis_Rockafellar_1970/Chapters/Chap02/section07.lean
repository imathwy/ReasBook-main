import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_2_7 (from Chap01) -/
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

/-! ### Definition_2_7_10 (from Chap01) -/
section

universe u

variable {R : Type*} [Zero R] [LE R]
variable {M : Type u} {N : Type*}
variable [Sub M] [HasPairing M N R]

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.7.10 introduces the normal cone to a set `C` at a point `a`,
  equivalently the set of dual vectors whose pairings with all displacements `x - a` into `C` are
  nonpositive, with the base-point feasibility condition `a ∈ C` built into the owner so that the
  normal cone is empty off `C`.
- `core/canonical`: the primitive owner data are the source-facing inequalities
  `∀ x ∈ C, 0 ≤ ⟪a - x, x⋆⟫` together with feasibility `a ∈ C`; this keeps the declaration at the
  weakest statement layer needed to define the notion.
- `bridge/view`: under stronger ordered-ring assumptions, `normalCone C a` is exactly the canonical
  dual cone `PointedCone.dual p ((a - ·) '' C)` with the same feasibility condition.
- Primitive data vs derived API: the primitive public owner is the set `normalCone C a`; the
  bridge to `PointedCone.dual` and the companion pointwise-sign theorem
  `mem_normalCone_iff_sub_nonpos` are derived API.
- Ambient structure: the owner uses only subtraction in `M`, a raw pairing `HasPairing M N R`,
  and ordered-zero data on `R`.
- Domain-style sampling: the relevant declarations are `HasPairing`, `HasLinearPairing`,
  `PointedCone.dual`, `PointedCone.mem_dual`, and the adjacent bounded dual owner `barrierCone`.
- Layer target: `source-facing`.
-/
/-- Definition 2.7.10: the normal cone to a set `C` at a point `a`, written `N(a | C)` after
`open scoped Rockafellar`, as a source-facing feasible-point inequality owner. -/
def normalCone (C : Set M) (a : M) : Set N :=
  {xStar | a ∈ C ∧ ∀ x ∈ C, 0 ≤ (⟪a - x, xStar⟫ₚ : R)}

end

/-- Explicit normal-cone notation when both pairing codomain and dual carrier must be fixed. -/
scoped[Rockafellar] notation3:max "N[" R_ "," N_ "](" a " | " C ")" =>
  normalCone (R := R_) (N := N_) C a

/-- Explicit normal-cone notation when only the pairing codomain must be fixed. -/
scoped[Rockafellar] notation3:max "N[" R_ "](" a " | " C ")" =>
  normalCone (R := R_) C a

/-- Canonical source-facing normal-cone notation when the ambient pairing data are inferable. -/
scoped[Rockafellar] notation3:max "N(" a " | " C ")" => normalCone C a

section

universe u

variable {R : Type*} [Zero R] [LE R]
variable {M : Type u} {N : Type*}
variable [Sub M] [HasPairing M N R]

open scoped Rockafellar

/-- Membership in the normal cone is exactly the source-facing feasibility-plus-inequality
condition. -/
@[simp] theorem mem_normalCone_iff {C : Set M} {a : M} {xStar : N} :
    xStar ∈ N[R](a | C) ↔ a ∈ C ∧ ∀ x ∈ C, 0 ≤ (⟪a - x, xStar⟫ₚ : R) :=
  Iff.rfl

end

section

universe u

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type u} {N : Type*}
variable [AddCommMonoid M] [Sub M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [HasLinearPairing M N R]

open scoped Rockafellar

local notation "p" => (HasLinearPairing.pairingLinear : M →ₗ[R] N →ₗ[R] R)

/-- Bridge to the canonical dual-cone owner: over an ordered semiring, the source-facing normal
cone is exactly the feasible-point view of the dual cone of displacement vectors. -/
theorem mem_normalCone_iff_mem_dual_displacement {C : Set M} {a : M} {xStar : N} :
    xStar ∈ N[R](a | C) ↔ a ∈ C ∧ xStar ∈ PointedCone.dual p ((a - ·) '' C) := by
  constructor
  · rintro ⟨ha, hineq⟩
    refine ⟨ha, ?_⟩
    rw [PointedCone.mem_dual]
    intro y hy
    rcases hy with ⟨x, hxC, rfl⟩
    exact hineq x hxC
  · rintro ⟨ha, hdual⟩
    refine ⟨ha, ?_⟩
    intro x hxC
    exact (PointedCone.mem_dual.mp hdual) ⟨x, hxC, rfl⟩

end

section

universe u

variable {R : Type*} [Preorder R] [AddGroup R] [AddLeftMono R]
variable {M : Type u} {N : Type*}
variable [Sub M] [HasPairing M N R] [HasPairingSubLeft M N R]

open scoped Rockafellar

/-- Additive-order companion view: membership in the normal cone is equivalent to the textbook
nonpositivity condition on displacements `x - a`, with only the additive order data needed for the
sign flip. -/
theorem mem_normalCone_iff_sub_nonpos {C : Set M} {a : M} {xStar : N} :
    xStar ∈ N[R](a | C) ↔ a ∈ C ∧ ∀ x ∈ C, (⟪x - a, xStar⟫ₚ : R) ≤ 0 := by
  rw [mem_normalCone_iff]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun x hx => ?_⟩
    have hsub : (⟪a - x, xStar⟫ₚ : R) = - (⟪x - a, xStar⟫ₚ : R) := by
      calc
        (⟪a - x, xStar⟫ₚ : R) = (⟪a, xStar⟫ₚ : R) - (⟪x, xStar⟫ₚ : R) :=
          HasPairingSubLeft.pairing_sub_left a x xStar
        _ = -((⟪x, xStar⟫ₚ : R) - (⟪a, xStar⟫ₚ : R)) := by
            simp [sub_eq_add_neg]
        _ = - (⟪x - a, xStar⟫ₚ : R) := by
            rw [HasPairingSubLeft.pairing_sub_left x a xStar]
    have h' : 0 ≤ (-(⟪x - a, xStar⟫ₚ : R)) := by
      simpa [hsub] using h x hx
    exact neg_nonneg.mp h'
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun x hx => ?_⟩
    have hsub : (⟪a - x, xStar⟫ₚ : R) = - (⟪x - a, xStar⟫ₚ : R) := by
      calc
        (⟪a - x, xStar⟫ₚ : R) = (⟪a, xStar⟫ₚ : R) - (⟪x, xStar⟫ₚ : R) :=
          HasPairingSubLeft.pairing_sub_left a x xStar
        _ = -((⟪x, xStar⟫ₚ : R) - (⟪a, xStar⟫ₚ : R)) := by
            simp [sub_eq_add_neg]
        _ = - (⟪x - a, xStar⟫ₚ : R) := by
            rw [HasPairingSubLeft.pairing_sub_left x a xStar]
    have h' : 0 ≤ (-(⟪x - a, xStar⟫ₚ : R)) := neg_nonneg.mpr (h x hx)
    simpa [hsub] using h'

variable [AddRightMono R]

/-- A normal vector at `a` defines a pairing functional whose supremum on `C` is attained at
`a`. -/
theorem isMaxOn_pairing_of_mem_normalCone {C : Set M} {a : M} {xStar : N}
    (hxStar : xStar ∈ N[R](a | C)) :
    IsMaxOn (fun x : M ↦ (⟪x, xStar⟫ₚ : R)) C a := by
  rcases (mem_normalCone_iff_sub_nonpos.mp hxStar) with ⟨_, hxStar_nonpos⟩
  rw [isMaxOn_iff]
  intro x hxC
  have hsub : (⟪x - a, xStar⟫ₚ : R) = (⟪x, xStar⟫ₚ : R) - (⟪a, xStar⟫ₚ : R) :=
    HasPairingSubLeft.pairing_sub_left x a xStar
  have hle : (⟪x, xStar⟫ₚ : R) - (⟪a, xStar⟫ₚ : R) ≤ 0 := by
    simpa [hsub] using hxStar_nonpos x hxC
  exact sub_nonpos.mp hle

end

/-! ### Definition_2_7_11 (from Chap01) -/
section

universe u v w

variable {R : Type w} [Preorder R]
variable {M : Type u} {N : Type v}
variable [HasPairing M N R]

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.7.11 introduces the barrier cone of a subset as the set of
  vectors `x*` such that the values `⟪x, x*⟫` are bounded above on that subset.
- `core/canonical`: the primitive owner abstraction is the set-level barrier cone
  `barrierCone C : Set N`.
- `bridge/view`: `mem_barrier_iff_exists_bound` rewrites membership into the textbook
  quantifier form with
  an explicit bound `β : R`.
- Primitive data vs derived API: the source-facing owner is `barrierCone C`; the explicit-bound
  formulation is derived API through membership.
- Ambient structure: the source-facing owner uses only a pairing and order on the codomain.
- Domain-style sampling: the relevant owner/style declarations in this domain are `BddAbove`,
  `bddAbove_def`, and the adjacent owner `normalCone`.
-/

variable (R)
/-- Definition 2.7.11 (primitive owner): the barrier predicate of `C`, i.e. the set of vectors
`x*` for which the pairing image `{⟪x, x*⟫ | x ∈ C}` is bounded above. -/
def barrierCone (C : Set M) : Set N :=
  {xStar | BddAbove ((fun x : M ↦ (⟪x, xStar⟫ₚ : R)) '' C)}

end

/-- Canonical barrier-cone notation with explicit codomain parameter; the carrier is inferred from
surrounding terms. -/
scoped[Rockafellar] notation3:max "barr[" R "](" C ")" => (@barrierCone R _ _ _ _ C)

section

universe u v w

variable {R : Type w} [Preorder R]
variable {M : Type u} {N : Type v}
variable [HasPairing M N R]

open scoped Rockafellar

/-- Membership in the set-level barrier owner is exactly bounded-above pairing image. -/
@[simp] theorem mem_barrier_iff {C : Set M} {xStar : N} :
    xStar ∈ barr[R](C) ↔
      BddAbove ((fun x : M ↦ (⟪x, xStar⟫ₚ : R)) '' C) := by
  rfl

/-- Membership in `barr[R](C)` is exactly the textbook boundedness condition with an explicit
upper bound. -/
theorem mem_barrier_iff_exists_bound {C : Set M} {xStar : N} :
    xStar ∈ barr[R](C) ↔ ∃ β : R, ∀ x ∈ C, ⟪x, xStar⟫ₚ ≤ β := by
  rw [mem_barrier_iff]
  rw [bddAbove_def]
  constructor
  · rintro ⟨β, hβ⟩
    exact ⟨β, fun x hx ↦ hβ _ ⟨x, hx, rfl⟩⟩
  · rintro ⟨β, hβ⟩
    exact ⟨β, fun _ hx ↦ by rcases hx with ⟨x, hxC, rfl⟩; exact hβ x hxC⟩

end

/-! ### Proposition_2_7_12 (from Chap01) -/
section

universe u v w

variable {R : Type w} [MulZeroClass R] [Preorder R] [PosMulMono R]
variable {M : Type u} {N : Type v}
variable [Sub M]
variable [SMul R N]
variable [HasPairing M N R]
variable [HasPairingSMulRight M N R]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.7.12 says the source-owned set `normalCone C a` is a convex
  cone.
- `core/canonical`: the primitive owner data are the feasibility condition `a ∈ C` and the
  pointwise nonnegativity inequalities defining `normalCone C a`.
- `bridge/view`: the source-facing notation `N(a | C)` exposes this primitive owner directly
  without forcing a bundled cone bridge.
- `Primitive data vs derived API`: the primitive public object is the source-facing set
  `normalCone C a`; both cone closure and convexity are proved directly from the primitive
  inequality owner at weak order assumptions.
- Domain-style sampling: the relevant declarations are `normalCone`,
  `Set.isCone_iff_forall_pos_smul_subset`, pairing-right linearity bridges
  (`pairing_smul_right`, `HasPairingAddRight.pairing_add_right`), and `convex_iff_add_mem`.
- Layer target: `source-facing`.
-/

open scoped Rockafellar

/-- The normal cone to any subset is a cone in the sense of Definition 2.5.9. -/
theorem normalCone_isCone (C : Set M) (a : M) :
    Set.IsCone R ((N[R](a | C)) : Set N) := by
  rw [Set.isCone_iff_forall_pos_smul_subset]
  intro c hc xStar hxStar
  rcases Set.mem_smul_set.mp hxStar with ⟨yStar, hyStar, rfl⟩
  rw [mem_normalCone_iff] at hyStar ⊢
  rcases hyStar with ⟨haC, hyStar_mem⟩
  refine ⟨haC, ?_⟩
  intro x hxC
  have hsmul :
      (⟪a - x, c • yStar⟫ₚ : R) = c * (⟪a - x, yStar⟫ₚ : R) :=
    pairing_smul_right (x := a - x) (c := c) (y := yStar)
  have hnonneg : (0 : R) ≤ c * (⟪a - x, yStar⟫ₚ : R) := by
    exact mul_nonneg (le_of_lt hc) (hyStar_mem x hxC)
  simpa [hsmul] using hnonneg

end

section

universe u v w

variable {R : Type w} [Semiring R] [PartialOrder R] [PosMulMono R] [AddLeftMono R]
variable {M : Type u} {N : Type v}
variable [Sub M]
variable [AddCommMonoid N] [SMul R N]
variable [HasPairing M N R]
variable [HasPairingSMulRight M N R]
variable [HasPairingAddRight M N R]

open scoped Rockafellar

/-- Proposition 2.7.12: the normal cone to a set `C` at `a` is convex, hence together with
`normalCone_isCone` it is a convex cone in the source sense. -/
theorem normalCone_convex (C : Set M) (a : M) :
    Convex R ((N[R](a | C)) : Set N) := by
  refine convex_iff_add_mem.2 ?_
  intro xStar hxStar yStar hyStar α β hα hβ hαβ
  rw [mem_normalCone_iff] at hxStar hyStar ⊢
  rcases hxStar with ⟨haC, hxineq⟩
  rcases hyStar with ⟨_, hyineq⟩
  refine ⟨haC, ?_⟩
  intro x hxC
  have hxα : 0 ≤ α * (⟪a - x, xStar⟫ₚ : R) := mul_nonneg hα (hxineq x hxC)
  have hyβ : 0 ≤ β * (⟪a - x, yStar⟫ₚ : R) := mul_nonneg hβ (hyineq x hxC)
  have hpair :
      (⟪a - x, α • xStar + β • yStar⟫ₚ : R)
        = α * (⟪a - x, xStar⟫ₚ : R) + β * (⟪a - x, yStar⟫ₚ : R) := by
    calc
      (⟪a - x, α • xStar + β • yStar⟫ₚ : R)
          = (⟪a - x, α • xStar⟫ₚ : R) + (⟪a - x, β • yStar⟫ₚ : R) := by
              exact HasPairingAddRight.pairing_add_right (a - x) (α • xStar) (β • yStar)
      _ = α * (⟪a - x, xStar⟫ₚ : R) + β * (⟪a - x, yStar⟫ₚ : R) := by
            rw [pairing_smul_right, pairing_smul_right]
  exact hpair ▸ add_nonneg hxα hyβ

/-- Proposition 2.7.12 in canonical source-facing owner form: the normal cone is a convex cone. -/
theorem normalCone_isConvexCone (C : Set M) (a : M) :
    Set.IsConvexCone R ((N[R](a | C)) : Set N) :=
  ⟨normalCone_isCone (C := C) (a := a), normalCone_convex (C := C) (a := a)⟩

end

/-! ### Proposition_2_7_13 (from Chap01) -/
section

universe u v w

variable {R : Type w} [Mul R] [Zero R] [Preorder R] [PosMulMono R]
variable {M : Type u} {N : Type v}
variable [SMul R N]
variable [HasPairing M N R]
variable [HasPairingSMulRight M N R]

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.7.13 states that the barrier cone is a convex cone.
- `core/canonical`: the source-facing owner is the set-level barrier predicate
  `barr[R](C)`.
- `bridge/view`: the closure properties are proved directly from the membership bridge
  `mem_barrier_iff_exists_bound`, so the proposition works directly at the source-facing
  set-owner layer.
- Primitive data vs derived API: boundedness witnesses in `R` are primitive owner data; cone and
  convex closure are derived by transporting those witnesses through positive scaling and convex
  combinations.
-/

/-- Proposition 2.7.13, set-level cone form: the barrier cone is a cone. -/
theorem barrierCone_isCone (C : Set M) :
    Set.IsCone R (barr[R](C) : Set N) := by
  refine (Set.isCone_iff_forall_pos_smul_subset (K := (barr[R](C) : Set N))).2 ?_
  intro c hc xStar hxStar
  rcases Set.mem_smul_set.mp hxStar with ⟨yStar, hyStar, rfl⟩
  rw [mem_barrier_iff_exists_bound] at hyStar ⊢
  rcases hyStar with ⟨β, hβ⟩
  refine ⟨c * β, ?_⟩
  intro x hxC
  rw [pairing_smul_right]
  exact mul_le_mul_of_nonneg_left (hβ x hxC) (le_of_lt hc)

end

section

universe u v w

variable {R : Type w} [Semiring R] [PartialOrder R] [PosMulMono R] [AddLeftMono R]
variable {M : Type u} {N : Type v}
variable [AddCommMonoid N] [SMul R N]
variable [HasPairing M N R]
variable [HasPairingSMulRight M N R]
variable [HasPairingAddRight M N R]

open scoped Rockafellar

/-- Proposition 2.7.13, set-level convexity form: the barrier cone is convex. -/
theorem barrierCone_convex (C : Set M) :
    Convex R (barr[R](C) : Set N) := by
  refine convex_iff_add_mem.2 ?_
  intro xStar hxStar yStar hyStar a b ha hb hab
  rw [mem_barrier_iff_exists_bound] at hxStar hyStar ⊢
  rcases hxStar with ⟨βx, hβx⟩
  rcases hyStar with ⟨βy, hβy⟩
  refine ⟨a * βx + b * βy, ?_⟩
  intro x hxC
  have hxle : (⟪x, xStar⟫ₚ : R) ≤ βx := hβx x hxC
  have hyle : (⟪x, yStar⟫ₚ : R) ≤ βy := hβy x hxC
  have hpair :
      (⟪x, a • xStar + b • yStar⟫ₚ : R) =
        a * (⟪x, xStar⟫ₚ : R) + b * (⟪x, yStar⟫ₚ : R) := by
    calc
      (⟪x, a • xStar + b • yStar⟫ₚ : R)
          = (⟪x, a • xStar⟫ₚ : R) + (⟪x, b • yStar⟫ₚ : R) := by
              exact HasPairingAddRight.pairing_add_right x (a • xStar) (b • yStar)
      _ = a * (⟪x, xStar⟫ₚ : R) + b * (⟪x, yStar⟫ₚ : R) := by
            rw [pairing_smul_right, pairing_smul_right]
  refine hpair ▸ add_le_add ?_ ?_
  · exact mul_le_mul_of_nonneg_left hxle ha
  · exact mul_le_mul_of_nonneg_left hyle hb

/-- Proposition 2.7.13 in canonical source-facing owner form: the barrier cone is a convex cone. -/
theorem barrierCone_isConvexCone (C : Set M) :
    Set.IsConvexCone R (barr[R](C) : Set N) :=
  ⟨barrierCone_isCone C, barrierCone_convex C⟩

end
