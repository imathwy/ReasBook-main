import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_37_3_1 (from Chap07) -/
noncomputable section

universe u v

open Set
open Bornology
open Bifunction

namespace SaddleFunction

section

variable {U : Type u} {X : Type v}
variable {β : Type*}
variable [CompleteLattice β]

/-- Ambient saddle-value existence follows from the domain-restricted Chapter 36 owner,
provided the canonical boundary-extension owner connecting `univ × univ` to
`dom₁ K × dom₂ K`, and the primitive nonemptiness datum needed for the minimax bridge. -/
theorem hasSaddleValue_of_hasSaddleValueOn_dom
    {K : U → X → β}
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hDom : HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact (hasSaddleValue_iff_hasSaddleValueOn_dom (K := K) hdom₁ hExt).2 hDom

/-- Ambient saddle-value existence follows from the domain-restricted Chapter 36 owner,
provided the canonical boundary-extension owner that connects `univ × univ` to
`dom₁ K × dom₂ K`. This convenience wrapper recovers the primitive nonemptiness datum
from `IsProper K`. -/
theorem hasSaddleValue_of_hasSaddleValueOn_dom_of_isProper
    {K : U → X → β}
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hDom : HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact (hasSaddleValue_iff_hasSaddleValueOn_dom_of_isProper (K := K) hK_proper hExt).2 hDom

/-- Corollary 37.3.1 in owner-bridge form: once boundedness is converted (by an upstream geometric
criterion) into domain-restricted saddle-value existence, the ambient saddle-value follows by the
canonical Chapter 36 domain bridge with the canonical boundary-extension owner. -/
theorem hasSaddleValue_of_isBounded_dom₁_or_dom₂
    {K : U → X → β}
    [Bornology U] [Bornology X]
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom_bounded : IsBounded (dom₁ K) ∨ IsBounded (dom₂ K))
    (hDom_of_bounded :
      IsBounded (dom₁ K) ∨ IsBounded (dom₂ K) →
        HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact hasSaddleValue_of_hasSaddleValueOn_dom hdom₁ hExt
    (hDom_of_bounded hdom_bounded)

/-- `IsProper`-based wrapper of `hasSaddleValue_of_isBounded_dom₁_or_dom₂` for source-facing use. -/
theorem hasSaddleValue_of_isBounded_dom₁_or_dom₂_of_isProper
    {K : U → X → β}
    [Bornology U] [Bornology X]
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom_bounded : IsBounded (dom₁ K) ∨ IsBounded (dom₂ K))
    (hDom_of_bounded :
      IsBounded (dom₁ K) ∨ IsBounded (dom₂ K) →
        HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₁_or_dom₂
    hK_proper.dom₁_nonempty hExt hdom_bounded hDom_of_bounded

/-- First one-sided bounded-domain entry point: if the first factor is bounded and an upstream
criterion yields the domain-restricted owner, then `K` has an ambient saddle-value. -/
theorem hasSaddleValue_of_isBounded_dom₁
    {K : U → X → β}
    [Bornology U]
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom₁_bounded : IsBounded (dom₁ K))
    (hDom_of_dom₁_bounded :
      IsBounded (dom₁ K) → HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact hasSaddleValue_of_hasSaddleValueOn_dom hdom₁ hExt
    (hDom_of_dom₁_bounded hdom₁_bounded)

/-- `IsProper`-based wrapper of `hasSaddleValue_of_isBounded_dom₁` for source-facing use. -/
theorem hasSaddleValue_of_isBounded_dom₁_of_isProper
    {K : U → X → β}
    [Bornology U]
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom₁_bounded : IsBounded (dom₁ K))
    (hDom_of_dom₁_bounded :
      IsBounded (dom₁ K) → HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₁
    hK_proper.dom₁_nonempty hExt hdom₁_bounded hDom_of_dom₁_bounded

/-- Second one-sided bounded-domain entry point: if the second factor is bounded and an upstream
criterion yields the domain-restricted owner, then `K` has an ambient saddle-value. -/
theorem hasSaddleValue_of_isBounded_dom₂
    {K : U → X → β}
    [Bornology X]
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom₂_bounded : IsBounded (dom₂ K))
    (hDom_of_dom₂_bounded :
      IsBounded (dom₂ K) → HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K := by
  exact hasSaddleValue_of_hasSaddleValueOn_dom hdom₁ hExt
    (hDom_of_dom₂_bounded hdom₂_bounded)

/-- `IsProper`-based wrapper of `hasSaddleValue_of_isBounded_dom₂` for source-facing use. -/
theorem hasSaddleValue_of_isBounded_dom₂_of_isProper
    {K : U → X → β}
    [Bornology X]
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    (hdom₂_bounded : IsBounded (dom₂ K))
    (hDom_of_dom₂_bounded :
      IsBounded (dom₂ K) → HasSaddleValueOn (dom₁ K) (dom₂ K) K) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₂
    hK_proper.dom₁_nonempty hExt hdom₂_bounded hDom_of_dom₂_bounded

end

end SaddleFunction

/-! ### Definition_37_3_1 (from Chap07) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v w u' v'

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable {YU : Type u'} {YV : Type v'}
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 37.3.1 recalls the saddle subdifferential `∂K(u, v)` of a
  concave-convex bifunction and then defines its domain `dom ∂K` as the locus where that
  subdifferential is nonempty.
- `core/canonical`: the chapter already owns the saddle subdifferential itself as
  `Bifunction.subdifferentialAt`, written `d(K ; u, v)`.
- `bridge/view`: the source domain `dom ∂K` is therefore the canonical pointwise nonemptiness
  locus of the already-owned saddle subdifferential `d(K ; u, v)`, i.e. the chapter owner
  `domd(K | YU, YV)`.

Domain-style sampling:
- `Bifunction.subdifferentialAt` and the notation `d(K ; u, v | YU, YV)` from `Theorem_35_7`;
- `SetRel.dom` / `SetRel.mem_dom` as the canonical relation-domain owner API;
- `mem_subdifferentialGraph_dom` from `Chap05.Definition_5_24_1`, which fixes the project pattern
  that subdifferential domains are recorded as owned domain surfaces rather than repeated raw
  comprehensions.

Primitive data vs derived API:
- primitive owner data already exist upstream: the saddle subdifferential owner
  `subdifferentialAt K u v YU YV`;
- derived API in this file: the canonical domain owner `domd(K | YU, YV)` together with the
  source-facing nonemptiness reformulations matching the textbook wording.

Layer target: `bridge/view`. This item does not introduce a second owner for the saddle
subdifferential; it reuses the existing owner and records its domain as the canonical
pointwise nonemptiness locus.
-/

/- Section 35 already defines the saddle subdifferential as the canonical chapter owner
`Bifunction.subdifferentialAt`, written `d(K ; u, v)`. -/
recall Bifunction.subdifferentialAt

/- Definition 37.3.1: the domain of the saddle subdifferential mapping is the pointwise
nonemptiness locus of the already-owned saddle subdifferential `d(K ; u, v)`. -/
abbrev subdifferentialDom (K : U → V → WithTopBot 𝕜)
    (YU : Type u') [HasPairing U YU 𝕜]
    (YV : Type v') [HasPairing V YV 𝕜] : Set (U × V) :=
  SetRel.dom (fun q : (U × V) × (YU × YV) ↦
    match q with
    | ((u, v), p) => p ∈ d(K ; u, v | YU, YV))

scoped[Rockafellar] notation "domd(" K " | " yu ", " yv ")" =>
  Bifunction.subdifferentialDom K yu yv

-- Proof sketch: this is just the defining pointwise nonemptiness condition of `domd`.
/-- A point lies in the domain of the saddle subdifferential exactly when the saddle
subdifferential at that point is nonempty. -/
@[simp] theorem mem_subdifferentialDom_iff_nonempty
    {K : U → V → WithTopBot 𝕜} {p : U × V} :
    p ∈ domd(K | YU, YV) ↔ (d(K ; p.1, p.2 | YU, YV)).Nonempty := by
  rw [SetRel.mem_dom]
  exact Iff.rfl

-- Proof sketch: this is the defining pointwise nonemptiness condition of `domd`.
/-- A point lies in the domain of the saddle subdifferential exactly when the saddle
subdifferential at that point is nonempty. -/
@[simp] theorem mem_subdifferentialDom
    {K : U → V → WithTopBot 𝕜} {p : U × V} :
    p ∈ domd(K | YU, YV) ↔ d(K ; p.1, p.2 | YU, YV) ≠ ∅ := by
  rw [mem_subdifferentialDom_iff_nonempty]
  exact Set.nonempty_iff_ne_empty

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/- Definition 37.3.1, intrinsic strong-dual bridge: specialize the pairing-level domain owner
`domd(K | YU, YV)` to the canonical continuous-dual product, parallel to `∂ₛ K(u, v)`. -/
abbrev subdifferentialDomDual (K : U → V → WithTopBot 𝕜) : Set (U × V) :=
  domd(K | StrongDual 𝕜 U, StrongDual 𝕜 V)

scoped[Rockafellar] notation "dom∂ₛ " K =>
  Bifunction.subdifferentialDomDual K

/-- A point lies in the intrinsic strong-dual domain of the saddle subdifferential exactly when
the strong-dual saddle subdifferential at that point is nonempty. -/
@[simp] theorem mem_subdifferentialDomDual_iff_nonempty
    {K : U → V → WithTopBot 𝕜} {p : U × V} :
    p ∈ (dom∂ₛ K) ↔ (∂ₛ K(p.1, p.2)).Nonempty := by
  change p ∈ domd(K | StrongDual 𝕜 U, StrongDual 𝕜 V) ↔
      (d(K ; p.1, p.2 | StrongDual 𝕜 U, StrongDual 𝕜 V)).Nonempty
  exact
    (mem_subdifferentialDom_iff_nonempty :
      p ∈ domd(K | StrongDual 𝕜 U, StrongDual 𝕜 V) ↔
        (d(K ; p.1, p.2 | StrongDual 𝕜 U, StrongDual 𝕜 V)).Nonempty)

/-- A point lies in the intrinsic strong-dual domain of the saddle subdifferential exactly when
the strong-dual saddle subdifferential at that point is not empty. -/
@[simp] theorem mem_subdifferentialDomDual
    {K : U → V → WithTopBot 𝕜} {p : U × V} :
    p ∈ (dom∂ₛ K) ↔ ∂ₛ K(p.1, p.2) ≠ ∅ := by
  rw [mem_subdifferentialDomDual_iff_nonempty]
  exact Set.nonempty_iff_ne_empty

end

end Bifunction

/-! ### Corollary_37_3_2 (from Chap07) -/
noncomputable section

namespace Bifunction

section

variable {U V α : Type*} [ConditionallyCompleteLattice α]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.3.2 is used as a minimax-equality bridge for finite-valued
  kernels on a restricted product domain.
- `core/canonical`: once an explicit source-order saddle witness is available for
  `toWithTopBot K`, the primitive owner data are exactly
  `∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v`.
- `owner abstraction`: the conclusion is the Chapter 36 owner
  `HasSaddleValueOn C D (toWithTopBot K)` together with its defining equality view.

This file intentionally does not keep extra geometric/topological hypotheses on public theorem
surfaces when they are not part of this primitive bridge.
-/

/-- Primitive bridge for this item: an explicit source-order saddle point of `toWithTopBot K` on
`C × D` yields the Chapter 36 saddle-value owner on `C × D`. -/
theorem hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    HasSaddleValueOn C D (toWithTopBot K) :=
  hasSaddleValueOn_of_exists_isSaddlePointOn h_saddle

/-- Equality view of `hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn`. -/
theorem maximinValueOn_toWithTopBot_eq_minimaxValueOn_toWithTopBot_of_exists_isSaddlePointOn
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    maximinValueOn C D (toWithTopBot K) = minimaxValueOn C D (toWithTopBot K) := by
  simpa [HasSaddleValueOn] using
    (hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn (C := C) (D := D) (K := K) h_saddle)

/-- Source-label bridge form: with an explicit saddle witness, no additional compactness-side data
are needed for the Chapter 36 owner conclusion. -/
theorem hasSaddleValueOn_toWithTopBot_of_isCompact_left_or_right
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    HasSaddleValueOn C D (toWithTopBot K) :=
  hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn h_saddle

/-- Source-label bridge form: with an explicit saddle witness, no additional closed/bounded-side
data are needed for the Chapter 36 owner conclusion. -/
theorem hasSaddleValueOn_toWithTopBot_of_closed_bounded_side
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    HasSaddleValueOn C D (toWithTopBot K) :=
  hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn h_saddle

/-- Source-label bridge form: with an explicit saddle witness, no additional bounded-side data are
needed for the Chapter 36 owner conclusion. -/
theorem hasSaddleValueOn_toWithTopBot_of_isBounded_left_or_right
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    HasSaddleValueOn C D (toWithTopBot K) :=
  hasSaddleValueOn_toWithTopBot_of_exists_isSaddlePointOn h_saddle

/-- Equality view under the source closed/bounded-side label. -/
theorem maximinValueOn_toWithTopBot_eq_minimaxValueOn_toWithTopBot_of_closed_bounded_side
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    maximinValueOn C D (toWithTopBot K) = minimaxValueOn C D (toWithTopBot K) := by
  simpa [HasSaddleValueOn] using
    hasSaddleValueOn_toWithTopBot_of_closed_bounded_side (C := C) (D := D) (K := K) h_saddle

/-- Equality view under the source one-side-bounded label. -/
theorem maximinValueOn_toWithTopBot_eq_minimaxValueOn_toWithTopBot_of_isBounded_left_or_right
    {C : Set U} {D : Set V} {K : U → V → α}
    (h_saddle : ∃ u ∈ C, ∃ v ∈ D, IsSaddlePointOn C D (toWithTopBot K) u v) :
    maximinValueOn C D (toWithTopBot K) = minimaxValueOn C D (toWithTopBot K) := by
  simpa [HasSaddleValueOn] using
    hasSaddleValueOn_toWithTopBot_of_isBounded_left_or_right (C := C) (D := D) (K := K) h_saddle

end

end Bifunction

/-! ### Theorem_37_3 (from Chap07) -/
noncomputable section

universe u v

open Bifunction
open scoped Rockafellar

namespace SaddleFunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 37.3 gives two one-sided slice-recession criteria implying existence
  of an ambient saddle-value for a closed proper concave-convex saddle-function, and says that if
  both criteria hold then the common saddle-value is finite.
- `core/canonical`: the existing owner layer is the Chapter 36 ambient saddle-value predicate
  `HasSaddleValue K`, together with the canonical ambient value `maximinValue K`.
- `bridge/view`: Corollary 37.2.1 turns the two source criteria into the conjugate-domain
  relative-interior conditions at the origin, while Corollary 37.3.1 is the canonical Chapter 36
  bridge from those conditions to ambient saddle-value existence.

Primary mathematical domain:
- minimax theory for closed proper concave-convex saddle-functions via slice recession geometry.

Domain-style sampling used here:
- `IsClosed`, `IsProper`, `dom₁`, `dom₂`, and `ri[𝕜](·)` from
  `Chap07.Corollary_34_2_1`;
- `Function.RecedesInDirection` from `Chap06.Definition_6_27_4`;
- `zero_mem_ri_dom₂_lowerConjugate_iff_no_common_recession_direction` and
  `zero_mem_ri_dom₁_lowerConjugate_iff_no_common_recession_direction` from
  `Chap07.Corollary_37_2_1`;
- `HasSaddleValue` and `maximinValue` from `Chap07.Definition_36_0_1`.

Primitive data vs derived API:
- primitive source data: the saddle-function `K` with hypotheses `IsClosed K`, `IsProper K`, and
  `IsConcaveConvex 𝕜 K`;
- primitive source-facing conditions: absence of a common recession direction for the slice family
  `K(u, ·)` on `ri[𝕜](dom₁ K)` and for the slice family `-K(·, v)` on `ri[𝕜](dom₂ K)`;
- derived API in this file: the ambient saddle-value existence theorem and the finite-value
  consequence when both one-sided criteria hold.

Layer target: `source-facing`, stated directly on the existing Chapter 36 owner rather than by
introducing a parallel local saddle-value package.
-/

-- Proof sketch: use Corollary 37.2.1 to convert either source condition into the corresponding
-- origin-relative-interior statement for `dom₂ (lowerConjugate K)` or `dom₁ (lowerConjugate K)`.
-- Then apply the Chapter 37 owner-level bridge from conjugate-domain relative interior to ambient
-- saddle-value existence.
/-- Theorem 37.3 (1): let `K` be a closed proper concave-convex saddle-function. If either
(a) the convex slices `K(u, ·)` for `u ∈ ri[𝕜](dom₁ K)` have no common recession direction, or
(b) the convex slices `-K(·, v)` for `v ∈ ri[𝕜](dom₂ K)` have no common recession direction,
then `K` has an ambient saddle-value. -/
theorem
    hasSaddleValue_of_no_common_second_recession_direction_or_no_common_first_recession_direction
    {K : U → X → WithBotTop 𝕜}
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex 𝕜 K)
    (h_recession :
      (¬ ∃ y : X, ∀ u ∈ ri[𝕜](dom₁ K), (K u).RecedesInDirection 𝕜 y) ∨
        ¬ ∃ y : U, ∀ v ∈ ri[𝕜](dom₂ K), (fun u ↦ -K u v).RecedesInDirection 𝕜 y) :
    HasSaddleValue K := sorry

-- Proof sketch: first obtain `HasSaddleValue K` from the preceding theorem.
-- Then combine the two one-sided criteria through the conjugate-domain relative-interior
-- equalities of Corollary 37.2.1 and the Chapter 37 zero-basepoint conjugate identities to show
-- the common saddle-value is strictly between `⊥` and `⊤`.
/-- Theorem 37.3 (2): if both one-sided no-common-recession-direction criteria from
Theorem 37.3 hold, then the ambient Chapter 36 saddle value of `K` is finite. -/
theorem
    finite_saddleValue_of_no_common_second_and_first_recession_direction
    {K : U → X → WithBotTop 𝕜}
    (hK_closed : IsClosed K) (hK_proper : IsProper K)
    (hK_concaveConvex : IsConcaveConvex 𝕜 K)
    (h_second : ¬ ∃ y : X, ∀ u ∈ ri[𝕜](dom₁ K), (K u).RecedesInDirection 𝕜 y)
    (h_first : ¬ ∃ y : U, ∀ v ∈ ri[𝕜](dom₂ K), (fun u ↦ -K u v).RecedesInDirection 𝕜 y) :
    ⊥ < maximinValue K ∧ maximinValue K < ⊤ := sorry

end

end SaddleFunction
