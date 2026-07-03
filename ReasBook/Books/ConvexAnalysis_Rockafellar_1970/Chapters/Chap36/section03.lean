

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_36_3_1 (from Chap07) -/
noncomputable section

universe u v

open scoped Rockafellar
namespace SaddleFunction

section

open Bifunction

variable {U : Type u} {V : Type v}
variable {β : Type*}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 36.3.1 says that an ambient saddle-point of a saddle bifunction lies
  in the effective domain, so the associated ambient Chapter 36 saddle value is finite.
- `core/canonical`: the primitive bridge datum is `IsProper K`, which is exactly what is needed
  to recover domain membership and pointwise finiteness from an ambient saddle-point.
- `bridge/view`: the file stays on the canonical Chapter 34/36 owners
  `dom`, `IsSaddlePoint`, `maximinValue`, and `minimaxValue`.

Primary domain:
- minimax and saddle-point theory for ambient-vs-domain bridges.

Layer target: `source-facing`, at the primitive owner layer needed for this corollary.
-/

-- Proof sketch: use the properness-only ambient/domain saddle-point bridge from Theorem 36.3 and
-- read off product-domain membership directly.
/-- If `(u, v)` is an ambient saddle-point for `K`, then `(u, v)` lies in `dom K`,
assuming only the primitive properness owner `IsProper K`. -/
theorem mem_dom_of_isSaddlePoint
    [Preorder β] [Bot β] [Top β]
    {K : U → V → β}
    (hK_proper : IsProper K)
  {u : U} {v : V}
  (hsp : IsSaddlePoint K u v) :
  (u, v) ∈ dom K :=
  (mem_dom_and_isSaddlePointOn_dom_of_isSaddlePoint
    hK_proper hsp).1

-- Proof sketch: first place `(u, v)` in `dom K` from the properness-only ambient/domain bridge;
-- then apply the Chapter 34 product-domain finiteness owner.
/-- An ambient saddle-point is finite pointwise, at the primitive owner layer:
`⊥ < K u v` and `K u v < ⊤`. -/
theorem finite_value_of_isSaddlePoint
    [Preorder β] [Bot β] [Top β]
    {K : U → V → β}
    (hK_proper : IsProper K)
    {u : U} {v : V}
    (hsp : IsSaddlePoint K u v) :
    ⊥ < K u v ∧ K u v < ⊤ := by
  exact bot_lt_and_lt_top_of_mem_dom (mem_dom_of_isSaddlePoint hK_proper hsp)

-- Proof sketch: use primitive finiteness of `K u v` from the previous theorem and identify both
-- ambient Chapter 36 values with `K u v` via the canonical saddle-point value owners.
/-- An ambient saddle-point forces finiteness of both ambient Chapter 36 values:
`maximinValue K` and `minimaxValue K`. -/
theorem finite_saddleValue_of_isSaddlePoint
    [CompleteLattice β]
    {K : U → V → β}
    (hK_proper : IsProper K)
    {u : U} {v : V}
    (hsp : IsSaddlePoint K u v) :
    (⊥ < maximinValue K ∧ maximinValue K < ⊤) ∧
      (⊥ < minimaxValue K ∧ minimaxValue K < ⊤) := by
  have hfin : ⊥ < K u v ∧ K u v < ⊤ :=
    finite_value_of_isSaddlePoint hK_proper hsp
  have hvalue_max : maximinValue K = K u v :=
    maximinValue_eq_of_isSaddlePoint hsp
  have hvalue_min : minimaxValue K = K u v :=
    minimaxValue_eq_of_isSaddlePoint hsp
  refine ⟨?_, ?_⟩
  · exact ⟨by simpa [hvalue_max] using hfin.1, by simpa [hvalue_max] using hfin.2⟩
  · exact ⟨by simpa [hvalue_min] using hfin.1, by simpa [hvalue_min] using hfin.2⟩

end

end SaddleFunction

/-! ### Theorem_36_3 (from Chap07) -/
noncomputable section

universe u v

open Set
open scoped Rockafellar
namespace SaddleFunction

section ExtensionOwner

open Bifunction

variable {U : Type u} {X : Type v}
variable {β : Type*}
variable [LT β] [Bot β] [Top β]

/-- Canonical boundary-extension owner for a saddle bifunction restricted to its own Chapter 34
effective slices `dom₁ K × dom₂ K`. -/
theorem isSaddleExtensionOn_dom
    {K : U → X → β}
    (h_dom₂_top : ∀ ⦃u : U⦄ ⦃x : X⦄, u ∈ dom₁ K → x ∉ dom₂ K → K u x = ⊤)
    (h_dom₁_bot : ∀ ⦃u : U⦄ ⦃x : X⦄, u ∉ dom₁ K → x ∈ dom₂ K → K u x = ⊥) :
    IsSaddleExtensionOn K K (dom₁ K) (dom₂ K) := by
  refine ⟨?_, h_dom₂_top, h_dom₁_bot⟩
  intro u x hu hx
  rfl

end ExtensionOwner

section ValueBridge

open Bifunction

variable {U : Type u} {X : Type v}
variable {β : Type*}
variable [CompleteLattice β]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 36.3 compares the ambient minimax/saddle problem on `univ × univ`
  with the domain-restricted one on `dom₁ K × dom₂ K`.
- `core/canonical`: the primitive owners are `dom₁`, `dom₂`, `maximinValueOn`,
  `minimaxValueOn`, and `IsSaddlePointOn` (used through `Function.swap` for source order).
- `bridge/view`: instead of freezing this file at the stronger recognition route
  (`IsClosed`/`IsConcaveConvex ℝ` on `EReal`), this pass isolates the primitive bridge data that
  are actually used by the ambient-to-domain transfer:
  - outside `dom₂`, rows from `dom₁` take value `⊤`;
  - outside `dom₁`, columns in `dom₂` take value `⊥`;
  - properness for obtaining witness points in both domains.
  This keeps the public owner layer mathematically explicit and codomain-generic.

Primary domain:
- minimax and saddle-point theory for domain-restricted saddle-function problems.

Domain-style sampling used here:
- `SaddleFunction.dom₁` from `Chap07.Defn_34_3`;
- `SaddleFunction.dom₂` from `Chap07.Defn_34_3`;
- `Bifunction.maximinValueOn` from `Chap07.Definition_36_0_1`;
- `Bifunction.minimaxValueOn` from `Chap07.Definition_36_0_1`.

Primitive data vs derived API:
- primitive owner data used here: `K`, `dom₁ K`, `dom₂ K`, and the two outside-domain saturation
  bridges listed above; the value bridge uses only `(dom₁ K).Nonempty` where a witness is
  needed, while the later saddle-point bridge uses the chapter owner `IsProper K` to recover
  both domain witnesses canonically;
- derived API in this file: ambient/domain equality for Chapter 36 minimax owners and the
  ambient/domain saddle-point equivalence.

Layer target: `source-facing`, expressed through the canonical owner objects rather than through a
parallel local minimax wrapper.

Ambient-assumption minimization:
- no topological, scalar, normed, or finite-dimensional ambient structure is needed at this owner
  layer;
- the value-comparison layer below uses the canonical lattice condition
  `[CompleteLattice β]` required by the Chapter 36 minimax owners;
- the ambient/domain saddle-point bridge is separated afterward to the weaker order layer
  `[Preorder β] [Bot β] [Top β]`.
-/

private theorem rowInf_eq_bot_of_not_mem_dom₁
    (K : U → X → β)
    {u : U} (hu : u ∉ dom₁ K) :
    (⨅ x : X, K u x) = ⊥ := by
  classical
  rcases not_forall.mp hu with ⟨x, hx⟩
  have hux : K u x = ⊥ := by
    by_contra hux
    exact hx ((bot_lt_iff_ne_bot).2 hux)
  refine le_antisymm ?_ bot_le
  calc
    (⨅ x : X, K u x) ≤ K u x := iInf_le _ x
    _ = ⊥ := hux

private theorem rowInf_eq_rowInf_dom₂_of_mem_dom₁
    (K : U → X → β)
    (h_dom₂_top : ∀ ⦃u : U⦄ ⦃x : X⦄, u ∈ dom₁ K → x ∉ dom₂ K → K u x = ⊤)
    {u : U} (hu : u ∈ dom₁ K) :
    (⨅ x : X, K u x) = ⨅ x ∈ dom₂ K, K u x := by
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ ?_
    intro x hx
    exact iInf_le _ x
  · refine le_iInf ?_
    intro x
    by_cases hx : x ∈ dom₂ K
    · exact iInf₂_le x hx
    · simp [h_dom₂_top hu hx]

/-- Ambient-to-domain maximin bridge at primitive owner level: if every row indexed by `dom₁ K`
extends `K` by the canonical boundary-extension owner
`IsSaddleExtensionOn K K (dom₁ K) (dom₂ K)`, then the Chapter 36 maximin value on `univ × univ`
equals the value on `dom₁ K × dom₂ K`. -/
theorem maximinValue_eq_maximinValueOn_dom
    {K : U → X → β}
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K)) :
    maximinValue K = maximinValueOn (dom₁ K) (dom₂ K) K := by
  have h_dom₂_top : ∀ ⦃u : U⦄ ⦃x : X⦄, u ∈ dom₁ K → x ∉ dom₂ K → K u x = ⊤ :=
    fun {u} {x} hu hx ↦ IsSaddleExtensionOn.top_of_mem_left_of_not_mem_right hExt hu hx
  have h :
      (⨆ u : U, ⨅ x : X, K u x) = ⨆ u ∈ dom₁ K, ⨅ x ∈ dom₂ K, K u x := by
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro u
      by_cases hu : u ∈ dom₁ K
      · calc
          (⨅ x : X, K u x) = ⨅ x ∈ dom₂ K, K u x :=
            rowInf_eq_rowInf_dom₂_of_mem_dom₁ K h_dom₂_top hu
          _ ≤ ⨆ x ∈ dom₁ K, ⨅ y ∈ dom₂ K, K x y := le_iSup₂_of_le u hu le_rfl
      · calc
          (⨅ x : X, K u x) = ⊥ := rowInf_eq_bot_of_not_mem_dom₁ K hu
          _ ≤ ⨆ x ∈ dom₁ K, ⨅ y ∈ dom₂ K, K x y := bot_le
    · refine iSup₂_le ?_
      intro u hu
      calc
        (⨅ x ∈ dom₂ K, K u x) = ⨅ x : X, K u x :=
          (rowInf_eq_rowInf_dom₂_of_mem_dom₁ K h_dom₂_top hu).symm
        _ ≤ ⨆ x : U, ⨅ y : X, K x y := le_iSup (fun x : U ↦ ⨅ y : X, K x y) u
  simpa [maximinValue, maximinValueOn] using h

/-- Ambient-to-domain minimax bridge at primitive owner level: if `dom₁ K` is nonempty, rows from
`dom₁ K` and `dom₂ K` satisfy the canonical boundary-extension owner
`IsSaddleExtensionOn K K (dom₁ K) (dom₂ K)`, then the Chapter 36 minimax value on `univ × univ`
equals the value on `dom₁ K × dom₂ K`. -/
theorem minimaxValue_eq_minimaxValueOn_dom
    {K : U → X → β}
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K)) :
    minimaxValue K = minimaxValueOn (dom₁ K) (dom₂ K) K := by
  exact minimaxValue_eq_minimaxValueOn_of_extension hExt hdom₁

/-- Properness wrapper for the ambient-to-domain minimax bridge: the primitive nonemptiness datum
`(dom₁ K).Nonempty` is recovered from the canonical Chapter 34 owner `IsProper K`. -/
theorem minimaxValue_eq_minimaxValueOn_dom_of_isProper
    {K : U → X → β}
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K)) :
    minimaxValue K = minimaxValueOn (dom₁ K) (dom₂ K) K :=
  minimaxValue_eq_minimaxValueOn_dom hK_proper.dom₁_nonempty hExt

/-- Ambient/domain bridge for the Chapter 36 saddle-value owner at primitive data level:
under the boundary-extension owner and the primitive witness `(dom₁ K).Nonempty` required by the
minimax transfer, ambient and domain-restricted saddle-value owners are equivalent. -/
theorem hasSaddleValue_iff_hasSaddleValueOn_dom
    {K : U → X → β}
    (hdom₁ : (dom₁ K).Nonempty)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K)) :
    HasSaddleValue K ↔ HasSaddleValueOn (dom₁ K) (dom₂ K) K := by
  change maximinValue K = minimaxValue K ↔
    maximinValueOn (dom₁ K) (dom₂ K) K = minimaxValueOn (dom₁ K) (dom₂ K) K
  simp [maximinValue_eq_maximinValueOn_dom (K := K) hExt,
    minimaxValue_eq_minimaxValueOn_dom (K := K) hdom₁ hExt]

/-- Properness wrapper for `hasSaddleValue_iff_hasSaddleValueOn_dom`: the primitive nonemptiness
input is supplied by the canonical Chapter 34 owner `IsProper K`. -/
theorem hasSaddleValue_iff_hasSaddleValueOn_dom_of_isProper
    {K : U → X → β}
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K)) :
    HasSaddleValue K ↔ HasSaddleValueOn (dom₁ K) (dom₂ K) K :=
  hasSaddleValue_iff_hasSaddleValueOn_dom hK_proper.dom₁_nonempty hExt

end ValueBridge

section SaddlePointBridge

open Bifunction
local notation "IsSaddlePointOn" => Bifunction.IsSaddlePointOn

variable {U : Type u} {X : Type v}
variable {β : Type*}
variable [Preorder β] [Bot β] [Top β]

private theorem isSaddlePoint_imp_mem_dom_and_isSaddlePointOn_dom
    (K : U → X → β)
    (hK_proper : IsProper K)
    {u : U} {v : X}
    (hsp : IsSaddlePoint K u v) :
    (u, v) ∈ dom K ∧ IsSaddlePointOn (dom₁ K) (dom₂ K) K u v := by
  rcases hK_proper.dom₁_nonempty with ⟨u0, hu0⟩
  rcases hK_proper.dom₂_nonempty with ⟨x0, hx0⟩
  rcases (isSaddlePoint_iff_source_order : IsSaddlePoint K u v ↔ _).1 hsp with
    ⟨hu_max, hv_min⟩
  have hu : u ∈ dom₁ K := by
    intro x
    exact lt_of_lt_of_le (hu0 v) <| le_trans (hu_max u0) (hv_min x)
  have hv : v ∈ dom₂ K := by
    intro y
    exact lt_of_le_of_lt (le_trans (hu_max y) (hv_min x0)) (hx0 u)
  refine ⟨mem_dom_mk.mpr ⟨hu, hv⟩, (isSaddlePointOn_iff_source_order hu hv).2 ?_⟩
  exact ⟨fun y _ ↦ hu_max y, fun x _ ↦ hv_min x⟩

/-- Properness-only half of the Chapter 36 ambient/domain saddle-point bridge:
an ambient source-order saddle point of `K` lies in `dom K`, and its restriction to
`dom₁ K × dom₂ K` is a restricted saddle point. -/
theorem mem_dom_and_isSaddlePointOn_dom_of_isSaddlePoint
    {K : U → X → β}
    (hK_proper : IsProper K)
    {u : U} {v : X}
    (hsp : IsSaddlePoint K u v) :
    (u, v) ∈ dom K ∧ IsSaddlePointOn (dom₁ K) (dom₂ K) K u v :=
  isSaddlePoint_imp_mem_dom_and_isSaddlePointOn_dom K hK_proper hsp

private theorem isSaddlePointOn_dom_imp_isSaddlePoint
    (K : U → X → β)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    {u : U} {v : X}
    (huv : (u, v) ∈ dom K)
    (hsp : IsSaddlePointOn (dom₁ K) (dom₂ K) K u v) :
    IsSaddlePoint K u v := by
  rcases mem_dom_mk.mp huv with ⟨hu, hv⟩
  rcases (isSaddlePointOn_iff_source_order hu hv).1 hsp with
    ⟨hu_max, hv_min⟩
  refine (isSaddlePoint_iff_source_order : IsSaddlePoint K u v ↔ _).2 ?_
  refine ⟨?_, ?_⟩
  · intro y
    by_cases hy : y ∈ dom₁ K
    · exact hu_max y hy
    · have hbot : K y v = ⊥ :=
        IsSaddleExtensionOn.bot_of_not_mem_left_of_mem_right hExt hy hv
      have hbot_le : ⊥ ≤ K u v := le_of_lt (hu v)
      simpa [hbot] using hbot_le
  · intro x
    by_cases hx : x ∈ dom₂ K
    · exact hv_min x hx
    · have htop : K u x = ⊤ :=
        IsSaddleExtensionOn.top_of_mem_left_of_not_mem_right hExt hu hx
      have hv_le_top : K u v ≤ ⊤ := le_of_lt (hv u)
      simpa [htop] using hv_le_top

/-- Ambient/domain saddle-point bridge at primitive owner level: under properness and the same
boundary-extension owner used above, ambient source-order saddle points of `K` coincide with
restricted saddle points together with product-domain membership `(u, v) ∈ dom K`. Membership is
explicit on the right because `IsSaddlePointOn` itself does not encode constraints. -/
theorem isSaddlePoint_iff_mem_dom_and_isSaddlePointOn_dom
    {K : U → X → β}
    (hK_proper : IsProper K)
    (hExt : IsSaddleExtensionOn K K (dom₁ K) (dom₂ K))
    {u : U} {v : X} :
    IsSaddlePoint K u v ↔
      (u, v) ∈ dom K ∧ IsSaddlePointOn (dom₁ K) (dom₂ K) K u v := by
  constructor
  · exact isSaddlePoint_imp_mem_dom_and_isSaddlePointOn_dom K hK_proper
  · rintro ⟨huv, hsp⟩
    exact isSaddlePointOn_dom_imp_isSaddlePoint K hExt huv hsp

end SaddlePointBridge

end SaddleFunction
