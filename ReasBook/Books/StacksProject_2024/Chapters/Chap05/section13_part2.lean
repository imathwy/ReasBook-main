import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_13_6 (from Chap05) -/
open Set TopologicalSpace
open scoped Topology

universe u v

section

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable {I : Type v}

/- Domain-style sampling for shrinking open covers along a compact subset:
- primary domain: shrinking lemmas in locally compact Hausdorff spaces
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover.exists_shrinking`,
  `TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement`,
  `IsCompact.exists_open_between_and_isCompact_closure`,
  `exists_iUnion_eq_closure_subset`
- best owner abstraction: `IsCompact`

Layer triage:
- `source-facing`: the Stacks lemma below, which attaches prescribed tuplewise intersections to a
  fixed compact subset `Z`
- `core/canonical`: the compact-normal tuplewise shrinking owner
  `TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement`, together with the compact
  lifting API `IsCompact.exists_open_between_and_isCompact_closure`
- `bridge/view`: the ambient shrinking family `V`, whose cover property, closure control, and
  tuplewise containment are all derived from the compact owner data on the subtype of `Z`

Primitive data are exactly the compact subset `Z`, the ambient open family `U`, the prescribed
tuplewise opens `W`, and the two compatibility hypotheses on `Z`. The shrinking family `V` and its
closure/intersection properties are derived output, so the public API should live on the compact
owner `IsCompact` rather than as a parallel global wrapper.
-/

namespace IsCompact

/- Companion recall: the compact-normal tuplewise shrinking owner for open covers is the
chapter theorem `TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement`; the compact
subset theorem below is the corresponding source-facing bridge, used through the owner call shape
`hZ.exists_open_shrinking_with_prescribed_intersections`. -/
recall TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement

/-- A shrinking of an open family whose closures stay in the ambient opens and whose
`(p + 1)`-fold intersections land in the prescribed opens along a compact subset. -/
class IsOpenShrinkingWithPrescribedIntersections
    (Z : Set X) (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) : Prop where
  /-- The shrunken opens still cover the compact subset. -/
  cover : Z ⊆ ⋃ i, V i
  /-- The closure of each shrunken open stays inside the corresponding ambient open. -/
  closure_subset (i : I) : closure (V i : Set X) ⊆ U i
  /-- Every `(p + 1)`-fold intersection of the shrunken family lands in the prescribed open. -/
  tuplewise_subset (σ : Fin (p + 1) → I) : (⋂ j, (V (σ j) : Set X)) ⊆ W σ

/-- Helper for Lemma 5.13.6: compactness of `Z` reduces the ambient cover to finitely many
indices, reindexed by the corresponding subtype. -/
private lemma finite_support_reduction
    {Z : Set X} (hZ : IsCompact Z) (U : I → Opens X) (hcover : Z ⊆ ⋃ i, U i) :
    ∃ s : Finset I, Z ⊆ ⋃ i : {i // i ∈ s}, (U i.1 : Set X) := by
  -- Extract a finite subcover of `Z`, then rewrite it as a subtype-indexed union.
  obtain ⟨s, hs⟩ :=
    hZ.elim_finite_subcover (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hcover
  refine ⟨s, ?_⟩
  intro z hz
  rcases mem_iUnion₂.1 (hs hz) with ⟨i, hi, hzi⟩
  exact mem_iUnion.2 ⟨⟨i, hi⟩, hzi⟩

/-- Helper for Lemma 5.13.6: extending a subtype-indexed shrinking by `⊥` outside the chosen
finite support preserves the cover, closure, and tuplewise containment data. -/
private lemma extend_by_bot_preserves_shrinking_data
    [DecidableEq I] {Z : Set X} {p : ℕ} {s : Finset I} {U : I → Opens X}
    {W : (Fin (p + 1) → I) → Opens X} {V₀ : {i // i ∈ s} → Opens X}
    (hV₀ :
      IsOpenShrinkingWithPrescribedIntersections Z p
        (fun i : {i // i ∈ s} ↦ U i.1)
        (fun σ : Fin (p + 1) → {i // i ∈ s} ↦ W (fun j ↦ (σ j).1))
        V₀) :
    IsOpenShrinkingWithPrescribedIntersections Z p U W
      (fun i ↦ if hi : i ∈ s then V₀ ⟨i, hi⟩ else ⊥) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- The cover over the finite subtype is unchanged after extending by empty opens.
    intro z hz
    rcases mem_iUnion.1 (hV₀.cover hz) with ⟨i, hzi⟩
    refine mem_iUnion.2 ⟨i.1, ?_⟩
    simpa using hzi
  · -- Closure control is immediate on supported indices and trivial outside the support.
    intro i
    by_cases hi : i ∈ s
    · simpa [hi] using hV₀.closure_subset ⟨i, hi⟩
    · intro x hx
      have hx' : x ∈ closure ((⊥ : Opens X) : Set X) := by
        simpa [hi] using hx
      have hclosure : closure (((⊥ : Opens X) : Set X)) = (∅ : Set X) := by
        change closure (∅ : Set X) = ∅
        exact closure_empty
      have : x ∈ (∅ : Set X) := by
        simpa [hclosure] using hx'
      exact False.elim this
  · -- If every tuple entry lies in the support, reduce to the subtype theorem; otherwise the
    -- tuple intersection is empty because one factor is `⊥`.
    intro σ
    by_cases hσ : ∀ j, σ j ∈ s
    · let σ₀ : Fin (p + 1) → {i // i ∈ s} := fun j ↦ ⟨σ j, hσ j⟩
      simpa [σ₀, hσ] using hV₀.tuplewise_subset σ₀
    · have hσ' : ∃ j, σ j ∉ s := by
        simpa [not_forall] using hσ
      rcases hσ' with ⟨j, hj⟩
      intro x hx
      have hxj : x ∈ ((fun i ↦ if hi : i ∈ s then V₀ ⟨i, hi⟩ else ⊥) (σ j) : Set X) :=
        mem_iInter.1 hx j
      have : False := by
        simpa [hj] using hxj
      exact False.elim this

/-- Helper for Lemma 5.13.6: the case `p = 0` comes from shrinking a finite subcover of the
prescribed singleton neighborhoods. -/
private theorem exists_open_shrinking_with_prescribed_intersections_zero
    {Z : Set X} (hZ : IsCompact Z) (U : I → Opens X) (W : (Fin 1 → I) → Opens X)
    (hcover : Z ⊆ ⋃ i, U i)
    (hW_subset : ∀ σ, (W σ : Set X) ⊆ ⋂ j, U (σ j))
    (hW_on_Z : ∀ σ, (W σ : Set X) ∩ Z = (⋂ j, U (σ j)) ∩ Z) :
    ∃ V : I → Opens X, IsOpenShrinkingWithPrescribedIntersections Z 0 U W V := by
  classical
  obtain ⟨s, hscover⟩ := finite_support_reduction (Z := Z) hZ U hcover
  let I₀ := {i // i ∈ s}
  let W₀ : I₀ → Set X := fun i ↦ W (fun _ : Fin 1 ↦ i.1)
  have hW₀_open : ∀ i : I₀, IsOpen (W₀ i) := by
    intro i
    exact (W (fun _ : Fin 1 ↦ i.1)).isOpen
  have hW₀_cover : Z ⊆ ⋃ i : I₀, W₀ i := by
    -- On `Z`, the prescribed singleton open agrees with the original ambient open.
    intro z hz
    rcases mem_iUnion.1 (hscover hz) with ⟨i, hzi⟩
    refine mem_iUnion.2 ⟨i, ?_⟩
    have hzWZ : z ∈ (W (fun _ : Fin 1 ↦ i.1) : Set X) ∩ Z := by
      rw [hW_on_Z (fun _ : Fin 1 ↦ i.1)]
      refine ⟨?_, hz⟩
      refine mem_iInter.2 ?_
      intro j
      fin_cases j
      simpa using hzi
    exact hzWZ.1
  have hW₀_finite : ∀ x ∈ Z, { i : I₀ | x ∈ W₀ i }.Finite := by
    -- The reduced index type is finite, so the point-finiteness hypothesis is automatic.
    intro x hx
    classical
    exact Set.finite_univ.subset fun _ _ ↦ by simp
  obtain ⟨v₀, hv₀_cover, hv₀_open, hv₀_closure, _⟩ :=
    exists_subset_iUnion_closure_subset_t2space hZ hW₀_open hW₀_finite hW₀_cover
  let V₀ : I₀ → Opens X := fun i ↦ ⟨v₀ i, hv₀_open i⟩
  have hV₀ :
      IsOpenShrinkingWithPrescribedIntersections Z 0
        (fun i : I₀ ↦ U i.1)
        (fun σ : Fin 1 → I₀ ↦ W (fun j ↦ (σ j).1))
        V₀ := by
    refine ⟨hv₀_cover, ?_, ?_⟩
    · -- The singleton prescribed opens already sit inside the corresponding ambient opens.
      intro i
      exact (hv₀_closure i).trans <| by
        intro x hx
        have hxU : x ∈ ⋂ j : Fin 1, (U i.1 : Set X) := hW_subset (fun _ : Fin 1 ↦ i.1) hx
        simpa using (mem_iInter.1 hxU) 0
    · -- A `1`-fold intersection is just one member of the family.
      intro σ x hx
      have hx0 : x ∈ (V₀ (σ 0) : Set X) := by
        simpa using (mem_iInter.1 hx) 0
      have hxClosure : x ∈ closure (V₀ (σ 0) : Set X) := subset_closure hx0
      have hxW : x ∈ W (fun _ : Fin 1 ↦ (σ 0).1) :=
        hv₀_closure (σ 0) hxClosure
      have hσ : (fun j : Fin 1 ↦ (σ j).1) = fun _ : Fin 1 ↦ (σ 0).1 := by
        funext j
        fin_cases j
        rfl
      simpa [hσ] using hxW
  refine ⟨fun i ↦ if hi : i ∈ s then V₀ ⟨i, hi⟩ else ⊥, ?_⟩
  -- Returning to the original index type only adds empty opens outside the finite support.
  exact extend_by_bot_preserves_shrinking_data (Z := Z) (p := 0) (s := s)
    (U := U) (W := W) (V₀ := V₀) hV₀

/-- Helper for Lemma 5.13.6: for a finite index type, first shrink the ambient cover around `Z`,
then remove the finitely many closed bad intersections in one step. -/
private theorem exists_open_shrinking_with_prescribed_intersections_finite
    [Fintype I] {Z : Set X} (hZ : IsCompact Z) (p : ℕ) (U : I → Opens X)
    (W : (Fin (p + 1) → I) → Opens X)
    (hcover : Z ⊆ ⋃ i, U i)
    (hW_subset : ∀ σ, (W σ : Set X) ⊆ ⋂ j, U (σ j))
    (hW_on_Z : ∀ σ, (W σ : Set X) ∩ Z = (⋂ j, U (σ j)) ∩ Z) :
    ∃ V : I → Opens X, IsOpenShrinkingWithPrescribedIntersections Z p U W V := by
  classical
  have hU_finite : ∀ x ∈ Z, { i : I | x ∈ (U i : Set X) }.Finite := by
    -- A finite index type makes the point-finiteness hypothesis automatic.
    intro x hx
    exact Set.finite_univ.subset fun _ _ ↦ by simp
  obtain ⟨o, ho_cover, ho_open, ho_closure, _⟩ :=
    exists_subset_iUnion_closure_subset_t2space hZ (fun i ↦ (U i).isOpen) hU_finite hcover
  let O : I → Opens X := fun i ↦ ⟨o i, ho_open i⟩
  have hO_cover : Z ⊆ ⋃ i, (O i : Set X) := by
    -- The shrinking still covers the compact set `Z`.
    simpa [O] using ho_cover
  have hO_closure : ∀ i, closure (O i : Set X) ⊆ U i := by
    -- Each shrunk open has closure inside the corresponding ambient open.
    intro i
    simpa [O] using ho_closure i
  let bad : (Fin (p + 1) → I) → Set X :=
    fun σ ↦ closure ((⋂ j, (O (σ j) : Set X)) \ (W σ : Set X))
  have hbad_closed : ∀ σ : Fin (p + 1) → I, IsClosed (bad σ) := by
    -- By construction each bad set is a closure.
    intro σ
    exact isClosed_closure
  have hbad_disjoint_Z : ∀ σ : Fin (p + 1) → I, Disjoint (bad σ) Z := by
    intro σ
    refine disjoint_left.2 fun x hxBad hxZ ↦ ?_
    have hxW : x ∈ W σ := by
      -- Every bad closure point lying on `Z` already belongs to the prescribed open by the
      -- equality hypothesis along `Z`.
      have hxInter : x ∈ ⋂ j, U (σ j) := by
        refine mem_iInter.2 ?_
        intro j
        have hsubset :
            ((⋂ k, (O (σ k) : Set X)) \ (W σ : Set X)) ⊆ (O (σ j) : Set X) := by
          intro y hy
          exact mem_iInter.1 hy.1 j
        exact hO_closure (σ j) (closure_mono hsubset hxBad)
      have hxWZ : x ∈ (W σ : Set X) ∩ Z := by
        rw [hW_on_Z σ]
        exact ⟨hxInter, hxZ⟩
      exact hxWZ.1
    rcases mem_closure_iff.1 hxBad (W σ : Set X) (W σ).isOpen hxW with ⟨y, hyW, hyBad⟩
    exact hyBad.2 hyW
  let C : I → Set X := fun i ↦ ⋃ σ : Fin (p + 1) → I, if ∃ j, σ j = i then bad σ else ∅
  have hC_closed : ∀ i : I, IsClosed (C i) := by
    -- Only finitely many tuples occur, so each repaired closed set is a finite union.
    intro i
    exact isClosed_iUnion_of_finite fun σ ↦ by
      by_cases hσ : ∃ j, σ j = i
      · simpa [C, hσ] using hbad_closed σ
      · simp [C, hσ]
  have hC_disjoint_Z : ∀ i : I, Disjoint (C i) Z := by
    intro i
    refine disjoint_left.2 fun x hxC hxZ ↦ ?_
    rcases mem_iUnion.1 hxC with ⟨σ, hxσ⟩
    by_cases hσ : ∃ j, σ j = i
    · have hxBad : x ∈ bad σ := by
        simpa [C, hσ] using hxσ
      exact (Set.disjoint_left.1 (hbad_disjoint_Z σ)) hxBad hxZ
    · simp [C, hσ] at hxσ
  let V : I → Opens X := fun i ↦ ⟨(O i : Set X) \ C i, (O i).isOpen.sdiff (hC_closed i)⟩
  refine ⟨V, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Removing closed bad sets does not change the cover on `Z` because those bad sets miss `Z`.
    intro z hz
    rcases mem_iUnion.1 (hO_cover hz) with ⟨i, hzi⟩
    refine mem_iUnion.2 ⟨i, ?_⟩
    refine ⟨hzi, ?_⟩
    intro hzC
    exact (Set.disjoint_left.1 (hC_disjoint_Z i)) hzC hz
  · -- The final family is obtained by shrinking the original shrinking, so the closure bound
    -- survives by monotonicity.
    intro i
    exact (closure_mono fun x hx ↦ hx.1).trans (hO_closure i)
  · -- If a tuple intersection still missed the prescribed open, then its bad set would have been
    -- subtracted from the first coordinate.
    intro σ x hx
    by_contra hxW
    have hxO : x ∈ ⋂ j, (O (σ j) : Set X) := by
      refine mem_iInter.2 ?_
      intro j
      exact ((mem_iInter.1 hx) j).1
    have hxBadMem : x ∈ ((⋂ j, (O (σ j) : Set X)) \ (W σ : Set X)) := ⟨hxO, hxW⟩
    have hxBad : x ∈ bad σ := subset_closure hxBadMem
    have hxC : x ∈ C (σ 0) := by
      refine mem_iUnion.2 ⟨σ, ?_⟩
      have hσ0 : ∃ j, σ j = σ 0 := ⟨0, rfl⟩
      simpa [C, hσ0] using hxBad
    exact ((mem_iInter.1 hx) 0).2 hxC

/-- Lemma 5.13.6: a compact subset `Z` of a locally compact Hausdorff space, covered by opens
`U i` with prescribed `(p + 1)`-fold neighborhoods along `Z`, admits an open shrinking whose
closures stay in `U i` and whose `(p + 1)`-fold intersections land in the prescribed opens. -/
-- Proof sketch: reduce to the finite, quasi-compact case, then argue by induction on `p`; use
-- Lemma 5.13.4 to obtain the base-case shrinking, and in the induction step remove finitely many
-- closed error sets from the chosen opens to force the required intersection containments.
theorem exists_open_shrinking_with_prescribed_intersections
    {Z : Set X} (hZ : IsCompact Z) (p : ℕ) (U : I → Opens X)
    (W : (Fin (p + 1) → I) → Opens X)
    (hcover : Z ⊆ ⋃ i, U i)
    (hW_subset : ∀ σ, (W σ : Set X) ⊆ ⋂ j, U (σ j))
    (hW_on_Z : ∀ σ, (W σ : Set X) ∩ Z = (⋂ j, U (σ j)) ∩ Z) :
    ∃ V : I → Opens X, IsOpenShrinkingWithPrescribedIntersections Z p U W V := by
  classical
  obtain ⟨s, hscover⟩ := finite_support_reduction (Z := Z) hZ U hcover
  let I₀ := {i // i ∈ s}
  let U₀ : I₀ → Opens X := fun i ↦ U i.1
  let W₀ : (Fin (p + 1) → I₀) → Opens X := fun σ ↦ W (fun j ↦ (σ j).1)
  have hscover₀ : Z ⊆ ⋃ i : I₀, (U₀ i : Set X) := by
    -- The chosen finite subcover is the finite-index ambient problem we now solve.
    simpa [I₀, U₀] using hscover
  have hW_subset₀ : ∀ σ : Fin (p + 1) → I₀, (W₀ σ : Set X) ⊆ ⋂ j, U₀ (σ j) := by
    -- The tuplewise ambient containment is unchanged after restricting to the finite subtype.
    intro σ
    simpa [W₀, U₀] using hW_subset (fun j ↦ (σ j).1)
  have hW_on_Z₀ : ∀ σ : Fin (p + 1) → I₀,
      (W₀ σ : Set X) ∩ Z = (⋂ j, U₀ (σ j)) ∩ Z := by
    -- The prescribed opens still agree with the ambient intersections along `Z`.
    intro σ
    simpa [W₀, U₀] using hW_on_Z (fun j ↦ (σ j).1)
  haveI : Fintype I₀ := inferInstance
  obtain ⟨V₀, hV₀⟩ :=
    exists_open_shrinking_with_prescribed_intersections_finite
      (X := X) (I := I₀) (Z := Z) hZ p U₀ W₀ hscover₀ hW_subset₀ hW_on_Z₀
  refine ⟨fun i ↦ if hi : i ∈ s then V₀ ⟨i, hi⟩ else ⊥, ?_⟩
  -- Route correction: instead of an explicit induction on tuple cardinality, solve the finite
  -- support problem directly and subtract all bad tuple closures at once.
  exact extend_by_bot_preserves_shrinking_data
    (Z := Z) (p := p) (s := s) (U := U) (W := W) (V₀ := V₀) hV₀

end IsCompact

end

/-! ### Lemma_5_13_7 (from Chap05) -/
universe u v

open Set TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/- Domain-style sampling for tuplewise shrinking over a compact separated subset:
- core/canonical owner for shrinking with prescribed intersections:
  `exists_open_shrinking_with_prescribed_intersections`
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover.exists_shrinking`,
  `exists_open_shrinking_with_prescribed_intersections`,
  `SeparatedNhds`,
  `Mathlib.Topology.ShrinkingLemma.exists_subset_iUnion_closure_subset_t2space`
- target layer here: `source-facing` for the ambient theorem below, with a `bridge/view`
  through the Hausdorff subtype `Z`

Primitive data for the source statement are the compact subset `Z`, the ambient open cover `U`,
and the prescribed tuplewise opens `W`. The point-separation hypothesis is not a second owner:
it is exactly the `T2Space` owner on the subtype `Z`, so the core shrinking theorem should be
reused there rather than duplicated entrywise in the ambient proof.
-/

private theorem subtype_t2Space_of_pairwise_separatedNhds {Z : Set X}
    (hZsep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → SeparatedNhds ({x} : Set X) ({y} : Set X)) :
    T2Space Z := by
  refine ⟨fun x y hxy ↦ ?_⟩
  rcases hZsep x.1 x.2 y.1 y.2 (fun h ↦ hxy <| Subtype.ext h) with
    ⟨U, V, hU, hV, hxU, hyV, hUV⟩
  refine ⟨Subtype.val ⁻¹' U, Subtype.val ⁻¹' V, hU.preimage continuous_subtype_val,
    hV.preimage continuous_subtype_val, hxU (by simp), hyV (by simp), hUV.preimage Subtype.val⟩

private theorem exists_subtype_open_shrinking_with_prescribed_intersections
    (Z : Set X)
    (hZcompact : IsCompact Z)
    (hZsep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → SeparatedNhds ({x} : Set X) ({y} : Set X))
    (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (hcoverU : Z ⊆ ⋃ i, (U i : Set X))
    (hW_subset : ∀ σ : Fin (p + 1) → I, (W σ : Set X) ⊆ ⋂ k, (U (σ k) : Set X))
    (hW_on_Z : ∀ σ : Fin (p + 1) → I,
      (W σ : Set X) ∩ Z = (⋂ k, (U (σ k) : Set X)) ∩ Z) :
    ∃ V : I → Opens Z,
      (Set.univ : Set Z) ⊆ ⋃ i, (V i : Set Z) ∧
      (∀ i, closure (V i : Set Z) ⊆ Subtype.val ⁻¹' (U i : Set X)) ∧
      ∀ σ : Fin (p + 1) → I, (⋂ k, (V (σ k) : Set Z)) ⊆ Subtype.val ⁻¹' (W σ : Set X) := by
  letI : CompactSpace Z := isCompact_iff_compactSpace.mp hZcompact
  letI : T2Space Z := subtype_t2Space_of_pairwise_separatedNhds hZsep
  let pullback : Opens X → Opens Z := Opens.comap ⟨Subtype.val, continuous_subtype_val⟩
  let UZ : I → Opens Z := fun i ↦ pullback (U i)
  let WZ : (Fin (p + 1) → I) → Opens Z := fun σ ↦ pullback (W σ)
  have hcoverUZ : (Set.univ : Set Z) ⊆ ⋃ i, (UZ i : Set Z) := by
    intro z _
    rcases mem_iUnion.1 (hcoverU z.2) with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, by simpa [UZ, pullback, TopologicalSpace.Opens.coe_comap] using hi⟩
  have hW_subset_Z : ∀ σ : Fin (p + 1) → I, (WZ σ : Set Z) ⊆ ⋂ k, (UZ (σ k) : Set Z) := by
    intro σ z hz
    refine mem_iInter.2 fun k ↦ ?_
    have hz' : z.1 ∈ (W σ : Set X) := by
      simpa [WZ, pullback, TopologicalSpace.Opens.coe_comap] using hz
    simpa [UZ, pullback, TopologicalSpace.Opens.coe_comap] using mem_iInter.1 (hW_subset σ hz') k
  have hW_eq_Z :
      ∀ σ : Fin (p + 1) → I, (WZ σ : Set Z) = ⋂ k, (UZ (σ k) : Set Z) := by
    intro σ
    ext z
    simpa [WZ, UZ, pullback, TopologicalSpace.Opens.coe_comap, z.2] using
      (Set.ext_iff.mp (hW_on_Z σ) z.1)
  have hW_on_univ_Z :
      ∀ σ : Fin (p + 1) → I,
        (WZ σ : Set Z) ∩ Set.univ = (⋂ k, (UZ (σ k) : Set Z)) ∩ Set.univ := by
    intro σ
    simp [hW_eq_Z σ]
  rcases isCompact_univ.exists_open_shrinking_with_prescribed_intersections
      p UZ WZ hcoverUZ hW_subset_Z hW_on_univ_Z with
    ⟨V, hV⟩
  exact ⟨V, hV.cover, hV.closure_subset, hV.tuplewise_subset⟩

/-- A shrinking of an open family whose closures and tuplewise intersections are controlled over a
compact subset. -/
class IsTupleIntersectionShrinking
    (Z : Set X) (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) : Prop where
  /-- The shrunken opens still cover the compact subset. -/
  cover : Z ⊆ ⋃ i, (V i : Set X)
  /-- Each shrunken open lies in the corresponding ambient open. -/
  subset (i : I) : (V i : Set X) ⊆ U i
  /-- The closure of each shrunken open meets the compact subset inside the ambient open. -/
  closure_inter_subset (i : I) : closure (V i : Set X) ∩ Z ⊆ U i
  /-- Every `(p + 1)`-fold intersection of the shrunken family lands in the prescribed open. -/
  tuplewise_subset (σ : Fin (p + 1) → I) : (⋂ k, (V (σ k) : Set X)) ⊆ W σ

/-- Helper for Lemma 5.13.7: compact disjoint subsets of `Z` can be separated by ambient open
neighborhoods when distinct points of `Z` are already separated in `X`. -/
private theorem separatedNhds_of_compact_subsets {Z K L : Set X}
    (hZsep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → SeparatedNhds ({x} : Set X) ({y} : Set X))
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hKZ : K ⊆ Z) (hLZ : L ⊆ Z) (hKL : Disjoint K L) :
    SeparatedNhds K L := by
  classical
  -- First separate each point of `K` from the compact set `L`.
  have hpoint :
      ∀ x : K, ∀ y : L,
        ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ (x : X) ∈ U ∧ (y : X) ∈ V ∧ Disjoint U V := by
    intro x y
    have hxy : (x : X) ≠ (y : X) := by
      intro hxy
      exact (Set.disjoint_left.1 hKL x.2) (hxy ▸ y.2)
    rcases hZsep x.1 (hKZ x.2) y.1 (hLZ y.2) hxy with ⟨U, V, hU, hV, hxU, hyV, hUV⟩
    exact ⟨U, V, hU, hV, hxU (by simp), hyV (by simp), hUV⟩
  choose Uxy Vxy hUxy hVxy hxUxy hyVxy hUVxy using hpoint
  have hpoint_to_compact :
      ∀ x : K,
        ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ (x : X) ∈ U ∧ L ⊆ V ∧ Disjoint U V := by
    intro x
    -- Compactness of `L` turns the pointwise separation into one neighborhood of `L`.
    obtain ⟨t, ht⟩ :=
      hLcompact.elim_finite_subcover (fun y : L ↦ Vxy x y) (fun y ↦ hVxy x y) fun y hy ↦
        mem_iUnion.2 ⟨⟨y, hy⟩, hyVxy x ⟨y, hy⟩⟩
    let U : Set X := ⋂ y : t, Uxy x y
    let V : Set X := ⋃ y ∈ t, Vxy x y
    refine ⟨U, V, ?_, ?_, ?_, ?_, ?_⟩
    · -- The intersection is finite because `t` is finite.
      exact isOpen_iInter_of_finite fun y ↦ hUxy x y
    · exact isOpen_biUnion fun y _ ↦ hVxy x y
    · exact mem_iInter.2 fun y ↦ hxUxy x y
    · intro y hy
      rcases mem_iUnion₂.1 (ht hy) with ⟨z, hz, hyz⟩
      exact mem_iUnion₂.2 ⟨z, hz, hyz⟩
    · refine disjoint_left.2 fun z hzU hzV ↦ ?_
      rcases mem_iUnion₂.1 hzV with ⟨y, hy, hzVy⟩
      exact (Set.disjoint_left.1 (hUVxy x y)) (mem_iInter.1 hzU ⟨y, hy⟩) hzVy
  choose Ux Vx hUx_open hVx_open hxUx hLVx hUxVx using hpoint_to_compact
  -- Compactness of `K` now gives one neighborhood of `K` disjoint from one neighborhood of `L`.
  obtain ⟨s, hs⟩ :=
    hKcompact.elim_finite_subcover (fun x : K ↦ Ux x) (fun x ↦ hUx_open x) fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, hxUx ⟨x, hx⟩⟩
  refine ⟨⋃ x ∈ s, Ux x, ⋂ x : s, Vx x, isOpen_biUnion fun x _ ↦ hUx_open x,
    isOpen_iInter_of_finite fun x ↦ hVx_open x, hs, ?_, ?_⟩
  · intro y hy
    exact mem_iInter.2 fun x ↦ hLVx x hy
  · refine disjoint_left.2 fun z hzU hzV ↦ ?_
    rcases mem_iUnion₂.1 hzU with ⟨x, hx, hzUx⟩
    exact (Set.disjoint_left.1 (hUxVx x)) hzUx (mem_iInter.1 hzV ⟨x, hx⟩)

/-- Helper for Lemma 5.13.7: a relative open subset of `Z` whose closure in `Z` stays inside `U`
extends to an ambient open subset of `U` with the same trace on `Z` and the expected
`closure ∩ Z` control. -/
private theorem lift_subtype_open
    {Z : Set X}
    (hZcompact : IsCompact Z)
    (hZsep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → SeparatedNhds ({x} : Set X) ({y} : Set X))
    {U : Opens X} (V : Opens Z)
    (hVclosure : closure (V : Set Z) ⊆ Subtype.val ⁻¹' (U : Set X)) :
    ∃ O : Opens X,
      Subtype.val ⁻¹' (O : Set X) = (V : Set Z) ∧
      (O : Set X) ⊆ U ∧
      closure (O : Set X) ∩ Z ⊆ U := by
  classical
  letI : CompactSpace Z := isCompact_iff_compactSpace.mp hZcompact
  -- Start from an arbitrary ambient representative of the relative open subset.
  rcases isOpen_induced_iff.mp V.2 with ⟨O₀, hO₀_open, hO₀_trace⟩
  let K : Set X := Subtype.val '' closure (V : Set Z)
  have hKcompact : IsCompact K := by
    have hClosureCompact : IsCompact (closure (V : Set Z)) :=
      isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
    exact hClosureCompact.image continuous_subtype_val
  have hKZ : K ⊆ Z := by
    intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact z.2
  have hKsubsetU : K ⊆ U := by
    intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact hVclosure hz
  have hKL : Disjoint K (Z \ U) := by
    refine disjoint_left.2 fun x hxK hxZU ↦ ?_
    exact hxZU.2 (hKsubsetU hxK)
  rcases separatedNhds_of_compact_subsets hZsep hKcompact (hZcompact.diff U.2) hKZ
      (fun x hx ↦ hx.1) hKL with
    ⟨N, M, hN_open, hM_open, hKN, hZM, hNM⟩
  have hVsubsetU : (V : Set Z) ⊆ Subtype.val ⁻¹' (U : Set X) := by
    intro z hz
    exact hVclosure (subset_closure hz)
  have hO_open : IsOpen (O₀ ∩ N ∩ U : Set X) := (hO₀_open.inter hN_open).inter U.2
  refine ⟨⟨O₀ ∩ N ∩ U, hO_open⟩, ?_, ?_, ?_⟩
  · -- The trace on `Z` is unchanged because `V` already lies in the compact set we separated.
    ext z
    constructor
    · intro hz
      have hzO₀ : z ∈ Subtype.val ⁻¹' O₀ := hz.1.1
      rwa [hO₀_trace] at hzO₀
    · intro hz
      have hzO₀ : z ∈ Subtype.val ⁻¹' O₀ := by rwa [hO₀_trace]
      have hzN : (z : X) ∈ N := by
        exact hKN ⟨z, subset_closure hz, rfl⟩
      have hzU : (z : X) ∈ (U : Set X) := hVsubsetU hz
      exact ⟨⟨hzO₀, hzN⟩, hzU⟩
  · intro x hx
    exact hx.2
  · -- Any closure point of the ambient lift lying on `Z` must stay away from `Z \ U`.
    intro x hx
    by_contra hxU
    have hxM : x ∈ M := hZM ⟨hx.2, hxU⟩
    rcases mem_closure_iff.1 hx.1 M hM_open hxM with ⟨y, hyM, hyO⟩
    exact (Set.disjoint_left.1 hNM) hyO.1.2 hyM

-- Proof sketch: reduce to the case of a finite index set using compactness of `Z`. For `p = 0`,
-- shrink each `U i` near points of `Z` by separating a point from the compact subset `Z \ U i`.
-- For the induction step on `p`, first shrink to control repeated indices and then remove the
-- finitely many bad intersections coming from tuples of pairwise distinct indices.
/-- Lemma 5.13.7: a compact subset whose distinct points have disjoint neighborhoods admits a
shrinking of an open cover whose `(p + 1)`-fold intersections lie in prescribed open subsets that
already agree with the original intersections on the compact subset. -/
theorem exists_tuple_intersection_shrinking
    (Z : Set X)
    (hZcompact : IsCompact Z)
    (hZsep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → SeparatedNhds ({x} : Set X) ({y} : Set X))
    (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (hcoverU : Z ⊆ ⋃ i, (U i : Set X))
    (hW_subset : ∀ σ : Fin (p + 1) → I, (W σ : Set X) ⊆ ⋂ k, (U (σ k) : Set X))
    (hW_on_Z : ∀ σ : Fin (p + 1) → I,
      (W σ : Set X) ∩ Z = (⋂ k, (U (σ k) : Set X)) ∩ Z) :
    ∃ V : I → Opens X, IsTupleIntersectionShrinking Z p U W V := by
  classical
  -- First reduce to a finite subcover of `Z`, so that the ambient bad tuples are also finite.
  obtain ⟨t, ht⟩ :=
    hZcompact.elim_finite_subcover (fun i ↦ (U i : Set X)) (fun i ↦ (U i).2) hcoverU
  let UJ : (↑t) → Opens X := fun i ↦ U i.1
  let WJ : (Fin (p + 1) → ↑t) → Opens X := fun σ ↦ W (fun k ↦ (σ k).1)
  have hcoverUJ : Z ⊆ ⋃ i : ↑t, (UJ i : Set X) := by
    intro z hz
    rcases mem_iUnion₂.1 (ht hz) with ⟨i, hi, hzi⟩
    exact mem_iUnion.2 ⟨⟨i, hi⟩, hzi⟩
  have hW_subsetJ : ∀ σ : Fin (p + 1) → ↑t, (WJ σ : Set X) ⊆ ⋂ k, (UJ (σ k) : Set X) := by
    intro σ
    simpa [UJ, WJ] using hW_subset (fun k ↦ (σ k).1)
  have hW_on_ZJ : ∀ σ : Fin (p + 1) → ↑t,
      (WJ σ : Set X) ∩ Z = (⋂ k, (UJ (σ k) : Set X)) ∩ Z := by
    intro σ
    simpa [UJ, WJ] using hW_on_Z (fun k ↦ (σ k).1)
  -- Solve the tuplewise shrinking problem on the Hausdorff subtype `Z`.
  rcases exists_subtype_open_shrinking_with_prescribed_intersections
      Z hZcompact hZsep p UJ WJ hcoverUJ hW_subsetJ hW_on_ZJ with
    ⟨VZ, hVZcover, hVZclosure, hVZtuple⟩
  -- Lift each relative open subset back to an ambient open while keeping the `closure ∩ Z` bound.
  choose O hO_trace hO_subset hO_closure using
    fun i : ↑t ↦ lift_subtype_open hZcompact hZsep (U := UJ i) (VZ i) (hVZclosure i)
  let bad : (Fin (p + 1) → ↑t) → Set X :=
    fun σ ↦ closure ((⋂ k, (O (σ k) : Set X)) \ (WJ σ : Set X))
  have hbad_closed : ∀ σ : Fin (p + 1) → ↑t, IsClosed (bad σ) := by
    intro σ
    exact isClosed_closure
  have hbad_disjoint_Z : ∀ σ : Fin (p + 1) → ↑t, Disjoint (bad σ) Z := by
    intro σ
    refine disjoint_left.2 fun x hxBad hxZ ↦ ?_
    have hxU : x ∈ (WJ σ : Set X) := by
      have hxInter : x ∈ ⋂ k, (UJ (σ k) : Set X) := by
        refine mem_iInter.2 fun k ↦ ?_
        have hsubset :
            ((⋂ j, (O (σ j) : Set X)) \ (WJ σ : Set X)) ⊆ (O (σ k) : Set X) := by
          intro y hy
          exact mem_iInter.1 hy.1 k
        exact hO_closure (σ k) ⟨closure_mono hsubset hxBad, hxZ⟩
      have : x ∈ ((⋂ k, (UJ (σ k) : Set X)) ∩ Z) := ⟨hxInter, hxZ⟩
      rw [← hW_on_ZJ σ] at this
      exact this.1
    rcases mem_closure_iff.1 hxBad (WJ σ : Set X) (WJ σ).2 hxU with ⟨y, hyW, hyBad⟩
    exact hyBad.2 hyW
  let C : (↑t) → Set X := fun i ↦ ⋃ σ : Fin (p + 1) → ↑t, if ∃ k, σ k = i then bad σ else ∅
  have hC_closed : ∀ i : ↑t, IsClosed (C i) := by
    intro i
    exact isClosed_iUnion_of_finite fun σ ↦ by
      by_cases hσ : ∃ k, σ k = i
      · simpa [C, hσ] using hbad_closed σ
      · simp [hσ]
  have hC_disjoint_Z : ∀ i : ↑t, Disjoint (C i) Z := by
    intro i
    refine disjoint_left.2 fun x hxC hxZ ↦ ?_
    rcases mem_iUnion.1 hxC with ⟨σ, hxσ⟩
    by_cases hσ : ∃ k, σ k = i
    · have hxBad : x ∈ bad σ := by simpa [C, hσ] using hxσ
      exact (Set.disjoint_left.1 (hbad_disjoint_Z σ)) hxBad hxZ
    · simp [hσ] at hxσ
  have hVJ_open : ∀ i : ↑t, IsOpen ((O i : Set X) \ C i) := by
    intro i
    exact (O i).2.sdiff (hC_closed i)
  let VJ : (↑t) → Opens X := fun i ↦ ⟨(O i : Set X) \ C i, hVJ_open i⟩
  have hVJ_trace : ∀ i : ↑t, Subtype.val ⁻¹' (VJ i : Set X) = (VZ i : Set Z) := by
    intro i
    ext z
    constructor
    · intro hz
      have hzO : z ∈ Subtype.val ⁻¹' (O i : Set X) := hz.1
      rwa [hO_trace i] at hzO
    · intro hz
      have hzO : z ∈ Subtype.val ⁻¹' (O i : Set X) := by rwa [hO_trace i]
      have hzC : (z : X) ∉ C i := by
        intro hzC
        exact (Set.disjoint_left.1 (hC_disjoint_Z i)) hzC z.2
      exact ⟨hzO, hzC⟩
  let V : I → Opens X := fun i ↦ if hi : i ∈ t then VJ ⟨i, hi⟩ else ⊥
  refine ⟨V, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The cover on `Z` is preserved because the closed repair sets miss `Z`.
    intro z hz
    rcases mem_iUnion.1 (hVZcover (by simp : (⟨z, hz⟩ : Z) ∈ (Set.univ : Set Z))) with ⟨i, hzi⟩
    have hzi' : (⟨z, hz⟩ : Z) ∈ Subtype.val ⁻¹' (VJ i : Set X) := by
      rwa [hVJ_trace i]
    exact mem_iUnion.2 ⟨i.1, by simpa [V, i.2] using hzi'⟩
  · -- Every shrunken ambient open still lies in the corresponding `U i`.
    intro i
    by_cases hi : i ∈ t
    · intro x hx
      have hx' : x ∈ ((O ⟨i, hi⟩ : Set X) \ C ⟨i, hi⟩) := by
        simpa [V, hi, VJ] using hx
      exact hO_subset ⟨i, hi⟩ hx'.1
    · intro x hx
      exact False.elim <| by
        simpa [V, hi, TopologicalSpace.Opens.coe_bot] using hx
  · -- Shrinking by a closed set can only improve the closure control over `Z`.
    intro i x hx
    by_cases hi : i ∈ t
    · have hsubset : (V i : Set X) ⊆ (O ⟨i, hi⟩ : Set X) := by
        intro y hy
        have hy' : y ∈ ((O ⟨i, hi⟩ : Set X) \ C ⟨i, hi⟩) := by
          simpa [V, hi, VJ] using hy
        exact hy'.1
      exact hO_closure ⟨i, hi⟩ ⟨closure_mono hsubset hx.1, hx.2⟩
    · have hxBot : x ∈ closure (((⊥ : Opens X) : Set X)) := by
        simpa [V, hi] using hx.1
      change x ∈ closure (∅ : Set X) at hxBot
      have hxEmpty : x ∈ closure (∅ : Set X) := hxBot
      simp at hxEmpty
  · -- The tuplewise repair removes the closure of every ambient bad intersection at index `0`.
    intro σ x hx
    by_cases hσ : ∀ k, σ k ∈ t
    · let σJ : Fin (p + 1) → ↑t := fun k ↦ ⟨σ k, hσ k⟩
      have hxVJ : ∀ k, x ∈ (VJ (σJ k) : Set X) := by
        intro k
        simpa [V, hσ k, σJ] using mem_iInter.1 hx k
      have hxNotBad : x ∉ bad σJ := by
        intro hxBad
        have hxC : x ∈ C (σJ 0) := by
          refine mem_iUnion.2 ⟨σJ, ?_⟩
          simp [hxBad, σJ]
        exact (hxVJ 0).2 hxC
      by_contra hxW
      have hxBadMem : x ∈ ((⋂ k, (O (σJ k) : Set X)) \ (WJ σJ : Set X)) := by
        refine ⟨mem_iInter.2 fun k ↦ (hxVJ k).1, ?_⟩
        simpa [WJ, σJ] using hxW
      exact hxNotBad (by simpa [bad] using subset_closure hxBadMem)
    · push Not at hσ
      rcases hσ with ⟨k, hk⟩
      exact False.elim <| by
        have hxk : x ∈ (V (σ k) : Set X) := mem_iInter.1 hx k
        simpa [V, hk] using hxk

end
