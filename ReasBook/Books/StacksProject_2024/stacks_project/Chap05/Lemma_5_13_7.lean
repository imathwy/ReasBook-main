import Mathlib
import StacksProject_2024.Chap05.Lemma_5_13_6

-- Declarations for this item will be appended below by the statement pipeline.

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
  simpa [UZ, WZ] using
    isCompact_univ.exists_open_shrinking_with_prescribed_intersections
      p UZ WZ hcoverUZ hW_subset_Z hW_on_univ_Z

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
    ∃ V : I → Opens X, IsTupleIntersectionShrinking Z p U W V := sorry

end
