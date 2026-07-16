import Mathlib.AlgebraicGeometry.Properties
import StacksProject_2024.stacks_project.Chap28.Definition_28_4_2
import StacksProject_2024.stacks_project.Chap26.Definition_26_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the canonical scheme owner `AlgebraicGeometry.IsReduced`; the local
-- Chapter 28 API for “locally P” on schemes is `Scheme.HasRingPropertyLocally` from Definition
-- `28.4.2`. This item is therefore recorded as the bridge between those two existing owners.

variable (X : Scheme.{u})

/-- Lemma 28.4.4: a scheme `X` is reduced if and only if `X` is locally reduced in the sense of
Definition `28.4.2`, namely reduced on an affine open neighborhood of every point. -/
theorem isReduced_iff_hasRingPropertyLocally_isReduced :
    IsReduced X ↔
      X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ _root_.IsReduced A) := by
  constructor
  · intro hX
    refine ⟨fun x ↦ ?_⟩
    rcases exists_isAffineOpen_mem_and_subset (x := x) (U := (⊤ : X.Opens)) (by simp)
      with ⟨U, hU, hxU, -⟩
    refine ⟨⟨U, hU⟩, hxU, ?_⟩
    letI : IsReduced X := hX
    exact IsReduced.component_reduced U
  · intro hX
    let 𝒰 := X.affineOpenCover
    letI : ∀ i : 𝒰.I₀, IsReduced (𝒰.X i) := fun i ↦ by
      let hXi : _root_.IsReduced (Γ(X, (𝒰.f i).opensRange)) := by
        refine (hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing X
          (fun A : CommRingCat.{u} ↦ _root_.IsReduced A)).1 hX 𝒰.i
      letI : _root_.IsReduced (Γ(X, (𝒰.f i).opensRange)) := hXi
      exact isReduced_of_isAffine_isReduced (𝒰.X i)
    exact IsReduced.of_openCover X 𝒰.openCover

end AlgebraicGeometry.Scheme
