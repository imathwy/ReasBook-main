import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owner
-- `AlgebraicGeometry.UniversallyClosed` together with the locality instance
-- `AlgebraicGeometry.universallyClosed_isZariskiLocalAtTarget` and the bridge theorem
-- `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Restricting a scheme morphism to an open cover of the target detects universal closedness. -/
theorem universallyClosed_iff_forall_restrict
    {ι : Type v} (V : ι → S.Opens) (hV : iSup V = ⊤) :
    UniversallyClosed f ↔ ∀ i, UniversallyClosed (f ∣_ V i) := by
  simpa using
    universallyClosed_isZariskiLocalAtTarget.iff_of_iSup_eq_top V hV

/-- A morphism of schemes is universally closed if and only if it is universally closed after
restricting to each member of some open cover of the target. This is the canonical
`Scheme.OpenCover` form of target-local universal closedness. -/
theorem universallyClosed_iff_exists_openCover_restrict :
    UniversallyClosed f ↔
      ∃ 𝒰 : S.OpenCover, ∀ i : 𝒰.I₀, UniversallyClosed (f ∣_ (𝒰.f i).opensRange) := by
  constructor
  · intro hf
    refine ⟨S.openCoverOfIsOpenCover (fun _ : PUnit ↦ (⊤ : S.Opens)) (by
      change iSup (fun _ : PUnit ↦ (⊤ : S.Opens)) = ⊤
      simp), ?_⟩
    intro i
    have h :=
      (universallyClosed_iff_forall_restrict f (fun _ : PUnit ↦ (⊤ : S.Opens))
        (by simp)).1 hf
    exact (Scheme.Opens.opensRange_ι (⊤ : S.Opens)).symm ▸ h i
  · rintro ⟨𝒰, h𝒰⟩
    exact
      (universallyClosed_iff_forall_restrict f (fun i ↦ (𝒰.f i).opensRange)
        𝒰.isOpenCover_opensRange.iSup_eq_top).2 h𝒰

/-- Lemma 29.41.2: a morphism of schemes is universally closed if and only if there exists an
open covering of the target such that each restricted morphism over a member of the cover is
universally closed. -/
@[stacks 02K7]
theorem universallyClosed_iff_exists_openCover :
    UniversallyClosed f ↔
      ∃ (ι : Type v) (V : ι → S.Opens), iSup V = ⊤ ∧
        ∀ i, UniversallyClosed (f ∣_ V i) := by
  constructor
  · intro hf
    rcases (universallyClosed_iff_exists_openCover_restrict f).1 hf with ⟨𝒰, h𝒰⟩
    exact ⟨𝒰.I₀, fun i ↦ (𝒰.f i).opensRange, 𝒰.isOpenCover_opensRange.iSup_eq_top, h𝒰⟩
  · rintro ⟨ι, V, hV, hVf⟩
    exact (universallyClosed_iff_exists_openCover_restrict f).2
      ⟨S.openCoverOfIsOpenCover V hV, by
        intro i
        exact (Scheme.Opens.opensRange_ι (V i)).symm ▸ hVf i⟩

end AlgebraicGeometry
