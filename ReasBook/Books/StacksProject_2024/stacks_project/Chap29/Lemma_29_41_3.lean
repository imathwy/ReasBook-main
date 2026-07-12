import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owner `AlgebraicGeometry.IsProper`
-- together with the locality instance `AlgebraicGeometry.IsProper.instIsZariskiLocalAtTarget`
-- and the bridge theorem `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Restricting a scheme morphism to an open cover of the target detects properness. -/
theorem proper_iff_forall_restrict
    {ι : Type v} (V : ι → S.Opens) (hV : iSup V = ⊤) :
    IsProper f ↔ ∀ i, IsProper (f ∣_ V i) := sorry

/-- A morphism of schemes is proper if and only if it is proper after restricting to each member
of some open cover of the target. This is the canonical `Scheme.OpenCover` form of target-local
properness. -/
theorem proper_iff_exists_openCover_restrict :
    IsProper f ↔
      ∃ 𝒰 : S.OpenCover, ∀ i : 𝒰.I₀, IsProper (f ∣_ ((𝒰.f i).opensRange)) := sorry

/-- Lemma 29.41.3: a morphism of schemes is proper if and only if there exists an open covering of
the target such that each restricted morphism over a member of the cover is proper. -/
@[stacks 01W2]
theorem proper_iff_exists_openCover :
    IsProper f ↔
      ∃ (ι : Type v) (V : ι → S.Opens), iSup V = ⊤ ∧
        ∀ i, IsProper (f ∣_ V i) := sorry

end AlgebraicGeometry
