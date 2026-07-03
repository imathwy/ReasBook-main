import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap21.Definition_21_31_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over

/-- A chosen small full subcategory of `LC` together with a set of representative qc coverings on
each of its objects. This packages the set-theoretic small model denoted `LC_qc` in the remark. -/
structure LCQcSmallSite (Bound : Cardinal → Cardinal) (S₀ : Set LCCat.{u}) where
  /-- The chosen full subcategory `LC_α ⊆ LC`. -/
  carrier : Set LCCat.{u}
  /-- The initial set `S₀` is contained in the chosen stage. -/
  seed_subset : S₀ ⊆ carrier
  /-- The chosen stage is closed under countable limits that exist in `LC`. -/
  closed_under_countable_limits :
    ∀ {J : Type u} [SmallCategory J] [Countable J] (F : J ⥤ LCCat.{u}) [HasLimit F],
      (∀ j, F.obj j ∈ carrier) → limit F ∈ carrier
  /-- The chosen stage is closed under countable colimits that exist in `LC`. -/
  closed_under_countable_colimits :
    ∀ {J : Type u} [SmallCategory J] [Countable J] (F : J ⥤ LCCat.{u}) [HasColimit F],
      (∀ j, F.obj j ∈ carrier) → colimit F ∈ carrier
  /-- Any object of `LC` whose size is bounded in terms of an object already in the chosen stage is
  isomorphic to another object of the chosen stage. -/
  bounded_iso :
    ∀ ⦃X : LCCat.{u}⦄, X ∈ carrier →
      ∀ ⦃Y : LCCat.{u}⦄, Cardinal.mk Y.obj ≤ Bound (Cardinal.mk X.obj) →
        ∃ Z : LCCat.{u}, Z ∈ carrier ∧ Nonempty (Y ≅ Z)
  /-- For each object of the chosen stage, a set of representative qc coverings. -/
  representative_coverings :
    ∀ U : { X : LCCat.{u} // X ∈ carrier },
      Set (SemiRepresentableFamily.Over.{u, u + 1, u + 1} U.1)
  /-- Every chosen representative family is a qc covering of its target. -/
  representative_coverings_are_qc :
    ∀ ⦃U : { X : LCCat.{u} // X ∈ carrier }⦄
      ⦃𝒰 : SemiRepresentableFamily.Over.{u, u + 1, u + 1} U.1⦄,
      𝒰 ∈ representative_coverings U →
        𝒰.IsQcCoveringOne
  /-- Every qc covering of an object in the chosen stage is combinatorially equivalent to one of
  the chosen representatives. -/
  qc_covering_has_representative :
    ∀ (U : { X : LCCat.{u} // X ∈ carrier })
      (𝒰 : SemiRepresentableFamily.Over.{u, u + 1, u + 1} U.1),
      𝒰.IsQcCoveringOne →
        ∃ 𝒱 : SemiRepresentableFamily.Over.{u, u + 1, u + 1} U.1,
          𝒱 ∈ representative_coverings U ∧
            SemiRepresentableFamily.Over.CombinatoriallyEquivalent 𝒰 𝒱

-- Proof sketch: apply the cited set-theoretic replacement lemmas to the big category `LC`, the
-- chosen cardinal bound `Bound`, and the seed set `S₀` to obtain a small stage `LC_α` containing
-- `S₀` and stable under existing countable limits and colimits. Then choose one qc covering from
-- each combinatorial equivalence class on that stage to obtain the representative covering system
-- denoted `LC_qc`.
/-- Remark 21.31.5 (Set theoretic issues): after choosing a cardinal bound function `Bound` and an
initial set `S₀` of objects of `LC`, one can choose a small stage `LC_α ⊆ LC` containing `S₀`,
stable under all countable limits and colimits that exist in `LC`, such that any object of `LC`
whose underlying set has cardinality at most `Bound (Cardinal.mk X.obj)` for some `X ∈ LC_α` is
isomorphic to an object of `LC_α`; moreover, for each object of `LC_α` one can choose a set of
representative qc coverings, with every qc covering combinatorially equivalent to one of the
chosen representatives. -/
theorem exists_lc_qc_small_site
    (Bound : Cardinal → Cardinal) (S₀ : Set LCCat.{u}) :
    Nonempty (LCQcSmallSite Bound S₀) := sorry
