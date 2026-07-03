import StacksProject_2024.Chap21.Definition_21_31_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory CategoryTheory.Limits

/-- The category `LC` has a terminal object, corresponding to the one-point space. -/
instance : HasTerminal LCCat.{u} := by
  sorry

/-- The category `LC` has pullbacks. -/
instance : HasPullbacks LCCat.{u} := by
  sorry

/-- The category `LC` has finite limits because it has a terminal object and pullbacks. -/
instance : HasFiniteLimits LCCat.{u} :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

-- Proof sketch: use the chosen pullback object in `LC` and view it in `TopCat`. Its underlying
-- space is identified with the closed subspace `{(x, y) | f x = g y}` of `X.obj × Y.obj`, because
-- `Z.obj` is Hausdorff. If `X` and `Y` are quasi-compact, then `X.obj × Y.obj` is quasi-compact by
-- Tychonov, and a closed subspace of a quasi-compact space is quasi-compact.
/-- Lemma 21.31.1: for morphisms `X ⟶ Z` and `Y ⟶ Z` in `LC`, if `X` and `Y` are quasi-compact,
then the fiber product `X ×[Z] Y` is quasi-compact. -/
instance compactSpace_pullback
    {X Y Z : LCCat.{u}} [CompactSpace X.obj] [CompactSpace Y.obj] (f : X ⟶ Z) (g : Y ⟶ Z) :
    CompactSpace (pullback f g).obj := by
  sorry

/-- Companion formulation of Lemma 21.31.1 as compactness of the universal set. -/
theorem isCompact_univ_pullback_of_compact
    {X Y Z : LCCat.{u}} [CompactSpace X.obj] [CompactSpace Y.obj] (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsCompact (Set.univ : Set ((pullback f g).obj)) :=
  isCompact_univ
