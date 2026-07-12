import StacksProject_2024.Chap10.Lemma_10_102_2.Basic

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}
/-- Helper for Lemma 10.102.2: replace the chosen coordinate identifications only in degrees
`i + 1` and `i` by postcomposing with the specified automorphisms of the displayed standard free
modules. -/
noncomputable def recoordinateTermIsoAtAdjacentDegrees
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R))
    (j : Fin (e + 1)) :
    C.toChainComplex.X j ≅ ModuleCat.of R (Fin (C.rank j) → R) :=
  if h : j = i.succ then
    Eq.ndrec
      (motive := fun k : Fin (e + 1) ↦
        C.toChainComplex.X k ≅ ModuleCat.of R (Fin (C.rank k) → R))
      (C.termIso i.succ ≪≫ uSucc) h.symm
  else if h' : j = i.castSucc then
    Eq.ndrec
      (motive := fun k : Fin (e + 1) ↦
        C.toChainComplex.X k ≅ ModuleCat.of R (Fin (C.rank k) → R))
      (C.termIso i.castSucc ≪≫ uCast) h'.symm
  else
    C.termIso j

/-- Helper for Lemma 10.102.2: the owner-level recoordinated finite free complex keeps the same
underlying chain complex and rank function, changing only the two adjacent coordinate
identifications used in the source proof's basis changes. -/
noncomputable def recoordinateAtAdjacentDegrees
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    _root_.FiniteFreeComplex R e where
  toChainComplex := C.toChainComplex
  isZero_toChainComplex_X := C.isZero_toChainComplex_X
  rank := C.rank
  termIso := recoordinateTermIsoAtAdjacentDegrees C i uSucc uCast

/-- Helper for Lemma 10.102.2: the recoordinated owner does not alter the underlying chain
complex. -/
@[simp] theorem recoordinateAtAdjacentDegrees_toChainComplex
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).toChainComplex = C.toChainComplex := by
  -- The record update keeps the chain-complex owner unchanged.
  rfl

/-- Helper for Lemma 10.102.2: the recoordinated owner preserves the displayed rank function. -/
@[simp] theorem recoordinateAtAdjacentDegrees_rank
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).rank = C.rank := by
  -- Only the coordinate identifications change; the displayed ranks do not.
  rfl

/-- Helper for Lemma 10.102.2: at degree `i + 1`, the recoordinated owner uses the original
coordinate isomorphism followed by the chosen source automorphism. -/
@[simp] theorem recoordinateAtAdjacentDegrees_termIso_succ
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).termIso i.succ =
      C.termIso i.succ ≪≫ uSucc := by
  -- The first branch of the record update is the source-degree basis change.
  simp only [recoordinateAtAdjacentDegrees, recoordinateTermIsoAtAdjacentDegrees, dite_true]

/-- Helper for Lemma 10.102.2: at degree `i`, the recoordinated owner uses the original
coordinate isomorphism followed by the chosen target automorphism. -/
@[simp] theorem recoordinateAtAdjacentDegrees_termIso_castSucc
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).termIso i.castSucc =
      C.termIso i.castSucc ≪≫ uCast := by
  -- The `i` branch is selected after ruling out the impossible equality `i = i + 1`.
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have hval : i.1 = i.1 + 1 := congrArg Fin.val h
    omega
  simp only [recoordinateAtAdjacentDegrees, recoordinateTermIsoAtAdjacentDegrees, hne, dite_false,
    dite_true]

/-- Helper for Lemma 10.102.2: away from degrees `i + 1` and `i`, the recoordinated owner keeps
the original coordinate isomorphism. -/
@[simp] theorem recoordinateAtAdjacentDegrees_termIso_of_ne
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R))
    (j : Fin (e + 1))
    (hjSucc : j ≠ i.succ)
    (hjCast : j ≠ i.castSucc) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).termIso j = C.termIso j := by
  -- Outside the two adjacent degrees, both `if` branches collapse to the original coordinates.
  simp only [recoordinateAtAdjacentDegrees, recoordinateTermIsoAtAdjacentDegrees, hjSucc, hjCast,
    dite_false]

/-- Helper for Lemma 10.102.2: after recoordinating only in degrees `i + 1` and `i`, the middle
differential is conjugated by exactly those two chosen automorphisms. -/
@[simp] theorem recoordinateAtAdjacentDegrees_diffAt
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    ModuleCat.ofHom ((recoordinateAtAdjacentDegrees C i uSucc uCast).diffAt i) =
      uSucc.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ uCast.hom := by
  let D := recoordinateAtAdjacentDegrees C i uSucc uCast
  -- Put the recoordinated differential into the adjacent-degree normal form where the two
  -- modified `termIso`s are visible to rewriting.
  change ModuleCat.ofHom
      (((D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom).hom) =
    uSucc.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ uCast.hom
  -- Expand the original differential in the same adjacent-degree coordinates.
  change (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom =
    uSucc.inv ≫ ((C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫ (C.termIso i.castSucc).hom) ≫
      uCast.hom
  -- After that normalization, the two updated coordinate isomorphisms rewrite directly.
  rw [recoordinateAtAdjacentDegrees_termIso_succ (C := C) (i := i) (uSucc := uSucc)
      (uCast := uCast)]
  rw [recoordinateAtAdjacentDegrees_termIso_castSucc (C := C) (i := i) (uSucc := uSucc)
      (uCast := uCast)]
  -- The recoordinated owner keeps the same underlying differential, so only associativity remains.
  change (uSucc.inv ≫ (C.termIso i.succ).inv) ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
      (C.termIso i.castSucc).hom ≫ uCast.hom =
    uSucc.inv ≫ (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
      (C.termIso i.castSucc).hom ≫ uCast.hom
  simp [Category.assoc]

/-- Helper for Lemma 10.102.2: a unit coordinate in `C.diffAt i` forces the source rank
`rank(C_{i + 1})` to be positive. -/
theorem rank_succ_pos_of_isUnit_diffEntry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc), IsUnit (C.diffEntry i a b)) :
    0 < C.rank i.succ := by
  -- Any witnessed source coordinate already gives a nonempty `Fin`, hence positive rank.
  rcases hunit with ⟨a, -, -⟩
  exact lt_of_le_of_lt (Nat.zero_le a.1) a.2

/-- Helper for Lemma 10.102.2: a unit coordinate in `C.diffAt i` forces the target rank
`rank(C_i)` to be positive. -/
theorem rank_castSucc_pos_of_isUnit_diffEntry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc), IsUnit (C.diffEntry i a b)) :
    0 < C.rank i.castSucc := by
  -- Any witnessed target coordinate already gives a nonempty `Fin`, hence positive rank.
  rcases hunit with ⟨-, b, -⟩
  exact lt_of_le_of_lt (Nat.zero_le b.1) b.2

/-- Helper for Lemma 10.102.2: the two ranks adjacent to a unit differential entry can be written
as successors, so the distinguished coordinates can be moved to `0` and split off. -/
theorem exists_rank_eq_succ_of_isUnit_diffEntry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc), IsUnit (C.diffEntry i a b)) :
    ∃ ns nt : ℕ, C.rank i.succ = ns + 1 ∧ C.rank i.castSucc = nt + 1 := by
  -- Repackage the positivity forced by `hunit` into successor decompositions of the two ranks.
  obtain ⟨ns, hs⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (rank_succ_pos_of_isUnit_diffEntry (C := C) (i := i) hunit))
  obtain ⟨nt, ht⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (rank_castSucc_pos_of_isUnit_diffEntry (C := C) (i := i) hunit))
  exact ⟨ns, nt, hs, ht⟩

end FiniteFreeComplex

end
