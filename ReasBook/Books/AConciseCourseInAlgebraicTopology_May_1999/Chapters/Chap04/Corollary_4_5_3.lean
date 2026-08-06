module

public import Mathlib.GroupTheory.Schreier

public section

universe u

-- Semantic recall via `lean_leansearch`: `subgroupIsFreeOfIsFree` gives the freeness of
-- subgroups of free groups, while `Subgroup.rank_le_index_mul_rank` is the nearby canonical
-- rank-control theorem behind the Schreier index formula.

section

variable {G : Type u} [Group G]

/-- Corollary 4.5.3. If `G` is free on `k` generators and `H` has finite index `n` in `G`, then
`H` has rank `H.index * k + 1 - H.index`. Writing `n = H.index` recovers the usual
Schreier formula `n * k + 1 - n`. Together with the canonical Nielsen-Schreier instance
`subgroupIsFreeOfIsFree`, this records that `H` is free on `H.index * k + 1 - H.index`
generators. -/
theorem subgroup_rank_eq_of_freeGroupFinEquiv (H : Subgroup G) {k : ℕ}
    (hG : FreeGroup (Fin k) ≃* G) [H.FiniteIndex] :
    let _ : Group.FG G :=
      Group.fg_iff_monoid_fg.mpr <| Monoid.fg_of_surjective hG.toMonoidHom hG.surjective
    Group.rank H = H.index * k + 1 - H.index := sorry

/-- Companion form of `subgroup_rank_eq_of_freeGroupFinEquiv` using an explicit witness
`n = H.index`. -/
theorem subgroup_rank_eq_of_freeGroupFinEquiv_index_eq (H : Subgroup G) {k n : ℕ}
    (hG : FreeGroup (Fin k) ≃* G) [H.FiniteIndex] (hn : H.index = n) :
    let _ : Group.FG G :=
      Group.fg_iff_monoid_fg.mpr <| Monoid.fg_of_surjective hG.toMonoidHom hG.surjective
    Group.rank H = n * k + 1 - n := by
  simpa [hn] using subgroup_rank_eq_of_freeGroupFinEquiv H hG

end
