module

public import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv

public section

universe uι uκ uG uH

/-- Theorem 69.5 (1). Two free abelian groups with chosen bases are isomorphic if and
only if their basis index types have the same cardinality. -/
theorem freeAbelianGroupEquivIffBasisEquiv
    {ι : Type uι} {κ : Type uκ} {G : Type uG} {H : Type uH}
    [AddCommGroup G] [AddCommGroup H]
    (bG : Module.Basis ι ℤ G) (bH : Module.Basis κ ℤ H) :
    Nonempty (G ≃+ H) ↔ Nonempty (ι ≃ κ) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(bG.map e.toIntLinearEquiv).indexEquiv bH⟩
  · rintro ⟨e⟩
    exact ⟨(bG.equiv bH e).toAddEquiv⟩

/-- Theorem 69.5 (2). Two free groups with chosen systems of free generators are
isomorphic if and only if their generator index types have the same cardinality. -/
theorem freeGroupEquivIffBasisEquiv
    {ι : Type uι} {κ : Type uκ} {G : Type uG} {H : Type uH}
    [Group G] [Group H]
    (bG : FreeGroupBasis ι G) (bH : FreeGroupBasis κ H) :
    Nonempty (G ≃* H) ↔ Nonempty (ι ≃ κ) := by
  constructor
  · rintro ⟨e⟩
    let basisEquiv := bG.repr.symm
    exact ⟨Equiv.ofFreeGroupEquiv (basisEquiv.trans (e.trans bH.repr))⟩
  · rintro ⟨e⟩
    let generatorEquiv := FreeGroup.freeGroupCongr e
    exact ⟨bG.repr.trans (generatorEquiv.trans bH.repr.symm)⟩
