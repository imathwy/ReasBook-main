import Mathlib

noncomputable section

universe u x

namespace Representation

open Polynomial Module

set_option linter.unusedVariables false in
/-- An endomorphism of finite order prime to the characteristic of an algebraically closed field
admits an eigenbasis. -/
theorem exists_eigenbasis_of_pow_eq_one {k : Type u} [Field k] [IsAlgClosed k]
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (u : V →ₗ[k] V) {m : ℕ} (hm : m ≠ 0) (hmk : (m : k) ≠ 0) (hu : u ^ m = 1) :
    ∃ (κ : Type x) (_ : Fintype κ) (b : Module.Basis κ k V) (d : κ → k),
      ∀ i, u (b i) = d i • b i := by
  classical
  -- `u` is annihilated by the squarefree polynomial `X ^ m - 1`.
  have hann : aeval u (X ^ m - C (1 : k)) = 0 := by
    simp [hu]
  have hsq : Squarefree (X ^ m - C (1 : k)) :=
    (separable_X_pow_sub_C (1 : k) hmk one_ne_zero).squarefree
  have hss : Module.End.IsSemisimple u :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hann
  -- the eigenspaces fill out the whole space
  have htop : ⨆ μ : k, Module.End.eigenspace u μ = ⊤ :=
    hss.iSup_eigenspace_eq_top
  -- restrict to the finite set of roots of the characteristic polynomial
  set s : Finset k := u.charpoly.roots.toFinset with hs
  have hbot : ∀ μ : k, μ ∉ s → Module.End.eigenspace u μ = ⊥ := by
    intro μ hμ
    by_contra hne
    have hev : Module.End.HasEigenvalue u μ :=
      Module.End.hasEigenvalue_iff.mpr hne
    have hroot : u.charpoly.IsRoot μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mp hev
    exact hμ <| Multiset.mem_toFinset.mpr <|
      Polynomial.mem_roots'.mpr ⟨u.charpoly_monic.ne_zero, hroot⟩
  have htop' : ⨆ μ : s, Module.End.eigenspace u (μ : k) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ s
    · exact le_iSup_of_le ⟨μ, hμ⟩ le_rfl
    · rw [hbot μ hμ]
      exact bot_le
  have hind : iSupIndep fun μ : s => Module.End.eigenspace u (μ : k) :=
    (Module.End.eigenspaces_iSupIndep (u : Module.End k V)).comp Subtype.val_injective
  have hint : DirectSum.IsInternal fun μ : s => Module.End.eigenspace u (μ : k) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hind, htop'⟩
  -- collect bases of the eigenspaces into a basis of `V`
  let v : ∀ μ : s, Module.Basis
      (Fin (Module.finrank k (Module.End.eigenspace u (μ : k)))) k
      (Module.End.eigenspace u (μ : k)) :=
    fun μ => Module.finBasis k _
  let b₀ := hint.collectedBasis v
  have hb₀ : ∀ a, u (b₀ a) = (a.1 : k) • b₀ a := fun a =>
    Module.End.mem_eigenspace_iff.mp (hint.collectedBasis_mem v a)
  -- transport the basis to an index type in the universe of `V`
  let e := (b₀.indexEquiv (Module.finBasis k V)).trans
    (Equiv.ulift.{x} (α := Fin (Module.finrank k V))).symm
  refine ⟨ULift.{x} (Fin (Module.finrank k V)), inferInstance, b₀.reindex e,
    fun i => ((e.symm i).1 : k), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb₀ (e.symm i)]

/-- The characteristic polynomial roots of an endomorphism with an eigenbasis are the multiset of
eigenvalues attached to the basis. -/
theorem charpoly_roots_of_eigenbasis {k : Type u} [Field k]
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (u : V →ₗ[k] V) {κ : Type x} [Fintype κ] (b : Module.Basis κ k V) (d : κ → k)
    (hb : ∀ i, u (b i) = d i • b i) :
    u.charpoly.roots = Finset.univ.val.map d := by
  classical
  have hmat : LinearMap.toMatrix b b u = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, Module.Basis.repr_self]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij]
  rw [← LinearMap.charpoly_toMatrix u b, hmat, Matrix.charpoly_diagonal]
  have hprod : (∏ i, (X - C (d i)))
      = ((Finset.univ.val.map d).map fun a => X - C a).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  rw [hprod, roots_multiset_prod_X_sub_C]

end Representation
