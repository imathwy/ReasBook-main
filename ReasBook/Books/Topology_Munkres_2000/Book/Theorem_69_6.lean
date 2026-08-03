module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Module.PID

public section

universe u

/-- Helper for Theorem 69.6: subtracting the lift along a linear section leaves an
element in the kernel of the split map. -/
private lemma LinearMap.sub_section_mem_ker_of_comp_eq_id
    {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (h : f.comp s = LinearMap.id) (x : M) :
    x - s (f x) ∈ LinearMap.ker f := by
  -- Applying `f` cancels the lifted part by the section equation.
  have hleft : Function.LeftInverse f s := DFunLike.congr_fun h
  rw [LinearMap.mem_ker, map_sub, hleft, sub_self]

/-- Helper for Theorem 69.6: the range of a linear section is complementary to the
kernel of the map that it splits. -/
private lemma LinearMap.isCompl_range_ker_of_comp_eq_id
    {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (h : f.comp s = LinearMap.id) :
    IsCompl (LinearMap.range s) (LinearMap.ker f) := by
  -- The splitting equation first gives a pointwise left inverse for the section.
  have hleft : Function.LeftInverse f s := DFunLike.congr_fun h
  constructor
  · -- An element in both submodules has a zero preimage under the injective section.
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨y, rfl⟩ := hx.1
    have hy : y = 0 := (hleft y).symm.trans (LinearMap.mem_ker.mp hx.2)
    rw [hy, map_zero]
  · -- Every element is its lifted image plus an element killed by `f`.
    rw [codisjoint_iff_le_sup]
    intro x _
    have hlift : s (f x) ∈ LinearMap.range s := LinearMap.mem_range_self s (f x)
    have hremainder := LinearMap.sub_section_mem_ker_of_comp_eq_id f s h x
    rw [Submodule.mem_sup']
    exact ⟨⟨s (f x), hlift⟩, ⟨x - s (f x), hremainder⟩, add_sub_cancel _ _⟩

/-- Helper for Theorem 69.6: complementary ℤ-submodules remain complementary as
additive subgroups. -/
private lemma Submodule.isCompl_toAddSubgroup
    {G : Type*} [AddCommGroup G] {P Q : Submodule ℤ G} (h : IsCompl P Q) :
    IsCompl P.toAddSubgroup Q.toAddSubgroup := by
  -- Transport the complementary pair through the canonical order isomorphism.
  exact AddSubgroup.toIntSubmodule.symm.isCompl h

/-- Theorem 69.6. Every finitely generated abelian group has a finite-rank free
additive subgroup complementary to its canonical subgroup of finite-order elements.
Here `Module.Basis (Fin n) ℤ H` expresses that `H` is free abelian of finite rank,
and `IsCompl H (AddCommGroup.torsion G)` expresses the internal direct sum. -/
theorem exists_freeAddSubgroup_isCompl_torsion
    {G : Type u} [AddCommGroup G] [AddGroup.FG G] :
    ∃ (n : ℕ) (H : AddSubgroup G) (b : Module.Basis (Fin n) ℤ H),
      IsCompl H (AddCommGroup.torsion G) := by
  classical
  -- The torsion-free quotient supplies the finite rank and its basis.
  let T : Submodule ℤ G := Submodule.torsion ℤ G
  letI : Module.Finite ℤ (G ⧸ T) := Module.Finite.quotient ℤ T
  letI : Module.IsTorsionFree ℤ (G ⧸ T) :=
    Submodule.QuotientTorsion.instIsTorsionFree
  obtain ⟨n, bQ⟩ : Σ n, Module.Basis (Fin n) ℤ (G ⧸ T) :=
    Module.basisOfFiniteTypeTorsionFree'
  -- Projectivity of the free quotient produces a linear section of the quotient map.
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property T.mkQ LinearMap.id T.mkQ_surjective
  have hsLeftInverse : Function.LeftInverse T.mkQ s := DFunLike.congr_fun hs
  have hsInjective : Function.Injective s := hsLeftInverse.injective
  -- Transport the quotient basis to the range of the chosen section.
  let bH : Module.Basis (Fin n) ℤ (LinearMap.range s).toAddSubgroup :=
    bQ.map (LinearEquiv.ofInjective s hsInjective)
  -- The split quotient identifies that range as a complement of precisely `T`.
  have hCompl := LinearMap.isCompl_range_ker_of_comp_eq_id T.mkQ s hs
  rw [Submodule.ker_mkQ] at hCompl
  have hComplAdd := Submodule.isCompl_toAddSubgroup hCompl
  dsimp only [T] at hComplAdd
  rw [Submodule.torsion_int] at hComplAdd
  -- Assemble the internal direct-sum subgroup with its transported finite basis.
  exact ⟨n, (LinearMap.range s).toAddSubgroup, bH, hComplAdd⟩
