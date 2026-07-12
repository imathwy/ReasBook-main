import Mathlib
import StacksProject_2024.Chap10.Lemma_10_71_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ChainComplex
open HomologicalComplex

universe u

namespace ModuleCat

section

variable {R : Type u} [CommRing R]
variable (M N : ModuleCat R) [Module.Finite R M]

/-- Helper for Lemma 10.75.7: `Tor` in degree `p` is computed by the homology of a finite free
resolution of the second variable tensored with the first variable. -/
noncomputable def tor_iso_homology_tensorized_resolution
    {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj N)
    [ChainComplex.IsFiniteFreeResolution π] (p : ℕ) :
    (((Tor (ModuleCat R) p).obj M).obj N) ≅
      ((((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        F).homology p := by
  -- Convert the chosen finite free resolution into the projective resolution used by `Tor`.
  simpa [Tor] using
    (ChainComplex.IsFreeResolution.toProjectiveResolution (M := N) π).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat R)).obj M) p

/-- Helper for Lemma 10.75.7: tensoring a finite free resolution with a finite module stays
termwise finite. -/
lemma tensorized_resolution_termwise_finite
    {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj N)
    [ChainComplex.IsFiniteFreeResolution π] (n : ℕ) :
    Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          F).X n) := by
  -- The resolution gives finiteness of `F_n`, and tensor products of finite modules stay finite.
  letI : Module.Finite R (F.X n) := ChainComplex.IsFiniteFreeResolution.finite π n
  simpa using
    (Module.Finite.tensorProduct (R := R) (M := (M : Type u)) (N := (F.X n : Type u)))

/-- Helper for Lemma 10.75.7: the homology of a termwise finite chain complex of modules is
finite. -/
lemma homology_finite_of_termwise_finite
    [IsNoetherianRing R] (C : ChainComplex (ModuleCat R) ℕ) [∀ n, Module.Finite R (C.X n)]
    (p : ℕ) :
    Module.Finite R (C.homology p) := by
  -- The opcycles are finite because they are a quotient of the finite module `C.X p`.
  letI : Module.Finite R (C.opcycles p) := by
    exact
      Module.Finite.of_surjective (C.pOpcycles p).hom ((ModuleCat.epi_iff_surjective _).1
        inferInstance)
  -- The homology is finite because it injects into the finite module of opcycles.
  exact
    Module.Finite.of_injective (C.homologyι p).hom ((ModuleCat.mono_iff_injective _).1
      inferInstance)

section

variable [IsNoetherianRing R]
variable [Module.Finite R N]

-- Proof sketch: choose a projective resolution of `N` by finite free modules using
-- `module_exists_finite_free_resolution`; tensor it with `M`, so every term remains a finite
-- module by `Module.Finite.tensorProduct`; then identify `Tor` as the homology of this complex and
-- use that subquotients of finite modules over a Noetherian ring are finite.
/-- Library-facing form of Lemma 10.75.7 (Tag `0AZ4`): over a Noetherian commutative ring, the
`p`-th `Tor` of two finite modules is finite. -/
theorem finite_tor (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) p).obj M).obj N) := by
  -- Resolve `N` by finite free modules exactly as in Lemma 10.71.1.
  rcases module_exists_finite_free_resolution (R := R) (M := N) with ⟨F, π, hπ⟩
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let T :=
    ((((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj F)
  let e : (((Tor (ModuleCat R) p).obj M).obj N) ≅ T.homology p :=
    tor_iso_homology_tensorized_resolution (R := R) (M := M) (N := N) π p
  -- Every term of the tensorized resolution is finite.
  letI (n : ℕ) : Module.Finite R (T.X n) := by
    simpa [T] using tensorized_resolution_termwise_finite (R := R) (M := M) (N := N) π n
  -- The homology is therefore finite, and the comparison isomorphism transports finiteness back.
  letI : Module.Finite R (T.homology p) := homology_finite_of_termwise_finite (R := R) T p
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Typeclass support for finiteness of `Tor_p^R(M, N)` under the hypotheses of
`ModuleCat.finite_tor`. -/
instance (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) p).obj M).obj N) :=
  finite_tor M N p

end

end

end ModuleCat

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N]

/-- Lemma 10.75.7 (Tag 0AZ4): if `R` is Noetherian and `M`, `N` are finite `R`-modules, then
`Tor_p^R(M, N)` is a finite `R`-module for every `p`. -/
@[stacks 0AZ4]
theorem Lemma_10_75_7 (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) p).obj M).obj N) :=
  ModuleCat.finite_tor M N p

end
