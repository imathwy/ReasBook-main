import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksProject_2024.Chap10.Lemma_10_55_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section FiniteGrothendieckGroup

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact

variable (R : Type u) [Ring R]

/- Domain-style sampling for Lemma 10.55.1:
- primary domain: additive invariants of `K'_0(R)` for finitely generated `R`-modules, with the
  invariant given by module length over an Artinian ring;
- sampled owner declarations:
  `ModulePropertyK0.lift`,
  `ModulePropertyK0.lift_of`,
  `finiteGrothendieckGroup`,
  `Module.length_eq_add_of_exact`;
- best owner abstraction:
  the public map `finiteGrothendieckGroup_lengthMap` should be presented as the canonical Chapter
  10 quotient lift of the generator-level length functional, not as a parallel wrapper around the
  same quotient construction;
- primitive vs. derived:
  primitive data is only the value on a finite module,
  `M ↦ ((Module.length R M.obj).toNat : ℤ)`;
  the kernel statement, descended homomorphism, and evaluation-on-generators theorem are derived
  from that owner abstraction;
- source/core/bridge triage:
  `source-facing`: `finiteGrothendieckGroup_lengthMap`;
  `core/canonical`: `ModulePropertyK0.lift`;
  `bridge/view`: the Artinian-length realization given by `Module.length`.

This file should therefore keep the length functional private at the generator level and expose
only the descended map together with its generator evaluation formula.
-/

-- Proof sketch: over an Artinian ring every finite module has finite length, and module length is
-- additive on short exact sequences by `Module.length_eq_add_of_exact`, so every Grothendieck
-- relation is sent to zero.
/-- Helper for Lemma 10.55.1: the generator-level length functional vanishes on the defining
Grothendieck relations coming from short exact sequences of finitely generated modules. -/
private theorem relations_le_ker_length [IsArtinianRing R] :
    modulePropertyK0Relations R (ModuleCat.isFG R) ≤
      (FreeAbelianGroup.lift fun M : FGModuleCat R ↦ ((Module.length R M.obj).toNat : ℤ)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift (fun M : FGModuleCat R ↦ ((Module.length R M.obj).toNat : ℤ))
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  let T : ShortComplex (ModuleCat R) := S.map (ModuleCat.isFG R).ι
  let _ : Module.Finite R S.X₁.obj := S.X₁.property
  let _ : Module.Finite R S.X₂.obj := S.X₂.property
  let _ : Module.Finite R S.X₃.obj := S.X₃.property
  have hT : T.ShortExact := by
    simpa [T] using hS
  have hExact : Function.Exact T.f.hom T.g.hom := by
    simpa using (moduleCat_exact_iff_function_exact T).mp hT.exact
  have hlength :
      Module.length R S.X₂.obj =
        Module.length R S.X₁.obj + Module.length R S.X₃.obj := by
    simpa [T] using Module.length_eq_add_of_exact
      T.f.hom
      T.g.hom
      hT.moduleCat_injective_f
      hT.moduleCat_surjective_g
      hExact
  have hlen₁ : Module.length R S.X₁.obj ≠ ⊤ := Module.length_ne_top
  have hlen₃ : Module.length R S.X₃.obj ≠ ⊤ := Module.length_ne_top
  have hlengthNat :
      (Module.length R S.X₂.obj).toNat =
        (Module.length R S.X₁.obj).toNat + (Module.length R S.X₃.obj).toNat := by
    simpa [ENat.toNat_add hlen₁ hlen₃] using congrArg ENat.toNat hlength
  have hlength' :
      ((Module.length R S.X₂.obj).toNat : ℤ) =
        ((Module.length R S.X₁.obj).toNat : ℤ) + ((Module.length R S.X₃.obj).toNat : ℤ) := by
    simpa [Nat.cast_add] using congrArg (fun n : ℕ ↦ (n : ℤ)) hlengthNat
  linarith

/-- Lemma 10.55.1: if `R` is an Artinian local ring, then the length function defines a natural
abelian group homomorphism `K'_0(R) → ℤ`. Canonically, the same construction works for any
Artinian ring. -/
def finiteGrothendieckGroup_lengthMap [IsArtinianRing R] :
    finiteGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R
    (fun M : FGModuleCat R ↦ ((Module.length R M.obj).toNat : ℤ))
    (relations_le_ker_length R)

-- Proof sketch: `finiteGrothendieckGroup_lengthMap` is the quotient lift of the module-length
-- functional on `FGModuleCat R`, so on a generator class it returns the length of that finite
-- module.
/-- The length map sends the class of a finite module to its length. -/
@[simp]
theorem finiteGrothendieckGroup_lengthMap_apply_of
    [IsArtinianRing R] (M : FGModuleCat R) :
    finiteGrothendieckGroup_lengthMap R
        (finiteGrothendieckGroupOf R M) =
      ((Module.length R M.obj).toNat : ℤ) := by
  simpa using ModulePropertyK0.lift_of R
    (fun N : FGModuleCat R ↦ ((Module.length R N.obj).toNat : ℤ))
    (relations_le_ker_length R)
    M

end FiniteGrothendieckGroup
