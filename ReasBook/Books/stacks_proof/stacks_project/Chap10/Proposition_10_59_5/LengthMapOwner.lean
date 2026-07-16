import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import stacks_proof.stacks_project.Chap10.Proposition_10_58_7

-- Proof rescue support for Proposition 10.59.5: Grothendieck length map on the Chapter 10 owners
-- imported from Proposition 10.58.7.

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact

section FiniteGrothendieckGroup

variable (R : Type u) [Ring R]

/-- Helper for Proposition 10.59.5: the generator-level length functional on finite modules kills
the short-exact-sequence relations for the Grothendieck owners from Proposition `10.58.7`. -/
private theorem finiteGrothendieckGroup_relations_le_ker_length_owner [IsArtinianRing R] :
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
    -- Forgetting the finiteness predicate keeps the same short exact sequence in `ModuleCat`.
    simpa [T] using hS
  have hExact : Function.Exact T.f.hom T.g.hom := by
    -- The additive relation is controlled by the usual exactness statement on the underlying maps.
    simpa using (moduleCat_exact_iff_function_exact T).mp hT.exact
  have hlength :
      Module.length R S.X₂.obj =
        Module.length R S.X₁.obj + Module.length R S.X₃.obj := by
    -- Length is additive on short exact sequences over an Artinian ring.
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
    -- Passing to natural numbers is legitimate because all three lengths are finite.
    simpa [ENat.toNat_add hlen₁ hlen₃] using congrArg ENat.toNat hlength
  have hlengthInt :
      ((Module.length R S.X₂.obj).toNat : ℤ) =
        ((Module.length R S.X₁.obj).toNat : ℤ) + ((Module.length R S.X₃.obj).toNat : ℤ) := by
    -- The target additive group is `ℤ`, so cast the finite-length identity once at the end.
    simpa [Nat.cast_add] using congrArg (fun n : ℕ ↦ (n : ℤ)) hlengthNat
  linarith

/-- Helper for Proposition 10.59.5: the Chapter 10 Grothendieck owners from Proposition `10.58.7`
carry the same length realization `K'_0(R) → ℤ` over an Artinian ring. -/
def finiteGrothendieckGroup_lengthMap_owner [IsArtinianRing R] :
    finiteGrothendieckGroup R →+ ℤ :=
  QuotientAddGroup.lift (modulePropertyK0Relations R (ModuleCat.isFG R))
    (FreeAbelianGroup.lift fun M : FGModuleCat R ↦ ((Module.length R M.obj).toNat : ℤ))
    (finiteGrothendieckGroup_relations_le_ker_length_owner R)

/-- Helper for Proposition 10.59.5: the owner-level length map evaluates on a generator class by
the ordinary module length. -/
@[simp] theorem finiteGrothendieckGroup_lengthMap_owner_apply_of
    [IsArtinianRing R] (M : FGModuleCat R) :
    finiteGrothendieckGroup_lengthMap_owner R
        (finiteGrothendieckGroupOf R M) =
      ((Module.length R M.obj).toNat : ℤ) := by
  -- Unfold the quotient lift only at the generator class where the defining function is visible.
  simp [finiteGrothendieckGroup_lengthMap_owner, finiteGrothendieckGroupOf, ModulePropertyK0.of]

end FiniteGrothendieckGroup
