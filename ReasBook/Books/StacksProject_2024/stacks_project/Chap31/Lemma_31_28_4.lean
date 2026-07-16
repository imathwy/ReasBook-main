import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.Tactic.StacksAttribute
import StacksProject_2024.stacks_project.Chap17.Definition_17_25_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry RingedSpacePicard SpecOfNotation

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the ring-theoretic owner `CommRing.Pic`, while
-- local Chapter 31 precedent uses the ringed-space Picard notation
-- `Pic(X.toRingedSpace)` for scheme Picard groups. The affine-space clauses use mathlib's
-- canonical owner `𝔸(Fin n; Spec(R))`, identified with `Spec(R[x_1, ..., x_n])` by
-- `AffineSpace.SpecIso`.

/-- Lemma 31.28.4 (1): if `R` is a unique factorization domain, then the Picard group of
`Spec(R)` is trivial. -/
@[stacks 0BDA]
theorem subsingleton_picardGroup_Spec_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [MonoidalCategory (RingedSpace.Modules (Spec(R)).toRingedSpace)]
    [SymmetricCategory (RingedSpace.Modules (Spec(R)).toRingedSpace)] :
    Subsingleton (Pic((Spec(R)).toRingedSpace)) := sorry

/-- Lemma 31.28.4 (2): if `R` is a unique factorization domain, then the Picard group of every
open subscheme of `Spec(R)` is trivial. -/
@[stacks 0BDA]
theorem subsingleton_picardGroup_openSubscheme_Spec_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (U : (Spec(R)).Opens)
    [MonoidalCategory (RingedSpace.Modules U.toScheme.toRingedSpace)]
    [SymmetricCategory (RingedSpace.Modules U.toScheme.toRingedSpace)] :
    Subsingleton (Pic(U.toScheme.toRingedSpace)) := sorry

/-- Lemma 31.28.4 (3): if `R` is a unique factorization domain, then the Picard group of affine
`n`-space `𝔸^n_R`, represented as `𝔸(Fin n; Spec(R))`, is trivial. -/
@[stacks 0BDA]
theorem subsingleton_picardGroup_affineSpace_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (n : ℕ)
    [MonoidalCategory (RingedSpace.Modules (𝔸(Fin n; Spec(R))).toRingedSpace)]
    [SymmetricCategory (RingedSpace.Modules (𝔸(Fin n; Spec(R))).toRingedSpace)] :
    Subsingleton (Pic((𝔸(Fin n; Spec(R))).toRingedSpace)) := sorry

/-- Lemma 31.28.4 (4): if `R` is a unique factorization domain, then the Picard group of every
open subscheme of affine `n`-space `𝔸^n_R` is trivial. -/
@[stacks 0BDA]
theorem subsingleton_picardGroup_openSubscheme_affineSpace_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (n : ℕ)
    (U : (𝔸(Fin n; Spec(R))).Opens)
    [MonoidalCategory (RingedSpace.Modules U.toScheme.toRingedSpace)]
    [SymmetricCategory (RingedSpace.Modules U.toScheme.toRingedSpace)] :
    Subsingleton (Pic(U.toScheme.toRingedSpace)) := sorry

/-- Lemma 31.28.4 (5): in particular, over a field `k`, the Picard group of every open subscheme
of affine `n`-space `𝔸^n_k` is trivial. -/
@[stacks 0BDA]
theorem subsingleton_picardGroup_openSubscheme_affineSpace_of_field
    (k : Type u) [Field k] (n : ℕ) (U : (𝔸(Fin n; Spec(k))).Opens)
    [MonoidalCategory (RingedSpace.Modules U.toScheme.toRingedSpace)]
    [SymmetricCategory (RingedSpace.Modules U.toScheme.toRingedSpace)] :
    Subsingleton (Pic(U.toScheme.toRingedSpace)) := sorry

end AlgebraicGeometry.Scheme
