module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.CoprodI

public section

open scoped DirectSum

universe u v

namespace Abelianization

/-- The canonical inclusion of one factor abelianization into their direct sum. -/
noncomputable def factorToDirectSum {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)]
    (i : ι) : Additive (Abelianization (G i)) →+ ⨁ i, Additive (Abelianization (G i)) :=
  -- Local instance justification (noncanonical choice): this representation-level choice is
  -- encapsulated here so the mathematical inclusion API does not require `DecidableEq ι`.
  letI := Classical.decEq ι
  DirectSum.of (fun i ↦ Additive (Abelianization (G i))) i

/-- Helper for Exercise 69.2: the multiplicative form of a factor inclusion agrees
with `DirectSum.of` on every additive element. -/
lemma factorToDirectSum_toMultiplicative_apply {ι : Type u} (G : ι → Type v)
    [∀ i, Group (G i)] (i : ι) (x : Additive (Abelianization (G i))) :
    (factorToDirectSum G i).toMultiplicative (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (factorToDirectSum G i x) := by
  -- Unwrap the multiplicative type tag around the canonical factor inclusion.
  rw [AddMonoidHom.coe_toMultiplicative]
  simp only [Function.comp_apply, toAdd_ofAdd]

/-- The canonical homomorphism from the abelianization of an indexed free product to
the direct sum of the abelianizations of its factors. -/
noncomputable def coprodIToDirectSum {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)] :
    Abelianization (Monoid.CoprodI G) →*
      Multiplicative (⨁ i, Additive (Abelianization (G i))) :=
  lift <| Monoid.CoprodI.lift fun i ↦
    (factorToDirectSum G i).toMultiplicative.comp of

/-- The canonical homomorphism from the direct sum of the factor abelianizations to
the abelianization of their indexed free product. -/
noncomputable def directSumToCoprodI {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)] :
    Multiplicative (⨁ i, Additive (Abelianization (G i))) →*
      Abelianization (Monoid.CoprodI G) :=
  -- Local instance justification (noncanonical choice): `DirectSum` needs `DecidableEq ι`.
  letI := Classical.decEq ι
  -- Interpret the additive lift directly as a map into the target abelianization.
  (DirectSum.toAddMonoid fun i ↦
    (map (Monoid.CoprodI.of : G i →* Monoid.CoprodI G)).toAdditive).toMultiplicativeLeft

/-- Helper for Exercise 69.2: the canonical map from the direct sum restricts on each
factor to the map induced by the corresponding free-product inclusion. -/
lemma directSumToCoprodI_comp_factorToDirectSum {ι : Type u} (G : ι → Type v)
    [∀ i, Group (G i)] (i : ι) :
    (directSumToCoprodI G).comp (factorToDirectSum G i).toMultiplicative =
      map (Monoid.CoprodI.of : G i →* Monoid.CoprodI G) := by
  -- Evaluate the direct-sum lift on a generator from the chosen factor.
  classical
  apply MonoidHom.ext
  intro x
  induction x using Multiplicative.rec with
  | ofAdd x =>
      simp only [MonoidHom.comp_apply, directSumToCoprodI, factorToDirectSum]
      rw [AddMonoidHom.coe_toMultiplicative, AddMonoidHom.coe_toMultiplicativeLeft]
      simp only [Function.comp_apply, toAdd_ofAdd, DirectSum.toAddMonoid_of,
        MonoidHom.coe_toAdditive, toMul_ofMul]
      rfl

/-- Helper for Exercise 69.2: the canonical map to the direct sum restricts on each
abelianized factor to its direct-sum inclusion. -/
lemma coprodIToDirectSum_comp_map_of {ι : Type u} (G : ι → Type v)
    [∀ i, Group (G i)] (i : ι) :
    (coprodIToDirectSum G).comp
        (map (Monoid.CoprodI.of : G i →* Monoid.CoprodI G)) =
      (factorToDirectSum G i).toMultiplicative := by
  -- Reduce equality on an abelianization to equality on the original factor generators.
  apply hom_ext
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, map_of, lift_apply_of, coprodIToDirectSum,
    Monoid.CoprodI.lift_of]
  rfl

/-- Helper for Exercise 69.2: evaluating the canonical map after a factor inclusion
gives the corresponding direct-sum factor element. -/
lemma coprodIToDirectSum_map_of_apply {ι : Type u} (G : ι → Type v)
    [∀ i, Group (G i)] (i : ι) (x : Abelianization (G i)) :
    coprodIToDirectSum G
        (map (Monoid.CoprodI.of : G i →* Monoid.CoprodI G) x) =
      (factorToDirectSum G i).toMultiplicative x := by
  -- Specialize the factor-restriction equation and normalize homomorphism composition.
  have factorRestriction := DFunLike.congr_fun (coprodIToDirectSum_comp_map_of G i) x
  exact factorRestriction

/-- Composing the canonical map to the direct sum with the canonical map back to the
abelianized indexed free product gives the identity. -/
theorem directSumToCoprodI_comp_coprodIToDirectSum {ι : Type u} (G : ι → Type v)
    [∀ i, Group (G i)] :
    (directSumToCoprodI G).comp (coprodIToDirectSum G) =
      MonoidHom.id (Abelianization (Monoid.CoprodI G)) := by
  -- The abelianization and free-product universal properties reduce the identity to each factor.
  apply hom_ext
  apply Monoid.CoprodI.ext_hom
  intro i
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, lift_apply_of, coprodIToDirectSum,
    Monoid.CoprodI.lift_of, MonoidHom.id_apply]
  rw [← map_of (Monoid.CoprodI.of : G i →* Monoid.CoprodI G) x]
  exact DFunLike.congr_fun (directSumToCoprodI_comp_factorToDirectSum G i) (of x)

/-- Composing the canonical map to the abelianized indexed free product with the
canonical map back to the direct sum gives the identity. -/
theorem coprodIToDirectSum_comp_directSumToCoprodI {ι : Type u} (G : ι → Type v)
    [∀ i, Group (G i)] :
    (coprodIToDirectSum G).comp (directSumToCoprodI G) =
      MonoidHom.id (Multiplicative (⨁ i, Additive (Abelianization (G i)))) := by
  -- Move to additive homomorphisms and compare the two maps on direct-sum generators.
  classical
  apply Multiplicative.monoidHom_ext
  apply DirectSum.addHom_ext
  intro i x
  apply Additive.ext
  simp only [MonoidHom.coe_toAdditiveRight, Function.comp_apply, toMul_ofMul,
    MonoidHom.comp_apply, MonoidHom.id_apply]
  have factorImage := factorToDirectSum_toMultiplicative_apply G i x
  simp only [factorToDirectSum] at factorImage
  have backwardImage :=
    DFunLike.congr_fun (directSumToCoprodI_comp_factorToDirectSum G i)
      (Multiplicative.ofAdd x)
  rw [MonoidHom.comp_apply] at backwardImage
  have forwardImage := coprodIToDirectSum_map_of_apply G i (Multiplicative.ofAdd x)
  exact (congrArg (fun y ↦ coprodIToDirectSum G (directSumToCoprodI G y))
      factorImage.symm).trans
    ((congrArg (coprodIToDirectSum G) backwardImage).trans
      (forwardImage.trans factorImage))

/-- The abelianization of an indexed free product is canonically multiplicatively
equivalent to the direct sum of the abelianizations of its factors. -/
noncomputable def coprodIMulEquivDirectSum {ι : Type u} (G : ι → Type v)
    [∀ i, Group (G i)] :
    Abelianization (Monoid.CoprodI G) ≃*
      Multiplicative (⨁ i, Additive (Abelianization (G i))) :=
  (coprodIToDirectSum G).toMulEquiv (directSumToCoprodI G)
    (directSumToCoprodI_comp_coprodIToDirectSum G)
    (coprodIToDirectSum_comp_directSumToCoprodI G)

/-- The indexed equivalence sends a generator from a free-product factor to the
corresponding element of the direct sum. -/
@[simp]
theorem coprodIMulEquivDirectSum_of {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)]
    (i : ι) (x : G i) :
    coprodIMulEquivDirectSum G (of (Monoid.CoprodI.of x)) =
      Multiplicative.ofAdd (factorToDirectSum G i (Additive.ofMul (of x))) := by
  -- Compute the equivalence through the abelianization lift and the indexed coproduct lift.
  rfl

end Abelianization
