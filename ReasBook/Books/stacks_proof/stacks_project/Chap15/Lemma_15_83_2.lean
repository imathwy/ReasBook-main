import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_67_1
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import stacks_proof.stacks_project.Chap15.Lemma_15_82_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

attribute [local instance] HasDerivedCategory.standard

namespace RingHom

/-- Helper for Lemma 15.83.2: a ring map is pseudo-coherent when it is finite type and the
target is pseudo-coherent relative to the source. -/
class IsPseudoCoherentRingMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop where
  /-- The map is of finite type. -/
  finiteType : f.FiniteType
  /-- The target ring is pseudo-coherent relative to the source. -/
  isPseudoCoherentRelativeTo :
    let _ := f.toAlgebra
    let _ : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp finiteType
    (ModuleCat.of B B).IsPseudoCoherentRelativeTo A

/-- Helper for Lemma 15.83.2: a ring map is perfect when it is pseudo-coherent and the target
has finite tor dimension over the source. -/
class IsPerfectRingMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop extends IsPseudoCoherentRingMap f where
  /-- The target ring has finite tor dimension over the source. -/
  hasFiniteTorDimension :
    let _ := f.toAlgebra
    CategoryTheory.ModuleHasFiniteTorDimension (ModuleCat.of A B)

attribute [instance] IsPseudoCoherentRingMap.isPseudoCoherentRelativeTo
attribute [instance] IsPerfectRingMap.hasFiniteTorDimension

end RingHom

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Helper for Lemma 15.83.2: a pseudo-coherent ring map supplies the finite-type algebra
instance needed for relative pseudo-coherence. -/
instance finiteType_of_isPseudoCoherentRingMap
    [(algebraMap A B).IsPseudoCoherentRingMap] : Algebra.FiniteType A B := by
  exact
    RingHom.finiteType_algebraMap.mp
      (inferInstance : (algebraMap A B).IsPseudoCoherentRingMap).finiteType

/-- Lemma 15.83.2: a ring map `A → B` is perfect if and only if there exists a surjective
polynomial presentation `MvPolynomial (Fin n) A →ₐ[A] B` such that `B`, viewed as a module over
`MvPolynomial (Fin n) A`, is perfect. By Lemma `15.75.3`, this is equivalent to requiring a
finite resolution by finite projective `MvPolynomial (Fin n) A`-modules. -/
@[stacks 068Y]
theorem isPerfectRingMap_iff_exists_polynomialPresentation_with_perfect_restrictedModule :
    (algebraMap A B).IsPerfectRingMap ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B),
        Function.Surjective α ∧
          let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
          (ModuleCat.of (MvPolynomial (Fin n) A) B).IsPerfect := by
  sorry

end

end Algebra
