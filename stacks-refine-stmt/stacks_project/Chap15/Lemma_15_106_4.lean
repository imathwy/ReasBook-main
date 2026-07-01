import Mathlib
import stacks_project.Chap15.Lemma_15_106_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped MaximalWeaklyEtaleSubalgebraNotation

variable {K : Type u} [Field K]
variable {L : Type v} [Field L] [Algebra K L]
variable {A : Type w} [CommRing A] [Algebra K A]
variable (K) (L) (A)

/- Domain-style sampling for Lemma 15.106.4:
- primary domain: commutative algebra of maximal weakly étale subalgebras under base change along
  a field extension;
- sampled owner declarations:
  `maximalWeaklyEtaleSubalgebra`,
  `isWeaklyEtale_maximalWeaklyEtaleSubalgebra`,
  `le_maximalWeaklyEtaleSubalgebra`,
  `Algebra.IsWeaklyEtale.baseChange`;
- target layer: `source-facing`, since the Stacks lemma identifies the base change of `B_max(A⁄K)`
  with `B_max((A ⊗[K] L)⁄L)`;
- core/canonical owner abstraction: the source-facing owner remains `B_max` from
  `Lemma_15_106_2`; the only primitive bridge data here is the tensor-base-change hom obtained
  from the inclusion `B_max(A⁄K) ↪ A`;
- primitive vs. derived: the primitive data is the ambient tensor-base-change hom
  `B_max(A⁄K) ⊗[K] L →ₐ[L] A ⊗[K] L`; landing in `B_max((A ⊗[K] L)⁄L)` and bijectivity are
  derived API.

This file should therefore state the canonical map directly as an `L`-algebra hom into
`B_max((A ⊗[K] L)⁄L)`, rather than routing the public surface through a `K`-algebra map into a
`restrictScalars` codomain.
-/

/-- The ambient tensor-base-change map `B_max(A/K) ⊗[K] L → A ⊗[K] L` obtained by tensoring the
inclusion `B_max(A/K) ↪ A` with `L`, viewed in its natural `L`-algebra form. -/
def maximalWeaklyEtaleSubalgebraTensorBaseChangeMap :
    B_max(A⁄K) ⊗[K] L →ₐ[L] A ⊗[K] L :=
  { __ := (Algebra.TensorProduct.map B_max(A⁄K).val (AlgHom.id K L)).toRingHom
    commutes' := by
      intro l
      change (Algebra.TensorProduct.map B_max(A⁄K).val (AlgHom.id K L))
          ((includeRight : L →ₐ[K] B_max(A⁄K) ⊗[K] L) l) =
        (includeRight : L →ₐ[K] A ⊗[K] L) l
      simp }

-- Proof sketch: `B_max(A/K)` is weakly étale over `K` by Lemma `15.106.2`, so after base change
-- along `K → L` it remains weakly étale over `L`. Since the tensor-base-change map lands inside
-- `A ⊗[K] L`, maximality of `B_max((A ⊗[K] L)/L)` forces its image to lie in that subalgebra.
/-- The tensor-base-change map from `B_max(A/K) ⊗[K] L` lands in the maximal weakly étale
`L`-subalgebra of `A ⊗[K] L`. -/
theorem maximalWeaklyEtaleSubalgebraTensorBaseChangeMap_mem
    (x : B_max(A⁄K) ⊗[K] L) :
    (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A :
      B_max(A⁄K) ⊗[K] L → A ⊗[K] L) x ∈ B_max((A ⊗[K] L)⁄L) := sorry

/-- The canonical map from `B_max(A/K) ⊗[K] L` to the maximal weakly étale `L`-subalgebra of
`A ⊗[K] L`. -/
def maximalWeaklyEtaleSubalgebraTensorBaseChange :
    B_max(A⁄K) ⊗[K] L →ₐ[L] B_max((A ⊗[K] L)⁄L) :=
  (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A).codRestrict
    B_max((A ⊗[K] L)⁄L)
    (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap_mem K L A)

/-- The codomain-restricted tensor-base-change map agrees with the ambient tensor-base-change map
after forgetting the target subalgebra. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraTensorBaseChange_apply
    (x : B_max(A⁄K) ⊗[K] L) :
    ↑((maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
      B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) x) =
      (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A :
        B_max(A⁄K) ⊗[K] L → A ⊗[K] L) x := rfl

-- Proof sketch: first reduce to the case where `L` is algebraically closed, then to finite type
-- and reduced `K`-algebras, then to total quotient rings, and finally to finitely generated field
-- extensions. In the field case, decompose after base change using the separable field
-- `B_max(A/K)` and show each factor has maximal weakly étale subalgebra equal to `L`.
/-- Lemma 15.106.4: the canonical map
`B_max(A/K) ⊗[K] L → B_max((A ⊗[K] L)/L)` is bijective, i.e. base change carries the maximal
weakly étale `K`-subalgebra of `A` to the maximal weakly étale `L`-subalgebra of `A ⊗[K] L`. -/
theorem bijective_maximalWeaklyEtaleSubalgebraTensorBaseChange :
    Function.Bijective
      (maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
        B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) := sorry

end
