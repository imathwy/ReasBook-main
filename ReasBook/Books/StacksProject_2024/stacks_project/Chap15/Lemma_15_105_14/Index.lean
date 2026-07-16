import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_5
import StacksProject_2024.stacks_project.Chap15.Definition_15_105_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_6

-- Shared owner-level API extracted from `Lemma_15_105_14.lean`.

open scoped TensorProduct

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- If `A → B` is a filtered colimit of étale `A`-algebras, then it is weakly étale. -/
theorem isWeaklyEtale_of_isFilteredColimitOfEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale) :
    Algebra.IsWeaklyEtale A B := by
  refine
    { moduleFlat := by
        exact flat_of_isFilteredColimitOfEtale hcolim
      flat_tensorSquareMultiplication := by
        let _ : Algebra (B ⊗[A] B) B := (Algebra.TensorProduct.lmul' A).toAlgebra
        let _ : IsScalarTower B (B ⊗[A] B) B := by
          refine IsScalarTower.of_algebraMap_eq' ?_
          ext b
          change b = (Algebra.TensorProduct.lmul' A) (algebraMap B (B ⊗[A] B) b)
          simp [Algebra.TensorProduct.lmul'_apply_tmul]
        have htensorB :
            (algebraMap B (B ⊗[A] B)).IsFilteredColimitOfEtale :=
          RingHom.filteredColimitOfEtale_baseChange
            (R := A) (A := B) (R' := B) hcolim
        have htensorA :
            (algebraMap A (B ⊗[A] B)).IsFilteredColimitOfEtale :=
          RingHom.isFilteredColimitOfEtale_comp
            (algebraMap A B) (algebraMap B (B ⊗[A] B)) hcolim htensorB
        have hmul :
            (algebraMap (B ⊗[A] B) B).IsFilteredColimitOfEtale :=
          RingHom.isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base
            (R := A) (A := B ⊗[A] B) (B := B) htensorA hcolim
        have hflatMul : Module.Flat (B ⊗[A] B) B :=
          flat_of_isFilteredColimitOfEtale hmul
        have halg :
            (algebraMap (B ⊗[A] B) B).Flat :=
          RingHom.flat_algebraMap_iff.mpr hflatMul
        simpa [RingHom.algebraMap_toAlgebra] using halg }

end
