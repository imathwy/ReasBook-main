import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1.Index
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_6

noncomputable section
universe u
open scoped MonoidAlgebra Representation
namespace Representation

example {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] : IsDedekindDomain A := by
  infer_instance

example {p : ℕ} {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharP (IsLocalRing.ResidueField A) p] :
    Nonempty (NonzeroResidualCharacteristicMaximalIdeal A p) := by
  let M : MaximalSpectrum A := default
  refine ⟨⟨M, ?_, ?_⟩⟩
  · change (M : Ideal A) ≠ ⊥
    dsimp [M]
    exact IsDiscreteValuationRing.not_a_field A
  · dsimp [M]
    change CharP (IsLocalRing.maximalIdeal A).ResidueField p
    exact charP_of_injective_algebraMap
      (localResidueFieldToMaximalIdealResidueField (A := A)).injective p

end Representation
