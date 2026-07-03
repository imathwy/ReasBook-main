import StacksProject_2024.Chap10.Lemma_10_101_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsArtinianRing R]
variable {M : Type w} [AddCommGroup M] [Module R M]

-- Proof sketch: apply Lemma `10.101.5` to the Jacobson radical `Ring.jacobson R`. For an
-- Artinian ring this ideal is nilpotent, and the quotient `R ⧸ Ring.jacobson R` is semisimple,
-- so every module over it is projective and hence flat.
/-- Lemma 10.101.7: if `R` is Artinian, `R → S` is injective, and the base change `S ⊗[R] M` is
flat over `S`, then `M` is flat over `R`. -/
theorem flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := by
  have hnil : IsNilpotent (Ring.jacobson R) := by
    simpa [Ideal.jacobson_bot] using
      (IsArtinianRing.isNilpotent_jacobson_bot : IsNilpotent (Ideal.jacobson (⊥ : Ideal R)))
  let _ : Module.Projective (R ⧸ Ring.jacobson R) (M ⧸ (Ring.jacobson R • ⊤ : Submodule R M)) :=
    Module.projective_of_isSemisimpleRing _ _
  simpa [Ideal.jacobson_bot] using
    flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange
      hnil hinj (by infer_instance) hflat

end
