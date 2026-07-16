import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport
import LinearRepresentations_Serre_1977.Serre.Chap16.Lemma_16_16_3_1
import LinearRepresentations_Serre_1977.Serre.Chap16.Lemma_16_16_3_1.PositiveConeBridge
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.CommonOwner
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.ReductionProjectiveClassBridge
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.ProjectivePositiveReflection
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.PositiveGeneration

noncomputable section

universe u v

open CategoryTheory
open scoped Representation ZeroObject

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckBaseChangeHom K :
    finiteProjectiveGroupAlgebraGrothendieckGroup A G →+
      finiteRepGrothendieckGroup K G)

omit [IsLocalRing A] [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K]
  [Finite G] in
/-- Helper for Exercise 16-16.3-8: the source of a projective envelope of a simple module is
finitely generated, because essentiality makes any nonzero lift of a simple generator cyclic. -/
theorem moduleFinite_of_projectiveEnvelope_simpleField
    {L : Type u} [Field L]
    {P M : Type u} [AddCommGroup P] [Module (MonoidAlgebra L G) P]
    [AddCommGroup M] [Module (MonoidAlgebra L G) M]
    [IsSimpleModule (MonoidAlgebra L G) M]
    {f : P →ₗ[MonoidAlgebra L G] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite (MonoidAlgebra L G) P := by
  -- A nonzero lift of a simple generator spans a submodule whose image is nonzero, hence all of
  -- the simple target; essentiality then forces that cyclic submodule to be the whole source.
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := MonoidAlgebra L G) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule (MonoidAlgebra L G) P := Submodule.span (MonoidAlgebra L G) {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    intro hbot
    have hxmem : f x ∈ N.map f :=
      ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (MonoidAlgebra L G) P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := MonoidAlgebra L G) (x := x)).1
        (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective
    (LinearMap.toSpanSingleton (MonoidAlgebra L G) P x) hsurj

omit [IsLocalRing A] [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K] in
/-- Helper for Exercise 16-16.3-8: every simple finite-dimensional representation over a field
has a finite projective envelope in the group-algebra module category. -/
theorem existsFiniteProjectiveEnvelopeOfSimpleField
    {L : Type u} [Field L] (τ : FDRep L G) [Simple τ] :
    ∃ P : FiniteProjectiveGroupAlgebraModule L G,
      ∃ f : P.V →ₗ[MonoidAlgebra L G] Representation.asModule τ.ρ, f.IsProjectiveEnvelope := by
  -- Start with the Artinian projective envelope and repackage its source as a finite projective
  -- group-algebra module.
  let ρ : Representation L G τ := τ.ρ
  letI : Module (MonoidAlgebra L G) τ := by
    simpa using (inferInstance : Module (MonoidAlgebra L G) ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule (MonoidAlgebra L G) τ := by
    simpa [ρ] using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat (MonoidAlgebra L G) := ModuleCat.of (MonoidAlgebra L G) τ
  let _ : Module.Finite L (MonoidAlgebra L G) := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing (MonoidAlgebra L G) :=
    IsArtinianRing.of_finite L (MonoidAlgebra L G)
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite (MonoidAlgebra L G) P' :=
    moduleFinite_of_projectiveEnvelope_simpleField
      (G := G) (L := L) (P := P') (M := τ) (f := f'.hom) hf'
  let Pfg : FGModuleCat (MonoidAlgebra L G) := by
    refine ⟨P', ?_⟩
    change Module.Finite (MonoidAlgebra L G) P'
    exact hfinite
  have hproj : Module.Projective (MonoidAlgebra L G) Pfg := by
    change Module.Projective (MonoidAlgebra L G) P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule L G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  simpa [P, ρ] using hf'

end

end Representation
