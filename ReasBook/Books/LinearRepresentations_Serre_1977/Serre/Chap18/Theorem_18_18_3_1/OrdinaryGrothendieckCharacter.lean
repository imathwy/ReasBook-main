import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_6.Bases
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.CartanSubgroupInduction
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.PGroupBridges
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.CartanBasisExtension
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport

noncomputable section

universe u

namespace Representation

open CategoryTheory
open scoped Pointwise
open scoped MonoidAlgebra
open scoped MonoidalCategory
open scoped Representation
open scoped Representation.ExternalTensor
open scoped TensorProduct
open scoped ZeroObject

section

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Theorem 18-18.3-1: the ordinary character of a finite-dimensional
`K[G]`-representation belongs to Serre's character ring owner `R[K](G)`. -/
private theorem finiteRepCharacter_mem_characterRingOverField_local
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G] (V : FDRep K G) :
    V.character ∈ R[K](G) := by
  simpa using Representation.rep_character_mem_characterRingOverField
    (Rep.of V.ρ)

/-- Helper for Theorem 18-18.3-1: the generator-level ordinary-character lift from the free
abelian group on finite-dimensional `K[G]`-representations into `R[K](G)`. -/
private abbrev finiteRepGrothendieckCharacterLiftLocal
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G] :
    FreeAbelianGroup (FDRep K G) →+ R[K](G) :=
  FreeAbelianGroup.lift fun V ↦
    ⟨V.character, finiteRepCharacter_mem_characterRingOverField_local K G V⟩

/-- Helper for Theorem 18-18.3-1: the ordinary character is additive on short exact
sequences of finite-dimensional representations. -/
private theorem finiteRepCharacter_eq_add_of_shortExact_local
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G]
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    S.X₂.character = S.X₁.character + S.X₃.character := by
  let F : FDRep K G ⥤ ModuleCat K :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ (forget₂ (Rep K G) (ModuleCat K))
  have hSF : (S.map F).ShortExact := by
    simpa [F] using hS.map_of_exact F
  let f : S.X₁.V →ₗ[K] S.X₂.V := ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap
  let g : S.X₂.V →ₗ[K] S.X₃.V := ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap
  have hExact : Function.Exact f g := by
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  let W : Submodule K S.X₂.V := LinearMap.range f
  have hWker : W = LinearMap.ker g := by
    simpa [W, f, g] using hExact.linearMap_ker_eq.symm
  have hW : ∀ a : G, W ≤ W.comap (S.X₂.ρ a) := by
    intro a y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨S.X₁.ρ a x, ?_⟩
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.f) a x
  let e₁ : Representation.Equiv S.X₁.ρ (Representation.subrepresentation S.X₂.ρ W hW) := by
    refine Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_
    intro a
    ext x
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.f) a x
  let qg : S.X₂.V ⧸ W →ₗ[K] S.X₃.V := W.liftQ g hWker.le
  have hqg_injective : Function.Injective qg := by
    refine LinearMap.ker_eq_bot.mp ?_
    rw [Submodule.ker_liftQ_eq_bot']
    exact hWker
  have hqg_surjective : Function.Surjective qg := by
    rw [← LinearMap.range_eq_top]
    rw [Submodule.range_liftQ]
    exact LinearMap.range_eq_top.2 hg
  let e₃ : Representation.Equiv (Representation.quotient S.X₂.ρ W hW) S.X₃.ρ := by
    refine Representation.Equiv.mk (LinearEquiv.ofBijective qg ⟨hqg_injective, hqg_surjective⟩) ?_
    intro a
    ext x
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap (S.X₂.ρ a x) =
        S.X₃.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.g) a x
  have hchar₁ : S.X₁.character = (Representation.subrepresentation S.X₂.ρ W hW).character := by
    simpa [W, f] using Representation.char_iso e₁
  have hchar₃ : S.X₃.character = (Representation.quotient S.X₂.ρ W hW).character := by
    simpa [W, qg] using (Representation.char_iso e₃).symm
  calc
    S.X₂.character =
        (Representation.subrepresentation S.X₂.ρ W hW).character +
          (Representation.quotient S.X₂.ρ W hW).character := by
            simpa [W] using
              character_eq_add_character_quotient_of_invariant_submodule_local
                (K := K) (G := G) S.X₂.ρ W hW
    _ = S.X₁.character + S.X₃.character := by
          rw [← hchar₁, ← hchar₃]

/-- Helper for Theorem 18-18.3-1: the defining Grothendieck relations already vanish under the
generator-level ordinary-character lift. -/
private theorem finiteRepGrothendieckRelations_le_characterLift_ker_local
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G] :
    finiteRepGrothendieckRelations K G ≤
      (finiteRepGrothendieckCharacterLiftLocal K G).ker := by
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change finiteRepGrothendieckCharacterLiftLocal K G
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext g
  have hchar :
      S.X₂.character g = S.X₁.character g + S.X₃.character g :=
    congrFun (finiteRepCharacter_eq_add_of_shortExact_local K G S hS) g
  simpa [finiteRepGrothendieckCharacterLiftLocal, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using sub_eq_zero.mpr hchar

/-- Helper for Theorem 18-18.3-1: the ordinary-character map on `R₀[K](G)`. -/
noncomputable def ordinaryGrothendieckCharLocal
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G] :
    R₀[K](G) →+ R[K](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K G)
    (finiteRepGrothendieckCharacterLiftLocal K G)
    (finiteRepGrothendieckRelations_le_characterLift_ker_local K G)

/-- Helper for Theorem 18-18.3-1: on a genuine finite-dimensional representation class, the
ordinary Grothendieck-character owner evaluates to the ordinary character. -/
@[simp] theorem ordinaryGrothendieckCharLocal_class
    (K : Type u) [Field K] (G : Type u) [Group G] [Finite G]
    (V : FDRep K G) (g : G) :
    ordinaryGrothendieckCharLocal K G [V]₀ g = V.character g := by
  simp [ordinaryGrothendieckCharLocal, finiteRepGrothendieckClass,
    finiteRepGrothendieckCharacterLiftLocal]

end

end Representation
