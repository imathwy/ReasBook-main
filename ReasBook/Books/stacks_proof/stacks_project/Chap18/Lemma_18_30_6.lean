import Mathlib
import stacks_proof.stacks_project.Chap07.Lemma_7_12_5
import stacks_proof.stacks_project.Chap07.Lemma_7_29_4
import stacks_proof.stacks_project.Chap18.«18_19_2_1»
import stacks_proof.stacks_project.Chap18.Situation_18_30_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology.Cover
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type u)]
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

-- Proof sketch: use Situation `18.30.5` to choose, for each local section of `ℱ`, a covering
-- family by basis objects on which that section is represented by maps from the corresponding
-- `h_U^#`. Taking the coproduct over all such chosen basis objects gives a morphism to `ℱ` whose
-- image sieve contains a covering sieve at every section, hence is locally surjective.
/-- First assertion of Lemma 18.30.6: in Situation `18.30.5`, every sheaf of sets is the target of a locally
surjective map from a coproduct of sheafified representables `h_{U_i}^#` with `U_i ∈ B`. -/
theorem exists_locallySurjective_from_coproduct_basis_sheafifiedRepresentables
    (ℱ : Sheaf J (Type u)) :
    ∃ (I : Type u) (U : I → C),
      (∀ i, U i ∈ B) ∧
        ∃ _hc : HasCoproduct (fun i : I ↦ J.sheafifiedRepresentable (U i)),
          ∃ (φ : (∐ fun i : I ↦ J.sheafifiedRepresentable (U i)) ⟶ ℱ),
            Sheaf.IsLocallySurjective φ := by
  let hEnough :=
    HasQuasiCompactBasisWithQuasiCompactFiberProducts.hasEnoughObjectsWithProperty
      (J := J) (B := B)
  -- The Chapter 7 presentation theorem already chooses the basis-indexed coproduct map.
  rcases exists_coequalizer_presentation_by_sheafified_representables
      (J := J) (E := B) hEnough ℱ with
    ⟨𝒰₀, 𝒰₁, p, q, π, hπ, ⟨hcolim⟩⟩
  let _ : HasColimitsOfShape (Discrete 𝒰₀.1.index) (Sheaf J (Type u)) :=
    Sheaf.instHasColimitsOfShape
  refine ⟨𝒰₀.1.index, 𝒰₀.1.obj, 𝒰₀.2, inferInstance, π, ?_⟩
  -- Any coequalizer map is epi, and for sheaves of sets epi is exactly local surjectivity.
  letI : Epi π := Cofork.IsColimit.epi hcolim
  exact (Sheaf.isLocallySurjective_iff_epi π).2 inferInstance

end CategoryTheory.GrothendieckTopology

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

/-- Helper for Lemma 18.30.6: restriction of sections along `f`. -/
private def sectionMap
    {U V : C} (f : V ⟶ U) (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ →
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).obj ℱ :=
  ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op

section

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Helper for Lemma 18.30.6: restriction commutes with applying a morphism of module sheaves. -/
private theorem sectionMap_naturality
    {U V : C} {ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)}
    (f : V ⟶ U) (α : ℱ ⟶ 𝒢)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ) :
    ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).map α)
        (sectionMap (J := J) (𝒪 := 𝒪) f ℱ s) =
      sectionMap (J := J) (𝒪 := 𝒪) f 𝒢
        (((SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).map α) s) := by
  -- Restriction is the presheaf action, so naturality is just naturality of the underlying map.
  change ConcreteCategory.hom (α.val.app (op V))
      (ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op) s) =
    ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj 𝒢).1.map f.op)
      (ConcreteCategory.hom (α.val.app (op U)) s)
  simpa using ConcreteCategory.congr_hom (α.val.naturality f.op) s

end

section

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Helper for Lemma 18.30.6: the slice-site family attached to the arrows of a cover generates
the same sieve as the cover itself. -/
private theorem coverArrowObjects_overSieve_eq
    {U : C} (S : J.Cover U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun a : S.Arrow ↦ Over.mk a.f) (Over.mk (𝟙 U))) =
      (S : Sieve U) := by
  calc
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun a : S.Arrow ↦ Over.mk a.f) (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun a : S.Arrow ↦ a.Y) (fun a ↦ a.f) := by
        ext V f
        constructor
        · intro hf
          rw [Sieve.overEquiv_iff] at hf
          rw [Sieve.mem_ofObjects_iff] at hf
          rcases hf with ⟨a, ⟨g⟩⟩
          rw [Sieve.mem_ofArrows_iff]
          exact ⟨a, g.left, by simpa using g.w.symm⟩
        · intro hf
          rw [Sieve.overEquiv_iff]
          rw [Sieve.mem_ofArrows_iff] at hf
          rcases hf with ⟨a, g, hg⟩
          rw [Sieve.mem_ofObjects_iff]
          exact ⟨a, ⟨Over.homMk g (by simpa using hg.symm)⟩⟩
    _ = (S : Sieve U) := S.ofArrows_eq

/-- Helper for Lemma 18.30.6: a cover on `U` yields the corresponding `CoversTop` condition on
the slice site over `U`. -/
private theorem coverArrows_coversTop
    {U : C} (S : J.Cover U) :
    (J.over U).CoversTop (fun a : S.Arrow ↦ Over.mk a.f) := by
  -- Rewrite the slice-site terminal cover back to the ordinary covering sieve of `S`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, coverArrowObjects_overSieve_eq (J := J) S]
  exact S.property

end

/-- Helper for Lemma 18.30.6: sections of the restriction of `ℱ` to the slice site over `U`
are equivalent to ordinary sections of `ℱ` on `U`. -/
private noncomputable def overSectionsEquivEvaluation
    (U : C) (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    (SheafOfModules.over ℱ U).sections ≃
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (SheafOfModules.over ℱ U).val.sectionsMk
      (fun X ↦ (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from X.unop).op) m)
      (fun (X Y : (Over U)ᵒᵖ) (f : X ⟶ Y) ↦ by
        -- Every slice arrow to the terminal object is the canonical one.
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- A section over the slice site is determined by its values on the terminal comparison maps.
    ext X
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from X.unop).op)
  right_inv m := by
    -- Evaluating the reconstructed section at the terminal slice object recovers `m`.
    change
      (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using
      (SheafOfModules.over ℱ U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

section

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Helper for Lemma 18.30.6: evaluating the reconstructed slice-site section on a cover arrow
recovers ordinary restriction along that arrow. -/
private theorem overSectionsEquivEvaluation_symm_apply_cover
    {U V : C} (f : V ⟶ U) (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ) :
    ((overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) U ℱ).symm s).1
        (op (Over.mk f)) =
      sectionMap (J := J) (𝒪 := 𝒪) f ℱ s := by
  -- The canonical map from `Over.mk f` to the slice terminal object is `f` itself.
  have h : Over.mkIdTerminal.from (Over.mk f) = Over.homMk f (by simp) := by
    exact Over.mkIdTerminal.hom_ext _ _
  change ConcreteCategory.hom ((SheafOfModules.over ℱ U).val.map
      ((Over.mkIdTerminal.from (Over.mk f)).op)) s =
    ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op) s
  rw [h]
  rfl

end

section

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Helper for Lemma 18.30.6: `localizedStructureModuleExtensionByZero_homEquiv` is natural in
the target module sheaf. -/
private theorem localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    (U : C) {ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)}
    (β : j![𝒪, U] ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β) := by
  -- The owner equivalence is assembled from target-functorial constructions.
  rfl

/-- Helper for Lemma 18.30.6: precomposition by `localizedStructureModuleExtensionByZeroMap`
becomes restriction of sections. -/
private theorem localizedStructureModuleExtensionByZeroMap_homEquiv
    {V W : C} (f : V ⟶ W) (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (α : j![𝒪, W] ⟶ ℱ) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ
        (localizedStructureModuleExtensionByZeroMap J 𝒪 f ≫ α) =
      sectionMap (J := J) (𝒪 := 𝒪) f ℱ
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ α) := by
  -- Route correction: use the public owner equivalence plus its target naturality, rather than
  -- expanding the slice-site adjunction by hand.
  have hα : localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ α =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W (j![𝒪, W]) (𝟙 _)) := by
    simpa using
      localizedStructureModuleExtensionByZero_homEquiv_naturality_right
        (J := J) (𝒪 := 𝒪) W (β := 𝟙 (j![𝒪, W])) (α := α)
  rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    (J := J) (𝒪 := 𝒪) V (β := localizedStructureModuleExtensionByZeroMap J 𝒪 f) (α := α)]
  rw [SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroMap]
  rw [Equiv.apply_symm_apply]
  rw [hα]
  exact sectionMap_naturality (J := J) (𝒪 := 𝒪) f α _

/-- Helper for Lemma 18.30.6: morphisms out of a coproduct of localized structure modules are
exactly families of chosen sections. -/
private noncomputable def localizedStructureModuleExtensionByZeroCoproductHomEquiv
    {I : Type u} (U : I → C) (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ((∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ) ≃
      (∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).obj ℱ) where
  toFun α i :=
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ
      (Sigma.ι (fun i : I ↦ j![𝒪, (U i)]) i ≫ α)
  invFun s :=
    Sigma.desc fun i : I ↦
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ).symm (s i)
  left_inv α := by
    -- A morphism out of the coproduct is determined by its restrictions to the summands.
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.symm_apply_apply
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ)
      (Sigma.ι (fun i : I ↦ j![𝒪, (U i)]) i ≫ α)
  right_inv s := by
    -- Evaluating the reconstructed morphism on each summand recovers the prescribed section.
    funext i
    change
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ
        (Sigma.ι (fun k : I ↦ j![𝒪, (U k)]) i ≫
          Sigma.desc
            (fun k : I ↦
              (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U k) ℱ).symm
                (s k))) = s i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ)
      (s i)

/-- Helper for Lemma 18.30.6: every module sheaf admits an epimorphism from a coproduct of
unrestricted generators `j_{U!}\mathcal O_U`. -/
private theorem exists_epi_from_coproduct_localizedStructureModuleExtensionByZero'
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (U : I → C)
      (φ : (∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ), Epi φ := by
  let I : Type u := Σ U : C, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ
  let U : I → C := fun i ↦ i.1
  let φ : (∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ :=
    (localizedStructureModuleExtensionByZeroCoproductHomEquiv
      (J := J) (𝒪 := 𝒪) U ℱ).symm fun i ↦ i.2
  refine ⟨I, U, φ, ?_⟩
  refine ⟨?_⟩
  intro 𝒢 α β hαβ
  -- Equality after precomposition with the coproduct map is detected on the summand indexed by a
  -- tested local section.
  ext V s
  let i : I := ⟨V.unop, s⟩
  have hcomp := congrArg
    (fun ψ ↦
      (localizedStructureModuleExtensionByZeroCoproductHomEquiv
        (J := J) (𝒪 := 𝒪) U 𝒢) ψ)
    hαβ
  have hi := congrFun hcomp i
  have hi' :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ α) =
        localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ β) := by
    simpa [localizedStructureModuleExtensionByZeroCoproductHomEquiv] using hi
  have hφi :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ
          (Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) = s := by
    let hφfam := Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZeroCoproductHomEquiv (J := J) (𝒪 := 𝒪) U ℱ)
      (fun j : I ↦ j.2)
    have hφi' := congrFun hφfam i
    simpa [I, U, i, φ, localizedStructureModuleExtensionByZeroCoproductHomEquiv] using hφi'
  have hleft :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ α) =
        ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).map α) s := by
    rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right
      (J := J) (𝒪 := 𝒪) (U i)
      (β := Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) (α := α)]
    rw [hφi]
  have hright :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ β) =
        ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).map β) s := by
    rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right
      (J := J) (𝒪 := 𝒪) (U i)
      (β := Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) (α := β)]
    rw [hφi]
  rw [hleft, hright] at hi'
  simpa [I, U, i] using hi'

/-- Helper for Lemma 18.30.6: each unrestricted generator `j_{V!}\mathcal O_V` is already an epi
image of a coproduct indexed by basis objects. -/
private theorem basisCoverEpiToLocalizedStructureModule
    (V : C) :
    ∃ (A : Type u) (U : A → C),
      (∀ a, U a ∈ B) ∧
        ∃ (δ : (∐ fun a : A ↦ j![𝒪, (U a)]) ⟶ j![𝒪, V]),
          Epi δ := by
  let hEnough : J.HasEnoughObjectsWithProperty (· ∈ B) :=
    by
      let hBasis : J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B := inferInstance
      exact hBasis.hasEnoughObjectsWithProperty
  rcases hEnough V with ⟨S, hS⟩
  refine ⟨S.Arrow, fun a ↦ a.Y, hS, ?_⟩
  let δ :
      (∐ fun a : S.Arrow ↦ j![𝒪, a.Y]) ⟶ j![𝒪, V] :=
    Sigma.desc (fun a : S.Arrow ↦ localizedStructureModuleExtensionByZeroMap J 𝒪 a.f)
  refine ⟨δ, ?_⟩
  refine ⟨?_⟩
  intro ℱ α β hαβ
  let htop := coverArrows_coversTop (J := J) S
  let F :=
    ((sheafForget (J.over V)).obj
      ((SheafOfModules.toSheaf ((ringSheaf J 𝒪).over V)).obj (SheafOfModules.over ℱ V)))
  have hs :
      (overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) V ℱ).symm
          (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ α) =
        (overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) V ℱ).symm
          (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ β) := by
    -- Equality on a covering family of slice objects forces equality of the global slice section.
    apply htop.sections_ext F
    intro a
    rw [overSectionsEquivEvaluation_symm_apply_cover (J := J) (𝒪 := 𝒪)
      (f := a.f) (ℱ := ℱ)
      (s := localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ α)]
    rw [overSectionsEquivEvaluation_symm_apply_cover (J := J) (𝒪 := 𝒪)
      (f := a.f) (ℱ := ℱ)
      (s := localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ β)]
    have hpre := congrArg
      (fun γ ↦ Sigma.ι (fun b : S.Arrow ↦ j![𝒪, b.Y]) a ≫ γ)
      hαβ
    have hcomp :
        Sigma.ι (fun b : S.Arrow ↦ j![𝒪, b.Y]) a ≫ δ ≫ α =
          Sigma.ι (fun b : S.Arrow ↦ j![𝒪, b.Y]) a ≫ δ ≫ β := by
      simpa [Category.assoc] using hpre
    have hι :
        Sigma.ι (fun b : S.Arrow ↦ j![𝒪, b.Y]) a ≫ δ =
          localizedStructureModuleExtensionByZeroMap J 𝒪 a.f := by
      dsimp [δ]
      rw [Limits.Sigma.ι_desc]
    have hια :
        localizedStructureModuleExtensionByZeroMap J 𝒪 a.f ≫ α =
          Sigma.ι (fun b : S.Arrow ↦ j![𝒪, b.Y]) a ≫ δ ≫ α := by
      have h := congrArg (fun γ ↦ γ ≫ α) hι.symm
      simpa [Category.assoc] using h
    have hιβ :
        Sigma.ι (fun b : S.Arrow ↦ j![𝒪, b.Y]) a ≫ δ ≫ β =
          localizedStructureModuleExtensionByZeroMap J 𝒪 a.f ≫ β := by
      have h := congrArg (fun γ ↦ γ ≫ β) hι
      simpa [Category.assoc] using h
    have hcomp :
        localizedStructureModuleExtensionByZeroMap J 𝒪 a.f ≫ α =
          localizedStructureModuleExtensionByZeroMap J 𝒪 a.f ≫ β := by
      -- Move to the coproduct-component normal form before applying the owner equivalence.
      calc
        localizedStructureModuleExtensionByZeroMap J 𝒪 a.f ≫ α =
            Sigma.ι (fun b : S.Arrow ↦ j![𝒪, b.Y]) a ≫ δ ≫ α := hια
        _ = Sigma.ι (fun b : S.Arrow ↦ j![𝒪, b.Y]) a ≫ δ ≫ β := hcomp
        _ = localizedStructureModuleExtensionByZeroMap J 𝒪 a.f ≫ β := hιβ
    have hsec := congrArg
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 a.Y ℱ) hcomp
    rw [localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
        (f := a.f) (ℱ := ℱ) (α := α),
      localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
        (f := a.f) (ℱ := ℱ) (α := β)] at hsec
    exact hsec
  -- Translate equality of slice sections back to equality of ordinary sections on `V`.
  have hsec :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ α =
        localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ β := by
    simpa using congrArg (overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) V ℱ) hs
  exact (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ).injective hsec

end

/-- Helper for Lemma 18.30.6: flatten a nested coproduct of basis generators into a single
sigma-indexed coproduct before mapping to the outer coproduct of unrestricted generators. -/
private noncomputable def flattenedBasisCoproductMap
    {I : Type u} (A : I → Type u) (U : ∀ i, A i → C) (V : I → C)
    (δ : ∀ i,
      (∐ fun a : A i ↦ j![𝒪, (U i a)]) ⟶ j![𝒪, (V i)]) :
    (∐ fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟶
      (∐ fun i : I ↦ j![𝒪, (V i)]) :=
  Sigma.desc fun p : Sigma A ↦
    Sigma.ι (fun a : A p.1 ↦ j![𝒪, (U p.1 a)]) p.2 ≫
      δ p.1 ≫
        Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) p.1

section

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Helper for Lemma 18.30.6: the `⟨i, a⟩` summand of the flattened coproduct map is the
corresponding `a`-summand map into `δ i`, followed by the `i`-th outer coproduct inclusion. -/
private theorem flattenedBasisCoproductMap_ι
    {I : Type u} (A : I → Type u) (U : ∀ i, A i → C) (V : I → C)
    (δ : ∀ i,
      (∐ fun a : A i ↦ j![𝒪, (U i a)]) ⟶ j![𝒪, (V i)])
    (i : I) (a : A i) :
    Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
        flattenedBasisCoproductMap 𝒪 A U V δ =
      Sigma.ι (fun b : A i ↦ j![𝒪, (U i b)]) a ≫
        δ i ≫
          Sigma.ι (fun j : I ↦ j![𝒪, (V j)]) i := by
  -- Expanding `flattenedBasisCoproductMap` and evaluating on the chosen sigma summand gives the
  -- advertised component formula.
  dsimp [flattenedBasisCoproductMap]
  rw [Limits.Sigma.ι_desc]

/-- Helper for Lemma 18.30.6: the flattened coproduct map is epi when each summandwise map is
epi. -/
private theorem flattenedBasisCoproductEpi
    {I : Type u} (A : I → Type u) (U : ∀ i, A i → C) (V : I → C)
    (δ : ∀ i,
      (∐ fun a : A i ↦ j![𝒪, (U i a)]) ⟶ j![𝒪, (V i)])
    [∀ i, Epi (δ i)] :
    Epi (flattenedBasisCoproductMap 𝒪 A U V δ) := by
  refine ⟨?_⟩
  intro ℱ α β hαβ
  -- Equality on the flattened coproduct gives equality on each outer summand after canceling the
  -- epi map `δ i`.
  apply Limits.Sigma.hom_ext
  intro i
  apply (cancel_epi (δ i)).1
  apply Limits.Sigma.hom_ext
  intro a
  have hcomp := congrArg
    (fun γ ↦
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫ γ)
    hαβ
  have hpre :
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
          flattenedBasisCoproductMap 𝒪 A U V δ ≫ α =
        Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
          flattenedBasisCoproductMap 𝒪 A U V δ ≫ β := by
    simpa [Category.assoc] using hcomp
  have hflat := flattenedBasisCoproductMap_ι (𝒪 := 𝒪) (A := A) (U := U) (V := V) (δ := δ)
    (i := i) (a := a)
  have hflatα :
      Sigma.ι (fun a : A i ↦ j![𝒪, (U i a)]) a ≫ δ i ≫
          Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) i ≫ α =
        Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
          flattenedBasisCoproductMap 𝒪 A U V δ ≫ α := by
    have h := congrArg (fun γ ↦ γ ≫ α) hflat.symm
    simpa [Category.assoc] using h
  have hflatβ :
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
          flattenedBasisCoproductMap 𝒪 A U V δ ≫ β =
        Sigma.ι (fun a : A i ↦ j![𝒪, (U i a)]) a ≫ δ i ≫
          Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) i ≫ β := by
    have h := congrArg (fun γ ↦ γ ≫ β) hflat
    simpa [Category.assoc] using h
  -- Rewrite the sigma-indexed component into the `i`-th outer summand and cancel `δ i`.
  calc
    Sigma.ι (fun a : A i ↦ j![𝒪, (U i a)]) a ≫ δ i ≫
        Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) i ≫ α =
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
        flattenedBasisCoproductMap 𝒪 A U V δ ≫ α := hflatα
    _ =
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
        flattenedBasisCoproductMap 𝒪 A U V δ ≫ β := hpre
    _ =
      Sigma.ι (fun a : A i ↦ j![𝒪, (U i a)]) a ≫ δ i ≫
        Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) i ≫ β := hflatβ

end

-- Proof sketch: apply Situation `18.30.5` to choose, for every local generator of `ℱ`, a basis
-- object over which that generator is represented. By adjunction this yields maps
-- `j_{U!}\mathcal O_U ⟶ ℱ`; summing over all chosen basis objects produces an epimorphism.
section

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Lemma 18.30.6 (2): in Situation `18.30.5`, every `\mathcal O`-module is a quotient of a
direct sum of `j_{U_i!}\mathcal O_{U_i}` with `U_i ∈ B`. -/
@[stacks 093B]
theorem exists_epi_from_coproduct_basis_localizedStructureModuleExtensionByZero
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (U : I → C),
      (∀ i, U i ∈ B) ∧
        ∃ (φ : (∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ),
          Epi φ := by
  classical
  -- Start from the unrestricted epimorphic presentation of `ℱ`.
  rcases exists_epi_from_coproduct_localizedStructureModuleExtensionByZero'
      (J := J) (𝒪 := 𝒪) ℱ with
    ⟨I, V, ψ, hψ⟩
  -- Route correction: avoid the global-pullback Čech theorem; each summand is replaced by a
  -- basis-indexed epi using only slice-site separation on the chosen basis cover.
  choose A U hU δ hδ using
    (fun i : I ↦ basisCoverEpiToLocalizedStructureModule (J := J) (𝒪 := 𝒪) (B := B) (V i))
  let W : Sigma A → C := fun p ↦ U p.1 p.2
  let θ :
      (∐ fun p : Sigma A ↦ j![𝒪, (W p)]) ⟶
        (∐ fun i : I ↦ j![𝒪, (V i)]) :=
    flattenedBasisCoproductMap 𝒪 A U V δ
  let φ :
      (∐ fun p : Sigma A ↦ j![𝒪, (W p)]) ⟶ ℱ :=
    θ ≫ ψ
  refine ⟨Sigma A, W, ?_, φ, ?_⟩
  · intro p
    exact hU p.1 p.2
  · letI : ∀ i, Epi (δ i) := hδ
    letI : Epi θ :=
      flattenedBasisCoproductEpi 𝒪 A U V δ
    letI : Epi ψ := hψ
    dsimp [φ]
    infer_instance

end

end SheafOfModules.RingedSite
