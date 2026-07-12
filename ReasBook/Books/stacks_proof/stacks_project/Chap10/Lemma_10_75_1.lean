import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import StacksProject_2024.Chap10.Definition_10_71_2
import StacksProject_2024.Chap10.Lemma_10_71_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ProjectiveResolution
open ChainComplex
open HomologicalComplex
open MonoidalCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {M1 M2 : Type u}
variable [AddCommGroup M1] [Module R M1]
variable [AddCommGroup M2] [Module R M2]
variable {F G : ChainComplex (ModuleCat R) ℕ}

local notation "moduleSingle[" M "]" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

local notation "freeResolution[" π "]" =>
  IsFreeResolution.toProjectiveResolution π

local notation "tensorFunctor[" N "]" =>
  CategoryTheory.Functor.mapHomologicalComplex
    (tensorLeft (ModuleCat.of R N)) (ComplexShape.down ℕ)

namespace ProjectiveResolution.Hom

/-- The chain map on tensor complexes induced by a compatible lift between free resolutions. -/
noncomputable def tensorComplexMap
    (N : Type u) [AddCommGroup N] [Module R N]
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    (γ : freeResolution[πF].Hom freeResolution[πG] f) :
    (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G :=
  (tensorFunctor[N]).map γ.hom

/-- Helper for Lemma 10.75.1: tensoring carries a homotopy between compatible lifts to a
homotopy between the induced tensor-complex maps. -/
noncomputable def tensorComplexMap_homotopy
    (N : Type u) [AddCommGroup N] [Module R N]
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    (γ₁ γ₂ : freeResolution[πF].Hom freeResolution[πG] f) :
    Homotopy
      (tensorComplexMap N γ₁ : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G)
      (tensorComplexMap N γ₂ : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G) := by
  -- Follow the source proof: compatible lifts are homotopic on the resolution side.
  let hChain : Homotopy (γ₁.hom : F ⟶ G) (γ₂.hom : F ⟶ G) :=
    ProjectiveResolution.liftHomotopy f γ₁.hom γ₂.hom γ₁.hom_comp_π γ₂.hom_comp_π
  -- Tensoring is additive, so it transports that chain homotopy to the tensor complexes.
  simpa [tensorComplexMap] using
    (tensorLeft (ModuleCat.of R N)).mapHomotopy hChain

/-- Helper for Lemma 10.75.1: tensoring the literal identity lift gives the identity chain map on
the tensor complex. -/
lemma tensorComplexMap_id
    (N : Type u) [AddCommGroup N] [Module R N]
    {πF : F ⟶ moduleSingle[M1]} [IsFreeResolution πF] :
    tensorComplexMap N
        (identity_lift :
          freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1))) =
      𝟙 ((tensorFunctor[N]).obj F) := by
  -- The identity lift has underlying chain map `𝟙`, so functoriality gives the identity.
  apply HomologicalComplex.hom_ext
  intro j
  rw [tensorComplexMap, identity_lift]
  change ModuleCat.of R N ◁ 𝟙 (freeResolution[πF].complex.X j) =
    𝟙 (ModuleCat.of R N ⊗ freeResolution[πF].complex.X j)
  exact MonoidalCategory.whiskerLeft_id (ModuleCat.of R N) (freeResolution[πF].complex.X j)

/-- Helper for Lemma 10.75.1: casting the identity lift along an equality of module maps does not
change the induced tensor-complex map. -/
lemma casted_identity_lift_tensorComplexMap_id
    (N : Type u) [AddCommGroup N] [Module R N]
    {M : Type u} [AddCommGroup M] [Module R M]
    {K : ChainComplex (ModuleCat R) ℕ}
    {π : K ⟶ moduleSingle[M]} [IsFreeResolution π]
    {g : ModuleCat.of R M ⟶ ModuleCat.of R M}
    (e : g = 𝟙 (ModuleCat.of R M)) :
    tensorComplexMap N
        ((e.symm ▸ (identity_lift :
          freeResolution[π].Hom freeResolution[π] (𝟙 (ModuleCat.of R M)))) :
            freeResolution[π].Hom freeResolution[π] g) =
      𝟙 ((tensorFunctor[N]).obj K) := by
  -- After substituting the module-map equality, this is the literal identity-lift computation.
  subst e
  exact tensorComplexMap_id (R := R) (M1 := M) (F := K) N

/-- Helper for Lemma 10.75.1: tensoring respects composition of compatible lifts. -/
lemma tensorComplexMap_comp
    (N : Type u) [AddCommGroup N] [Module R N]
    {M3 : Type u} [AddCommGroup M3] [Module R M3]
    {H : ChainComplex (ModuleCat R) ℕ}
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]} {πH : H ⟶ moduleSingle[M3]}
    [IsFreeResolution πF] [IsFreeResolution πG] [IsFreeResolution πH]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {g : ModuleCat.of R M2 ⟶ ModuleCat.of R M3}
    {h : ModuleCat.of R M1 ⟶ ModuleCat.of R M3}
    (γ₁ : freeResolution[πF].Hom freeResolution[πG] f)
    (γ₂ : freeResolution[πG].Hom freeResolution[πH] g)
    (γcomp : freeResolution[πF].Hom freeResolution[πH] h)
    (hγcomp : γcomp.hom = γ₁.hom ≫ γ₂.hom) :
    tensorComplexMap N γcomp =
      tensorComplexMap N γ₁ ≫ tensorComplexMap N γ₂ := by
  -- Route correction: compose the lifts on the resolution side first, then apply tensor functoriality.
  rcases γcomp with ⟨γhom, γcomm⟩
  dsimp at hγcomp
  subst γhom
  apply HomologicalComplex.hom_ext
  intro j
  rw [tensorComplexMap]
  change ModuleCat.of R N ◁ (γ₁.hom.f j ≫ γ₂.hom.f j) =
    ModuleCat.of R N ◁ γ₁.hom.f j ≫ ModuleCat.of R N ◁ γ₂.hom.f j
  exact MonoidalCategory.whiskerLeft_comp (ModuleCat.of R N) (γ₁.hom.f j) (γ₂.hom.f j)

end ProjectiveResolution.Hom

open ProjectiveResolution.Hom

-- Proof sketch: the compatible lift data is already packaged by
-- `freeResolution[πF].Hom freeResolution[πG] f`. The associated projective-resolution lifts
-- `α.hom` and `β.hom` are homotopic by `ProjectiveResolution.liftHomotopy`; tensoring with the
-- fixed module `N` sends that homotopy to a homotopy of tensor complexes, and homotopic chain
-- maps induce the same map on homology.
/-- Lemma 10.75.1 (1): any two augmentation-compatible lifts of a module map between free
resolutions induce the same map on the homology of the tensor complexes with `N`. -/
@[stacks 00LZ]
theorem tensor_resolution_homologyMap_eq_of_compatible_lifts
    (N : Type u) [AddCommGroup N] [Module R N]
    (f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2)
    (πF : F ⟶ moduleSingle[M1]) (πG : G ⟶ moduleSingle[M2])
    [IsFreeResolution πF] [IsFreeResolution πG]
    (α β : freeResolution[πF].Hom freeResolution[πG] f)
    (i : ℕ) :
    homologyMap
        (tensorComplexMap N β : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G) i =
      homologyMap
        (tensorComplexMap N α : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G) i := by
  -- The source proof compares compatible lifts by homotopy; tensoring preserves that homotopy.
  exact (ProjectiveResolution.Hom.tensorComplexMap_homotopy
    (R := R) (M1 := M1) (M2 := M2) (F := F) (G := G) N α β).homologyMap_eq i |>.symm

-- Proof sketch: lift the inverse module isomorphism to a morphism of the associated projective
-- resolutions. The two composites are compatible lifts of the identity, so part `(1)` shows that
-- the induced homology maps on the tensor complexes are inverse to one another.
/-- Lemma 10.75.1 (2): if the module map is an isomorphism, then any compatible lift between free
resolutions induces an isomorphism on every homology group after tensoring with `N`. -/
@[stacks 00LZ]
theorem tensor_resolution_homologyMap_isIso_of_isIso
    (N : Type u) [AddCommGroup N] [Module R N]
    (f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2) [IsIso f]
    (πF : F ⟶ moduleSingle[M1]) (πG : G ⟶ moduleSingle[M2])
    [IsFreeResolution πF] [IsFreeResolution πG]
    (α : freeResolution[πF].Hom freeResolution[πG] f)
    (i : ℕ) :
    IsIso
      (homologyMap
        (tensorComplexMap N α : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G) i) :=
  by
  -- Lift the inverse module isomorphism to the chosen free resolutions.
  let β : freeResolution[πG].Hom freeResolution[πF] (inv f) :=
    inverse_lift (R := R) (M1 := M1) (M2 := M2) f πF πG
  let eF : f ≫ inv f = 𝟙 (ModuleCat.of R M1) := IsIso.hom_inv_id f
  let eG : inv f ≫ f = 𝟙 (ModuleCat.of R M2) := IsIso.inv_hom_id f
  let idLiftF : freeResolution[πF].Hom freeResolution[πF] (f ≫ inv f) :=
    eF.symm ▸ (identity_lift :
      freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)))
  let idLiftG : freeResolution[πG].Hom freeResolution[πG] (inv f ≫ f) :=
    eG.symm ▸ (identity_lift :
      freeResolution[πG].Hom freeResolution[πG] (𝟙 (ModuleCat.of R M2)))
  have hcompF :
      homologyMap (tensorComplexMap N (comp_lift (R := R) α β) :
        (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i =
        homologyMap (tensorComplexMap N α) i ≫
          homologyMap (tensorComplexMap N β) i := by
    -- Tensoring is covariantly functorial, so the composite lift maps to the composite tensor map.
    rw [ProjectiveResolution.Hom.tensorComplexMap_comp
      (R := R) (M1 := M1) (M2 := M2) (M3 := M1) (F := F) (G := G) (H := F) N α β
      (comp_lift (R := R) α β) rfl, HomologicalComplex.homologyMap_comp]
  have hcompG :
      homologyMap (tensorComplexMap N (comp_lift (R := R) β α) :
        (tensorFunctor[N]).obj G ⟶ (tensorFunctor[N]).obj G) i =
        homologyMap (tensorComplexMap N β) i ≫
          homologyMap (tensorComplexMap N α) i := by
    -- The same tensor-functoriality computation handles the opposite composite.
    rw [ProjectiveResolution.Hom.tensorComplexMap_comp
      (R := R) (M1 := M2) (M2 := M1) (M3 := M2) (F := G) (G := F) (H := G) N β α
      (comp_lift (R := R) β α) rfl, HomologicalComplex.homologyMap_comp]
  have hidF :
      homologyMap (tensorComplexMap N idLiftF :
        (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i = 𝟙 _ := by
    -- Casting the identity lift along `f ≫ inv f = 𝟙` leaves the tensor map equal to `𝟙`.
    have hmap :
        tensorComplexMap N idLiftF = 𝟙 ((tensorFunctor[N]).obj F) := by
      simpa [idLiftF] using
        (ProjectiveResolution.Hom.casted_identity_lift_tensorComplexMap_id
          (R := R) (M := M1) (K := F) N (π := πF) (g := f ≫ inv f) eF)
    simpa [hmap] using
      (HomologicalComplex.homologyMap_id (K := (tensorFunctor[N]).obj F) (i := i))
  have hidG :
      homologyMap (tensorComplexMap N idLiftG :
        (tensorFunctor[N]).obj G ⟶ (tensorFunctor[N]).obj G) i = 𝟙 _ := by
    -- The inverse composite is handled identically on the `G`-resolution.
    have hmap :
        tensorComplexMap N idLiftG = 𝟙 ((tensorFunctor[N]).obj G) := by
      simpa [idLiftG] using
        (ProjectiveResolution.Hom.casted_identity_lift_tensorComplexMap_id
          (R := R) (M := M2) (K := G) N (π := πG) (g := inv f ≫ f) eG)
    simpa [hmap] using
      (HomologicalComplex.homologyMap_id (K := (tensorFunctor[N]).obj G) (i := i))
  have hhom_inv_id :
      homologyMap (tensorComplexMap N α) i ≫
        homologyMap (tensorComplexMap N β) i = 𝟙 _ := by
    have hEqF :
        homologyMap (tensorComplexMap N (comp_lift (R := R) α β) :
          (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i =
          homologyMap (tensorComplexMap N idLiftF :
            (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i := by
      -- The composite lift and the casted identity lift induce the same homology map.
      exact (tensor_resolution_homologyMap_eq_of_compatible_lifts
        (R := R) (M1 := M1) (M2 := M1) (F := F) (G := F) N (f ≫ inv f) πF πF
        (comp_lift (R := R) α β) idLiftF i).symm
    calc
      homologyMap (tensorComplexMap N α) i ≫
          homologyMap (tensorComplexMap N β) i =
        homologyMap (tensorComplexMap N (comp_lift (R := R) α β) :
          (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i := by
            exact hcompF.symm
      _ = homologyMap (tensorComplexMap N idLiftF :
          (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i := hEqF
      _ = 𝟙 _ := hidF
  have hinv_hom_id :
      homologyMap (tensorComplexMap N β) i ≫
        homologyMap (tensorComplexMap N α) i = 𝟙 _ := by
    have hEqG :
        homologyMap (tensorComplexMap N (comp_lift (R := R) β α) :
          (tensorFunctor[N]).obj G ⟶ (tensorFunctor[N]).obj G) i =
          homologyMap (tensorComplexMap N idLiftG :
            (tensorFunctor[N]).obj G ⟶ (tensorFunctor[N]).obj G) i := by
      -- The same comparison with the casted identity lift closes the other composite.
      exact (tensor_resolution_homologyMap_eq_of_compatible_lifts
        (R := R) (M1 := M2) (M2 := M2) (F := G) (G := G) N (inv f ≫ f) πG πG
        (comp_lift (R := R) β α) idLiftG i).symm
    calc
      homologyMap (tensorComplexMap N β) i ≫
          homologyMap (tensorComplexMap N α) i =
        homologyMap (tensorComplexMap N (comp_lift (R := R) β α) :
          (tensorFunctor[N]).obj G ⟶ (tensorFunctor[N]).obj G) i := by
            exact hcompG.symm
      _ = homologyMap (tensorComplexMap N idLiftG :
          (tensorFunctor[N]).obj G ⟶ (tensorFunctor[N]).obj G) i := hEqG
      _ = 𝟙 _ := hidG
  let invMap :=
    homologyMap (tensorComplexMap N β :
      (tensorFunctor[N]).obj G ⟶ (tensorFunctor[N]).obj F) i
  exact ⟨⟨invMap, hhom_inv_id, hinv_hom_id⟩⟩

-- Proof sketch: apply part `(1)` to the given identity lift and the identity morphism of the
-- associated projective resolution. The identity lift tensors to the identity chain map, so the
-- induced map on homology is the identity.
/-- Lemma 10.75.1 (3): an endomorphism lift of the identity map on a free resolution induces the
identity on every homology group after tensoring with `N`. -/
@[stacks 00LZ]
theorem tensor_resolution_homologyMap_eq_id_of_identity_lift
    (N : Type u) [AddCommGroup N] [Module R N]
    (πF : F ⟶ moduleSingle[M1]) [IsFreeResolution πF]
    (α : freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)))
    (i : ℕ) :
    homologyMap
        (tensorComplexMap N α : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i =
      𝟙 _ := by
  -- Compare the given identity lift with the literal identity lift of the same resolution.
  let β : freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)) :=
    identity_lift
  calc
    homologyMap
        (tensorComplexMap N α : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i =
      homologyMap
        (tensorComplexMap N β : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i := by
          simpa [β] using
            (tensor_resolution_homologyMap_eq_of_compatible_lifts
              (R := R) (M1 := M1) (M2 := M1) (F := F) (G := F)
              N (𝟙 (ModuleCat.of R M1)) πF πF α β i).symm
    _ = 𝟙 _ := by
          have hβ :
              tensorComplexMap N β = 𝟙 ((tensorFunctor[N]).obj F) := by
            simpa [β] using
              (ProjectiveResolution.Hom.tensorComplexMap_id
                (R := R) (M1 := M1) (F := F) N (πF := πF))
          simpa [hβ] using
            (HomologicalComplex.homologyMap_id
              (K := (tensorFunctor[N]).obj F) (i := i))

end
