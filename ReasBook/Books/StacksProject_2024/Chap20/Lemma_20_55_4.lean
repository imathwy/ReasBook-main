import StacksProject_2024.Chap15.Lemma_15_96_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
/-- The category of `\mathcal O_X`-modules on a ringed space `X`. -/
variable {X : RingedSpace.{u}}
variable {ℐ : (RingedSpace.Modules X)}

-- Proof sketch: this is the standard module structure on the stalk of a sheaf of modules, induced
-- from the presheaf-of-modules structure before passing to the filtered colimit defining the
-- stalk.
/-- The stalk of an `\mathcal O_X`-module sheaf at `x` has its canonical
`\mathcal O_{X, x}`-module structure. -/
instance stalkModule (ℱ : (RingedSpace.Modules X)) (x : X) :
    Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x) := sorry

/-- The stalk of an `\mathcal O_X`-module sheaf at `x`, bundled as an `\mathcal O_{X, x}`-module.
-/
abbrev stalkModuleCat (ℱ : (RingedSpace.Modules X)) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)

/-- The underlying additive stalk of the unit `\mathcal O_X`-module identifies with the additive
group underlying the ring stalk `\mathcal O_{X, x}`. -/
private noncomputable abbrev unitStalkAddIso (x : X) :
    TopCat.Presheaf.stalk (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf x ≅
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat).obj
        (X.presheaf.stalk x) := by
  change TopCat.Presheaf.stalk
      (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat) x ≅ _
  exact Limits.colimit.isoColimitCocone
    ⟨_, Limits.isColimitOfPreserves
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙ X.presheaf))⟩

-- Proof sketch: the additive stalk identification comes from forgetting the ring structure along a
-- colimit-preserving functor, so it respects the scalar action of `\mathcal O_{X, x}` coming from
-- the unit module structure.
/-- The additive stalk identification for the unit module is linear over the stalk ring. -/
private theorem unitStalkLinearEquiv_map_smul (x : X)
    (r : X.presheaf.stalk x) (m : ↑(stalkModuleCat (SheafOfModules.unit (RingedSpace.ringCatSheaf X)) x)) :
    (show ↑(X.presheaf.stalk x) from (unitStalkAddIso x).hom (r • m)) =
      r • (show ↑(X.presheaf.stalk x) from (unitStalkAddIso x).hom m) := sorry

/-- The stalk of the unit `\mathcal O_X`-module, identified linearly with the stalk ring
`\mathcal O_{X, x}` itself. -/
noncomputable def unitStalkLinearEquiv (x : X) :
    ↑(stalkModuleCat (SheafOfModules.unit (RingedSpace.ringCatSheaf X)) x) ≃ₗ[X.presheaf.stalk x]
      ↑(X.presheaf.stalk x) where
  __ := (unitStalkAddIso x).addCommGroupIsoToAddEquiv
  map_smul' := unitStalkLinearEquiv_map_smul x

/-- The linear map identifying the stalk of the unit module sheaf with the stalk ring. -/
private noncomputable def unitStalkLinearMap (x : X) :
    stalkModuleCat (SheafOfModules.unit (RingedSpace.ringCatSheaf X)) x ⟶
      ModuleCat.of (X.presheaf.stalk x) ↑(X.presheaf.stalk x) :=
  ModuleCat.ofHom (unitStalkLinearEquiv x).toLinearMap

variable {A : Type u} [CommRing A]

/-- The category of `ℕ`-indexed cochain complexes of `\mathcal O_X`-modules. -/
abbrev NatSheafModuleCochainComplex (X : RingedSpace.{u}) :=
  CochainComplex (RingedSpace.Modules X) ℕ

/-- The underlying map on stalks induced by a morphism of `\mathcal O_X`-modules. -/
private noncomputable abbrev stalkModuleUnderlyingMap (x : X)
    {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢) :
    TopCat.Presheaf.stalk ℱ.val.presheaf x ⟶ TopCat.Presheaf.stalk 𝒢.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val)

-- Proof sketch: the stalk map is a morphism in `AddCommGrpCat`, so it preserves addition.
/-- The map on stalks induced by a morphism of `\mathcal O_X`-modules is additive. -/
private theorem stalkModuleUnderlyingMap_add (x : X)
    {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢)
    (m n : ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)) :
    stalkModuleUnderlyingMap x φ (m + n) =
      stalkModuleUnderlyingMap x φ m + stalkModuleUnderlyingMap x φ n := sorry

-- Proof sketch: represent scalars and elements by germs, use linearity of `φ` on sections, and
-- pass to the filtered colimit defining the stalk.
/-- The map on stalks induced by a morphism of `\mathcal O_X`-modules is linear over the stalk
ring. -/
private theorem stalkModuleUnderlyingMap_smul (x : X)
    {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢)
    (r : X.presheaf.stalk x) (m : ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)) :
    stalkModuleUnderlyingMap x φ (r • m) =
      r • stalkModuleUnderlyingMap x φ m := sorry

/-- The morphism on stalk modules induced by a morphism of `\mathcal O_X`-modules. -/
private noncomputable def stalkModuleMap (x : X)
    {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢) :
    stalkModuleCat ℱ x ⟶ stalkModuleCat 𝒢 x :=
  ModuleCat.ofHom
    { toFun := stalkModuleUnderlyingMap x φ
      map_add' := stalkModuleUnderlyingMap_add x φ
      map_smul' := stalkModuleUnderlyingMap_smul x φ }

-- Proof sketch: if `j ≠ i + 1`, then `K.d i j = 0` by the cochain-shape axiom, so the induced map
-- on stalks is also zero.
/-- The stalk differential is zero away from consecutive degrees. -/
private theorem stalkNatComplex_shape
    (K : NatSheafModuleCochainComplex X) (x : X)
    (i j : ℕ) (hij : ¬ (ComplexShape.up ℕ).Rel i j) :
    stalkModuleMap x (K.d i j) = 0 := sorry

-- Proof sketch: the composite of two stalk differentials is the stalk map of the composite
-- differential in `K`, and that composite vanishes because `K` is a cochain complex.
/-- Two successive differentials in the stalk complex compose to zero. -/
private theorem stalkNatComplex_d_comp_d
    (K : NatSheafModuleCochainComplex X) (x : X)
    (i j k : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) (hjk : (ComplexShape.up ℕ).Rel j k) :
    stalkModuleMap x (K.d i j) ≫ stalkModuleMap x (K.d j k) = 0 := sorry

/-- The cochain complex of stalk modules obtained from an `ℕ`-indexed complex of
`\mathcal O_X`-modules. -/
noncomputable def stalkNatComplex (K : NatSheafModuleCochainComplex X) (x : X) :
    NatModuleCochainComplex (X.presheaf.stalk x) where
  X i := stalkModuleCat (K.X i) x
  d i j := stalkModuleMap x (K.d i j)
  shape i j hij := stalkNatComplex_shape K x i j hij
  d_comp_d' i j k hij hjk := stalkNatComplex_d_comp_d K x i j k hij hjk

/-- The ideal of the local ring `\mathcal O_{X, x}` obtained from the image of the ideal-sheaf
stalk inside the stalk of the structure sheaf. -/
noncomputable def idealSheafStalkIdeal
    (ι : ℐ ⟶ SheafOfModules.unit (RingedSpace.ringCatSheaf X)) (x : X) : Ideal (X.presheaf.stalk x) :=
  show Ideal (X.presheaf.stalk x) from
    LinearMap.range ((stalkModuleMap x ι ≫ unitStalkLinearMap x).hom)

/-- A cochain complex is termwise `\mathcal I`-torsion free when, for every point `x` and every
generator `f` of the ideal `\mathcal I_x`, multiplication by `f` is injective on each stalk term.
-/
def IsTermwiseIdealTorsionFree
    (ι : ℐ ⟶ SheafOfModules.unit (RingedSpace.ringCatSheaf X))
    (K : NatSheafModuleCochainComplex X) : Prop :=
  ∀ n : ℕ, ∀ x : X, ∀ f : X.presheaf.stalk x,
    idealSheafStalkIdeal ι x = Ideal.span ({f} : Set (X.presheaf.stalk x)) →
      Function.Injective ((f • ·) : (stalkNatComplex K x).X n → (stalkNatComplex K x).X n)

/-- The degree-`n` term of the stalkwise Berthelot-Ogus operator attached to the ideal sheaf
`\mathcal I`. It models the stalk `(η_\mathcal I K^\bullet)_x` without choosing a local
generator. -/
abbrev etaIdealStalkDegreeSubmodule
    (ι : ℐ ⟶ SheafOfModules.unit (RingedSpace.ringCatSheaf X))
    (K : NatSheafModuleCochainComplex X) (x : X) (n : ℕ) :
    Submodule (X.presheaf.stalk x) ((stalkNatComplex K x).X n) :=
  ((idealSheafStalkIdeal ι x ^ n) •
      (⊤ : Submodule (X.presheaf.stalk x) ((stalkNatComplex K x).X n))) ⊓
    (((idealSheafStalkIdeal ι x ^ (n + 1)) •
      (⊤ : Submodule (X.presheaf.stalk x) ((stalkNatComplex K x).X (n + 1)))).comap
        ((stalkNatComplex K x).d n (n + 1)).hom)

-- Proof sketch: the differential is linear, so it sends the `\mathcal I_x^n`-multiple condition
-- into the `\mathcal I_x^{n + 1}`-multiple condition, and the second defining condition advances
-- by one degree because successive differentials compose to zero.
/-- The stalk differential sends the degree-`n` Berthelot-Ogus submodule into degree `n + 1`. -/
theorem etaIdealStalkDifferential_mem
    (ι : ℐ ⟶ SheafOfModules.unit (RingedSpace.ringCatSheaf X))
    (K : NatSheafModuleCochainComplex X) (x : X) (n : ℕ) :
    ∀ s : etaIdealStalkDegreeSubmodule ι K x n,
      (stalkNatComplex K x).d n (n + 1) s ∈ etaIdealStalkDegreeSubmodule ι K x (n + 1) := sorry

/-- The degree-`n` differential on the stalkwise Berthelot-Ogus complex attached to
`\mathcal I`. -/
abbrev etaIdealStalkDifferentialLinear
    (ι : ℐ ⟶ SheafOfModules.unit (RingedSpace.ringCatSheaf X))
    (K : NatSheafModuleCochainComplex X) (x : X) (n : ℕ) :
    etaIdealStalkDegreeSubmodule ι K x n →ₗ[X.presheaf.stalk x]
      etaIdealStalkDegreeSubmodule ι K x (n + 1) :=
  (((stalkNatComplex K x).d n (n + 1)).hom.comp
      (etaIdealStalkDegreeSubmodule ι K x n).subtype).codRestrict
    (etaIdealStalkDegreeSubmodule ι K x (n + 1))
    (etaIdealStalkDifferential_mem ι K x n)

-- Proof sketch: the differentials are restrictions of the stalk differentials of `K`, so their
-- composite is the restriction of `d ∘ d = 0`.
/-- Two successive differentials in the stalkwise Berthelot-Ogus complex compose to zero. -/
theorem etaIdealStalkDifferential_sq
    (ι : ℐ ⟶ SheafOfModules.unit (RingedSpace.ringCatSheaf X))
    (K : NatSheafModuleCochainComplex X) (x : X) (n : ℕ) :
    ModuleCat.ofHom (etaIdealStalkDifferentialLinear ι K x n) ≫
        ModuleCat.ofHom (etaIdealStalkDifferentialLinear ι K x (n + 1)) =
      0 := sorry

/-- The stalkwise Berthelot-Ogus complex attached to the ideal sheaf inclusion
`\mathcal I \hookrightarrow \mathcal O_X`. This is the source-facing model for
`(η_\mathcal I K^\bullet)_x`. -/
noncomputable def etaIdealStalkComplex
    (ι : ℐ ⟶ SheafOfModules.unit (RingedSpace.ringCatSheaf X))
    (K : NatSheafModuleCochainComplex X) (x : X) :
    NatModuleCochainComplex (X.presheaf.stalk x) :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of (X.presheaf.stalk x) (etaIdealStalkDegreeSubmodule ι K x n))
    (fun n ↦ ModuleCat.ofHom (etaIdealStalkDifferentialLinear ι K x n))
    (fun n ↦ etaIdealStalkDifferential_sq ι K x n)

-- Proof sketch: unfold `etaIdealStalkComplex`; `CochainComplex.of` stores the chosen degreewise
-- submodules as the object function of the resulting complex.
/-- The degree-`n` term of the stalkwise Berthelot-Ogus complex is the displayed degreewise
submodule. -/
theorem etaIdealStalkComplex_X
    (ι : ℐ ⟶ SheafOfModules.unit (RingedSpace.ringCatSheaf X))
    (K : NatSheafModuleCochainComplex X) (x : X) (n : ℕ) :
    (etaIdealStalkComplex ι K x).X n =
      ModuleCat.of (X.presheaf.stalk x) (etaIdealStalkDegreeSubmodule ι K x n) := sorry

-- Proof sketch: if `\mathcal I_x = (f)`, then the ideal-power filtration
-- `\mathcal I_x^n (K_x^n)` is exactly the principal-power filtration `f^n (K_x^n)`. After
-- rewriting both degreewise submodules using the generator equation `hf`, the two complexes have
-- the same terms and the same restricted differentials.
/-- Lemma 20.55.4: let `K^\bullet` be a complex of `\mathcal I`-torsion free
`\mathcal O_X`-modules. For a point `x` and a generator `f` of the ideal stalk `\mathcal I_x`,
the stalkwise Berthelot-Ogus complex `(η_\mathcal I K^\bullet)_x` is canonically isomorphic to
the local Berthelot-Ogus complex `η_f(K_x^\bullet)` from More on Algebra, Section `15.96`. -/
theorem etaIdealStalkComplex_iso_etaFComplex_of_generator
    (ι : ℐ ⟶ SheafOfModules.unit (RingedSpace.ringCatSheaf X))
    (K : NatSheafModuleCochainComplex X) (hK : IsTermwiseIdealTorsionFree ι K)
    (x : X) (f : X.presheaf.stalk x)
    (hf : idealSheafStalkIdeal ι x = Ideal.span ({f} : Set (X.presheaf.stalk x))) :
    Nonempty (etaIdealStalkComplex ι K x ≅ η[f] (stalkNatComplex K x)) := sorry

end AlgebraicGeometry.RingedSpace
