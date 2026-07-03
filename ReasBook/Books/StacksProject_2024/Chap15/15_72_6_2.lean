import Mathlib
import stacks_project.Chap15.Lemma_15_72_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open HomologicalComplex
open ModuleCat
open MonoidalCategory
open MonoidalClosed
open scoped ModuleComplexInternalHom

noncomputable section

universe u

variable {R : Type u} [CommRing R]
variable (K L M : CochainComplex (ModuleCat R) ℤ)
variable (p q r : ℤ)

private abbrev HomObj (A B : ModuleCat R) : ModuleCat R :=
  (ihom A).obj B

/- Domain-style sampling for 15.72.6.2:
- primary domain: the differential on the tensor totalization
  `HomologicalComplex.tensorObj (module_complex_internal_hom L M) K`, together with the
  componentwise differential on the canonical internal-Hom complex `module_complex_internal_hom L M`;
- sampled owner declarations:
  `module_complex_internal_hom`,
  `module_complex_internal_hom_piIso`,
  `module_complex_internal_hom_piProj`,
  `Cochain.single`,
  `HomologicalComplex.mapBifunctor.d_eq` / `d₁_eq` / `d₂_eq`,
  `CochainComplex.HomComplex.δ_zero_cochain_v`;
- best owner abstraction:
  `core/canonical`: the total tensor differential is owned by
  `HomologicalComplex.mapBifunctor`, and the internal-Hom differential is owned by
  `CochainComplex.HomComplex`;
  `source-facing`: a fixed tensor-Hom component `α^{p,q,r}`;
  `bridge/view`: the private maps below insert the single component `α^{p,q,r}` into the canonical
  tensor complex and extract the three relevant target components from the actual target degree;
- primitive data vs. derived API: the primitive data are the actual tensor and Hom-complex
  differentials together with the canonical one-component cochain constructor `Cochain.single`;
  the owner-side projection bridge `module_complex_internal_hom_piProj` together with the
  source-component insertion and target-component extraction are derived bridge maps and are kept
  private.
- source/core/bridge triage:
  this file is purely `bridge/view`: the public source-facing statement is the chain-map theorem
  `tensor_internal_hom_to_iterated_internal_hom_f_comm` in `Lemma_15_72_6`, while the
  componentwise extraction maps here are only proof support and should not appear in exported API.
-/

local notation "S" =>
  TensorProduct R (HomObj (L.X (-q)) (M.X p)) (K.X r)

local notation "T₁" =>
  TensorProduct R (HomObj (L.X (-q)) (M.X (p + 1))) (K.X r)

local notation "T₂" =>
  TensorProduct R (HomObj (L.X (-q - 1)) (M.X p)) (K.X r)

local notation "T₃" =>
  TensorProduct R (HomObj (L.X (-q)) (M.X p)) (K.X (r + 1))

private noncomputable def alphaCochain :
    ↑(HomObj (L.X (-q)) (M.X p)) →ₗ[R] ↑((⟪L, M⟫).X (p + q)) where
  toFun := fun f ↦ Cochain.single f (p + q)
  map_add' _ _ := by
    sorry
  map_smul' _ _ := by
    sorry

private noncomputable def alphaTensorHomSource :
    ModuleCat.of R S ⟶
      (HomologicalComplex.tensorObj (⟪L, M⟫) K).X (p + q + r) :=
  ModuleCat.ofHom
      (TensorProduct.map
        (alphaCochain L M p q)
        (LinearMap.id : K.X r →ₗ[R] K.X r)) ≫
    HomologicalComplex.ιTensorObj
      (⟪L, M⟫) K (p + q) r (p + q + r) rfl

private noncomputable def alphaTensorHomTargetDesc :
    (HomologicalComplex.tensorObj (⟪L, M⟫) K).X (p + q + r + 1) ⟶
      ModuleCat.of R (T₁ × (T₂ × T₃)) :=
  HomologicalComplex.mapBifunctorDesc fun t s _ ↦
      if ht : t = p + q + 1 then
        if hs : s = r then by
          subst t
          subst s
          exact ModuleCat.ofHom <|
            LinearMap.prod
              (TensorProduct.map
                ((module_complex_internal_hom_piProj L M (p + q + 1) (-q) ≫
                    (ihom (L.X (-q))).map
                      (eqToHom (congrArg (fun z : ℤ ↦ M.X z) (by abel)))).hom)
                (LinearMap.id : K.X r →ₗ[R] K.X r))
              (LinearMap.prod
                (TensorProduct.map
                  ((module_complex_internal_hom_piProj L M (p + q + 1) (-q - 1) ≫
                      (ihom (L.X (-q - 1))).map
                        (eqToHom (congrArg (fun z : ℤ ↦ M.X z) (by abel)))).hom)
                  (LinearMap.id : K.X r →ₗ[R] K.X r))
                0)
        else
          0
      else if ht : t = p + q then
        if hs : s = r + 1 then by
          subst t
          subst s
          exact ModuleCat.ofHom <|
            LinearMap.prod
              0
              (LinearMap.prod
                0
                (TensorProduct.map
                  ((module_complex_internal_hom_piProj L M (p + q) (-q) ≫
                      (ihom (L.X (-q))).map
                        (eqToHom (congrArg (fun z : ℤ ↦ M.X z) (by abel)))).hom)
                  (LinearMap.id : K.X (r + 1) →ₗ[R] K.X (r + 1))))
        else
          0
      else
        0

private noncomputable def alphaPostcomposeDifferential :
    S →ₗ[R] T₁ :=
  TensorProduct.map
    (((ihom (L.X (-q))).map (M.d p (p + 1))).hom)
    (LinearMap.id : K.X r →ₗ[R] K.X r)

private noncomputable def alphaPrecomposeDifferential :
    S →ₗ[R] T₂ :=
  TensorProduct.map
    (((MonoidalClosed.pre (L.d (-q - 1) (-q))).app (M.X p)).hom)
    (LinearMap.id : K.X r →ₗ[R] K.X r)

private noncomputable def alphaTensorDifferential :
    S →ₗ[R] T₃ :=
  TensorProduct.map
    (LinearMap.id :
      ↑(((ihom (L.X (-q))).obj (M.X p))) →ₗ[R] ↑(((ihom (L.X (-q))).obj (M.X p))))
    (K.d r (r + 1)).hom

/- Bridge-view helper for the proof of `Lemma_15_72_6`: after inserting the fixed component
`α^{p,q,r} ∈ Hom_R(L^{-q}, M^p) ⊗ K^r` into the canonical tensor-Hom complex, the actual
differential on `HomologicalComplex.tensorObj (module_complex_internal_hom L M) K` decomposes,
after applying the private target extractor below, into the contributions of `d_M`, `d_L`, and
`d_K` with the standard signs. Since both the source insertion and the target extraction are
private bridge data, this calculation remains private as well. -/
private theorem alpha_tensor_hom_differential_components_eq :
    alphaTensorHomSource K L M p q r ≫
        (HomologicalComplex.tensorObj (⟪L, M⟫) K).d
          (p + q + r) (p + q + r + 1) ≫
      alphaTensorHomTargetDesc K L M p q r =
    ModuleCat.ofHom
      (LinearMap.prod
        (alphaPostcomposeDifferential K L M p q r)
        (LinearMap.prod
          (-((p + q).negOnePow) • alphaPrecomposeDifferential K L M p q r)
          ((p + q).negOnePow • alphaTensorDifferential K L M p q r))) := by
  sorry
