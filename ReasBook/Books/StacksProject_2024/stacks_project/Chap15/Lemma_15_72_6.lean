import Mathlib.Algebra.Homology.Monoidal
import StacksProject_2024.stacks_project.Chap15.Lemma_15_72_1

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open ComplexShape
open HomologicalComplex
open MonoidalClosed
open scoped ModuleComplexInternalHom

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation:70 A " ⊗ " B => tensorObj A B

/- Domain-style sampling for 15.72.6:
- primary domain: the tensor-to-iterated-internal-Hom comparison for the chapter internal-Hom
  complex on cochain complexes of `R`-modules;
- sampled owner declarations:
  `module_complex_internal_hom`,
  `module_complex_internal_hom_piIso`,
  `module_complex_internal_hom_piProj`,
  `HomologicalComplex.tensorObj`,
  `HomologicalComplex.mapBifunctorDesc`,
  `MonoidalClosed.curry`,
  `ihom.ev`;
- best owner abstraction: the public owner remains the source-facing Chapter 15 internal-Hom
  complex `⟪-, -⟫`, and the tensor source should be presented on the theorem surface by the
  canonical cochain-complex tensor notation `⊗`; the ambient module-level closed-monoidal
  structure supplies the summandwise evaluation/currying maps used to build the chain map, but it
  does not replace the chapter owner;
- primitive data vs. derived API: the primitive owner data are the complexes `⟪K, L⟫` and their
  canonical degree decompositions `module_complex_internal_hom_piIso`; the owner-side projection
  bridge `module_complex_internal_hom_piProj` and the canonical morphism
  `⟪L, M⟫ ⊗ K ⟶ ⟪⟪K, L⟫, M⟫`, together with its three source-facing naturality squares in `K`,
  `L`, and `M`, are derived API expressed through the owner-side bifunctorial bridge
  `module_complex_internal_homMap`;
- source/core/bridge triage:
  `source-facing`: `tensor_internal_hom_to_iterated_internal_hom`;
  `core/canonical`: `module_complex_internal_hom`, `module_complex_internal_hom_piIso`,
    `HomologicalComplex.tensorObj`, `MonoidalClosed.curry`, and `ihom.ev`;
  `bridge/view`: the projection maps from the product decomposition of the source and target
  internal-Hom complexes together with the owner-side bifunctoriality map
  `module_complex_internal_homMap`.
-/ 

-- Proof sketch: rewrite `n` as `t + r` and reassociate the sum on `ℤ`.
/-- Reindexing the target degree in the iterated tensor-Hom comparison map. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_indexEq
    {t r n p : ℤ} (h : t + r = n) :
    t + (p + r) = n + p := by
  omega

section

open MonoidalCategory

/-- The summandwise braiding/evaluation map contributing to the degree-`n` component of the
canonical morphism `Tot(⟪L, M⟫ ⊗ K) ⟶ ⟪⟪K, L⟫, M⟫`. This is the owner-level component whose
sign is analyzed in Remark `15.72.7`. -/
noncomputable def tensor_internal_hom_to_iterated_internal_hom_component
    (K L M : CpxR) (t r n p : ℤ) (h : t + r = n) :
    ((⟪L, M⟫).X t ⊗ K.X r) ⟶
      (ihom ((⟪K, L⟫).X p)).obj (M.X (n + p)) :=
  (r * p).negOnePow •
    MonoidalClosed.curry
      (((module_complex_internal_hom_piProj K L p r) ⊗ₘ
          ((module_complex_internal_hom_piProj L M t (p + r)) ⊗ₘ 𝟙 (K.X r))) ≫
        (α_ ((ihom (K.X r)).obj (L.X (p + r)))
          ((ihom (L.X (p + r))).obj (M.X (t + (p + r)))) (K.X r)).inv ≫
        ((β_ ((ihom (K.X r)).obj (L.X (p + r)))
            ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))).hom ⊗ₘ
          𝟙 (K.X r)) ≫
        (β_ (((ihom (L.X (p + r))).obj (M.X (t + (p + r)))) ⊗
            ((ihom (K.X r)).obj (L.X (p + r)))) (K.X r)).hom ≫
        (K.X r ◁
          (β_ ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))
            ((ihom (K.X r)).obj (L.X (p + r)))).hom) ≫
        (α_ (K.X r) ((ihom (K.X r)).obj (L.X (p + r)))
          ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))).inv ≫
        ((ihom.ev (K.X r)).app (L.X (p + r)) ⊗ₘ
          𝟙 ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))) ≫
        (ihom.ev (L.X (p + r))).app (M.X (t + (p + r))) ≫
        eqToHom (congrArg (fun z : ℤ ↦ M.X z)
          (tensor_internal_hom_to_iterated_internal_hom_indexEq h)))

end

/-- The degree-`n` component of the canonical tensor-to-iterated-internal-Hom morphism. -/
private noncomputable def tensor_internal_hom_to_iterated_internal_hom_f
    (K L M : CpxR) [HasTensor (⟪L, M⟫) K] (n : ℤ) :
    (⟪L, M⟫ ⊗ K).X n ⟶ (⟪⟪K, L⟫, M⟫).X n :=
  let desc :
      (⟪L, M⟫ ⊗ K).X n ⟶
        ∏ᶜ fun p : ℤ ↦ (ihom ((⟪K, L⟫).X p)).obj (M.X (n + p)) :=
    mapBifunctorDesc fun t r h ↦
      Pi.lift fun p ↦
        tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h
  desc ≫ (module_complex_internal_hom_piIso ⟪K, L⟫ M n).hom

/-- Helper for Lemma 15.72.6: the `p`-th projection out of a degree-`n` internal-Hom object is
the corresponding stored cochain component. -/
private theorem module_complex_internal_hom_piProj_apply_eq_v
    (K L : CpxR) (n p : ℤ) (z : (⟪K, L⟫).X n) :
    (module_complex_internal_hom_piProj K L n p).hom z = z.v p (n + p) (by omega) := by
  -- The product projection was defined by unpacking the degreewise cochain family.
  rfl

/-- Helper for Lemma 15.72.6: after restricting to a fixed tensor summand and then projecting to
the `p`-th target factor, the descended degree-`n` map is the corresponding summandwise
braiding/evaluation component. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_f_ι_pi
    (K L M : CpxR) [HasTensor (⟪L, M⟫) K]
    (t r n p : ℤ) (h : t + r = n) :
    HomologicalComplex.ιTensorObj (⟪L, M⟫) K t r n h ≫
        tensor_internal_hom_to_iterated_internal_hom_f K L M n ≫
        module_complex_internal_hom_piProj ⟪K, L⟫ M n p =
      tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h := by
  -- Remove the target product isomorphism, then evaluate the coproduct descender on the chosen
  -- tensor summand and finally project to the selected target factor.
  unfold tensor_internal_hom_to_iterated_internal_hom_f
  rw [Category.assoc]
  have hdesc := congrArg
    (fun u ↦ u ≫ Pi.π (fun q : ℤ ↦ (ihom ((⟪K, L⟫).X q)).obj (M.X (n + q))) p)
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := ⟪L, M⟫) (K₂ := K) (F := MonoidalCategory.curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ)
      (A := ∏ᶜ fun q : ℤ ↦ (ihom ((⟪K, L⟫).X q)).obj (M.X (n + q)))
      (j := n)
      (f := fun t r h ↦
        Pi.lift fun p ↦ tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h)
      t r h)
  simpa [Category.assoc, HomologicalComplex.ιTensorObj, CategoryTheory.Limits.Pi.lift_π,
    module_complex_internal_hom_piIso, module_complex_internal_hom_piProj] using hdesc

/-- Helper for Lemma 15.72.6: on the diagonal `p = q + r` singled out by the `r`-projection of
`⟪K, L⟫`, the braiding sign `(-1)^(rp)` agrees with the direct-construction sign
`(-1)^(r + qr)`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_component_sign_eq
    {q r p : ℤ} (hp : q + r = p) :
    (r * p).negOnePow = (r + q * r).negOnePow := by
  calc
    (r * p).negOnePow = (r * (q + r)).negOnePow := by rw [hp]
    _ = (q * r + r * r).negOnePow := by
      congr 1
      ring
    _ = (q * r).negOnePow * (r * r).negOnePow := by
      rw [Int.negOnePow_add]
    _ = (q * r).negOnePow * r.negOnePow := by
      rw [Int.negOnePow_mul_self]
    _ = (q * r + r).negOnePow := by
      rw [← Int.negOnePow_add]
    _ = (r + q * r).negOnePow := by
      congr 1
      ring

/-- Helper for Lemma 15.72.6: shifting the left tensor index by one preserves the total
degree. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_left_succ_indexEq
    (t r : ℤ) :
    (t + 1) + r = t + r + 1 := by
  omega

/-- Helper for Lemma 15.72.6: shifting the right tensor index by one preserves the total
degree. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_right_succ_indexEq
    (t r : ℤ) :
    t + (r + 1) = t + r + 1 := by
  omega

section

open MonoidalCategory

/-- Helper for Lemma 15.72.6: on a fixed tensor summand, the total tensor differential splits
into the horizontal differential plus the signed vertical differential. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_source_d_on_summand
    (K L M : CpxR) [HasTensor (⟪L, M⟫) K] (t r : ℤ) :
    HomologicalComplex.ιTensorObj (⟪L, M⟫) K t r (t + r) rfl ≫
        (⟪L, M⟫ ⊗ K).d (t + r) (t + r + 1) =
      (((⟪L, M⟫).d t (t + 1)) ⊗ₘ 𝟙 (K.X r)) ≫
          HomologicalComplex.ιTensorObj (⟪L, M⟫) K (t + 1) r (t + r + 1)
            (tensor_internal_hom_to_iterated_internal_hom_left_succ_indexEq t r) +
        t.negOnePow •
          ((𝟙 ((⟪L, M⟫).X t) ⊗ₘ K.d r (r + 1)) ≫
            HomologicalComplex.ιTensorObj (⟪L, M⟫) K t (r + 1) (t + r + 1)
              (tensor_internal_hom_to_iterated_internal_hom_right_succ_indexEq t r)) := by
  -- Route correction: use the owner tensor-totalization Leibniz rule on the chosen summand
  -- instead of unfolding the total tensor complex by hand.
  change
    HomologicalComplex.ιMapBifunctor (⟪L, M⟫) K
        (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) t r (t + r) rfl ≫
        (HomologicalComplex.mapBifunctor (⟪L, M⟫) K
          (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).d
          (t + r) (t + r + 1) =
      (((⟪L, M⟫).d t (t + 1)) ⊗ₘ 𝟙 (K.X r)) ≫
          HomologicalComplex.ιMapBifunctor (⟪L, M⟫) K
            (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
            (t + 1) r (t + r + 1)
            (tensor_internal_hom_to_iterated_internal_hom_left_succ_indexEq t r) +
        t.negOnePow •
          ((𝟙 ((⟪L, M⟫).X t) ⊗ₘ K.d r (r + 1)) ≫
            HomologicalComplex.ιMapBifunctor (⟪L, M⟫) K
              (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
              t (r + 1) (t + r + 1)
              (tensor_internal_hom_to_iterated_internal_hom_right_succ_indexEq t r))
  -- Rewrite the total differential into its horizontal and vertical pieces on this summand.
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq (⟪L, M⟫) K
      (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
      (show (ComplexShape.up ℤ).Rel t (t + 1) by simp) r (t + r + 1)
      (tensor_internal_hom_to_iterated_internal_hom_left_succ_indexEq t r),
    HomologicalComplex.mapBifunctor.d₂_eq (⟪L, M⟫) K
      (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) t
      (show (ComplexShape.up ℤ).Rel r (r + 1) by simp) (t + r + 1)
      (tensor_internal_hom_to_iterated_internal_hom_right_succ_indexEq t r)]
  -- For cochain complexes over `ℤ`, the vertical sign is exactly `(-1)^t`.
  simp only [MonoidalCategory.curriedTensor_obj_obj, ε₁_def,
    MonoidalCategory.curriedTensor_map_app, ε₂_def, ComplexShape.ε_up_ℤ,
    MonoidalCategory.curriedTensor_obj_map, tensorHom_id, id_tensorHom]
  let A :=
    (⟪L, M⟫).d t (t + 1) ▷ K.X r ≫
      HomologicalComplex.ιMapBifunctor (⟪L, M⟫) K
        (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
        (t + 1) r (t + r + 1)
        (tensor_internal_hom_to_iterated_internal_hom_left_succ_indexEq t r)
  let B :=
    t.negOnePow •
      ((⟪L, M⟫).X t ◁ K.d r (r + 1) ≫
        HomologicalComplex.ιMapBifunctor (⟪L, M⟫) K
          (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
          t (r + 1) (t + r + 1)
          (tensor_internal_hom_to_iterated_internal_hom_right_succ_indexEq t r))
  change ((1 : ℤ) • A) + B = A + B
  have hA : (1 : ℤ) • A = A := by
    simp
  exact congrArg (fun u ↦ u + B) hA

end

/-- Helper for Lemma 15.72.6: projecting `module_complex_internal_homMap fK fL` to the `p`-th
target factor gives precomposition by `fK.f p` and postcomposition by `fL.f (n + p)`. -/
private theorem module_complex_internal_homMap_piProj_apply
    {K₁ K₂ L₁ L₂ : CpxR}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂)
    (n p : ℤ) (z : (⟪K₁, L₁⟫).X n) (x : K₂.X p) :
    (ModuleCat.Hom.hom
        ((module_complex_internal_hom_piProj K₂ L₂ n p).hom
          (((module_complex_internal_homMap fK fL).f n).hom z))) x =
      (ModuleCat.Hom.hom (fL.f (n + p)))
        ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K₁ L₁ n p).hom z))
          ((ModuleCat.Hom.hom (fK.f p)) x)) := by
  -- Rewrite the internal-Hom map and both projections in cochain coordinates.
  rw [module_complex_internal_hom_piProj_apply_eq_v,
    module_complex_internal_hom_piProj_apply_eq_v]
  simp only [module_complex_internal_homMap, Cochain.comp_zero_cochain_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

/-- Helper for Lemma 15.72.6: on a pure tensor and a fixed target cochain, the summandwise
comparison map is given by nested evaluation along the two internal-Hom projections. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul
    (K L M : CpxR) (t r n p : ℤ) (h : t + r = n)
    (g : (⟪L, M⟫).X t) (k : K.X r) (φ : (⟪K, L⟫).X p) :
    (ModuleCat.Hom.hom
        ((tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h).hom
          (TensorProduct.tmul R g k))) φ =
      (r * p).negOnePow •
        (ModuleCat.Hom.hom
            (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
              (tensor_internal_hom_to_iterated_internal_hom_indexEq h))))
          ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L M t (p + r)).hom g))
            ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p r).hom φ)) k)) := by
  -- Evaluate the braided currying composite on the chosen pure tensor and target cochain.
  unfold tensor_internal_hom_to_iterated_internal_hom_component
  -- The closed-structure curry, braiding, and evaluation morphisms reduce to direct nested
  -- application in `ModuleCat R`.
  simp only [Category.assoc, ModuleCat.hom_smul, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply, ModuleCat.monoidalClosed_curry,
    ModuleCat.ihom_map_apply, module_complex_internal_hom_piProj_apply_eq_v]

/-- Helper for Lemma 15.72.6: advancing the source degree by one matches the target degree after
using the cochain-complex relation `j = i + 1`. -/
private theorem module_complex_internal_hom_shift_indexEq
    (i j p : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    i + (p + 1) = j + p := by
  -- Rewrite the cochain-shape relation as `j = i + 1` and reassociate the sum.
  have hij' : i + 1 = j := by
    simpa using hij
  simpa [add_assoc, add_left_comm, add_comm] using congrArg (fun z : ℤ ↦ z + p) hij'

/-- Helper for Lemma 15.72.6: the shifted `(p + 1)` projection in the internal-Hom differential
is the transported `(p + 1, j + p)` cochain component. -/
private theorem module_complex_internal_hom_piProj_succ_transport_apply
    (K L : CpxR) (i j p : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (z : (⟪K, L⟫).X i) (x : K.X p) :
    (ModuleCat.Hom.hom
        (eqToHom (congrArg (fun z : ℤ ↦ L.X z)
          (module_complex_internal_hom_shift_indexEq i j p hij))))
      ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L i (p + 1)).hom z))
        ((ModuleCat.Hom.hom (K.d p (p + 1))) x)) =
      (ModuleCat.Hom.hom
          (z.v (p + 1) (j + p)
            (by
              simpa [module_complex_internal_hom_shift_indexEq i j p hij] using
                (show i + (p + 1) = i + (p + 1) by omega))))
        ((ModuleCat.Hom.hom (K.d p (p + 1))) x) := by
  -- Rewrite the shifted projection as a concrete cochain component and then eliminate the
  -- remaining `eqToHom` by turning it into a cast on elements.
  have hij' : i + 1 = j := by
    simpa using hij
  subst j
  rw [module_complex_internal_hom_piProj_apply_eq_v]
  change
    cast (congrArg (fun z : ℤ ↦ L.X z)
        (module_complex_internal_hom_shift_indexEq i (i + 1) p
          (by simpa using (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))))
      ((ModuleCat.Hom.hom
          (z.v (p + 1) (i + (p + 1))
            (by omega)))
        ((ModuleCat.Hom.hom (K.d p (p + 1))) x)) =
    (ModuleCat.Hom.hom
        (z.v (p + 1) (i + 1 + p)
          (by
            simpa [module_complex_internal_hom_shift_indexEq i (i + 1) p
              (by simpa using (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))] using
              (show i + (p + 1) = i + (p + 1) by omega))))
      ((ModuleCat.Hom.hom (K.d p (p + 1))) x)
  simpa using
    cast_eq
      (congrArg (fun z : ℤ ↦ L.X z)
        (module_complex_internal_hom_shift_indexEq i (i + 1) p
          (by simpa using (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))))
      ((ModuleCat.Hom.hom
          (z.v (p + 1) (i + (p + 1))
            (by omega)))
        ((ModuleCat.Hom.hom (K.d p (p + 1))) x))

/-- Helper for Lemma 15.72.6: after projecting the iterated internal-Hom differential to the
`p`-th factor and then evaluating at `φ`, one obtains the owner Leibniz formula `δ_v`. -/
private theorem module_complex_internal_hom_d_piProj_apply
    (K L M : CpxR) (i j p : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (η : (⟪⟪K, L⟫, M⟫).X i) (φ : (⟪K, L⟫).X p) :
    (ModuleCat.Hom.hom
        ((module_complex_internal_hom_piProj ⟪K, L⟫ M j p).hom
          (((⟪⟪K, L⟫, M⟫).d i j).hom η))) φ =
      (ModuleCat.Hom.hom (M.d (i + p) (j + p)))
          ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj ⟪K, L⟫ M i p).hom η)) φ) +
        j.negOnePow •
          (
          (ModuleCat.Hom.hom
              (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
                (module_complex_internal_hom_shift_indexEq i j p hij))))
            ((ModuleCat.Hom.hom
                ((module_complex_internal_hom_piProj ⟪K, L⟫ M i (p + 1)).hom η))
              (((⟪K, L⟫).d p (p + 1)).hom φ))) := by
  -- Rewrite both projections as owner cochain components so that the differential is exactly
  -- the standard Hom-complex differential `δ_v`.
  rw [module_complex_internal_hom_piProj_apply_eq_v]
  rw [module_complex_internal_hom_piProj_succ_transport_apply ⟪K, L⟫ M i j p hij η φ]
  have hij' : i + 1 = j := by
    simpa using hij
  have hq₁ : i + p = j + p - 1 := by
    omega
  simpa using
    congrArg
      (fun f : (⟪K, L⟫).X p ⟶ M.X (j + p) ↦ ModuleCat.Hom.hom f φ)
      (CochainComplex.HomComplex.δ_v (F := ⟪K, L⟫) (G := M) i j hij' η p (j + p)
        (by omega) (i + p) (p + 1) hq₁ rfl)

/-- Helper for Lemma 15.72.6: after projecting the ordinary internal-Hom differential to the
`p`-th factor and then evaluating at `x`, one obtains the owner Leibniz formula `δ_v`. -/
private theorem module_complex_internal_hom_d_after_piProj_apply
    (K L : CpxR) (i j p : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (z : (⟪K, L⟫).X i) (x : K.X p) :
    (ModuleCat.Hom.hom
        ((module_complex_internal_hom_piProj K L j p).hom (((⟪K, L⟫).d i j).hom z))) x =
      (ModuleCat.Hom.hom (L.d (i + p) (j + p)))
          ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L i p).hom z)) x) +
        j.negOnePow •
          (ModuleCat.Hom.hom
              (eqToHom (congrArg (fun z : ℤ ↦ L.X z)
                (module_complex_internal_hom_shift_indexEq i j p hij))))
            ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L i (p + 1)).hom z))
              ((ModuleCat.Hom.hom (K.d p (p + 1))) x)) := by
  -- Rewrite both projections as owner cochain components so that the differential is exactly
  -- the standard Hom-complex differential `δ_v`.
  rw [module_complex_internal_hom_piProj_apply_eq_v]
  rw [module_complex_internal_hom_piProj_succ_transport_apply K L i j p hij z x]
  have hij' : i + 1 = j := by
    simpa using hij
  have hq₁ : i + p = j + p - 1 := by
    omega
  simpa using
    congrArg
      (fun f : K.X p ⟶ L.X (j + p) ↦ ModuleCat.Hom.hom f x)
      (CochainComplex.HomComplex.δ_v (F := K) (G := L) i j hij' z p (j + p)
        (by omega) (i + p) (p + 1) hq₁ rfl)

/-- Helper for Lemma 15.72.6: the target-horizontal sign coming from the degree `p + 1`
projection matches the source-horizontal sign after inserting the component sign `(-1)^(rp)`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_horizontal_sign
    (t r p : ℤ) :
    ((t + r + 1).negOnePow : R) * (r * (p + 1)).negOnePow =
      (r * p).negOnePow * (t + 1).negOnePow := by
  calc
    ((t + r + 1).negOnePow : R) * (r * (p + 1)).negOnePow =
        ((t + r + 1) + r * (p + 1)).negOnePow := by
          rw [← Int.negOnePow_add]
    _ = (r * p + (t + 1)).negOnePow := by
      congr 1
      ring
    _ = (r * p).negOnePow * (t + 1).negOnePow := by
      rw [Int.negOnePow_add]

/-- Helper for Lemma 15.72.6: the target-vertical sign coming from the degree `p + 1`
projection matches the source-vertical sign after inserting the component sign `(-1)^(rp)`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_vertical_sign
    (t r p : ℤ) :
    (((t + r + 1).negOnePow : R) * (r * (p + 1)).negOnePow) * (p + 1).negOnePow =
      t.negOnePow * ((r + 1) * p).negOnePow := by
  calc
    (((t + r + 1).negOnePow : R) * (r * (p + 1)).negOnePow) * (p + 1).negOnePow =
        ((t + r + 1) + r * (p + 1) + (p + 1)).negOnePow := by
          rw [← Int.negOnePow_add, ← Int.negOnePow_add]
          ring
    _ = (t + ((r + 1) * p)).negOnePow := by
      congr 1
      ring
    _ = t.negOnePow * ((r + 1) * p).negOnePow := by
      rw [Int.negOnePow_add]

/-- Helper for Lemma 15.72.6: after evaluating both chain-map candidates on a pure tensor and a
fixed target cochain, the remaining equality is the textbook three-term Leibniz rule with the
component sign `(-1)^(rp)`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_pointwise_leibniz
    (K L M : CpxR) [HasTensor (⟪L, M⟫) K]
    (t r p : ℤ) (g : (⟪L, M⟫).X t) (k : K.X r) (φ : (⟪K, L⟫).X p) :
    (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K t r (t + r) rfl ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L M (t + r) ≫
            (⟪⟪K, L⟫, M⟫).d (t + r) (t + r + 1) ≫
            module_complex_internal_hom_piProj ⟪K, L⟫ M (t + r + 1) p).hom)
          (TensorProduct.tmul R g k))) φ =
      (ModuleCat.Hom.hom
          (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K t r (t + r) rfl ≫
              (⟪L, M⟫ ⊗ K).d (t + r) (t + r + 1) ≫
              tensor_internal_hom_to_iterated_internal_hom_f K L M (t + r + 1) ≫
              module_complex_internal_hom_piProj ⟪K, L⟫ M (t + r + 1) p).hom)
            (TensorProduct.tmul R g k))) φ := by
  -- First rewrite the degree-`t + r` comparison map on the chosen tensor summand and the
  -- `p`- and `(p + 1)`-projections needed in the target internal-Hom differential.
  have hproj_p :=
    congrArg
      (fun kmap : ((⟪L, M⟫).X t ⊗ K.X r) ⟶
          (ihom ((⟪K, L⟫).X p)).obj (M.X (t + r + p)) ↦
        ModuleCat.Hom.hom (kmap.hom (TensorProduct.tmul R g k)) φ)
      (tensor_internal_hom_to_iterated_internal_hom_f_ι_pi K L M t r (t + r) p rfl)
  rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K L M t r (t + r) p rfl
      g k φ] at hproj_p
  have hproj_succ :=
    congrArg
      (fun kmap : ((⟪L, M⟫).X t ⊗ K.X r) ⟶
          (ihom ((⟪K, L⟫).X (p + 1))).obj (M.X (t + r + (p + 1))) ↦
        ModuleCat.Hom.hom (kmap.hom (TensorProduct.tmul R g k))
          (((⟪K, L⟫).d p (p + 1)).hom φ))
      (tensor_internal_hom_to_iterated_internal_hom_f_ι_pi K L M t r (t + r) (p + 1) rfl)
  rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K L M t r (t + r)
      (p + 1) rfl g k (((⟪K, L⟫).d p (p + 1)).hom φ)] at hproj_succ
  -- Expand the target differential in the outer internal-Hom complex.
  have hleft :=
    module_complex_internal_hom_d_piProj_apply K L M (t + r) (t + r + 1) p
      (by simpa using (show (ComplexShape.up ℤ).Rel (t + r) (t + r + 1) by simp))
      (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K t r (t + r) rfl ≫
          tensor_internal_hom_to_iterated_internal_hom_f K L M (t + r)).hom)
        (TensorProduct.tmul R g k))
      φ
  rw [hproj_p, hproj_succ] at hleft
  -- Expand the inner internal-Hom differential applied to `φ` and evaluated at `k`.
  have hφ :=
    module_complex_internal_hom_d_after_piProj_apply K L p (p + 1) r
      (by simpa using (show (ComplexShape.up ℤ).Rel p (p + 1) by simp))
      φ k
  -- Expand the source tensor differential on the same summand.
  have hright :=
    congrArg
      (fun kmap : ((⟪L, M⟫).X t ⊗ K.X r) ⟶
          (ihom ((⟪K, L⟫).X p)).obj (M.X (t + r + 1 + p)) ↦
        (ModuleCat.Hom.hom (kmap.hom (TensorProduct.tmul R g k))) φ)
      (by
        have hs :=
          congrArg
            (fun kmap :
              ((⟪L, M⟫).X t ⊗ K.X r) ⟶ (⟪L, M⟫ ⊗ K).X (t + r + 1) ↦
                kmap ≫ tensor_internal_hom_to_iterated_internal_hom_f K L M (t + r + 1) ≫
                  module_complex_internal_hom_piProj ⟪K, L⟫ M (t + r + 1) p)
            (tensor_internal_hom_to_iterated_internal_hom_source_d_on_summand K L M t r)
        simpa [Category.assoc, Preadditive.add_comp, smul_comp] using hs)
  rw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_smul, LinearMap.smul_apply] at hright
  simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_id, id_tensorHom,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hright
  rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K L M (t + 1) r
      (t + r + 1) p (tensor_internal_hom_to_iterated_internal_hom_left_succ_indexEq t r)
      (((⟪L, M⟫).d t (t + 1)).hom g) k φ,
    tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K L M t (r + 1)
      (t + r + 1) p (tensor_internal_hom_to_iterated_internal_hom_right_succ_indexEq t r)
      g (((K.d r (r + 1)).hom) k) φ] at hright
  -- Rewrite the source-horizontal term through the owner differential of `g`.
  have hg :=
    module_complex_internal_hom_d_after_piProj_apply L M t (t + 1) (p + r)
      (by simpa using (show (ComplexShape.up ℤ).Rel t (t + 1) by simp))
      g ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p r).hom φ)) k)
  -- Normalize the target differential using the inner Leibniz rule for `φ`, then compare the
  -- resulting three terms with the rewritten source differential using the two sign identities.
  rw [hφ] at hleft
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply, map_add, map_smul, smul_add, smul_smul,
    mul_assoc] at hleft
  have hg' := congrArg (fun y ↦ (r * p).negOnePow • y) hg
  simp only [smul_add, smul_smul, mul_assoc] at hg'
  calc
    (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K t r (t + r) rfl ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L M (t + r) ≫
            (⟪⟪K, L⟫, M⟫).d (t + r) (t + r + 1) ≫
            module_complex_internal_hom_piProj ⟪K, L⟫ M (t + r + 1) p).hom)
          (TensorProduct.tmul R g k))) φ
        =
      (r * p).negOnePow •
          ((ModuleCat.Hom.hom (M.d (t + (p + r)) (t + 1 + (p + r))))
              ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L M t (p + r)).hom g))
                ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p r).hom φ)) k))) +
            (t + 1).negOnePow •
              ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L M t (p + r + 1)).hom g))
                ((ModuleCat.Hom.hom (L.d (p + r) (p + r + 1)))
                  ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p r).hom φ)) k))))
        +
      (t.negOnePow * ((r + 1) * p).negOnePow) •
        ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L M t (p + (r + 1))).hom g))
          ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p (r + 1)).hom φ))
            (((K.d r (r + 1)).hom) k))) := by
          simpa [tensor_internal_hom_to_iterated_internal_hom_horizontal_sign t r p,
            tensor_internal_hom_to_iterated_internal_hom_vertical_sign t r p,
            add_assoc, add_left_comm, add_comm, mul_left_comm, mul_comm]
            using hleft
    _ =
      (r * p).negOnePow •
          (ModuleCat.Hom.hom
            ((module_complex_internal_hom_piProj L M (t + 1) (p + r)).hom
              (((⟪L, M⟫).d t (t + 1)).hom g)))
            ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p r).hom φ)) k) +
      (t.negOnePow * ((r + 1) * p).negOnePow) •
        ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L M t (p + (r + 1))).hom g))
          ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p (r + 1)).hom φ))
            (((K.d r (r + 1)).hom) k))) := by
          simpa [smul_add, add_assoc, add_left_comm, add_comm] using hg'
    _ =
      (ModuleCat.Hom.hom
          (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K t r (t + r) rfl ≫
              (⟪L, M⟫ ⊗ K).d (t + r) (t + r + 1) ≫
              tensor_internal_hom_to_iterated_internal_hom_f K L M (t + r + 1) ≫
              module_complex_internal_hom_piProj ⟪K, L⟫ M (t + r + 1) p).hom)
            (TensorProduct.tmul R g k))) φ := by
          simpa [smul_assoc, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
            add_comm] using hright.symm

/-- Helper for Lemma 15.72.6: after restricting to a tensor summand and a target factor, the
chain-map identity is the three-term sign comparison from the textbook proof. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_component_chain
    (K L M : CpxR) [HasTensor (⟪L, M⟫) K]
    (i j t r p : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (h : t + r = i) :
    HomologicalComplex.ιTensorObj (⟪L, M⟫) K t r i h ≫
        tensor_internal_hom_to_iterated_internal_hom_f K L M i ≫
        (⟪⟪K, L⟫, M⟫).d i j ≫
        (module_complex_internal_hom_piIso ⟪K, L⟫ M j).inv ≫
        Pi.π (fun q : ℤ ↦ (ihom ((⟪K, L⟫).X q)).obj (M.X (j + q))) p =
      HomologicalComplex.ιTensorObj (⟪L, M⟫) K t r i h ≫
        (⟪L, M⟫ ⊗ K).d i j ≫
        tensor_internal_hom_to_iterated_internal_hom_f K L M j ≫
        (module_complex_internal_hom_piIso ⟪K, L⟫ M j).inv ≫
        Pi.π (fun q : ℤ ↦ (ihom ((⟪K, L⟫).X q)).obj (M.X (j + q))) p := by
  -- Route correction: after the source-faithful component sign `(-1)^(rp)` is inserted, the
  -- remaining chain-map check is exactly the pointwise Leibniz identity on pure tensors.
  subst i
  have hij' : j = t + r + 1 := by
    simpa using hij
  subst j
  simp only [module_complex_internal_hom_piIso, module_complex_internal_hom_piProj, Category.assoc]
  apply ModuleCat.hom_ext
  refine TensorProduct.ext ?_
  intro g k
  ext φ
  simpa [Category.assoc] using
    tensor_internal_hom_to_iterated_internal_hom_pointwise_leibniz K L M t r p g k φ

-- Proof sketch: project both sides to a tensor summand in total degree `i` and then to a factor
-- of the target product. The source differential splits into the tensor differential on
-- `⟪L, M⟫ ⊗ K`, while the target differential is the internal-Hom differential on
-- `⟪⟪K, L⟫, M⟫`; the component identities are exactly the sign computations isolated in the
-- local auxiliary development.
/-- The degreewise tensor-to-iterated-internal-Hom maps commute with the differentials. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_f_comm
    (K L M : CpxR) [HasTensor (⟪L, M⟫) K] (i j : ℤ) (hij : (up ℤ).Rel i j) :
    tensor_internal_hom_to_iterated_internal_hom_f K L M i ≫
      (⟪⟪K, L⟫, M⟫).d i j =
        (⟪L, M⟫ ⊗ K).d i j ≫
          tensor_internal_hom_to_iterated_internal_hom_f K L M j := by
  -- Compare both candidate morphisms after transporting the target to its canonical product
  -- decomposition in degree `j`.
  apply (cancel_mono (module_complex_internal_hom_piIso ⟪K, L⟫ M j).inv).1
  apply Pi.hom_ext
  intro p
  -- Restrict further to each tensor summand in source degree `i`.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro t r h
  simpa [Category.assoc] using
    tensor_internal_hom_to_iterated_internal_hom_component_chain K L M i j t r p hij h

section

variable [∀ K L : CochainComplex (ModuleCat R) ℤ, HasTensor K L]

/-- Lemma 15.72.6: there is a canonical morphism from the total tensor complex
`Tot(⟪L, M⟫ ⊗ K)` to the iterated internal-Hom complex `⟪⟪K, L⟫, M⟫`. -/
noncomputable def tensor_internal_hom_to_iterated_internal_hom
    (K L M : CpxR) :
    (⟪L, M⟫ ⊗ K) ⟶ ⟪⟪K, L⟫, M⟫ :=
  { f := tensor_internal_hom_to_iterated_internal_hom_f K L M
    comm' := tensor_internal_hom_to_iterated_internal_hom_f_comm K L M }

/-- Helper for Lemma 15.72.6: on a fixed `(t,r)` tensor summand, the source map for
`K`-naturality is just `𝟙 ⊗ α.f r`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_natural_K_source_summand
    {K₁ K₂ L M : CpxR} (α : K₁ ⟶ K₂)
    (t r n : ℤ) (h : t + r = n) :
    HomologicalComplex.ιTensorObj (⟪L, M⟫) K₁ t r n h ≫
        (tensorHom (𝟙 (⟪L, M⟫)) α).f n =
      ((𝟙 ((⟪L, M⟫).X t)) ⊗ₘ α.f r) ≫
        HomologicalComplex.ιTensorObj (⟪L, M⟫) K₂ t r n h := by
  -- This is the owner summand formula for the fixed-left tensor functor.
  simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom, HomologicalComplex.id_f,
    Category.assoc] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := ⟪L, M⟫) (K₂ := K₁) (L₁ := ⟪L, M⟫) (L₂ := K₂)
      (f₁ := 𝟙 (⟪L, M⟫)) (f₂ := α)
      (F := MonoidalCategory.curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) t r n h)

/-- Helper for Lemma 15.72.6: after restricting the `K`-naturality square to one tensor summand,
projecting to the `p`-th target factor, and evaluating on a pure tensor and a target cochain, the
two routes both become the same nested evaluation `g (φ (α(k)))`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_natural_K_pointwise
    {K₁ K₂ L M : CpxR} (α : K₁ ⟶ K₂)
    (t r n p : ℤ) (h : t + r = n)
    (g : (⟪L, M⟫).X t) (k : K₁.X r) (φ : (⟪K₂, L⟫).X p) :
    (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K₁ t r n h ≫
            (tensorHom (𝟙 (⟪L, M⟫)) α).f n ≫
            tensor_internal_hom_to_iterated_internal_hom_f K₂ L M n ≫
            module_complex_internal_hom_piProj ⟪K₂, L⟫ M n p).hom)
          (TensorProduct.tmul R g k))) φ =
      (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K₁ t r n h ≫
            tensor_internal_hom_to_iterated_internal_hom_f K₁ L M n ≫
            ((module_complex_internal_homMap (module_complex_internal_homMap α (𝟙 L))
              (𝟙 M)).f n) ≫
            module_complex_internal_hom_piProj ⟪K₂, L⟫ M n p).hom)
          (TensorProduct.tmul R g k))) φ := by
  subst n
  -- Normalize the left route by rewriting the fixed tensor summand through `𝟙 ⊗ α`.
  have hleft :
      (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K₁ t r (t + r) rfl ≫
            (tensorHom (𝟙 (⟪L, M⟫)) α).f (t + r) ≫
            tensor_internal_hom_to_iterated_internal_hom_f K₂ L M (t + r) ≫
            module_complex_internal_hom_piProj ⟪K₂, L⟫ M (t + r) p).hom)
          (TensorProduct.tmul R g k))) φ =
        (r * p).negOnePow •
          (ModuleCat.Hom.hom
              (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
                (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                  (n := t + r) rfl))))
            ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L M t (p + r)).hom g))
              ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K₂ L p r).hom φ))
                ((α.f r).hom k))) := by
    rw [Category.assoc, tensor_internal_hom_to_iterated_internal_hom_natural_K_source_summand,
      Category.assoc, tensor_internal_hom_to_iterated_internal_hom_f_ι_pi]
    simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_id, id_tensorHom,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K₂ L M t r (t + r) p
      rfl g ((α.f r).hom k) φ]
  -- Projecting the outer internal-Hom map sends `φ` to its image under
  -- `module_complex_internal_homMap α (𝟙 L)`.
  have hright :
      (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K₁ t r (t + r) rfl ≫
            tensor_internal_hom_to_iterated_internal_hom_f K₁ L M (t + r) ≫
            ((module_complex_internal_homMap (module_complex_internal_homMap α (𝟙 L))
              (𝟙 M)).f (t + r)) ≫
            module_complex_internal_hom_piProj ⟪K₂, L⟫ M (t + r) p).hom)
          (TensorProduct.tmul R g k))) φ =
        (ModuleCat.Hom.hom
          (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K₁ t r (t + r) rfl ≫
              tensor_internal_hom_to_iterated_internal_hom_f K₁ L M (t + r) ≫
              module_complex_internal_hom_piProj ⟪K₁, L⟫ M (t + r) p).hom)
            (TensorProduct.tmul R g k)))
          (((module_complex_internal_homMap α (𝟙 L)).f p).hom φ) := by
    rw [Category.assoc, Category.assoc]
    simpa [Category.assoc] using
      module_complex_internal_homMap_piProj_apply
        (module_complex_internal_homMap α (𝟙 L)) (𝟙 M) (t + r) p
        (((HomologicalComplex.ιTensorObj (⟪L, M⟫) K₁ t r (t + r) rfl ≫
            tensor_internal_hom_to_iterated_internal_hom_f K₁ L M (t + r)).hom)
          (TensorProduct.tmul R g k)) φ
  rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K₁ L M t r (t + r) p
      rfl g k (((module_complex_internal_homMap α (𝟙 L)).f p).hom φ)] at hright
  -- Both normalized routes now differ only by the explicit formula for the inner-Hom map in `K`.
  rw [hleft, hright]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  simpa [tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r) (n := t + r)
      rfl, add_assoc, add_left_comm, add_comm] using
    congrArg
      (fun y : L.X (p + r) ↦
        (r * p).negOnePow •
          (ModuleCat.Hom.hom
              (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
                (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                  (n := t + r) rfl))))
            ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L M t (p + r)).hom g))
              y))
      (module_complex_internal_homMap_piProj_apply α (𝟙 L) p r φ k)

/-- The comparison morphism of Lemma 15.72.6 is functorial in `K`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_natural_K
    {K₁ K₂ L M : CpxR} (α : K₁ ⟶ K₂) :
    CommSq
      (tensorHom (𝟙 (⟪L, M⟫)) α)
      (tensor_internal_hom_to_iterated_internal_hom K₁ L M)
      (tensor_internal_hom_to_iterated_internal_hom K₂ L M)
      (module_complex_internal_homMap (module_complex_internal_homMap α (𝟙 L)) (𝟙 M)) := by
  -- Project to a fixed tensor summand and a fixed target factor, where both routes reduce to the
  -- same nested evaluation formula from the textbook component maps `c_{p,q,r}`.
  refine CommSq.mk ?_
  apply HomologicalComplex.hom_ext
  intro n
  apply (cancel_mono (module_complex_internal_hom_piIso ⟪K₂, L⟫ M n).inv).1
  apply Pi.hom_ext
  intro p
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro t r h
  apply ModuleCat.hom_ext
  refine TensorProduct.ext ?_
  intro g k
  ext φ
  simpa [Category.assoc] using
    tensor_internal_hom_to_iterated_internal_hom_natural_K_pointwise α t r n p h g k φ

/-- Helper for Lemma 15.72.6: on a fixed `(t,r)` tensor summand, the source map for
`L`-naturality is just `((module_complex_internal_homMap β (𝟙 M)).f t) ⊗ 𝟙`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_natural_L_source_summand
    (K : CpxR) {L₁ L₂ M : CpxR} (β : L₁ ⟶ L₂)
    (t r n : ℤ) (h : t + r = n) :
    HomologicalComplex.ιTensorObj (⟪L₂, M⟫) K t r n h ≫
        (tensorHom (module_complex_internal_homMap β (𝟙 M)) (𝟙 K)).f n =
      (((module_complex_internal_homMap β (𝟙 M)).f t) ⊗ₘ 𝟙 (K.X r)) ≫
        HomologicalComplex.ιTensorObj (⟪L₁, M⟫) K t r n h := by
  -- This is the owner summand formula for the fixed-right tensor functor.
  simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom, HomologicalComplex.id_f,
    Category.assoc] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := ⟪L₂, M⟫) (K₂ := K) (L₁ := ⟪L₁, M⟫) (L₂ := K)
      (f₁ := module_complex_internal_homMap β (𝟙 M)) (f₂ := 𝟙 K)
      (F := MonoidalCategory.curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) t r n h)

/-- Helper for Lemma 15.72.6: after restricting the `L`-naturality square to one tensor summand,
projecting to the `p`-th target factor, and evaluating on a pure tensor and a target cochain, the
two routes both become the same nested evaluation `g (β (φ(k)))`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_natural_L_pointwise
    (K : CpxR) {L₁ L₂ M : CpxR} (β : L₁ ⟶ L₂)
    (t r n p : ℤ) (h : t + r = n)
    (g : (⟪L₂, M⟫).X t) (k : K.X r) (φ : (⟪K, L₁⟫).X p) :
    (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L₂, M⟫) K t r n h ≫
            (tensorHom (module_complex_internal_homMap β (𝟙 M)) (𝟙 K)).f n ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L₁ M n ≫
            module_complex_internal_hom_piProj ⟪K, L₁⟫ M n p).hom)
          (TensorProduct.tmul R g k))) φ =
      (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L₂, M⟫) K t r n h ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L₂ M n ≫
            ((module_complex_internal_homMap (module_complex_internal_homMap (𝟙 K) β)
              (𝟙 M)).f n) ≫
            module_complex_internal_hom_piProj ⟪K, L₁⟫ M n p).hom)
          (TensorProduct.tmul R g k))) φ := by
  subst n
  -- Normalize the left route by rewriting the fixed tensor summand through
  -- `(module_complex_internal_homMap β (𝟙 M)) ⊗ 𝟙`.
  have hleft :
      (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L₂, M⟫) K t r (t + r) rfl ≫
            (tensorHom (module_complex_internal_homMap β (𝟙 M)) (𝟙 K)).f (t + r) ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L₁ M (t + r) ≫
            module_complex_internal_hom_piProj ⟪K, L₁⟫ M (t + r) p).hom)
          (TensorProduct.tmul R g k))) φ =
        (r * p).negOnePow •
          (ModuleCat.Hom.hom
              (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
                (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                  (n := t + r) rfl))))
            ((ModuleCat.Hom.hom
                ((module_complex_internal_hom_piProj L₁ M t (p + r)).hom
                  (((module_complex_internal_homMap β (𝟙 M)).f t).hom g)))
              ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L₁ p r).hom φ)) k)) := by
    rw [Category.assoc, tensor_internal_hom_to_iterated_internal_hom_natural_L_source_summand,
      Category.assoc, tensor_internal_hom_to_iterated_internal_hom_f_ι_pi]
    simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_id, id_tensorHom,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K L₁ M t r (t + r) p
      rfl (((module_complex_internal_homMap β (𝟙 M)).f t).hom g) k φ]
  -- Projecting the outer internal-Hom map sends `φ` to its image under
  -- `module_complex_internal_homMap (𝟙 K) β`.
  have hright :
      (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L₂, M⟫) K t r (t + r) rfl ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L₂ M (t + r) ≫
            ((module_complex_internal_homMap (module_complex_internal_homMap (𝟙 K) β)
              (𝟙 M)).f (t + r)) ≫
            module_complex_internal_hom_piProj ⟪K, L₁⟫ M (t + r) p).hom)
          (TensorProduct.tmul R g k))) φ =
        (ModuleCat.Hom.hom
          (((HomologicalComplex.ιTensorObj (⟪L₂, M⟫) K t r (t + r) rfl ≫
              tensor_internal_hom_to_iterated_internal_hom_f K L₂ M (t + r) ≫
              module_complex_internal_hom_piProj ⟪K, L₂⟫ M (t + r) p).hom)
            (TensorProduct.tmul R g k)))
          (((module_complex_internal_homMap (𝟙 K) β).f p).hom φ) := by
    rw [Category.assoc, Category.assoc]
    simpa [Category.assoc] using
      module_complex_internal_homMap_piProj_apply
        (module_complex_internal_homMap (𝟙 K) β) (𝟙 M) (t + r) p
        (((HomologicalComplex.ιTensorObj (⟪L₂, M⟫) K t r (t + r) rfl ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L₂ M (t + r)).hom)
          (TensorProduct.tmul R g k)) φ
  rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K L₂ M t r (t + r) p
      rfl g k (((module_complex_internal_homMap (𝟙 K) β).f p).hom φ)] at hright
  -- First move `β` through the source cochain `g`, then move it through the target cochain `φ`.
  rw [hleft, hright]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  calc
    (r * p).negOnePow •
        (ModuleCat.Hom.hom
            (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
              (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                (n := t + r) rfl))))
          ((ModuleCat.Hom.hom
              ((module_complex_internal_hom_piProj L₁ M t (p + r)).hom
                (((module_complex_internal_homMap β (𝟙 M)).f t).hom g)))
            ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L₁ p r).hom φ)) k))
        =
      (r * p).negOnePow •
        (ModuleCat.Hom.hom
            (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
              (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                (n := t + r) rfl))))
          ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L₂ M t (p + r)).hom g))
            ((ModuleCat.Hom.hom (β.f (p + r)))
              ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L₁ p r).hom φ)) k))) := by
          simpa [tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
              (n := t + r) rfl, add_assoc, add_left_comm, add_comm] using
            congrArg
              (fun y : M.X (t + (p + r)) ↦
                (r * p).negOnePow •
                  (ModuleCat.Hom.hom
                      (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
                        (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                          (n := t + r) rfl))))
                    y)
              (module_complex_internal_homMap_piProj_apply β (𝟙 M) t (p + r) g
                ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L₁ p r).hom φ)) k))
    _ =
      (r * p).negOnePow •
        (ModuleCat.Hom.hom
            (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
              (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                (n := t + r) rfl))))
          ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L₂ M t (p + r)).hom g))
            ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L₂ p r).hom
                (((module_complex_internal_homMap (𝟙 K) β).f p).hom φ))) k)) := by
          simpa [tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
              (n := t + r) rfl, add_assoc, add_left_comm, add_comm] using
            congrArg
              (fun y : L₂.X (p + r) ↦
                (r * p).negOnePow •
                  (ModuleCat.Hom.hom
                      (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
                        (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                          (n := t + r) rfl))))
                    ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L₂ M t (p + r)).hom
                        g)) y))
              (module_complex_internal_homMap_piProj_apply (𝟙 K) β p r φ k).symm

/-- The comparison morphism of Lemma 15.72.6 is functorial in `L`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_natural_L
    (K : CpxR) {L₁ L₂ M : CpxR} (β : L₁ ⟶ L₂) :
    CommSq
      (tensorHom (module_complex_internal_homMap β (𝟙 M)) (𝟙 K))
      (tensor_internal_hom_to_iterated_internal_hom K L₂ M)
      (tensor_internal_hom_to_iterated_internal_hom K L₁ M)
      (module_complex_internal_homMap (module_complex_internal_homMap (𝟙 K) β) (𝟙 M)) := by
  -- Project to a fixed tensor summand and a fixed target factor, where both routes reduce to the
  -- same nested evaluation formula from the textbook component maps `c_{p,q,r}`.
  refine CommSq.mk ?_
  apply HomologicalComplex.hom_ext
  intro n
  apply (cancel_mono (module_complex_internal_hom_piIso ⟪K, L₁⟫ M n).inv).1
  apply Pi.hom_ext
  intro p
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro t r h
  apply ModuleCat.hom_ext
  refine TensorProduct.ext ?_
  intro g k
  ext φ
  simpa [Category.assoc] using
    tensor_internal_hom_to_iterated_internal_hom_natural_L_pointwise K β t r n p h g k φ

/-- Helper for Lemma 15.72.6: after restricting the `M`-naturality square to one tensor summand,
projecting to the `p`-th target factor, and evaluating on a pure tensor and a target cochain, the
two routes both become postcomposition by `γ`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_natural_M_pointwise
    (K L : CpxR) {M₁ M₂ : CpxR} (γ : M₁ ⟶ M₂)
    (t r n p : ℤ) (h : t + r = n)
    (g : (⟪L, M₁⟫).X t) (k : K.X r) (φ : (⟪K, L⟫).X p) :
    (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M₁⟫) K t r n h ≫
            (tensorHom (module_complex_internal_homMap (𝟙 L) γ) (𝟙 K)).f n ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L M₂ n ≫
            module_complex_internal_hom_piProj ⟪K, L⟫ M₂ n p).hom)
          (TensorProduct.tmul R g k))) φ =
      (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M₁⟫) K t r n h ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L M₁ n ≫
            ((module_complex_internal_homMap (𝟙 ⟪K, L⟫) γ).f n) ≫
            module_complex_internal_hom_piProj ⟪K, L⟫ M₂ n p).hom)
          (TensorProduct.tmul R g k))) φ := by
  subst n
  -- Rewrite the source tensor map on the fixed `(t,r)` summand.
  have hsource :
      HomologicalComplex.ιTensorObj (⟪L, M₁⟫) K t r (t + r) rfl ≫
          (tensorHom (module_complex_internal_homMap (𝟙 L) γ) (𝟙 K)).f (t + r) =
        (((module_complex_internal_homMap (𝟙 L) γ).f t) ⊗ₘ 𝟙 (K.X r)) ≫
          HomologicalComplex.ιTensorObj (⟪L, M₂⟫) K t r (t + r) rfl := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom, HomologicalComplex.id_f,
      Category.assoc] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := ⟪L, M₁⟫) (K₂ := K) (L₁ := ⟪L, M₂⟫) (L₂ := K)
        (f₁ := module_complex_internal_homMap (𝟙 L) γ) (f₂ := 𝟙 K)
        (F := MonoidalCategory.curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) t r (t + r) rfl)
  -- Normalize the left route to the explicit component formula with the source cochain replaced by
  -- its image under `module_complex_internal_homMap (𝟙 L) γ`.
  have hleft :
      (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M₁⟫) K t r (t + r) rfl ≫
            (tensorHom (module_complex_internal_homMap (𝟙 L) γ) (𝟙 K)).f (t + r) ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L M₂ (t + r) ≫
            module_complex_internal_hom_piProj ⟪K, L⟫ M₂ (t + r) p).hom)
          (TensorProduct.tmul R g k))) φ =
        (r * p).negOnePow •
          (ModuleCat.Hom.hom
              (eqToHom (congrArg (fun z : ℤ ↦ M₂.X z)
                (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                  (n := t + r) rfl))))
            ((ModuleCat.Hom.hom
                ((module_complex_internal_hom_piProj L M₂ t (p + r)).hom
                  (((module_complex_internal_homMap (𝟙 L) γ).f t).hom g)))
              ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p r).hom φ)) k)) := by
    rw [Category.assoc, hsource, Category.assoc,
      tensor_internal_hom_to_iterated_internal_hom_f_ι_pi]
    simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_id, id_tensorHom,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K L M₂ t r (t + r) p
      rfl (((module_complex_internal_homMap (𝟙 L) γ).f t).hom g) k φ]
  -- Projecting the outer internal-Hom map identifies the right route with postcomposition by `γ`.
  have hright :
      (ModuleCat.Hom.hom
        (((HomologicalComplex.ιTensorObj (⟪L, M₁⟫) K t r (t + r) rfl ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L M₁ (t + r) ≫
            ((module_complex_internal_homMap (𝟙 ⟪K, L⟫) γ).f (t + r)) ≫
            module_complex_internal_hom_piProj ⟪K, L⟫ M₂ (t + r) p).hom)
          (TensorProduct.tmul R g k))) φ =
        (ModuleCat.Hom.hom (γ.f (t + r + p)))
          ((ModuleCat.Hom.hom
              (((HomologicalComplex.ιTensorObj (⟪L, M₁⟫) K t r (t + r) rfl ≫
                  tensor_internal_hom_to_iterated_internal_hom_f K L M₁ (t + r) ≫
                  module_complex_internal_hom_piProj ⟪K, L⟫ M₁ (t + r) p).hom)
                (TensorProduct.tmul R g k))) φ) := by
    rw [Category.assoc, Category.assoc]
    simpa [Category.assoc] using
      module_complex_internal_homMap_piProj_apply (𝟙 ⟪K, L⟫) γ (t + r) p
        (((HomologicalComplex.ιTensorObj (⟪L, M₁⟫) K t r (t + r) rfl ≫
            tensor_internal_hom_to_iterated_internal_hom_f K L M₁ (t + r)).hom)
          (TensorProduct.tmul R g k)) φ
  rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul K L M₁ t r (t + r) p
      rfl g k φ] at hright
  -- Compare the two normalized expressions using functoriality of the inner `L → M` component.
  rw [hleft, hright]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  simpa [tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r) (n := t + r)
      rfl, add_assoc, add_left_comm, add_comm] using
    congrArg
      (fun y : M₁.X (t + (p + r)) ↦
        (r * p).negOnePow •
          (ModuleCat.Hom.hom
              (eqToHom (congrArg (fun z : ℤ ↦ M₂.X z)
                (tensor_internal_hom_to_iterated_internal_hom_indexEq (t := t) (r := r)
                  (n := t + r) rfl))))
            ((ModuleCat.Hom.hom (γ.f (t + (p + r)))) y))
      (module_complex_internal_homMap_piProj_apply (𝟙 L) γ t (p + r) g
        ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p r).hom φ)) k))

/-- The comparison morphism of Lemma 15.72.6 is functorial in `M`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_natural_M
    (K L : CpxR) {M₁ M₂ : CpxR} (γ : M₁ ⟶ M₂) :
    CommSq
      (tensorHom (module_complex_internal_homMap (𝟙 L) γ) (𝟙 K))
      (tensor_internal_hom_to_iterated_internal_hom K L M₁)
      (tensor_internal_hom_to_iterated_internal_hom K L M₂)
      (module_complex_internal_homMap (𝟙 ⟪K, L⟫) γ) := by
  -- Project to a fixed tensor summand and a fixed target factor, where both routes reduce to the
  -- same postcomposition-by-`γ` formula from the textbook component maps `c_{p,q,r}`.
  refine CommSq.mk ?_
  apply HomologicalComplex.hom_ext
  intro n
  apply (cancel_mono (module_complex_internal_hom_piIso ⟪K, L⟫ M₂ n).inv).1
  apply Pi.hom_ext
  intro p
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro t r h
  apply ModuleCat.hom_ext
  refine TensorProduct.ext ?_
  intro g k
  ext φ
  simpa [Category.assoc] using
    tensor_internal_hom_to_iterated_internal_hom_natural_M_pointwise K L γ t r n p h g k φ

end

end
