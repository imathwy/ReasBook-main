import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open ComplexShape
open HomologicalComplex
open MonoidalCategory
open MonoidalClosed

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for 15.72.1:
- primary domain: cochain Hom complexes in `ModuleCat R`, viewed as a concrete module-valued bridge
  for the chapter's later tensor/internal-Hom statements;
- sampled owner declarations:
  `CochainComplex.HomComplex`,
  `CochainComplex.HomComplex.Cochain`,
  `CochainComplex.HomComplex.δ_hom`,
  `ModuleCat.piIsoPi`;
- best owner abstraction: the primitive cochain and differential data are already owned by
  `CochainComplex.HomComplex`, while the only chapter-specific bridge still needed downstream is
  the `ModuleCat`-valued realization together with its canonical degreewise product
  decomposition;
- primitive data vs. derived API: the primitive owner data are the cochains and differential from
  `CochainComplex.HomComplex`; the `ModuleCat` realization, its degree-`n` product isomorphism,
  and the single bifunctorial owner map below are derived bridge API. The previous chapter-local
  separate precomposition/postcomposition wrapper layer duplicated later owner abstractions and has
  been removed in favor of this one owner-level bridge;
- source/core/bridge triage:
  `source-facing`: the module-valued internal-Hom complex used throughout the local `15.72` family;
  `core/canonical`: `CochainComplex.HomComplex` and `ModuleCat.piIsoPi`;
  `bridge/view`: the `ModuleCat` realization, its product decomposition in each degree, and the
    owner bifunctorial map `module_complex_internal_homMap`.
-/

/-- The `ModuleCat`-valued realization of the canonical Hom complex on cochain complexes of
`R`-modules. Its degree-`n` term is the module of `n`-cochains from `K` to `L`. -/
noncomputable def module_complex_internal_hom
    (K L : CochainComplex (ModuleCat R) ℤ) : CochainComplex (ModuleCat R) ℤ where
  X n := ModuleCat.of R (Cochain K L n)
  d i j := ModuleCat.ofHom (δ_hom R K L i j)
  shape i j hij := by
    ext z p q hpq x
    simpa using LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (Cochain.congr_v (δ_shape i j hij z) p q hpq)) x
  d_comp_d' i j k hij hjk := by
    ext z p q hpq x
    simpa using LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (Cochain.congr_v (δ_δ i j k z) p q hpq)) x

namespace ModuleComplexInternalHom

/- Textbook surface notation for the module-valued internal-Hom complex from `K^•` to `L^•`. -/
scoped notation "⟪" K ", " L "⟫" => module_complex_internal_hom K L

end ModuleComplexInternalHom

open scoped ModuleComplexInternalHom

private def cochainFamilyLinearEquiv
    (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (∀ p : ℤ, (ihom (K.X p)).obj (L.X (n + p))) ≃ₗ[R] Cochain K L n where
  toFun f :=
    Cochain.mk fun p q hpq ↦
      f p ≫ eqToHom (congrArg (fun z : ℤ ↦ L.X z) (by simpa [add_comm] using hpq))
  invFun z p := z.v p (n + p) (by abel)
  left_inv f := by
    funext p
    ext x
    simp [Cochain.mk_v]
  right_inv z := by
    ext p q hpq x
    have h' : n + p = q := by
      simpa [add_comm] using hpq
    subst h'
    simp [Cochain.mk_v]
  map_add' f g := by
    ext p q hpq x
    simp only [Pi.add_apply, Cochain.mk_v, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply, Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply]
    exact (ModuleCat.Hom.hom
      (eqToHom (congrArg (fun z : ℤ ↦ L.X z) (by simpa [add_comm] using hpq)))).map_add _ _
  map_smul' a f := by
    ext p q hpq x
    simp only [Pi.smul_apply, Cochain.mk_v, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply, RingHom.id_apply, Cochain.smul_v, ModuleCat.hom_smul,
      LinearMap.smul_apply]
    exact (ModuleCat.Hom.hom
      (eqToHom (congrArg (fun z : ℤ ↦ L.X z) (by simpa [add_comm] using hpq)))).map_smul _ _

/-- Helper for Lemma 15.72.1: evaluating the cochain built from a degreewise family at the
matching `q`-component recovers that original family component. -/
private theorem cochainFamilyLinearEquiv_apply_v
    (K L : CpxR) (n q : ℤ)
    (f : ∀ p : ℤ, (ihom (K.X p)).obj (L.X (n + p))) :
    ((cochainFamilyLinearEquiv K L n) f).v q (n + q) (by abel) = f q := by
  simp [cochainFamilyLinearEquiv, Cochain.mk_v]

/-- Helper for Lemma 15.72.1: the inverse family map reads off the `q`-component of a cochain. -/
private theorem cochainFamilyLinearEquiv_symm_apply
    (K L : CpxR) (n q : ℤ) (z : Cochain K L n) :
    (cochainFamilyLinearEquiv K L n).symm z q = z.v q (n + q) (by abel) := by
  rfl

/-- The degree-`n` term of `module_complex_internal_hom K L` is canonically the product of the
degreewise internal-Hom objects `Hom_R(K^p, L^{p + n})`. -/
noncomputable def module_complex_internal_hom_piIso
    (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ∏ᶜ (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p))) ≅ (⟪K, L⟫).X n := by
  let Z : ℤ → ModuleCat R := fun p ↦ ModuleCat.of R (K.X p ⟶ L.X (n + p))
  change ∏ᶜ Z ≅ ModuleCat.of R (Cochain K L n)
  exact
    (ModuleCat.piIsoPi Z).trans (cochainFamilyLinearEquiv K L n).toModuleIso

/-- Projection to the `p`-th degreewise internal-Hom factor in `(⟪K, L⟫).X n`, obtained from the
canonical product decomposition `module_complex_internal_hom_piIso`. -/
noncomputable abbrev module_complex_internal_hom_piProj
    (K L : CochainComplex (ModuleCat R) ℤ) (n p : ℤ) :
    (⟪K, L⟫).X n ⟶ (ihom (K.X p)).obj (L.X (n + p)) :=
  (cochainFamilyLinearEquiv K L n).symm.toModuleIso.hom ≫
    ModuleCat.ofHom (LinearMap.proj p)

/- The chapter internal-Hom complex is bifunctorial: a morphism `fK : K₂ ⟶ K₁` acts
contravariantly on the source complex, while a morphism `fL : L₁ ⟶ L₂` acts covariantly on the
target complex. This is the single owner-side bridge from the concrete cochain presentation to the
usual functoriality of internal Hom. -/
/-- Helper for Lemma 15.72.1: the underlying degree-`n` linear map of
`module_complex_internal_homMap fK fL`. -/
private noncomputable def module_complex_internal_homMapCochainMap
    {K₁ K₂ L₁ L₂ : CpxR}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) (n : ℤ) :
    Cochain K₁ L₁ n →ₗ[R] Cochain K₂ L₂ n :=
  { toFun := fun z ↦
      ((Cochain.ofHom fK).comp z (zero_add n)).comp (Cochain.ofHom fL) (add_zero n)
    map_add' := fun z₁ z₂ ↦ by
      simp [Cochain.add_comp, Cochain.comp_add]
    map_smul' := fun a z ↦ by
      simp [Cochain.smul_comp, Cochain.comp_smul] }

/-- Helper for Lemma 15.72.1: precomposition by `fK` and postcomposition by `fL` commute with the
Hom-complex differential. -/
private theorem module_complex_internal_homMap_comm
    {K₁ K₂ L₁ L₂ : CpxR}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂)
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ModuleCat.ofHom (module_complex_internal_homMapCochainMap (R := R) fK fL i) ≫
      ModuleCat.ofHom (δ_hom R K₂ L₂ i j) =
    ModuleCat.ofHom (δ_hom R K₁ L₁ i j) ≫
      ModuleCat.ofHom (module_complex_internal_homMapCochainMap (R := R) fK fL j) := by
  -- Rewrite the differential on the nested composition by the owner formulas for `δ`.
  ext z p q hpq x
  change (((δ i j (((Cochain.ofHom fK).comp z (zero_add i)).comp (Cochain.ofHom fL) (add_zero i))).v
      p q hpq) : _) x =
    ((((Cochain.ofHom fK).comp (δ i j z) (zero_add j)).comp (Cochain.ofHom fL) (add_zero j)).v
      p q hpq : _) x
  have hz₁ := δ_comp_zero_cochain
    (((Cochain.ofHom fK).comp z (zero_add i)))
    (Cochain.ofHom fL)
    j
    hij
  have hz₂ := δ_zero_cochain_comp
    (Cochain.ofHom fK)
    z
    j
    hij
  simp only [δ_ofHom, Cochain.comp_zero, Cochain.zero_comp, zero_add] at hz₁ hz₂
  rw [smul_zero, add_zero] at hz₂
  rw [hz₁, hz₂]

noncomputable def module_complex_internal_homMap
    {K₁ K₂ L₁ L₂ : CochainComplex (ModuleCat R) ℤ}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    ⟪K₁, L₁⟫ ⟶ ⟪K₂, L₂⟫ :=
  { f := fun n ↦ ModuleCat.ofHom
      (module_complex_internal_homMapCochainMap (R := R) fK fL n)
    comm' := by
      -- The chain-map condition is exactly the owner-level `δ`-compatibility above.
      intro i j hij
      simpa using module_complex_internal_homMap_comm (R := R) fK fL i j hij }

section Currying

/-- Helper for Lemma 15.72.1: the `(p,q)`-summand object in total degree `p + q` of the tensor
product complex `tensorObj K L`. -/
private abbrev tensorDegreeSummand
    (K L : CpxR) (p q : ℤ) : ModuleCat R :=
  ((curriedTensor (ModuleCat R)).obj (K.X p)).obj (L.X q)

/-- Helper for Lemma 15.72.1: maps out of a fixed total tensor degree are determined by their
restrictions to the `(p,q)`-summands with `p + q = r`. This is the coproduct-side bridge that
matches the owner API `tensorObjDesc`/`ιTensorObj`. -/
private noncomputable def tensorDegreeDescLinearEquiv
    (K L : CpxR) [HomologicalComplex.HasTensor K L] (r : ℤ) (N : ModuleCat R) :
    (((HomologicalComplex.tensorObj K L).X r) ⟶ N) ≃ₗ[R]
      (∀ s : {pq : ℤ × ℤ // pq.1 + pq.2 = r},
        tensorDegreeSummand K L s.1.1 s.1.2 ⟶ N) where
  toFun f s := HomologicalComplex.ιTensorObj K L s.1.1 s.1.2 r s.2 ≫ f
  invFun g := HomologicalComplex.mapBifunctorDesc fun p q h ↦ g ⟨(p, q), h⟩
  left_inv f := by
    -- Compare the two maps out of the tensor totalization on each summand separately.
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    simpa using
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R)) (c := up ℤ)
        (A := N) (j := r)
        (f := fun p q h ↦ HomologicalComplex.ιTensorObj K L p q r h ≫ f) p q h)
  right_inv g := by
    -- Restricting the descended map back to the indexed summand recovers the chosen component.
    funext s
    simpa using
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R)) (c := up ℤ)
        (A := N) (j := r)
        (f := fun p q h ↦ g ⟨(p, q), h⟩) s.1.1 s.1.2 s.2)
  map_add' f g := by
    funext s
    change HomologicalComplex.ιTensorObj K L s.1.1 s.1.2 r s.2 ≫ (f + g) =
      HomologicalComplex.ιTensorObj K L s.1.1 s.1.2 r s.2 ≫ f +
        HomologicalComplex.ιTensorObj K L s.1.1 s.1.2 r s.2 ≫ g
    rw [Preadditive.comp_add]
  map_smul' a f := by
    funext s
    change HomologicalComplex.ιTensorObj K L s.1.1 s.1.2 r s.2 ≫ (a • f) =
      a • (HomologicalComplex.ιTensorObj K L s.1.1 s.1.2 r s.2 ≫ f)
    simpa using
      (Linear.comp_smul
        (X := tensorDegreeSummand K L s.1.1 s.1.2)
        (Y := (HomologicalComplex.tensorObj K L).X r)
        (Z := N)
        (f := HomologicalComplex.ιTensorObj K L s.1.1 s.1.2 r s.2)
        (r := a) (g := f))

/-- Helper for Lemma 15.72.1: on the `(p,q)`-summand of the tensor totalization, the differential
splits into the horizontal differential plus `(-1)^p` times the vertical differential. -/
private theorem tensorObj_d_on_summand_eq_currying
    (K L : CpxR) [HomologicalComplex.HasTensor K L] (p q : ℤ) :
    HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
        (HomologicalComplex.tensorObj K L).d (p + q) (p + q + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
          HomologicalComplex.ιTensorObj K L (p + 1) q (p + q + 1) (by abel_nf) +
        p.negOnePow •
          ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
            HomologicalComplex.ιTensorObj K L p (q + 1) (p + q + 1) (by abel_nf)) := by
  -- Route correction: reuse the owner tensor-totalization Leibniz rule directly, rather than
  -- pushing this normalization through the unstable degree-family bridge first.
  change
    HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ) p q (p + q) rfl ≫
        (HomologicalComplex.mapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ)).d
          (p + q) (p + q + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
          HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ)
            (p + 1) q (p + q + 1)
            (by simpa using (show (p + 1) + q = p + q + 1 by abel_nf)) +
        p.negOnePow •
          ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
            HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ)
              p (q + 1) (p + q + 1)
              (by simpa using (show p + (q + 1) = p + q + 1 by abel_nf)))
  -- Rewrite the total differential into its horizontal and vertical parts on this summand.
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq K L (curriedTensor (ModuleCat R)) (up ℤ)
      (show (up ℤ).Rel p (p + 1) by simp) q (p + q + 1)
      (by simpa using (show (p + 1) + q = p + q + 1 by abel_nf)),
    HomologicalComplex.mapBifunctor.d₂_eq K L (curriedTensor (ModuleCat R)) (up ℤ) p
      (show (up ℤ).Rel q (q + 1) by simp) (p + q + 1)
      (by simpa using (show p + (q + 1) = p + q + 1 by abel_nf))]
  -- For cochain complexes on `ℤ`, the vertical sign is exactly `(-1)^p`.
  simp only [curriedTensor_obj_obj, ε₁_def, curriedTensor_map_app, ε₂_def,
    ComplexShape.ε_up_ℤ, curriedTensor_obj_map, tensorHom_id, id_tensorHom]
  let A :=
    K.d p (p + 1) ▷ L.X q ≫
      HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ)
        (p + 1) q (p + q + 1) (by simpa using (show (p + 1) + q = p + q + 1 by abel_nf))
  let B :=
    p.negOnePow •
      (K.X p ◁ L.d q (q + 1) ≫
        HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ)
          p (q + 1) (p + q + 1) (by simpa using (show p + (q + 1) = p + q + 1 by abel_nf)))
  change ((1 : ℤ) • A) + B = A + B
  have hA : (1 : ℤ) • A = A := by
    simp
  exact congrArg (fun t ↦ t + B) hA

/-- Helper for Lemma 15.72.1: the canonical projection to the `p`-th internal-Hom factor reads off
the `v`-component of a cochain in degree `n`. -/
private theorem module_complex_internal_hom_piProj_apply_eq_v
    (K L : CpxR) (n p : ℤ) (z : (⟪K, L⟫).X n) :
    (module_complex_internal_hom_piProj K L n p).hom z = z.v p (n + p) (by abel) := by
  -- The projection was defined by unfolding the degreewise product decomposition, so its action is
  -- exactly the stored component map of the cochain.
  rfl

/-- Helper for Lemma 15.72.1: advancing the source degree by one matches the target degree after
rewriting the cochain-complex relation `j = i + 1`. -/
private theorem module_complex_internal_hom_shift_indexEq
    (i j p : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    i + (p + 1) = j + p := by
  -- Rewrite the shape relation as `j = i + 1` and reassociate the sum.
  have hij' : i + 1 = j := by
    simpa using hij
  simpa [add_assoc, add_left_comm, add_comm] using congrArg (fun z : ℤ ↦ z + p) hij'

/-- Helper for Lemma 15.72.1: the cochain-component index for the shifted internal-Hom
projection agrees with the transported target degree. -/
private theorem module_complex_internal_hom_shift_component_indexEq
    (i j p : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    p + 1 + i = j + p := by
  have hij' : i + 1 = j := by
    simpa using hij
  omega

/-- Helper for Lemma 15.72.1: the `(p + 1, q)` tensor-degree target agrees with the shifted
outer target degree `j + p + q`. -/
private theorem currying_left_target_indexEq
    (i j p q : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    i + (p + 1) + q = j + p + q := by
  have hij' : i + 1 = j := by
    simpa using hij
  omega

/-- Helper for Lemma 15.72.1: the `(p, q + 1)` tensor-degree target agrees with the shifted
outer target degree `j + p + q`. -/
private theorem currying_right_target_indexEq
    (i j p q : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    i + p + (q + 1) = j + p + q := by
  have hij' : i + 1 = j := by
    simpa using hij
  omega

/-- Helper for Lemma 15.72.1: the shifted `(p + 1)` projection in the internal-Hom differential
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
            (module_complex_internal_hom_shift_component_indexEq i j p hij))
        ((ModuleCat.Hom.hom (K.d p (p + 1))) x)) := by
  -- Rewrite the shifted projection as the stored cochain component and then eliminate the
  -- remaining `eqToHom` by turning it into an explicit cast on elements.
  have hij' : i + 1 = j := by
    simpa using hij
  subst j
  rw [module_complex_internal_hom_piProj_apply_eq_v]
  change
    cast (congrArg (fun z : ℤ ↦ ↥(L.X z))
        (module_complex_internal_hom_shift_indexEq i (i + 1) p
          (by simpa using (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))))
      ((ModuleCat.Hom.hom
          (z.v (p + 1) (i + (p + 1)) (by omega)))
        ((ModuleCat.Hom.hom (K.d p (p + 1))) x)) =
    (ModuleCat.Hom.hom
        (z.v (p + 1) (i + 1 + p)
          (module_complex_internal_hom_shift_component_indexEq i (i + 1) p
            (by simpa using (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))))
      ((ModuleCat.Hom.hom (K.d p (p + 1))) x))
  simpa using
    cast_eq
      (congrArg (fun z : ℤ ↦ ↥(L.X z))
        (module_complex_internal_hom_shift_indexEq i (i + 1) p
          (by simpa using (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))))
      ((ModuleCat.Hom.hom
          (z.v (p + 1) (i + (p + 1)) (by omega)))
        ((ModuleCat.Hom.hom (K.d p (p + 1))) x))

/-- Helper for Lemma 15.72.1: after projecting the internal-Hom differential to the `p`-th factor
and evaluating at `x`, one obtains the owner formula `δ_v`. -/
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
  -- Rewrite both projections as cochain components so that the owner differential formula `δ_v`
  -- applies directly to the resulting equality of morphisms.
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
        (by abel) (i + p) (p + 1) hq₁ rfl)

/-- Helper for Lemma 15.72.1: in `ModuleCat R`, a morphism `A ⟶ Hom(B, C)` curries to a morphism
`A ⊗ B ⟶ C` by first using the closed-structure `uncurry` and then transporting across the
symmetry isomorphism. -/
private noncomputable def moduleCat_uncurryLinearEquiv
    (A B C : ModuleCat R) :
    (A ⟶ (ihom B).obj C) ≃ₗ[R] (((curriedTensor (ModuleCat R)).obj A).obj B ⟶ C) where
  toFun f := (β_ A B).hom ≫ MonoidalClosed.uncurry f
  invFun g := MonoidalClosed.curry ((β_ B A).hom ≫ g)
  left_inv f := by
    -- Uncurry after re-currying; the two braidings cancel and recover the original morphism.
    apply MonoidalClosed.uncurry_injective
    simp
  right_inv g := by
    -- The same cancellation on the tensor side shows that currying is inverse to uncurrying here.
    simp
  map_add' f g := by
    -- First record that `uncurry` is additive on `ModuleCat` by evaluating on pure tensors.
    have huncurry :
        MonoidalClosed.uncurry (f + g) =
          MonoidalClosed.uncurry f + MonoidalClosed.uncurry g := by
      ext : 1
      refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
      rfl
    -- Postcomposition by the fixed braiding morphism is additive.
    change (β_ A B).hom ≫ MonoidalClosed.uncurry (f + g) =
      (β_ A B).hom ≫ MonoidalClosed.uncurry f +
        (β_ A B).hom ≫ MonoidalClosed.uncurry g
    rw [huncurry, Preadditive.comp_add]
  map_smul' a f := by
    -- The same pure-tensor computation shows that `uncurry` commutes with scalar multiplication.
    have huncurry :
        MonoidalClosed.uncurry (a • f) =
          a • MonoidalClosed.uncurry f := by
      ext : 1
      refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
      rfl
    -- Then postcomposition by the braiding is linear in the uncurry target.
    change (β_ A B).hom ≫ MonoidalClosed.uncurry (a • f) =
      a • ((β_ A B).hom ≫ MonoidalClosed.uncurry f)
    rw [huncurry]
    simpa using
      (Linear.comp_smul
        (X := ((curriedTensor (ModuleCat R)).obj A).obj B)
        (Y := ((curriedTensor (ModuleCat R)).obj B).obj A)
        (Z := C)
        (f := (β_ A B).hom)
        (r := a)
        (g := MonoidalClosed.uncurry f))

/-- Helper for Lemma 15.72.1: the `ModuleCat` currying adapter is concretely the braided
`uncurry` map. -/
private theorem moduleCat_uncurryLinearEquiv_apply
    (A B C : ModuleCat R) (f : A ⟶ (ihom B).obj C) :
    moduleCat_uncurryLinearEquiv (R := R) A B C f =
      (β_ A B).hom ≫ MonoidalClosed.uncurry f :=
  rfl

/-- Helper for Lemma 15.72.1: the inverse `ModuleCat` currying adapter is concretely the braided
`curry` map. -/
private theorem moduleCat_uncurryLinearEquiv_symm_apply
    (A B C : ModuleCat R) (g : (((curriedTensor (ModuleCat R)).obj A).obj B ⟶ C)) :
    (moduleCat_uncurryLinearEquiv (R := R) A B C).symm g =
      MonoidalClosed.curry ((β_ B A).hom ≫ g) :=
  rfl

/-- Helper for Lemma 15.72.1: evaluating the currying adapter on a pure tensor is just double
evaluation of the original map. -/
private theorem moduleCat_uncurryLinearEquiv_apply_tmul
    (A B C : ModuleCat R) (f : A ⟶ (ihom B).obj C) (x : A) (y : B) :
    ModuleCat.Hom.hom (moduleCat_uncurryLinearEquiv (R := R) A B C f)
        (TensorProduct.tmul R x y) =
      ModuleCat.Hom.hom (ModuleCat.Hom.hom f x) y := by
  -- Evaluate the braided `uncurry` map on a pure tensor and simplify the braiding away.
  simpa only [moduleCat_uncurryLinearEquiv_apply, MonoidalClosed.uncurry_eq, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply]

-- Helper for Lemma 15.72.1: the source-side degree-`n` cochains in
-- `Hom(K, Hom(L, M))` are organized through the common `(p,q)` family below.
-- Route correction: the owner-level bridge is now `moduleCat_uncurryLinearEquiv`, so the
-- remaining blocker is no longer the closed-structure conversion itself. What still needs to be
-- packaged carefully is the inverse map from a `(p,q)`-family back to a cochain
-- `K ⟶ ⟪L, M⟫`, using `Pi.lift` and `module_complex_internal_hom_piIso` without reintroducing
-- unstable transport.
/-- Helper for Lemma 15.72.1: reconstructing a cochain in `Hom^•(L, M)^{n + p}` from a family of
`(p,q)`-components and then projecting back to the fixed `q`-component recovers that original
component. -/
private theorem iterated_internal_hom_component_reconstruction
    (K L M : CpxR) (n p q : ℤ)
    (g : ∀ q : ℤ, tensorDegreeSummand K L p q ⟶ M.X (n + p + q)) :
    (ModuleCat.ofHom
        (LinearMap.pi fun q : ℤ ↦
          ModuleCat.Hom.hom
            ((moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q))).symm
              (g q))) ≫
      (cochainFamilyLinearEquiv L M (n + p)).toModuleIso.hom) ≫
        module_complex_internal_hom_piProj L M (n + p) q =
      (moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q))).symm (g q) := by
  let φ :
      K.X p ⟶ (⟪L, M⟫).X (n + p) :=
    ModuleCat.ofHom
      (LinearMap.pi fun q : ℤ ↦
        ModuleCat.Hom.hom
          ((moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q))).symm
            (g q))) ≫
      (cochainFamilyLinearEquiv L M (n + p)).toModuleIso.hom
  apply ModuleCat.hom_ext
  ext x
  apply ModuleCat.hom_ext
  ext y
  have hq :=
    cochainFamilyLinearEquiv_apply_v (K := L) (L := M) (n := n + p) (q := q)
      (fun q : ℤ ↦
        ModuleCat.Hom.hom
          ((moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q))).symm
            (g q)) x)
  calc
    ModuleCat.Hom.hom
        ((ModuleCat.Hom.hom (φ ≫ module_complex_internal_hom_piProj L M (n + p) q)) x) y =
      (ModuleCat.Hom.hom (((ModuleCat.Hom.hom φ) x).v q (n + p + q) (by abel))) y := by
        simpa [φ, Category.assoc] using
          congrArg
            (fun z : L.X q ⟶ M.X (n + p + q) ↦ (ModuleCat.Hom.hom z) y)
            (module_complex_internal_hom_piProj_apply_eq_v
              (K := L) (L := M) (n := n + p) (p := q) ((ModuleCat.Hom.hom φ) x))
    _ = ModuleCat.Hom.hom
          ((ModuleCat.Hom.hom
              ((moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q)
                (M.X (n + p + q))).symm (g q))) x) y := by
        simpa [φ] using
          congrArg (fun z : L.X q ⟶ M.X (n + p + q) ↦ (ModuleCat.Hom.hom z) y) hq

/-- Helper for Lemma 15.72.1: for a fixed source degree `p`, a map
`K^p ⟶ Hom^•(L, M)^{n + p}` is equivalent to the family of its curried `(p,q)` components
`K^p ⊗ L^q ⟶ M^{n + p + q}`. -/
private noncomputable def iteratedInternalHomDegreeLinearEquiv
    (K L M : CpxR) (n p : ℤ) :
    (K.X p ⟶ (⟪L, M⟫).X (n + p)) ≃ₗ[R]
      (∀ q : ℤ, tensorDegreeSummand K L p q ⟶ M.X (n + p + q)) where
  toFun f q :=
    moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q))
      (f ≫ module_complex_internal_hom_piProj L M (n + p) q)
  invFun g :=
    ModuleCat.ofHom
        (LinearMap.pi fun q : ℤ ↦
          ModuleCat.Hom.hom
            ((moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q)
              (M.X (n + p + q))).symm (g q))) ≫
      (cochainFamilyLinearEquiv L M (n + p)).toModuleIso.hom
  map_add' f g := by
    -- Proof comment: each `(p,q)` component is obtained by projection and then by the linear
    -- currying equivalence, so addition is checked componentwise.
    funext q
    rw [Preadditive.add_comp]
    simpa using
      (moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q))).map_add
        (f ≫ module_complex_internal_hom_piProj L M (n + p) q)
        (g ≫ module_complex_internal_hom_piProj L M (n + p) q)
  map_smul' a f := by
    -- Proof comment: the same componentwise description makes scalar multiplication immediate.
    funext q
    simpa using
      (moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q))).map_smul
        a
        (f ≫ module_complex_internal_hom_piProj L M (n + p) q)
  left_inv f := by
    -- Proof comment: compare the two maps into `⟪L, M⟫.X (n + p)` after projecting to every
    -- `q`-component, where the currying equivalence cancels by construction.
    apply ModuleCat.hom_ext
    ext x
    apply ((cochainFamilyLinearEquiv L M (n + p)).symm).injective
    funext q
    have h :=
      congrArg
        (fun z : K.X p ⟶ (ihom (L.X q)).obj (M.X (n + p + q)) ↦ (ModuleCat.Hom.hom z) x)
        (iterated_internal_hom_component_reconstruction K L M n p q
          (fun q : ℤ ↦
            (moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q)))
              (f ≫ module_complex_internal_hom_piProj L M (n + p) q)))
    simpa [cochainFamilyLinearEquiv_symm_apply] using h
  right_inv g := by
    -- Proof comment: after rebuilding the cochain from its `q`-components, projecting back to a
    -- fixed `q` recovers exactly the chosen tensor summand map.
    funext q
    have h :=
      congrArg
        (fun z : K.X p ⟶ (ihom (L.X q)).obj (M.X (n + p + q)) ↦
          moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q)) z)
        (iterated_internal_hom_component_reconstruction K L M n p q g)
    simpa using h.trans
      ((moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q))).apply_symm_apply
        (g q))

private noncomputable def iteratedInternalHomFamilyLinearEquiv
    (K L M : CpxR) (n : ℤ) :
    Cochain K (⟪L, M⟫) n ≃ₗ[R]
      (∀ p q : ℤ, tensorDegreeSummand K L p q ⟶ M.X (n + p + q)) :=
  -- Proof comment: first decompose a degree-`n` cochain by its outer `p`-component, then
  -- curry each `p`-component degreewise in the inner Hom complex.
  ((cochainFamilyLinearEquiv K (⟪L, M⟫) n).symm).trans
    (LinearEquiv.piCongrRight fun p : ℤ ↦
      iteratedInternalHomDegreeLinearEquiv K L M n p)

/-- Helper for Lemma 15.72.1: the source-side family equivalence sends a cochain to its
`(p,q)`-component obtained by outer projection and then currying the inner projection. -/
private theorem iteratedInternalHomFamilyLinearEquiv_apply
    (K L M : CpxR) (n p q : ℤ) (z : Cochain K (⟪L, M⟫) n) :
    iteratedInternalHomFamilyLinearEquiv K L M n z p q =
      moduleCat_uncurryLinearEquiv (R := R) (K.X p) (L.X q) (M.X (n + p + q))
        (z.v p (n + p) (by abel) ≫ module_complex_internal_hom_piProj L M (n + p) q) := by
  -- Unpack the outer `p`-decomposition first, then the inner currying equivalence at the fixed
  -- source degree `p`.
  rfl

/-- Helper for Lemma 15.72.1: reindex the tensor-side family from fixed total degree `r` with a
summand index `p + q = r` to the common `(p,q)` family used on both sides of currying. -/
private noncomputable def tensorDegreeFamilyReindexLinearEquiv
    (K L M : CpxR) (n : ℤ) :
    (∀ r : ℤ, ∀ s : {pq : ℤ × ℤ // pq.1 + pq.2 = r},
      tensorDegreeSummand K L s.1.1 s.1.2 ⟶ M.X (n + r)) ≃ₗ[R]
      (∀ p q : ℤ, tensorDegreeSummand K L p q ⟶ M.X (n + p + q)) where
  toFun f p q :=
    f (p + q) ⟨(p, q), by simp⟩ ≫
      eqToHom (congrArg (fun z : ℤ ↦ M.X z) (by abel))
  invFun g r s :=
    g s.1.1 s.1.2 ≫
      eqToHom (congrArg (fun z : ℤ ↦ M.X z) (by simpa [add_assoc] using s.2))
  map_add' f g := by
    -- Composition with the unique reindexing isomorphism is linear in the chosen family map.
    funext p q
    let e : M.X (n + (p + q)) ⟶ M.X (n + p + q) :=
      eqToHom (congrArg (fun z : ℤ ↦ M.X z) (by abel))
    let fp : tensorDegreeSummand K L p q ⟶ M.X (n + (p + q)) :=
      f (p + q) ⟨(p, q), by simp⟩
    let gp : tensorDegreeSummand K L p q ⟶ M.X (n + (p + q)) :=
      g (p + q) ⟨(p, q), by simp⟩
    ext x
    change (ModuleCat.Hom.hom e) ((ModuleCat.Hom.hom fp + ModuleCat.Hom.hom gp) x) =
      (ModuleCat.Hom.hom e ∘ₗ ModuleCat.Hom.hom fp) x +
        (ModuleCat.Hom.hom e ∘ₗ ModuleCat.Hom.hom gp) x
    exact (ModuleCat.Hom.hom e).map_add _ _
  map_smul' a f := by
    -- The same reindexing postcomposition also commutes with scalar multiplication.
    funext p q
    let e : M.X (n + (p + q)) ⟶ M.X (n + p + q) :=
      eqToHom (congrArg (fun z : ℤ ↦ M.X z) (by abel))
    let fp : tensorDegreeSummand K L p q ⟶ M.X (n + (p + q)) :=
      f (p + q) ⟨(p, q), by simp⟩
    ext x
    change (ModuleCat.Hom.hom e) ((a • ModuleCat.Hom.hom fp) x) =
      a • (ModuleCat.Hom.hom e ∘ₗ ModuleCat.Hom.hom fp) x
    exact (ModuleCat.Hom.hom e).map_smul _ _
  left_inv f := by
    -- Going to `(p,q)` and back only changes the proof object for `p + q = r`.
    funext r s
    rcases s with ⟨⟨p, q⟩, hpq⟩
    subst r
    ext x
    simp
  right_inv g := by
    -- Specializing to `r = p + q` and then forgetting `r` returns the original `(p,q)` family.
    funext p q
    ext x
    simp

/-- Helper for Lemma 15.72.1: identify tensor-side degree-`n` cochains with the common
`(p,q)`-family by first decomposing the cochain by total degree and then descending along the
tensor coproduct in each degree. -/
private noncomputable def tensorCochainFamilyLinearEquiv
    (K L M : CpxR) [HomologicalComplex.HasTensor K L] (n : ℤ) :
    Cochain (HomologicalComplex.tensorObj K L) M n ≃ₗ[R]
      (∀ p q : ℤ, tensorDegreeSummand K L p q ⟶ M.X (n + p + q)) :=
  (((cochainFamilyLinearEquiv (HomologicalComplex.tensorObj K L) M n).symm).trans
      (LinearEquiv.piCongrRight fun r ↦
        tensorDegreeDescLinearEquiv K L r (M.X (n + r)))).trans
    (tensorDegreeFamilyReindexLinearEquiv K L M n)

/-- Helper for Lemma 15.72.1: the tensor-side family equivalence reads a cochain on the total
tensor product by restricting to the `(p,q)` summand and then applying the canonical reindexing in
the target degree. -/
private theorem tensorCochainFamilyLinearEquiv_apply
    (K L M : CpxR) [HomologicalComplex.HasTensor K L]
    (n p q : ℤ) (z : Cochain (HomologicalComplex.tensorObj K L) M n) :
    tensorCochainFamilyLinearEquiv K L M n z p q =
      HomologicalComplex.ιTensorObj K L p q (p + q) (by simp) ≫
        z.v (p + q) (n + (p + q)) (by abel) ≫
          eqToHom (congrArg (fun z : ℤ ↦ M.X z) (by abel)) := by
  -- Unpack the tensor cochain by total degree, descend to the chosen summand, and then reindex
  -- from `n + (p + q)` to the common target degree `n + p + q`.
  rfl

/-- Helper for Lemma 15.72.1: the degree-`n` currying comparison is the composition of the
source-side and tensor-side identifications with the common `(p,q)` family. -/
private noncomputable def iteratedInternalHomCochainCurryingLinearEquiv
    (K L M : CpxR) [HomologicalComplex.HasTensor K L] (n : ℤ) :
    Cochain K (⟪L, M⟫) n ≃ₗ[R] Cochain (HomologicalComplex.tensorObj K L) M n :=
  (iteratedInternalHomFamilyLinearEquiv K L M n).trans
    (tensorCochainFamilyLinearEquiv K L M n).symm

/-- Helper for Lemma 15.72.1: evaluating the source-side differential on a pure tensor yields the
textbook three-term formula. -/
private theorem iterated_internal_hom_source_d_apply_tmul
    (K L M : CpxR)
    (i j p q : ℤ) (hij : (up ℤ).Rel i j)
    (z : Cochain K (⟪L, M⟫) i) (x : K.X p) (y : L.X q) :
    ModuleCat.Hom.hom
        (iteratedInternalHomFamilyLinearEquiv K L M j
          (((⟪K, ⟪L, M⟫⟫).d i j).hom z) p q)
        (TensorProduct.tmul R x y) =
      (ModuleCat.Hom.hom (M.d (i + p + q) (j + p + q)))
          (ModuleCat.Hom.hom
            (iteratedInternalHomFamilyLinearEquiv K L M i z p q)
            (TensorProduct.tmul R x y)) +
        j.negOnePow •
          (ModuleCat.Hom.hom
            (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
              (currying_left_target_indexEq i j p q hij)))
            (ModuleCat.Hom.hom
              (iteratedInternalHomFamilyLinearEquiv K L M i z (p + 1) q)
              (TensorProduct.tmul R ((ModuleCat.Hom.hom (K.d p (p + 1))) x) y))) +
        (j + p).negOnePow •
          (ModuleCat.Hom.hom
            (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
              (currying_right_target_indexEq i j p q hij)))
            (ModuleCat.Hom.hom
              (iteratedInternalHomFamilyLinearEquiv K L M i z p (q + 1))
              (TensorProduct.tmul R x ((ModuleCat.Hom.hom (L.d q (q + 1))) y)))) := by
  have hij' : j = i + 1 := by
    simpa [eq_comm] using hij
  subst j
  -- Apply the outer internal-Hom differential formula at the fixed source degree `p`.
  have houter :=
    module_complex_internal_hom_d_after_piProj_apply
      K (⟪L, M⟫) i (i + 1) p
      (by simpa using (show (up ℤ).Rel i (i + 1) by simp))
      z x
  have houter' :=
    congrArg
      (fun w : (⟪L, M⟫).X (i + 1 + p) =>
        (ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L M (i + 1 + p) q).hom w)) y)
      houter
  -- Expand the first outer term by the inner internal-Hom differential formula at degree `q`.
  have hinner :=
    module_complex_internal_hom_d_after_piProj_apply
      L M (i + p) (i + p + 1) q
      (by simpa using (show (up ℤ).Rel (i + p) (i + p + 1) by simp))
      ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K (⟪L, M⟫) i p).hom z)) x)
      y
  have hinner' := by
    simpa only [add_assoc, add_left_comm, add_comm] using hinner
  rw [hinner'] at houter'
  -- Rewrite all projected components as the common `(p,q)` family and evaluate on `x ⊗ y`.
  simpa only [iteratedInternalHomFamilyLinearEquiv_apply, moduleCat_uncurryLinearEquiv_apply_tmul,
    currying_left_target_indexEq, currying_right_target_indexEq,
    add_assoc, add_left_comm, add_comm] using houter'

/-- Helper for Lemma 15.72.1: evaluating the tensor-side differential on a pure tensor yields the
same textbook three-term formula. -/
private theorem tensor_cochain_family_d_apply_tmul
    (K L M : CpxR) [HomologicalComplex.HasTensor K L]
    (i j p q : ℤ) (hij : (up ℤ).Rel i j)
    (z : Cochain (HomologicalComplex.tensorObj K L) M i)
    (x : K.X p) (y : L.X q) :
    ModuleCat.Hom.hom
        (tensorCochainFamilyLinearEquiv K L M j
          (((⟪HomologicalComplex.tensorObj K L, M⟫).d i j).hom z) p q)
        (TensorProduct.tmul R x y) =
      (ModuleCat.Hom.hom (M.d (i + p + q) (j + p + q)))
          (ModuleCat.Hom.hom
            (tensorCochainFamilyLinearEquiv K L M i z p q)
            (TensorProduct.tmul R x y)) +
        j.negOnePow •
          (ModuleCat.Hom.hom
            (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
              (currying_left_target_indexEq i j p q hij)))
            (ModuleCat.Hom.hom
              (tensorCochainFamilyLinearEquiv K L M i z (p + 1) q)
              (TensorProduct.tmul R ((ModuleCat.Hom.hom (K.d p (p + 1))) x) y))) +
        (j + p).negOnePow •
          (ModuleCat.Hom.hom
            (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
              (currying_right_target_indexEq i j p q hij)))
            (ModuleCat.Hom.hom
              (tensorCochainFamilyLinearEquiv K L M i z p (q + 1))
              (TensorProduct.tmul R x ((ModuleCat.Hom.hom (L.d q (q + 1))) y)))) := by
  have hij' : j = i + 1 := by
    simpa [eq_comm] using hij
  subst j
  let u : (HomologicalComplex.tensorObj K L).X (p + q) :=
    (ModuleCat.Hom.hom (HomologicalComplex.ιTensorObj K L p q (p + q) rfl))
      (TensorProduct.tmul R x y)
  -- First apply the ordinary internal-Hom differential formula at total source degree `p + q`.
  have houter :=
    module_complex_internal_hom_d_after_piProj_apply
      (HomologicalComplex.tensorObj K L) M i (i + 1) (p + q)
      (by simpa using (show (up ℤ).Rel i (i + 1) by simp))
      z u
  -- Rewrite the tensor differential on the chosen summand as the horizontal and vertical pieces.
  have hsummand :=
    congrArg
      (fun k : tensorDegreeSummand K L p q ⟶ (HomologicalComplex.tensorObj K L).X (p + q + 1) =>
        ModuleCat.Hom.hom k (TensorProduct.tmul R x y))
      (tensorObj_d_on_summand_eq_currying K L p q)
  have hsummand' : (ModuleCat.Hom.hom ((HomologicalComplex.tensorObj K L).d (p + q) (p + q + 1))) u =
      (fun k ↦ (ModuleCat.Hom.hom k) (TensorProduct.tmul R x y))
        ((K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫ ιTensorObj K L (p + 1) q (p + q + 1) (by omega) +
          p.negOnePow • (𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
            ιTensorObj K L p (q + 1) (p + q + 1) (by omega)) := by
    dsimp [u]
    simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_add,
      LinearMap.add_apply, ModuleCat.hom_smul, LinearMap.smul_apply] using hsummand
  rw [hsummand'] at houter
  -- Normalize the resulting three terms to the common `(p,q)` family description.
  simpa only [u, tensorCochainFamilyLinearEquiv_apply, add_assoc, add_left_comm, add_comm,
    smul_add, smul_assoc, Int.negOnePow_add, currying_left_target_indexEq,
    currying_right_target_indexEq, ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_id, id_tensorHom] using houter

/-- Helper for Lemma 15.72.1: after transporting both sides to the common `(p,q)` family, the
iterated-Hom differential and the tensor-side differential agree componentwise. -/
private theorem iteratedInternalHomCochainCurrying_comm
    (K L M : CpxR) [HomologicalComplex.HasTensor K L]
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ModuleCat.ofHom ((iteratedInternalHomCochainCurryingLinearEquiv K L M i).toLinearMap) ≫
      (⟪HomologicalComplex.tensorObj K L, M⟫).d i j =
    (⟪K, ⟪L, M⟫⟫).d i j ≫
      ModuleCat.ofHom ((iteratedInternalHomCochainCurryingLinearEquiv K L M j).toLinearMap) := by
  -- Route correction: finish the source-faithful proof on pure tensors, rather than at the level
  -- of transported morphism equalities in the common `(p,q)` family.
  apply (cancel_mono (tensorCochainFamilyLinearEquiv K L M j).toModuleIso.hom).1
  -- Compare both candidates in the common `(p,q)` family and then on pure tensors `x ⊗ y`.
  ext z p q
  refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
  have hleft :=
    tensor_cochain_family_d_apply_tmul K L M i j p q hij
      ((iteratedInternalHomCochainCurryingLinearEquiv K L M i) z) x y
  have hright :=
    iterated_internal_hom_source_d_apply_tmul K L M i j p q hij z x y
  exact hleft.trans <|
    (by
      simpa only [iteratedInternalHomCochainCurryingLinearEquiv, Category.assoc, add_assoc,
        add_left_comm, add_comm] using hright.symm)

/-- Helper for Lemma 15.72.1: packaging the textbook currying comparison as an isomorphism of
internal-Hom complexes. -/
-- Route correction: the earlier object-level fixed-degree tensor-product bridge drifts from the
-- owner tensor API. The stable source-faithful route is to use `tensorDegreeDescLinearEquiv`
-- degreewise on Hom spaces, then package the common family
-- `∀ p q, (K.X p ⊗ L.X q) ⟶ M.X (n + p + q)` and compare differentials there.
-- TODO: construct this isomorphism by the source-faithful degreewise route. Start from
-- `iteratedInternalHomFamilyLinearEquiv`, compare the source and tensor differentials after
-- transporting both sides to the common `(p,q)` family, and then package the degreewise maps with
-- `HomologicalComplex.Hom.isoOfComponents`.
private noncomputable def module_complex_internal_hom_currying_iso
    (K L M : CpxR) [HomologicalComplex.HasTensor K L] :
    ⟪K, ⟪L, M⟫⟫ ≅ ⟪HomologicalComplex.tensorObj K L, M⟫ :=
  -- Proof comment: once the degreewise currying maps are known to commute with the
  -- differentials, `isoOfComponents` packages them into an isomorphism of complexes.
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (iteratedInternalHomCochainCurryingLinearEquiv K L M n).toModuleIso)
    (fun i j hij ↦ by
      simpa using iteratedInternalHomCochainCurrying_comm K L M i j hij)

/-- Lemma 15.72.1: for cochain complexes `K^•`, `L^•`, and `M^•` of `R`-modules, the iterated
internal-Hom complex `Hom^•(K^•, Hom^•(L^•, M^•))` is canonically isomorphic to the internal-Hom
complex from the totalized tensor product `Tot(K^• ⊗_R L^•)` to `M^•`. -/
theorem module_complex_internal_hom_currying_isomorphic
    (K L M : CpxR) [HomologicalComplex.HasTensor K L] :
    IsIsomorphic
      (⟪K, ⟪L, M⟫⟫)
      (⟪HomologicalComplex.tensorObj K L, M⟫) :=
  ⟨module_complex_internal_hom_currying_iso K L M⟩

end Currying

end
