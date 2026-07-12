import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Tactic.StacksAttribute

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open ComplexShape
open HomologicalComplex
open MonoidalClosed

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation:70 A " ⊗ " B => tensorObj A B

/-- Helper for Lemma 15.72.3: the `ModuleCat`-valued realization of the canonical Hom complex on
cochain complexes of `R`-modules. Its degree-`n` term is the module of `n`-cochains from `K` to
`L`. -/
noncomputable def module_complex_internal_hom
    (K L : CpxR) : CpxR where
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

/-- Helper for Lemma 15.72.3: textbook surface notation for the module-valued internal-Hom
complex from `K^•` to `L^•`. -/
scoped notation "⟪" K ", " L "⟫" => module_complex_internal_hom K L

end ModuleComplexInternalHom

open scoped ModuleComplexInternalHom

/-- Helper for Lemma 15.72.3: the module of degree-`n` cochains is canonically equivalent to the
family of degreewise internal-Hom components `Hom_R(K^p, L^{n + p})`. -/
private def cochainFamilyLinearEquiv
    (K L : CpxR) (n : ℤ) :
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

/-- Helper for Lemma 15.72.3: evaluating the cochain built from a degreewise family at the
matching component recovers that original family entry. -/
private theorem cochainFamilyLinearEquiv_apply_v
    (K L : CpxR) (n q : ℤ)
    (f : ∀ p : ℤ, (ihom (K.X p)).obj (L.X (n + p))) :
    ((cochainFamilyLinearEquiv K L n) f).v q (n + q) (by abel) = f q := by
  simp [cochainFamilyLinearEquiv, Cochain.mk_v]

/-- Helper for Lemma 15.72.3: the degree-`n` term of `module_complex_internal_hom K L` is
canonically the product of the degreewise internal-Hom objects `Hom_R(K^p, L^{p + n})`. -/
noncomputable def module_complex_internal_hom_piIso
    (K L : CpxR) (n : ℤ) :
    ∏ᶜ (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p))) ≅ (⟪K, L⟫).X n := by
  let Z : ℤ → ModuleCat R := fun p ↦ ModuleCat.of R (K.X p ⟶ L.X (n + p))
  change ∏ᶜ Z ≅ ModuleCat.of R (Cochain K L n)
  exact
    (ModuleCat.piIsoPi Z).trans (cochainFamilyLinearEquiv K L n).toModuleIso

/-- Helper for Lemma 15.72.3: projection to the `p`-th degreewise internal-Hom factor in
`(⟪K, L⟫).X n`, obtained from the canonical product decomposition
`module_complex_internal_hom_piIso`. -/
noncomputable abbrev module_complex_internal_hom_piProj
    (K L : CpxR) (n p : ℤ) :
    (⟪K, L⟫).X n ⟶ (ihom (K.X p)).obj (L.X (n + p)) :=
  (cochainFamilyLinearEquiv K L n).symm.toModuleIso.hom ≫
    ModuleCat.ofHom (LinearMap.proj p)

/-- Helper for Lemma 15.72.3: applying an `eqToHom` in `ModuleCat` is the corresponding type-level
transport on elements. -/
private theorem moduleCat_eqToHom_apply
    {X Y : ModuleCat R} (h : X = Y) (x : X) :
    (ModuleCat.Hom.hom (eqToHom h)) x =
      cast (congrArg (fun Z : ModuleCat R ↦ ↥Z) h) x := by
  cases h
  rfl

/- Domain-style sampling for 15.72.3:
- primary domain: the source-facing composition morphism on the Chapter 15 internal-Hom complexes
  `⟪-, -⟫` of cochain complexes of `R`-modules;
- sampled owner declarations:
  `module_complex_internal_hom`,
  `module_complex_internal_hom_piIso`,
  `module_complex_internal_hom_piProj`,
  `HomologicalComplex.mapBifunctorDesc`,
  `MonoidalClosed.comp`;
- best owner abstraction: the public owner remains the chapter internal-Hom complex `⟪-, -⟫`;
  the ambient module-level closed-monoidal composition `MonoidalClosed.comp` supplies only the
  degreewise composition maps used to build the chain map;
- primitive data vs. derived API: the primitive owner data are the complexes `⟪K, L⟫` and their
  canonical degree decompositions `module_complex_internal_hom_piIso`; the projection maps
  `module_complex_internal_hom_piProj` and the composition morphism
  `⟪L, M⟫ ⊗ ⟪K, L⟫ ⟶ ⟪K, M⟫` are derived bridge API;
- source/core/bridge triage:
  `source-facing`: `module_complex_internal_hom_comp`;
  `core/canonical`: `module_complex_internal_hom`, `module_complex_internal_hom_piIso`,
    `HomologicalComplex.tensorObj`, `HomologicalComplex.mapBifunctorDesc`, and the degreewise
    module-level `MonoidalClosed.comp`;
  `bridge/view`: the product projections `module_complex_internal_hom_piProj` together with the
    index-transport map on the target degree.
-/

/-- Reindexing the target degree in the internal-Hom composition map. -/
private theorem module_complex_internal_hom_comp_indexEq
    {t r n p : ℤ} (h : t + r = n) :
    t + (r + p) = n + p := by
  omega

/-- Helper for Lemma 15.72.3: commuting the two cochain degrees does not change their total sum. -/
private theorem module_complex_internal_hom_comp_comm_indexEq
    {t r n : ℤ} (h : t + r = n) :
    r + t = n := by
  omega

/-- Helper for Lemma 15.72.3: shifting the left tensor index by one preserves the total degree. -/
private theorem module_complex_internal_hom_comp_left_succ_indexEq
    (t r : ℤ) :
    (t + 1) + r = t + r + 1 := by
  abel_nf

/-- Helper for Lemma 15.72.3: shifting the right tensor index by one preserves the total degree. -/
private theorem module_complex_internal_hom_comp_right_succ_indexEq
    (t r : ℤ) :
    t + (r + 1) = t + r + 1 := by
  abel_nf

/-- Helper for Lemma 15.72.3: the `p`-th internal-Hom component is indexed by the commuted sum
`n + p`. -/
private theorem module_complex_internal_hom_piProj_indexEq
    (n p : ℤ) :
    p + n = n + p := by
  abel

section

open MonoidalCategory

/-- The summandwise composition map contributing to the degree-`n` component of
`⟪L, M⟫ ⊗ ⟪K, L⟫ ⟶ ⟪K, M⟫`. -/
noncomputable def module_complex_internal_hom_comp_component
    (K L M : CpxR) (t r n p : ℤ) (h : t + r = n) :
    ((⟪L, M⟫).X t ⊗ (⟪K, L⟫).X r) ⟶
      (ihom (K.X p)).obj (M.X (n + p)) :=
  ((module_complex_internal_hom_piProj L M t (r + p)) ⊗ₘ
      (module_complex_internal_hom_piProj K L r p)) ≫
    (β_ ((ihom (L.X (r + p))).obj (M.X (t + (r + p))))
      ((ihom (K.X p)).obj (L.X (r + p)))).hom ≫
    MonoidalClosed.comp (K.X p) (L.X (r + p)) (M.X (t + (r + p))) ≫
    (ihom (K.X p)).map
      (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
        (module_complex_internal_hom_comp_indexEq h)))

end

/-- The degree-`n` component of the composition morphism on the chapter internal-Hom complexes. -/
private noncomputable def module_complex_internal_hom_comp_f
    (K L M : CpxR) [HasTensor (⟪L, M⟫) (⟪K, L⟫)] (n : ℤ) :
    (⟪L, M⟫ ⊗ ⟪K, L⟫).X n ⟶ (⟪K, M⟫).X n :=
  let desc :
      (⟪L, M⟫ ⊗ ⟪K, L⟫).X n ⟶
        ∏ᶜ fun p : ℤ ↦ (ihom (K.X p)).obj (M.X (n + p)) :=
    mapBifunctorDesc fun t r h ↦
      Pi.lift fun p ↦
        module_complex_internal_hom_comp_component K L M t r n p h
  desc ≫ (module_complex_internal_hom_piIso K M n).hom

/-- Helper for Lemma 15.72.3: after restricting to a fixed tensor summand and then projecting to
the `p`-th factor of the target product decomposition, the descended degree-`n` map is exactly
the corresponding summandwise composition map. -/
private theorem module_complex_internal_hom_comp_f_on_summand_proj
    (K L M : CpxR) [HasTensor (⟪L, M⟫) (⟪K, L⟫)]
    (t r n p : ℤ) (h : t + r = n) :
    HomologicalComplex.ιTensorObj (⟪L, M⟫) (⟪K, L⟫) t r n h ≫
        module_complex_internal_hom_comp_f K L M n ≫
        module_complex_internal_hom_piProj K M n p =
      module_complex_internal_hom_comp_component K L M t r n p h := by
  -- First remove the target product isomorphism, then evaluate `mapBifunctorDesc` on the chosen
  -- tensor summand and finally project to the `p`-th factor.
  unfold module_complex_internal_hom_comp_f
  rw [Category.assoc]
  have hdesc := congrArg
    (fun u ↦ u ≫ Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (M.X (n + q))) p)
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := ⟪L, M⟫) (K₂ := ⟪K, L⟫) (F := MonoidalCategory.curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ)
      (A := ∏ᶜ fun q : ℤ ↦ (ihom (K.X q)).obj (M.X (n + q)))
      (j := n)
      (f := fun t r h ↦ Pi.lift fun p ↦ module_complex_internal_hom_comp_component K L M t r n p h)
      t r h)
  simpa [Category.assoc, HomologicalComplex.ιTensorObj, CategoryTheory.Limits.Pi.lift_π,
    module_complex_internal_hom_piIso, module_complex_internal_hom_piProj] using hdesc

section

open MonoidalCategory

/-- Helper for Lemma 15.72.3: on a fixed tensor summand, the differential in the total tensor
complex splits into the horizontal differential plus the signed vertical differential. -/
private theorem module_complex_internal_hom_comp_source_d_on_summand
    (K L M : CpxR) [HasTensor (⟪L, M⟫) (⟪K, L⟫)] (t r : ℤ) :
    HomologicalComplex.ιTensorObj (⟪L, M⟫) (⟪K, L⟫) t r (t + r) rfl ≫
        (⟪L, M⟫ ⊗ ⟪K, L⟫).d (t + r) (t + r + 1) =
      (((⟪L, M⟫).d t (t + 1)) ⊗ₘ 𝟙 ((⟪K, L⟫).X r)) ≫
          HomologicalComplex.ιTensorObj (⟪L, M⟫) (⟪K, L⟫) (t + 1) r (t + r + 1)
            (module_complex_internal_hom_comp_left_succ_indexEq t r) +
        t.negOnePow •
          ((𝟙 ((⟪L, M⟫).X t) ⊗ₘ (⟪K, L⟫).d r (r + 1)) ≫
            HomologicalComplex.ιTensorObj (⟪L, M⟫) (⟪K, L⟫) t (r + 1) (t + r + 1)
              (module_complex_internal_hom_comp_right_succ_indexEq t r)) := by
  -- Route correction: use the owner tensor-totalization Leibniz rule directly on the chosen
  -- summand, rather than unfolding the total tensor complex by hand.
  change
    HomologicalComplex.ιMapBifunctor (⟪L, M⟫) (⟪K, L⟫)
        (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) t r (t + r) rfl ≫
        (HomologicalComplex.mapBifunctor (⟪L, M⟫) (⟪K, L⟫)
          (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).d
          (t + r) (t + r + 1) =
      (((⟪L, M⟫).d t (t + 1)) ⊗ₘ 𝟙 ((⟪K, L⟫).X r)) ≫
          HomologicalComplex.ιMapBifunctor (⟪L, M⟫) (⟪K, L⟫)
            (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
            (t + 1) r (t + r + 1)
            (module_complex_internal_hom_comp_left_succ_indexEq t r) +
        t.negOnePow •
          ((𝟙 ((⟪L, M⟫).X t) ⊗ₘ (⟪K, L⟫).d r (r + 1)) ≫
            HomologicalComplex.ιMapBifunctor (⟪L, M⟫) (⟪K, L⟫)
              (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
              t (r + 1) (t + r + 1)
              (module_complex_internal_hom_comp_right_succ_indexEq t r))
  -- Rewrite the total differential into its horizontal and vertical pieces on this summand.
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq (⟪L, M⟫) (⟪K, L⟫)
      (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
      (show (ComplexShape.up ℤ).Rel t (t + 1) by simp) r (t + r + 1)
      (module_complex_internal_hom_comp_left_succ_indexEq t r),
    HomologicalComplex.mapBifunctor.d₂_eq (⟪L, M⟫) (⟪K, L⟫)
      (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) t
      (show (ComplexShape.up ℤ).Rel r (r + 1) by simp) (t + r + 1)
      (module_complex_internal_hom_comp_right_succ_indexEq t r)]
  -- For cochain complexes over `ℤ`, the vertical sign is exactly `(-1)^t`.
  simp only [MonoidalCategory.curriedTensor_obj_obj, ε₁_def,
    MonoidalCategory.curriedTensor_map_app, ε₂_def, ComplexShape.ε_up_ℤ,
    MonoidalCategory.curriedTensor_obj_map, tensorHom_id, id_tensorHom]
  let A :=
    (⟪L, M⟫).d t (t + 1) ▷ (⟪K, L⟫).X r ≫
      HomologicalComplex.ιMapBifunctor (⟪L, M⟫) (⟪K, L⟫)
        (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
        (t + 1) r (t + r + 1)
        (module_complex_internal_hom_comp_left_succ_indexEq t r)
  let B :=
    t.negOnePow •
      ((⟪L, M⟫).X t ◁ (⟪K, L⟫).d r (r + 1) ≫
        HomologicalComplex.ιMapBifunctor (⟪L, M⟫) (⟪K, L⟫)
          (MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
          t (r + 1) (t + r + 1)
          (module_complex_internal_hom_comp_right_succ_indexEq t r))
  change ((1 : ℤ) • A) + B = A + B
  have hA : (1 : ℤ) • A = A := by
    simp
  exact congrArg (fun u ↦ u + B) hA

end

/-- Helper for Lemma 15.72.3: the projection to the `p`-th factor of the degree-`n`
internal-Hom complex is exactly the corresponding cochain component map. -/
private theorem module_complex_internal_hom_piProj_apply_eq_v
    (K L : CpxR) (n p : ℤ) (z : (⟪K, L⟫).X n) :
    (module_complex_internal_hom_piProj K L n p).hom z =
      z.v p (n + p) (module_complex_internal_hom_piProj_indexEq n p) := by
  -- The projection is defined by the canonical product decomposition of degree-`n` cochains.
  rfl

/-- Helper for Lemma 15.72.3: advancing the source degree by one matches the target degree after
using the cochain-complex relation `j = i + 1`. -/
private theorem module_complex_internal_hom_shift_indexEq
    (i j p : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    i + (p + 1) = j + p := by
  have hij' : i + 1 = j := by
    simpa using hij
  simpa [add_assoc, add_left_comm, add_comm] using congrArg (fun z : ℤ ↦ z + p) hij'

/-- Helper for Lemma 15.72.3: the shifted `(p + 1)` projection in `δ_v` is the transported
`(p + 1, j + p)` cochain component. -/
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
                module_complex_internal_hom_piProj_indexEq i (p + 1))))
        ((ModuleCat.Hom.hom (K.d p (p + 1))) x) := by
  sorry

/-- Helper for Lemma 15.72.3: after projecting the internal-Hom differential to the `p`-th
factor and then evaluating at `x`, one obtains the owner formula `δ_v`. -/
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
  -- Apply the owner differential formula at target degree `j + p`.
  simpa using
    congrArg
      (fun f : K.X p ⟶ L.X (j + p) ↦ ModuleCat.Hom.hom f x)
      (CochainComplex.HomComplex.δ_v (F := K) (G := L) i j hij' z p (j + p)
        (module_complex_internal_hom_piProj_indexEq j p) (i + p) (p + 1) hq₁ rfl)

/-- Helper for Lemma 15.72.3: on a pure tensor of cochains, the summandwise composition map is
the corresponding component of the owner cochain composition. -/
private theorem module_complex_internal_hom_comp_component_tmul
    (K L M : CpxR) (t r i p : ℤ) (h : t + r = i)
    (f : (⟪L, M⟫).X t) (g : (⟪K, L⟫).X r) :
    ModuleCat.Hom.hom
        ((module_complex_internal_hom_comp_component K L M t r i p h).hom
          (TensorProduct.tmul R f g)) =
      ModuleCat.Hom.hom
        ((g.comp f (module_complex_internal_hom_comp_comm_indexEq h)).v p (i + p)
          (module_complex_internal_hom_piProj_indexEq i p)) := by
  sorry

/-- Helper for Lemma 15.72.3: the remaining component check after restricting to a tensor summand
and a target factor. The pointwise identity is the owner Leibniz rule `δ_comp` for the cochain
composition read on the chosen tensor summand. -/
private theorem module_complex_internal_hom_comp_component_chain
    (K L M : CpxR) [HasTensor (⟪L, M⟫) (⟪K, L⟫)]
    (i j t r p : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (h : t + r = i) :
    HomologicalComplex.ιTensorObj (⟪L, M⟫) (⟪K, L⟫) t r i h ≫
        module_complex_internal_hom_comp_f K L M i ≫
        (⟪K, M⟫).d i j ≫
        (module_complex_internal_hom_piIso K M j).inv ≫
        Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (M.X (j + q))) p =
      HomologicalComplex.ιTensorObj (⟪L, M⟫) (⟪K, L⟫) t r i h ≫
        (⟪L, M⟫ ⊗ ⟪K, L⟫).d i j ≫
        module_complex_internal_hom_comp_f K L M j ≫
        (module_complex_internal_hom_piIso K M j).inv ≫
        Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (M.X (j + q))) p := by
  sorry

-- Proof sketch: project both sides to a tensor summand in degree `i` and then to a factor of the
-- target product decomposition. The source differential is the tensor differential on
-- `⟪L, M⟫ ⊗ ⟪K, L⟫`, while the target differential is the internal-Hom differential on `⟪K, M⟫`;
-- the component identities reduce to the sign conventions in the Hom-complex differential.
/-- Lemma 15.72.3: the chapter internal-Hom complexes admit the canonical composition morphism
`⟪L, M⟫ ⊗ ⟪K, L⟫ ⟶ ⟪K, M⟫`. -/
@[stacks 0A8I]
noncomputable def module_complex_internal_hom_comp
    (K L M : CpxR) [HasTensor (⟪L, M⟫) (⟪K, L⟫)] :
    (⟪L, M⟫ ⊗ ⟪K, L⟫) ⟶ ⟪K, M⟫ :=
  { f := module_complex_internal_hom_comp_f K L M
    comm' := by
      intro i j hij
      -- Compare the two candidate morphisms after transporting the target to its canonical
      -- product decomposition in degree `j`.
      apply (cancel_mono (module_complex_internal_hom_piIso K M j).inv).1
      apply Pi.hom_ext
      intro p
      -- Restrict further to each tensor summand in source degree `i`.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro t r h
      simpa [Category.assoc] using
        module_complex_internal_hom_comp_component_chain K L M i j t r p hij h }

end
