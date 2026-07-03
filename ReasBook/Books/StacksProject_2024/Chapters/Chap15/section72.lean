import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_72_1 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open MonoidalClosed

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

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

/-- The chapter internal-Hom complex is bifunctorial: a morphism `fK : K₂ ⟶ K₁` acts
contravariantly on the source complex, while a morphism `fL : L₁ ⟶ L₂` acts covariantly on the
target complex. This is the single owner-side bridge from the concrete cochain presentation to the
usual functoriality of internal Hom. -/
noncomputable def module_complex_internal_homMap
    {K₁ K₂ L₁ L₂ : CochainComplex (ModuleCat R) ℤ}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    ⟪K₁, L₁⟫ ⟶ ⟪K₂, L₂⟫ :=
  { f := fun n ↦ ModuleCat.ofHom
      { toFun := fun z ↦
          ((Cochain.ofHom fK).comp z (zero_add n)).comp (Cochain.ofHom fL) (add_zero n)
        map_add' := fun z₁ z₂ ↦ by
          simp [Cochain.add_comp, Cochain.comp_add]
        map_smul' := fun a z ↦ by
          simp [Cochain.smul_comp, Cochain.comp_smul] }
    comm' := by
      sorry }

end

/-! ### Remark_15_72_2 (from Chap15) -/
open CategoryTheory
open CochainComplex.HomComplex

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : CochainComplex C ℤ}

/- Domain-style sampling:
- primary domain: the Hom complex of cochain complexes and its degree-zero cocycles;
- sampled owner declarations:
  `CochainComplex.HomComplex.Cocycle.equivHom`,
  `CochainComplex.HomComplex.Cocycle.mem_iff`,
  `CochainComplex.HomComplex.Cocycle.ofHom`,
  `CochainComplex.HomComplex.Cocycle.homOf`;
- best owner abstraction: `CochainComplex.HomComplex.Cocycle`, whose degree-zero specialization is
  canonically equivalent to actual morphisms of cochain complexes via `Cocycle.equivHom`;
- primitive data vs. derived API:
  primitive owner data is the cocycle subtype together with the canonical equivalence
  `Cocycle.equivHom`, while the textbook existential criterion for a degree-zero cochain is only a
  source-facing bridge derived from that owner API and the cocycle criterion `Cocycle.mem_iff`;
- ambient minimization: all sampled declarations already live over an arbitrary preadditive
  category, so the remark should be stated for `{C} [Category C] [Preadditive C]` rather than the
  special model `CochainComplex (ModuleCat R) ℤ`;
- source/core/bridge triage:
  `source-facing`: the remark that a degree-zero cochain defines a morphism exactly when its
    differential vanishes;
  `core/canonical`: `Cocycle.equivHom`, `Cocycle.mem_iff`, `Cocycle.ofHom`, `Cocycle.homOf`;
  `bridge/view`: the theorem below translating the textbook existential wording into the canonical
    degree-zero cocycle owner.
-/

/- Remark 15.72.2 is owned canonically by the additive equivalence between morphisms of cochain
complexes and degree-zero cocycles in the Hom complex. -/
recall Cocycle.equivHom

/- The cocycle condition in degree `0` is exactly the vanishing of the Hom-complex differential. -/
recall Cocycle.mem_iff

/-- Companion bridge for Remark 15.72.2: a degree-zero element of the Hom complex
`Hom^•(K^•, L^•)` defines a morphism of complexes exactly when its differential vanishes. -/
theorem degreeZeroCochain_defines_morphism_iff_d_eq_zero (z : Cochain K L 0) :
    (∃ f : K ⟶ L, Cochain.ofHom f = z) ↔ δ 0 1 z = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    simpa using (Cocycle.ofHom f).δ_eq_zero 1
  · intro hz
    let z₀ : Cocycle K L 0 := Cocycle.mk z 1 (zero_add 1) hz
    refine ⟨z₀.homOf, ?_⟩
    change Cochain.ofHom z₀.homOf = (z₀ : Cochain K L 0)
    exact Cocycle.cochain_ofHom_homOf_eq_coe z₀

/-! ### Lemma_15_72_3 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalClosed
open scoped ModuleComplexInternalHom

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation:70 A " ⊗ " B => tensorObj A B

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

-- Proof sketch: project both sides to a tensor summand in degree `i` and then to a factor of the
-- target product decomposition. The source differential is the tensor differential on
-- `⟪L, M⟫ ⊗ ⟪K, L⟫`, while the target differential is the internal-Hom differential on `⟪K, M⟫`;
-- the component identities reduce to the sign conventions in the Hom-complex differential.
/-- Lemma 15.72.3: the chapter internal-Hom complexes admit the canonical composition morphism
`⟪L, M⟫ ⊗ ⟪K, L⟫ ⟶ ⟪K, M⟫`. -/
noncomputable def module_complex_internal_hom_comp
    (K L M : CpxR) [HasTensor (⟪L, M⟫) (⟪K, L⟫)] :
    (⟪L, M⟫ ⊗ ⟪K, L⟫) ⟶ ⟪K, M⟫ :=
  { f := module_complex_internal_hom_comp_f K L M
    comm' := by
      sorry }

end

/-! ### Lemma_15_72_4 (from Chap15) -/
open CategoryTheory
open HomologicalComplex
open MonoidalCategory
open MonoidalClosed
open BraidedCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
  [MonoidalCategory (CochainComplex (ModuleCat R) ℤ)]
  [BraidedCategory (CochainComplex (ModuleCat R) ℤ)]
  [MonoidalClosed (CochainComplex (ModuleCat R) ℤ)]
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for 15.72.4:
- primary domain: tensor-internal-Hom comparison morphisms for cochain complexes of `R`-modules;
- sampled owner declarations:
  `MonoidalClosed.curry`,
  `(ihom.ev M).app L`,
  `MonoidalClosed.pre f`;
- best owner abstraction: the source-facing morphism
  `K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L))` is the curried braiding/evaluation composite in the
  closed monoidal category of cochain complexes, so its canonical owner is `MonoidalClosed.curry`
  rather than a chapter-local reassembly through coevaluation and enriched composition;
- primitive data vs. derived API: the primitive owner data are the braiding and associator
  isomorphisms moving `M` past `K`, together with the evaluation map
  `M ⊗ (M ⟶[CpxR] L) ⟶ L`; the tensor-internal-Hom comparison is the derived curried morphism
  built from those owner maps;
- source/core/bridge triage:
  `source-facing`: the canonical morphism
    `K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L))`
    and its functoriality;
  `core/canonical`: `MonoidalClosed.curry`, `(ihom.ev M).app L`, `MonoidalClosed.pre`,
    `(ihom M).map`, and `⊗ₘ`;
  `bridge/view`: none beyond the source-order presentation of the canonical comparison.
-/

/-- The uncurried braiding/evaluation composite whose transpose is the tensor-Hom comparison. -/
private noncomputable def module_complex_tensor_internal_hom_comparisonTranspose
    (K L M : CpxR) :
    M ⊗ (K ⊗ (M ⟶[CpxR] L)) ⟶ K ⊗ L :=
  (α_ M K (M ⟶[CpxR] L)).inv ≫
    (β_ M K).hom ▷ (M ⟶[CpxR] L) ≫
    (α_ K M (M ⟶[CpxR] L)).hom ≫
    K ◁ (ihom.ev M).app L

/-- Lemma 15.72.4: there is a canonical morphism
`K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L))`
of cochain complexes of `R`-modules. -/
noncomputable def module_complex_tensor_internal_hom_comparison
    (K L M : CpxR) :
    K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L)) :=
  curry (module_complex_tensor_internal_hom_comparisonTranspose K L M)

/-- Uncurrying the canonical tensor-Hom comparison recovers the braiding-evaluation composite used
to define it. -/
theorem module_complex_tensor_internal_hom_comparison_uncurry
    (K L M : CpxR) :
    uncurry (module_complex_tensor_internal_hom_comparison K L M) =
      (α_ M K (M ⟶[CpxR] L)).inv ≫
        (β_ M K).hom ▷ (M ⟶[CpxR] L) ≫
        (α_ K M (M ⟶[CpxR] L)).hom ≫
        K ◁ (ihom.ev M).app L := by
  simp [module_complex_tensor_internal_hom_comparison,
    module_complex_tensor_internal_hom_comparisonTranspose]

-- Proof sketch: uncurry both sides to the defining braiding/evaluation composite. Naturality then
-- follows from functoriality of `⊗ₘ`, naturality of the associator and braiding, and the
-- owner identities `MonoidalClosed.uncurry_pre_app` and `MonoidalClosed.uncurry_natural_right`.
/-- The tensor-Hom comparison is natural in the tensor factor and in both variables of the
internal-Hom term. -/
theorem module_complex_tensor_internal_hom_comparison_natural
    {K₁ K₂ L₁ L₂ M₁ M₂ : CpxR}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (fK ⊗ₘ ((pre fM).app L₁ ≫ (ihom M₁).map fL))
      (module_complex_tensor_internal_hom_comparison K₁ L₁ M₂)
      (module_complex_tensor_internal_hom_comparison K₂ L₂ M₁)
      ((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := sorry

end

/-! ### Lemma_15_72_5 (from Chap15) -/
open CategoryTheory
open HomologicalComplex
open MonoidalCategory
open MonoidalClosed
open BraidedCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
  [MonoidalCategory (CochainComplex (ModuleCat R) ℤ)]
  [BraidedCategory (CochainComplex (ModuleCat R) ℤ)]
  [MonoidalClosed (CochainComplex (ModuleCat R) ℤ)]
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for 15.72.5:
- primary domain: closed braided monoidal structure on cochain complexes of `R`-modules;
- sampled owner declarations:
  `MonoidalClosed.curry`,
  `MonoidalClosed.curry_eq`,
  `MonoidalClosed.pre`,
  `MonoidalClosed.uncurry_pre_app`;
- best owner abstraction: the canonical owner of the unit map is the curried braiding
  `curry ((β_ L K).hom)`, with the coevaluation composite only as its specification via
  `MonoidalClosed.curry_eq`;
- primitive data vs. derived API: the primitive data are the braiding `β_` and the closed-monoidal
  adjunction owner `curry`; the source-facing morphism `K ⟶ (L ⟶[CpxR] (K ⊗ L))` is the
  specialization of that owner to cochain complexes, while the coevaluation composite is derived
  API recording the same morphism in textbook form;
- source/core/bridge triage:
  `source-facing`: the Stacks morphism `K ⟶ (L ⟶[CpxR] (K ⊗ L))` and its naturality squares;
  `core/canonical`: `MonoidalClosed.curry`, `MonoidalClosed.uncurry`, `pre`, `(ihom L).map`,
    and `β_`;
  `bridge/view`: the source-order presentation of the curried braiding as a coevaluation composite.
-/
/- Lemma 15.72.5 is the source-facing transport of the closed-monoidal coevaluation map along the
braiding `L ⊗ K ≅ K ⊗ L`. -/

/-- Lemma 15.72.5: the canonical morphism
`K^• ⟶ (L^• ⟶[CpxR] (K^• ⊗ L^•))`
of cochain complexes of `R`-modules, obtained from the closed-monoidal coevaluation map by
transport across the braiding. -/
noncomputable def tensor_totalization_internal_hom_unit
    (K L : CpxR) :
    K ⟶ (L ⟶[CpxR] (K ⊗ L)) :=
  curry ((β_ L K).hom)

/-- The canonical unit morphism is the coevaluation composite transported across the braiding. -/
theorem tensor_totalization_internal_hom_unit_spec
    (K L : CpxR) :
    tensor_totalization_internal_hom_unit K L =
      (ihom.coev L).app K ≫
        (ihom L).map (β_ L K).hom := by
  simp [tensor_totalization_internal_hom_unit, MonoidalClosed.curry_eq]

-- Proof sketch: uncurry both sides and use braiding naturality in the second variable.
/-- The canonical morphism is functorial in the left complex. -/
theorem tensor_totalization_internal_hom_unit_natural_left
    {K₁ K₂ L : CpxR} (α : K₁ ⟶ K₂) :
    CommSq
      α
      (tensor_totalization_internal_hom_unit K₁ L)
      (tensor_totalization_internal_hom_unit K₂ L)
      ((ihom L).map (α ▷ L)) := by
  sorry

-- Proof sketch: uncurry both sides, rewrite with `MonoidalClosed.uncurry_pre_app`, and use
-- braiding naturality in the first variable.
/-- The canonical morphism is functorial in the right complex. -/
theorem tensor_totalization_internal_hom_unit_natural_right
    (K : CpxR) {L₁ L₂ : CpxR}
    (β : L₁ ⟶ L₂) :
    CommSq
      (tensor_totalization_internal_hom_unit K L₂)
      (tensor_totalization_internal_hom_unit K L₁)
      ((pre β).app (K ⊗ L₂))
      ((ihom L₁).map (K ◁ β)) := by
  sorry

end

/-! ### Lemma_15_72_6 (from Chap15) -/
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
  sorry

section

variable [∀ K L : CochainComplex (ModuleCat R) ℤ, HasTensor K L]

/-- Lemma 15.72.6: there is a canonical morphism from the total tensor complex
`Tot(⟪L, M⟫ ⊗ K)` to the iterated internal-Hom complex `⟪⟪K, L⟫, M⟫`. -/
noncomputable def tensor_internal_hom_to_iterated_internal_hom
    (K L M : CpxR) :
    (⟪L, M⟫ ⊗ K) ⟶ ⟪⟪K, L⟫, M⟫ :=
  { f := tensor_internal_hom_to_iterated_internal_hom_f K L M
    comm' := tensor_internal_hom_to_iterated_internal_hom_f_comm K L M }

/-- The comparison morphism of Lemma 15.72.6 is functorial in `K`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_natural_K
    {K₁ K₂ L M : CpxR} (α : K₁ ⟶ K₂) :
    CommSq
      (tensorHom (𝟙 (⟪L, M⟫)) α)
      (tensor_internal_hom_to_iterated_internal_hom K₁ L M)
      (tensor_internal_hom_to_iterated_internal_hom K₂ L M)
      (module_complex_internal_homMap (module_complex_internal_homMap α (𝟙 L)) (𝟙 M)) := by
  sorry

/-- The comparison morphism of Lemma 15.72.6 is functorial in `L`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_natural_L
    (K : CpxR) {L₁ L₂ M : CpxR} (β : L₁ ⟶ L₂) :
    CommSq
      (tensorHom (module_complex_internal_homMap β (𝟙 M)) (𝟙 K))
      (tensor_internal_hom_to_iterated_internal_hom K L₂ M)
      (tensor_internal_hom_to_iterated_internal_hom K L₁ M)
      (module_complex_internal_homMap (module_complex_internal_homMap (𝟙 K) β) (𝟙 M)) := by
  sorry

/-- The comparison morphism of Lemma 15.72.6 is functorial in `M`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_natural_M
    (K L : CpxR) {M₁ M₂ : CpxR} (γ : M₁ ⟶ M₂) :
    CommSq
      (tensorHom (module_complex_internal_homMap (𝟙 L) γ) (𝟙 K))
      (tensor_internal_hom_to_iterated_internal_hom K L M₁)
      (tensor_internal_hom_to_iterated_internal_hom K L M₂)
      (module_complex_internal_homMap (𝟙 ⟪K, L⟫) γ) := by
  sorry

end

end

/-! ### Remark_15_72_7 (from Chap15) -/
open CategoryTheory
open MonoidalCategory
open MonoidalClosed
open scoped ModuleComplexInternalHom

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Remark 15.72.7:
- primary domain: the summandwise sign in the tensor-to-iterated-internal-Hom comparison of
  Lemma `15.72.6`, expressed through the chapter owner `⟪-, -⟫` and its degreewise product
  decomposition;
- sampled owner declarations:
  `tensor_internal_hom_to_iterated_internal_hom_component`,
  `tensor_internal_hom_to_iterated_internal_hom`,
  `module_complex_internal_hom_piProj`,
  `Int.negOnePow_mul_self`;
- best owner abstraction:
  `source-facing`: the sign comparison for the specific braiding/evaluation component used in
    Lemma `15.72.6`;
  `core/canonical`: `tensor_internal_hom_to_iterated_internal_hom_component`,
    `module_complex_internal_hom_piProj`, and `Int.negOnePow`;
  `bridge/view`: the diagonal-index observation and the resulting simplification of the braiding
    sign to the direct-construction sign;
- primitive data vs. derived API: the primitive owner data are the actual component map of
  Lemma `15.72.6` and the canonical degree decomposition of `⟪K, L⟫`; the remark is derived bridge
  API explaining that, in the `(-r')`-factor of `((⟪K, L⟫).X p)`, the braiding sign only matters
  on the diagonal forced by the degree bookkeeping.
-/

variable (K L M : CpxR) (t r n p : ℤ) (h : t + r = n)

/- Remark 15.72.7 concerns the summandwise braiding/evaluation component used to build the
comparison morphism `tensor_internal_hom_to_iterated_internal_hom K L M`. -/
#check tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h

section

variable {q r r' p : ℤ}

/-- In the `(-r')`-factor `Hom_R(K^{-r'}, L^q)` of `((⟪K, L⟫).X p)`, the degree bookkeeping from
Remark `15.72.7` forces the tensor summand indexed by `K^r` to lie on the diagonal `r = r'`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_component_diagonal
    (hp : q + r = p) (hp' : q + r' = p) :
    r = r' := by
  exact add_left_cancel (hp.trans hp'.symm)

/-- For the `(-r')`-factor of the target internal Hom in
`tensor_internal_hom_to_iterated_internal_hom_component`, the braiding sign `(-1)^(rp)` agrees,
on the diagonal singled out in Remark `15.72.7`, with the direct-construction sign
`(-1)^(r + qr)`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_component_sign_agrees
    (hp : q + r = p) (hp' : q + r' = p) :
    (r * p).negOnePow = (r + q * r).negOnePow := by
  have hr : r = r' :=
    tensor_internal_hom_to_iterated_internal_hom_component_diagonal hp hp'
  subst hr
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

end

end
