import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

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
