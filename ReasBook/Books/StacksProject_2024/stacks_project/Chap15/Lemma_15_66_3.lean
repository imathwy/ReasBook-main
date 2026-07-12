import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import StacksProject_2024.Chap10.Lemma_10_78_9
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_66_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ModuleCat
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "singleCpx₀" => CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
private abbrev Q : Cpx ⥤ DerivedCategory (ModuleCat R) := DerivedCategory.Q

/-- Helper for Lemma 15.66.3: transport of derived morphisms across source and target
isomorphisms is additive. -/
private theorem iso_hom_congr_add_equiv_map_add
    {X Y X₁ Y₁ : DerivedCategory (ModuleCat R)} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- Proof comment: `Iso.homCongr` is additive because composition is additive on both sides.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 15.66.3: an isomorphism on source and target induces an additive equivalence
on the corresponding derived Hom groups. -/
private noncomputable def iso_hom_congr_add_equiv
    {X Y X₁ Y₁ : DerivedCategory (ModuleCat R)} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) :=
  { toEquiv := α.homCongr β
    map_add' := iso_hom_congr_add_equiv_map_add α β }

/- Domain-style sampling for Lemma 15.66.3:
- primary domain: tensor-Hom comparison maps in `ModuleCat R` and their derived `Ext`
  analogues;
- sampled owner declarations:
  `TensorProduct.rTensorHomToHomRTensor`,
  `TensorProduct.rTensorHomEquivHomRTensor`,
  `CategoryTheory.Abelian.Ext.linearEquiv₀`,
  `CategoryTheory.Abelian.Ext.bilinearCompOfLinear`;
- best owner abstraction: the `Hom` comparison is owned by
  `TensorProduct.rTensorHomToHomRTensor`, while the `Ext` comparison is the derived bilinear
  postcomposition map built from `Ext.bilinearCompOfLinear`;
- primitive data: the ring `R`, the modules `M`, `N`, `L`, and the cohomological degree `i`;
- derived API: the `ModuleCat` packaging `homTensorComparisonHom`, the `Ext` comparison morphism
  `extTensorComparisonHom`, and the source-facing isomorphism theorems below;
- source/core/bridge triage:
  `source-facing`: the isomorphism statements of Lemma `15.66.3`;
  `core/canonical`: `TensorProduct.rTensorHomToHomRTensor` and `Ext.bilinearCompOfLinear`;
  `bridge/view`: the `ModuleCat` repackaging of the `Hom` comparison through
    `ModuleCat.homLinearEquiv`.
-/

/-- The degree-zero `Ext` class of the canonical map `n ↦ n ⊗ l`. -/
private noncomputable def tensorToExtZeroLinear
    (N L : ModuleCat.{u} R) :
    L →ₗ[R] Ext.{u} N (ModuleCat.of R (TensorProduct R N L)) 0 :=
  (((Ext.linearEquiv₀ :
      Ext.{u} N (ModuleCat.of R (TensorProduct R N L)) 0 ≃ₗ[R]
        (N ⟶ ModuleCat.of R (TensorProduct R N L))).symm.toLinearMap).comp
    (((homLinearEquiv :
        (N ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
          (N →ₗ[R] TensorProduct R N L)).symm.toLinearMap).comp
      ((TensorProduct.mk R N L).flip)))

/-- The canonical comparison map `Ext^i_R(M, N) ⊗_R L → Ext^i_R(M, N ⊗_R L)`. -/
noncomputable def extTensorComparisonHom
    (M N L : ModuleCat.{u} R) (i : ℕ) :
    ModuleCat.of R (TensorProduct R (Ext.{u} M N i) L) ⟶
      ModuleCat.of R (Ext.{u} M (ModuleCat.of R (TensorProduct R N L)) i) :=
  ModuleCat.ofHom <|
    TensorProduct.lift <|
      LinearMap.compl₂
        (Ext.bilinearCompOfLinear R M N (ModuleCat.of R (TensorProduct R N L)) i 0 i
          (add_zero i))
        (tensorToExtZeroLinear N L)

/-- The canonical comparison map `Hom_R(M, N) ⊗_R L → Hom_R(M, N ⊗_R L)`. -/
noncomputable def homTensorComparisonHom
    (M N L : ModuleCat.{u} R) :
    ModuleCat.of R (TensorProduct R (M ⟶ N) L) ⟶
      ModuleCat.of R (M ⟶ ModuleCat.of R (TensorProduct R N L)) :=
  ModuleCat.ofHom <|
    ((homLinearEquiv :
        (M ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
          (M →ₗ[R] TensorProduct R N L)).symm.toLinearMap) ∘ₗ
      TensorProduct.rTensorHomToHomRTensor (.id R) M N L ∘ₗ
      (LinearEquiv.rTensor L homLinearEquiv).toLinearMap

/-- Helper for Lemma 15.66.3: tensoring on the left with a flat module is an exact functor on
`ModuleCat R`. -/
private theorem tensorLeft_exact_of_flat
    (L : ModuleCat.{u} R) [Module.Flat R L] :
    Functor.Exact (tensorLeft L) := by
  -- Proof comment: flatness is exactly preservation of finite limits by tensoring with `L`,
  -- while finite colimits are preserved because tensoring is a left adjoint.
  letI : PreservesFiniteLimits (tensorLeft L) :=
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft L).1 inferInstance
  letI : PreservesFiniteColimits (tensorLeft L) := by
    infer_instance
  exact (exactFunctor_iff (tensorLeft L)).2 ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 15.66.3: the raw tensor-Hom comparison commutes with precomposition in the
source module. This is the compatibility square needed to compare the differentials in the
finite-free Hom complex before and after tensoring. -/
private theorem tensor_hom_comparison_lcomp
    {M₁ M₂ N L : ModuleCat.{u} R} (φ : M₁ ⟶ M₂) :
    TensorProduct.rTensorHomToHomRTensor (.id R) M₁ N L ∘ₗ
        (LinearMap.lcomp R N φ.hom).rTensor L =
      LinearMap.lcomp R (TensorProduct R N L) φ.hom ∘ₗ
        TensorProduct.rTensorHomToHomRTensor (.id R) M₂ N L := by
  -- Proof comment: both composites send a pure tensor `f ⊗ l` to the function
  -- `m ↦ f (φ m) ⊗ l`, so extensionality closes the comparison.
  ext f l m
  simp [LinearMap.comp_apply]

/-- Helper for Lemma 15.66.3: each finite free term of the chosen projective-minus approximation
has an isomorphic tensor-Hom comparison map. -/
private theorem projective_minus_term_tensor_hom_isIso_of_free
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (hPfree : ∀ q : ℤ, Module.Free R ((P : Cpx).X q))
    (hPfinite : ∀ q : ℤ, Module.Finite R ((P : Cpx).X q))
    (N L : ModuleCat.{u} R) (q : ℤ) :
    IsIso (ModuleCat.ofHom
      (TensorProduct.rTensorHomToHomRTensor (.id R) ((P : Cpx).X q) N L)) := by
  letI : Module.Free R ((P : Cpx).X q) := hPfree q
  letI : Module.Finite R ((P : Cpx).X q) := hPfinite q
  letI : Module.Projective R ((P : Cpx).X q) := Module.Projective.of_free
  -- Proof comment: finite free modules are finite projective, so the owner theorem from
  -- Lemma `10.78.9` upgrades the raw comparison to a bijection.
  have hbij :
      Function.Bijective
        (TensorProduct.rTensorHomToHomRTensor (.id R) ((P : Cpx).X q) N L) := by
    simpa using
      (rTensorHomToHomRTensor_bijective_of_finite_projective
        (R := R) (M := ((P : Cpx).X q)) (N := N) (L := L))
  exact
    (CategoryTheory.isIso_iff_bijective
      (ModuleCat.ofHom
        (TensorProduct.rTensorHomToHomRTensor (.id R) ((P : Cpx).X q) N L))).2 <| by
      simpa using hbij

/-- Helper for Lemma 15.66.3: precomposition with a morphism acts linearly on represented
Hom modules. -/
private noncomputable def represented_hom_precompose
    {X Y N : ModuleCat.{u} R} (u : X ⟶ Y) :
    ModuleCat.of R (Y ⟶ N) ⟶ ModuleCat.of R (X ⟶ N) :=
  ModuleCat.ofHom (LinearMap.lcomp R N u.hom)

/-- Helper for Lemma 15.66.3: the represented-Hom precomposition morphism is exactly the packaged
linear precomposition map. -/
private theorem represented_hom_precompose_hom
    {X Y N : ModuleCat.{u} R} (u : X ⟶ Y) :
    (represented_hom_precompose (R := R) (N := N) u).hom = LinearMap.lcomp R N u.hom := by
  -- Proof comment: both linear maps evaluate a morphism `g` by sending `x` to `g (u x)`.
  rfl

/-- Helper for Lemma 15.66.3: postcomposition with a module morphism acts linearly on represented
Hom modules. -/
private noncomputable def represented_hom_postcompose
    {X M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.of R (X ⟶ M) ⟶ ModuleCat.of R (X ⟶ N) :=
  ModuleCat.ofHom (LinearMap.compRight R f.hom)

/-- Helper for Lemma 15.66.3: the explicit represented-Hom row attached to the chosen
projective-minus complex still has zero composite. -/
private theorem represented_hom_row_zero
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (N : ModuleCat.{u} R) (p : ℤ) :
    represented_hom_precompose
        (R := R) (N := N) ((P : Cpx).d (-p) (-p + 1)) ≫
      represented_hom_precompose
        (R := R) (N := N) ((P : Cpx).d (-p - 1) (-p)) =
        0 := by
  -- Proof comment: composing the two represented-Hom differentials is precomposition by
  -- `d ≫ d`, which vanishes by the cochain-complex identity.
  ext g x
  simp [represented_hom_precompose, LinearMap.lcomp_apply,
    (P : Cpx).d_comp_d (-p - 1) (-p) (-p + 1)]

/-- Helper for Lemma 15.66.3: the source proof uses the represented-Hom row obtained from the
three terms around degree `p` of the chosen projective-minus complex. -/
private abbrev represented_hom_row
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (N : ModuleCat.{u} R) (p : ℤ) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (represented_hom_precompose (R := R) ((P : Cpx).d (-p) (-p + 1)))
    (represented_hom_precompose (R := R) ((P : Cpx).d (-p - 1) (-p)))
    (represented_hom_row_zero (R := R) P N p)

/-- Helper for Lemma 15.66.3: precomposition in the source variable commutes with
postcomposition in the module variable on represented Hom modules. -/
private theorem represented_hom_precompose_comp_postcompose
    {X Y M N : ModuleCat.{u} R} (u : X ⟶ Y) (f : M ⟶ N) :
    represented_hom_precompose (R := R) (N := M) u ≫
        represented_hom_postcompose (R := R) (X := X) f =
      represented_hom_postcompose (R := R) (X := Y) f ≫
        represented_hom_precompose (R := R) (N := N) u := by
  -- Proof comment: both composites send `g : Y ⟶ M` to the same map `x ↦ f (g (u x))`.
  apply ModuleCat.hom_ext
  ext g x
  rfl

/-- Helper for Lemma 15.66.3: a module morphism `N ⟶ N'` induces the expected morphism between
the represented-Hom rows by postcomposition on each term. -/
private noncomputable def represented_hom_row_map
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {N N' : ModuleCat.{u} R} (f : N ⟶ N') (p : ℤ) :
    represented_hom_row (R := R) P N p ⟶ represented_hom_row (R := R) P N' p :=
  -- Proof comment: the three termwise postcomposition maps form a short-complex morphism because
  -- precomposition by each differential commutes with postcomposition by `f`.
  ShortComplex.homMk
    (represented_hom_postcompose (R := R) (X := (P : Cpx).X (-p + 1)) f)
    (represented_hom_postcompose (R := R) (X := (P : Cpx).X (-p)) f)
    (represented_hom_postcompose (R := R) (X := (P : Cpx).X (-p - 1)) f)
    (represented_hom_precompose_comp_postcompose
      (R := R) ((P : Cpx).d (-p) (-p + 1)) f)
    (represented_hom_precompose_comp_postcompose
      (R := R) ((P : Cpx).d (-p - 1) (-p)) f)

/-- Helper for Lemma 15.66.3: the finite-free tensor-Hom comparison on one term of the chosen
projective-minus complex is promoted to a `ModuleCat` isomorphism. -/
private noncomputable def represented_hom_term_tensor_iso_of_projectiveMinus_finiteFree
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (hPfree : ∀ q : ℤ, Module.Free R ((P : Cpx).X q))
    (hPfinite : ∀ q : ℤ, Module.Finite R ((P : Cpx).X q))
    (N L : ModuleCat.{u} R) (q : ℤ) :
    ModuleCat.of R (TensorProduct R (((P : Cpx).X q) ⟶ N) L) ≅
      ModuleCat.of R (((P : Cpx).X q) ⟶ ModuleCat.of R (TensorProduct R N L)) := by
  letI :=
    projective_minus_term_tensor_hom_isIso_of_free
      (R := R) P hPfree hPfinite N L q
  -- Proof comment: the termwise tensor-Hom comparison is already known to be an isomorphism on
  -- each finite free projective term of `P`.
  exact
    asIso (ModuleCat.ofHom
      (TensorProduct.rTensorHomToHomRTensor (.id R) ((P : Cpx).X q) N L))

/-- Helper for Lemma 15.66.3: the finite-free tensor-Hom comparison commutes with represented-Hom
row differentials coming from precomposition by a source morphism. -/
private theorem represented_hom_term_tensor_iso_natural_precompose
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (hPfree : ∀ q : ℤ, Module.Free R ((P : Cpx).X q))
    (hPfinite : ∀ q : ℤ, Module.Finite R ((P : Cpx).X q))
    (N L : ModuleCat.{u} R) {q₁ q₂ : ℤ} (u : (P : Cpx).X q₁ ⟶ (P : Cpx).X q₂) :
    (tensorLeft L).map (represented_hom_precompose (R := R) (N := N) u) ≫
        (represented_hom_term_tensor_iso_of_projectiveMinus_finiteFree
          (R := R) P hPfree hPfinite N L q₁).hom =
      (represented_hom_term_tensor_iso_of_projectiveMinus_finiteFree
        (R := R) P hPfree hPfinite N L q₂).hom ≫
        represented_hom_precompose
          (R := R) (N := ModuleCat.of R (TensorProduct R N L)) u := by
  -- Proof comment: after unpacking the `ModuleCat` wrappers, this is exactly the owner
  -- naturality square `tensor_hom_comparison_lcomp`.
  apply ModuleCat.hom_ext
  ext x
  simpa [represented_hom_precompose, represented_hom_term_tensor_iso_of_projectiveMinus_finiteFree,
    LinearMap.comp_apply] using
    congrArg
      (fun T : TensorProduct R (((P : Cpx).X q₂) ⟶ N) L →ₗ[R]
          ((P : Cpx).X q₁) ⟶ ModuleCat.of R (TensorProduct R N L) ↦ T x)
      (tensor_hom_comparison_lcomp (R := R) (N := N) (L := L) (φ := u))

/-- Helper for Lemma 15.66.3: tensoring the represented-Hom row with `L` and then applying the
termwise finite-free tensor-Hom comparisons gives a short-complex isomorphism. -/
private noncomputable def represented_hom_row_tensor_iso_of_projectiveMinus_finiteFree
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (hPfree : ∀ q : ℤ, Module.Free R ((P : Cpx).X q))
    (hPfinite : ∀ q : ℤ, Module.Finite R ((P : Cpx).X q))
    (N L : ModuleCat.{u} R) (p : ℤ) :
    (represented_hom_row (R := R) P N p).map (tensorLeft L) ≅
      represented_hom_row
        (R := R) P (ModuleCat.of R (TensorProduct R N L)) p :=
  -- Proof comment: the source proof compares the three represented-Hom terms separately and then
  -- packages the two naturality squares into `ShortComplex.isoMk`.
  ShortComplex.isoMk
    (represented_hom_term_tensor_iso_of_projectiveMinus_finiteFree
      (R := R) P hPfree hPfinite N L (-p + 1))
    (represented_hom_term_tensor_iso_of_projectiveMinus_finiteFree
      (R := R) P hPfree hPfinite N L (-p))
    (represented_hom_term_tensor_iso_of_projectiveMinus_finiteFree
      (R := R) P hPfree hPfinite N L (-p - 1))
    (represented_hom_term_tensor_iso_natural_precompose
      (R := R) P hPfree hPfinite N L ((P : Cpx).d (-p) (-p + 1)))
    (represented_hom_term_tensor_iso_natural_precompose
      (R := R) P hPfree hPfinite N L ((P : Cpx).d (-p - 1) (-p)))

/-- Helper for Lemma 15.66.3: postcomposition by a module map acts linearly on the degree-`n`
cochains of `HomComplex(P, -[0])`. -/
private noncomputable def homComplex_single_postcompose
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℤ) :
    CochainComplex.HomComplex.Cochain (P : Cpx) ((singleCpx₀).obj M) n →ₗ[R]
      CochainComplex.HomComplex.Cochain (P : Cpx) ((singleCpx₀).obj N) n :=
  { toFun := fun z ↦
      z.comp (CochainComplex.HomComplex.Cochain.ofHom ((singleCpx₀).map f)) (add_zero n)
    map_add' := by
      -- Proof comment: cochain postcomposition is additive termwise.
      intro z z'
      simpa only using
        (CochainComplex.HomComplex.Cochain.add_comp
          (n₁ := n) (n₂ := 0) (n₁₂ := n) (h := add_zero n) z z'
          (CochainComplex.HomComplex.Cochain.ofHom ((singleCpx₀).map f)))
    map_smul' := by
      -- Proof comment: scalar multiplication commutes with cochain postcomposition.
      intro a z
      simp [Cochain.smul_comp, Cochain.comp_smul] }

/-- Helper for Lemma 15.66.3: degree-`n` cochains from `P` to the degree-zero complex on `N`
identify module-linearly with the represented Hom module of the term `P^{-n}`. -/
private noncomputable def homComplex_single_cochain_to_term_moduleIso
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (N : ModuleCat.{u} R) (n : ℤ) :
    ModuleCat.of R (CochainComplex.HomComplex.Cochain (P : Cpx) ((singleCpx₀).obj N) n) ≅
      ModuleCat.of R (((P : Cpx).X (-n)) ⟶ N) :=
  -- Proof comment: this is the source-faithful `toSingleEquiv`, repackaged as a `ModuleCat`
  -- isomorphism so it can later be fed directly into `ShortComplex.isoMk`.
  (CochainComplex.HomComplex.Cochain.toSingleEquiv
    (K := (P : Cpx)) (X := N) (p := -n) (q := 0) (n := n) (by omega)).toModuleIso

/-- Helper for Lemma 15.66.3: under the `toSingleEquiv` identification, postcomposition on
degree-`n` cochains becomes the usual postcomposition on represented Hom modules. -/
private theorem homComplex_single_cochain_to_term_moduleIso_natural_apply
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain (P : Cpx) ((singleCpx₀).obj M) n) :
    (homComplex_single_cochain_to_term_moduleIso (R := R) P N n).hom
        (homComplex_single_postcompose (P := P) f n z) =
      ((homComplex_single_cochain_to_term_moduleIso (R := R) P M n).hom z) ≫ f := by
  obtain ⟨g, rfl⟩ :=
    (CochainComplex.HomComplex.Cochain.toSingleEquiv
      (K := (P : Cpx)) (X := M) (p := -n) (q := 0) (n := n) (by omega)).surjective z
  have hpost :
      homComplex_single_postcompose (P := P) f n
          ((homComplex_single_cochain_to_term_moduleIso (R := R) P M n).inv.hom g) =
        (homComplex_single_cochain_to_term_moduleIso (R := R) P N n).inv.hom (g ≫ f) := by
    -- Proof comment: rewrite the inverse image of `g` as `toSingleMk g` and use the owner
    -- postcomposition compatibility lemma for single-complex cochains.
    simpa [homComplex_single_postcompose, homComplex_single_cochain_to_term_moduleIso] using
      (CochainComplex.HomComplex.Cochain.toSingleMk_postcomp
        (K := (P : Cpx)) (X := M) (p := -n) (q := 0) (f := g) (n := n) (h := by omega)
        (g := f)).symm
  rw [hpost]
  simp [homComplex_single_cochain_to_term_moduleIso]

/-- Helper for Lemma 15.66.3: the module-linear `toSingleEquiv` bridge is natural in the module
variable. -/
private theorem homComplex_single_cochain_to_term_moduleIso_natural
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℤ) :
    ModuleCat.ofHom (homComplex_single_postcompose (P := P) f n) ≫
        (homComplex_single_cochain_to_term_moduleIso (R := R) P N n).hom =
      (homComplex_single_cochain_to_term_moduleIso (R := R) P M n).hom ≫
        represented_hom_postcompose (R := R) (X := (P : Cpx).X (-n)) f := by
  apply ModuleCat.hom_ext
  ext z x
  -- Proof comment: after evaluating at `x`, this is exactly the pointwise naturality computed
  -- in the previous lemma.
  simpa [represented_hom_postcompose] using
    congrArg (fun h : ((P : Cpx).X (-n) ⟶ N) ↦ h x)
      (homComplex_single_cochain_to_term_moduleIso_natural_apply
        (R := R) (P := P) f n z)

/-- Helper for Lemma 15.66.3: transporting the actual degree-`p` Hom row through the three
degreewise `toSingleEquiv` isomorphisms preserves the square-zero relation. -/
private theorem transported_hom_row_zero
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (N : ModuleCat.{u} R) (p : ℤ) :
    ((homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1)).inv ≫
        ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).f ≫
        (homComplex_single_cochain_to_term_moduleIso (R := R) P N p).hom) ≫
      ((homComplex_single_cochain_to_term_moduleIso (R := R) P N p).inv ≫
        ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).g ≫
        (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p + 1)).hom) =
      0 := by
  have hzero :
      (((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).f) ≫
          (((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).g) =
        0 := ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).zero
  -- Proof comment: conjugating the actual short-complex row by fixed degreewise isomorphisms
  -- does not change the zero-composite property.
  calc
    ((homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1)).inv ≫
          ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).f ≫
          (homComplex_single_cochain_to_term_moduleIso (R := R) P N p).hom) ≫
        ((homComplex_single_cochain_to_term_moduleIso (R := R) P N p).inv ≫
          ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).g ≫
          (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p + 1)).hom) =
        (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1)).inv ≫
          ((((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).f) ≫
              (((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).g)) ≫
            (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p + 1)).hom) := by
      simp [Category.assoc]
    _ = (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1)).inv ≫
          (0 ≫ (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p + 1)).hom) := by
      rw [hzero]
    _ = 0 := by
      simp

/-- Helper for Lemma 15.66.3: transport the actual degree-`p` Hom-complex row to represented
Hom terms by conjugating the differentials with the degreewise `toSingleEquiv` isomorphisms. -/
private noncomputable def transported_hom_row
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (N : ModuleCat.{u} R) (p : ℤ) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    ((homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1)).inv ≫
      ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).f ≫
      (homComplex_single_cochain_to_term_moduleIso (R := R) P N p).hom)
    ((homComplex_single_cochain_to_term_moduleIso (R := R) P N p).inv ≫
      ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).g ≫
      (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p + 1)).hom)
    (transported_hom_row_zero (R := R) P N p)

/-- Helper for Lemma 15.66.3: the left square in the transported-row comparison is tautological
from the definition of the transported differential. -/
private theorem transported_hom_row_f_comm
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (N : ModuleCat.{u} R) (p : ℤ) :
    (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1)).hom ≫
        (transported_hom_row (R := R) P N p).f =
      ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).f ≫
        (homComplex_single_cochain_to_term_moduleIso (R := R) P N p).hom := by
  -- Proof comment: the defining inverse/hom pair on the left term cancels immediately.
  calc
    (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1)).hom ≫
        (transported_hom_row (R := R) P N p).f =
      ((homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1)).hom ≫
          (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1)).inv) ≫
        ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).f ≫
        (homComplex_single_cochain_to_term_moduleIso (R := R) P N p).hom := by
      simp [transported_hom_row, Category.assoc]
    _ = ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).f ≫
          (homComplex_single_cochain_to_term_moduleIso (R := R) P N p).hom := by
      simp [Category.assoc]

/-- Helper for Lemma 15.66.3: the right square in the transported-row comparison is tautological
from the definition of the transported differential. -/
private theorem transported_hom_row_g_comm
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (N : ModuleCat.{u} R) (p : ℤ) :
    (homComplex_single_cochain_to_term_moduleIso (R := R) P N p).hom ≫
        (transported_hom_row (R := R) P N p).g =
      ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).g ≫
        (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p + 1)).hom := by
  -- Proof comment: the same conjugation cancellation proves the right square.
  calc
    (homComplex_single_cochain_to_term_moduleIso (R := R) P N p).hom ≫
        (transported_hom_row (R := R) P N p).g =
      ((homComplex_single_cochain_to_term_moduleIso (R := R) P N p).hom ≫
          (homComplex_single_cochain_to_term_moduleIso (R := R) P N p).inv) ≫
        ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).g ≫
        (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p + 1)).hom := by
      simp [transported_hom_row, Category.assoc]
    _ = ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).g ≫
          (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p + 1)).hom := by
      simp [Category.assoc]

/-- Helper for Lemma 15.66.3: the actual degree-`p` short complex of `HomComplex(P, N[0])` is
canonically isomorphic to the represented-term row obtained by transporting the differentials
across the degreewise `toSingleEquiv` identifications. -/
private noncomputable def homComplex_single_row_iso_represented_shortComplex
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (N : ModuleCat.{u} R) (p : ℤ) :
    ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p) ≅
      transported_hom_row (R := R) P N p :=
  -- Proof comment: package the three degreewise `toSingleEquiv` isomorphisms into
  -- `ShortComplex.isoMk` after transporting the two differentials by conjugation.
  ShortComplex.isoMk
    (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p - 1))
    (homComplex_single_cochain_to_term_moduleIso (R := R) P N p)
    (homComplex_single_cochain_to_term_moduleIso (R := R) P N (p + 1))
    (transported_hom_row_f_comm (R := R) P N p)
    (transported_hom_row_g_comm (R := R) P N p)

/-- Helper for Lemma 15.66.3: the left homology of the degree-`p` Hom-complex row computes the
corresponding `Ext` group against the bounded-above projective complex `P`. -/
private noncomputable theorem homComplex_row_leftHomology_iso_ext_of_projectiveMinus
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (N : ModuleCat.{u} R) (p : ℤ) :
    ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).leftHomology ≅
      ModuleCat.of R (Ext^p(Q.obj (P : Cpx), (single₀).obj N)) := by
  -- Proof comment: first replace short-complex left homology by ordinary Hom-complex homology,
  -- then invoke the projective-minus Ext computation from Lemma `15.66.1`.
  refine
    (sc_leftHomology_iso_homology
      (R := R) (E := CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)) p) ≪≫ ?_
  simpa [Q] using
    (projective_minus_homology_add_equiv_shiftedHom_single0 (R := R) P N p).toModuleIso

/-- Helper for Lemma 15.66.3: after fixing a projective-minus representative `P`, an isomorphism
`Q(P) ≅ M[0]` transports the row-homology computation from `Q(P)` to the derived `Ext^p`
against `M[0]`. -/
private noncomputable theorem homComplex_row_leftHomology_iso_ext_of_iso
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {M : ModuleCat.{u} R} (e : Q.obj (P : Cpx) ≅ single₀.obj M)
    (N : ModuleCat.{u} R) (p : ℤ) :
    ((CochainComplex.HomComplex (P : Cpx) ((singleCpx₀).obj N)).sc p).leftHomology ≅
      ModuleCat.of R (Ext^p((single₀).obj M, (single₀).obj N)) := by
  -- Proof comment: compute `Ext` for the represented source `Q(P)` and then transport along the
  -- source isomorphism `e`.
  refine homComplex_row_leftHomology_iso_ext_of_projectiveMinus (R := R) P N p ≪≫ ?_
  simpa [Q, single₀] using
    (iso_hom_congr_add_equiv e (Iso.refl _)).toModuleIso

/-- Helper for Lemma 15.66.3: the `Ext` comparison is bijective below the pseudo-coherence bound.
This isolates the source-faithful finite-free-resolution step from the degree-zero transport used
to recover the `Hom` statements first. -/
private theorem extTensorComparison_bijective_of_isMPseudoCoherent
    (M N L : ModuleCat.{u} R) (m i : ℕ) [Module.Flat R L]
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    Function.Bijective (extTensorComparisonHom M N L i).hom := by
  -- Route correction: the unresolved part is now concentrated in the transport from the
  -- projective-minus row comparison to the canonical `Ext` map. The new helper
  -- `extTensorComparison_precompOfLinear` above supplies the missing tensor/precomposition
  -- commutation on pure tensors; the remaining blocker is still packaging the actual row
  -- comparison and descending it to homology.
  rcases hM with ⟨E, ⟨a, b, hEa, hEb⟩, hEfree, α, hαiso, hαepi⟩
  let P : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hEb⟩⟩,
      fun q ↦ by
        letI : CochainComplex.IsTermwiseFiniteFree (R := R) E := hEfree
        exact inferInstance⟩
  have hPfree : ∀ q : ℤ, Module.Free R ((P : Cpx).X q) := by
    intro q
    -- Proof comment: the packaged `ProjectiveMinus` complex still uses the original finite free
    -- representative termwise.
    simpa [P] using
      (show Module.Free R (E.X q) by
        letI : CochainComplex.IsTermwiseFiniteFree (R := R) E := hEfree
        infer_instance)
  have hPfinite : ∀ q : ℤ, Module.Finite R ((P : Cpx).X q) := by
    intro q
    -- Proof comment: the same packaging preserves the termwise finiteness needed for the tensor-
    -- Hom owner theorem.
    simpa [P] using
      (show Module.Finite R (E.X q) by
        letI : CochainComplex.IsTermwiseFiniteFree (R := R) E := hEfree
        infer_instance)
  have hTensorExact : Functor.Exact (tensorLeft L) :=
    tensorLeft_exact_of_flat (R := R) L
  have hTensorTerm :
      ∀ q : ℤ,
        IsIso (ModuleCat.ofHom
          (TensorProduct.rTensorHomToHomRTensor (.id R) ((P : Cpx).X q) N L)) := by
    intro q
    exact projective_minus_term_tensor_hom_isIso_of_free
      (R := R) P hPfree hPfinite N L q
  -- Proof comment: the main source-faithful finite-free approximation and the termwise
  -- tensor-Hom isomorphisms are now fixed. The remaining work is to package `hTensorTerm` into a
  -- short-complex isomorphism on `HomComplex(P, N[0])`, descend it to homology using
  -- `hTensorExact`, and identify the resulting map with `extTensorComparisonHom` via the
  -- `projective_minus_homology_add_equiv_shiftedHom_single0` bridge.
  -- TODO: use `homComplex_single_row_iso_represented_shortComplex` together with the new
  -- `extTensorComparison_precompOfLinear` helper to identify the descended homology map with the
  -- canonical `Ext` comparison after rowwise tensor-Hom normalization.
  -- TODO: alternatively, finish the positive-degree row comparison through
  -- `shortExact_extClass_precompOfLinear_bijective_of_projective` once the actual-row
  -- tensor-comparison short-complex isomorphism is packaged.
  let _ := hTensorExact
  let _ := hTensorTerm
  let _ := α
  let _ := hαiso
  let _ := hαepi
  let _ := hi
  let _ := a
  sorry

/-- Helper for Lemma 15.66.3: under `Ext^0 = Hom`, the class attached to `l : L` is the ordinary
map `n ↦ n ⊗ l`. -/
private theorem ext_zero_linearEquiv_apply_tensorToExtZeroLinear
    (N L : ModuleCat.{u} R) (l : L) :
    (Ext.linearEquiv₀ :
        Ext.{u} N (ModuleCat.of R (TensorProduct R N L)) 0 ≃ₗ[R]
          (N ⟶ ModuleCat.of R (TensorProduct R N L)))
      (tensorToExtZeroLinear N L l) =
        ((homLinearEquiv :
            (N ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
              (N →ₗ[R] TensorProduct R N L)).symm
          (((TensorProduct.mk R N L).flip) l)) := by
  -- Proof comment: this is just the defining composition of `tensorToExtZeroLinear`.
  simp [tensorToExtZeroLinear]

/-- Helper for Lemma 15.66.3: in degree `0`, bilinear `Ext` composition with concrete morphisms is
ordinary composition. -/
private theorem ext_zero_bilinearCompOfLinear_apply_mk₀
    {M N P : ModuleCat.{u} R} (f : M ⟶ N) (g : N ⟶ P) :
    (Ext.bilinearCompOfLinear R M N P 0 0 0 (add_zero 0)) (Ext.mk₀ f) (Ext.mk₀ g) =
      Ext.mk₀ (f ≫ g) := by
  -- Proof comment: the degree-zero Yoneda product of `mk₀` classes is the class of the
  -- composite morphism.
  simpa using (Ext.mk₀_comp_mk₀ (f := f) (g := g))

/-- Helper for Lemma 15.66.3: after transporting through `Ext^0 = Hom`, the degree-zero
comparison map is the `Hom`-tensor comparison already defined above. -/
private theorem ext_zero_tensor_comparison_eq_homTensorComparison
    (M N L : ModuleCat.{u} R) :
    ((Ext.linearEquiv₀ :
          Ext.{u} M (ModuleCat.of R (TensorProduct R N L)) 0 ≃ₗ[R]
            (M ⟶ ModuleCat.of R (TensorProduct R N L))).toLinearMap).comp
        (extTensorComparisonHom M N L 0).hom.comp
        ((LinearEquiv.rTensor L
            (Ext.linearEquiv₀ : Ext.{u} M N 0 ≃ₗ[R] (M ⟶ N))).symm.toLinearMap)
      = (homTensorComparisonHom M N L).hom := by
  -- Proof comment: it is enough to compare both linear maps on pure tensors from
  -- `Hom_R(M, N) ⊗_R L`.
  ext x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro f l
    -- Proof comment: on a pure tensor, the `Ext` comparison composes the degree-zero class of `f`
    -- with the degree-zero class of `n ↦ n ⊗ l`, which is exactly the canonical `Hom` comparison.
    simp [extTensorComparisonHom, homTensorComparisonHom,
      ext_zero_linearEquiv_apply_tensorToExtZeroLinear,
      ext_zero_bilinearCompOfLinear_apply_mk₀, Ext.homEquiv₀_symm_apply]
  · intro x y hx hy
    simp [hx, hy]

/-- Helper for Lemma 15.66.3: the canonical tensor-`Ext` comparison commutes with
precomposition in the first variable. -/
private theorem extTensorComparison_precompOfLinear
    {X Y Z L : ModuleCat.{u} R} {n a b : ℕ}
    (α : Ext.{u} X Y n) (h : n + a = b) :
    (extTensorComparisonHom X Z L b).hom.comp
        ((Ext.precompOfLinear (R := R) α Z h).rTensor L) =
      (Ext.precompOfLinear (R := R) α (ModuleCat.of R (TensorProduct R Z L)) h).comp
        (extTensorComparisonHom Y Z L a).hom := by
  ext x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Proof comment: both linear maps preserve zero.
    simp [LinearMap.comp_apply]
  · intro η l
    -- Proof comment: on a pure tensor `η ⊗ l`, both sides are triple Yoneda products with the
    -- degree-zero tensor class; associativity is the only non-formal input.
    simpa [extTensorComparisonHom, LinearMap.comp_apply] using
      (Ext.comp_assoc α η (tensorToExtZeroLinear Z L l) h (add_zero a)
        (by simpa [h]))
  · intro x y hx hy
    -- Proof comment: the comparison map is bilinear, so the tensor sum case follows from the
    -- inductive hypotheses.
    simp [LinearMap.comp_apply, hx, hy]

/-- Helper for Lemma 15.66.3: in a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with
projective middle term, the contravariant connecting map is bijective in positive degree. -/
private theorem shortExact_extClass_precompOfLinear_bijective_of_projective
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Projective S.X₂] (Y : ModuleCat.{u} R) (q : ℕ) :
    Function.Bijective
      (Ext.precompOfLinear (R := R) hS.extClass Y (Nat.add_zero (q + 1))) := by
  let δ :
      Ext S.X₁ Y (q + 1) →ₗ[R] Ext S.X₃ Y (q + 2) :=
    Ext.precompOfLinear (R := R) hS.extClass Y (Nat.add_zero (q + 1))
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hsub : δ (x - y) = 0 := by
      rw [LinearMap.map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁ hS Y (x - y)
      (Nat.add_zero (q + 1)) hsub
    have hzzero : z = 0 := by
      -- Proof comment: the neighboring `Ext` group vanishes because the middle term is projective.
      exact Ext.eq_zero_of_projective z
    have hxy' : x - y = 0 := by
      -- Proof comment: exactness identifies the kernel of `δ` with the image from the projective
      -- middle term, hence only the zero class maps to zero.
      simpa [δ, hzzero] using hz.symm
    exact sub_eq_zero.mp hxy'
  · intro e
    -- Proof comment: the same exact sequence gives surjectivity because the next `Ext` group out
    -- of the projective middle term also vanishes.
    simpa [δ] using
      (Ext.contravariant_sequence_exact₃ hS Y e (Ext.eq_zero_of_projective _)
        (Nat.add_zero (q + 1)))

/-- The owner comparison `rTensorHomToHomRTensor` is bijective for a finitely presented module and
a flat tensor factor. -/
theorem rTensorHomToHomRTensor_bijective_of_finitePresentation
    (M N L : ModuleCat.{u} R) [Module.FinitePresentation R M] [Module.Flat R L] :
    Function.Bijective (TensorProduct.rTensorHomToHomRTensor (.id R) M N L) := by
  -- Route correction: this degree-zero bridge previously depended on
  -- `moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation`, but the imported owner file
  -- currently does not build. The source-faithful fallback is to reprove the Hom comparison
  -- directly from a finite free presentation of `M`.
  rcases (Module.FinitePresentation.iff_exists_exact_free_sequence R M).mp inferInstance with
    ⟨n, m, f, g, hfg, hg⟩
  let αM := TensorProduct.rTensorHomToHomRTensor (.id R) M N L
  let αn := TensorProduct.rTensorHomToHomRTensor (.id R) (Fin n → R) N L
  let αm := TensorProduct.rTensorHomToHomRTensor (.id R) (Fin m → R) N L
  let β : (M ⟶ N) →ₗ[R] ((Fin n → R) ⟶ N) := LinearMap.lcomp R N g.hom
  let γ : ((Fin n → R) ⟶ N) →ₗ[R] ((Fin m → R) ⟶ N) := LinearMap.lcomp R N f.hom
  let β' : (M ⟶ ModuleCat.of R (TensorProduct R N L)) →ₗ[R]
      ((Fin n → R) ⟶ ModuleCat.of R (TensorProduct R N L)) :=
    LinearMap.lcomp R (TensorProduct R N L) g.hom
  let γ' : ((Fin n → R) ⟶ ModuleCat.of R (TensorProduct R N L)) →ₗ[R]
      ((Fin m → R) ⟶ ModuleCat.of R (TensorProduct R N L)) :=
    LinearMap.lcomp R (TensorProduct R N L) f.hom
  have hExact : Function.Exact β γ :=
    LinearMap.exact_lcomp_of_exact_of_surjective N hfg hg
  have hExact' : Function.Exact β' γ' :=
    LinearMap.exact_lcomp_of_exact_of_surjective (TensorProduct R N L) hfg hg
  have hβinj : Function.Injective β :=
    LinearMap.lcomp_injective_of_surjective g.hom hg
  have hβ'inj : Function.Injective β' :=
    LinearMap.lcomp_injective_of_surjective g.hom hg
  have hTensorExact : Function.Exact (β.rTensor L) (γ.rTensor L) :=
    Module.Flat.rTensor_exact L hExact
  have hβTensorInj : Function.Injective (β.rTensor L) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := L) β hβinj
  have hαn : Function.Bijective αn := by
    -- Proof comment: the free presentation term `R^n` is finite projective, so the owner theorem
    -- from Lemma `10.78.9` applies directly.
    simpa [αn] using
      (rTensorHomToHomRTensor_bijective_of_finite_projective
        (R := R) (M := Fin n → R) (N := N) (L := L))
  have hαm : Function.Bijective αm := by
    -- Proof comment: the same finite-projective comparison holds for the `R^m` term.
    simpa [αm] using
      (rTensorHomToHomRTensor_bijective_of_finite_projective
        (R := R) (M := Fin m → R) (N := N) (L := L))
  have hcomm_g : αn ∘ₗ β.rTensor L = β' ∘ₗ αM := by
    -- Proof comment: the comparison map is natural in the source module, so it commutes with the
    -- presentation map `g`.
    simpa [αM, αn, β, β'] using
      (tensor_hom_comparison_lcomp (R := R) (N := N) (L := L) (φ := g))
  have hcomm_f : αm ∘ₗ γ.rTensor L = γ' ∘ₗ αn := by
    -- Proof comment: the same naturality square controls the presentation differential `f`.
    simpa [αn, αm, γ, γ'] using
      (tensor_hom_comparison_lcomp (R := R) (N := N) (L := L) (φ := f))
  refine ⟨?_, ?_⟩
  · intro x y hxy
    -- Proof comment: compare the images of `x` and `y` inside the tensorized middle free term,
    -- where the vertical comparison is already bijective.
    apply hβTensorInj
    apply hαn.injective
    calc
      αn ((β.rTensor L) x) = β' (αM x) := by
        simpa [LinearMap.comp_apply] using congrArg (fun T ↦ T x) hcomm_g
      _ = β' (αM y) := by rw [hxy]
      _ = αn ((β.rTensor L) y) := by
        symm
        simpa [LinearMap.comp_apply] using congrArg (fun T ↦ T y) hcomm_g
  · intro y
    obtain ⟨z, hz⟩ := hαn.surjective (β' y)
    have hzker : (γ.rTensor L) z = 0 := by
      -- Proof comment: transport the kernel condition `γ' (β' y) = 0` across the right vertical
      -- isomorphism on the presentation row.
      apply hαm.injective
      calc
        αm ((γ.rTensor L) z) = γ' (αn z) := by
          simpa [LinearMap.comp_apply] using congrArg (fun T ↦ T z) hcomm_f
        _ = γ' (β' y) := by rw [hz]
        _ = 0 := by
          exact (hExact' (β' y)).2 ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := (hTensorExact z).1 hzker
    refine ⟨x, ?_⟩
    -- Proof comment: exactness of the tensorized row produces a preimage `x`; injectivity of
    -- `β'` then forces its comparison image to equal the original `y`.
    apply hβ'inj
    calc
      β' (αM x) = αn ((β.rTensor L) x) := by
        symm
        simpa [LinearMap.comp_apply] using congrArg (fun T ↦ T x) hcomm_g
      _ = αn z := by rw [hx]
      _ = β' y := hz

-- Proof sketch: identify `Hom_R(M, N)` with `Ext^0_R(M, N)`, express the comparison as the
-- degree-zero instance of the `Ext`-tensor comparison, and use finite presentation of `M`
-- together with flatness of `L` to show that this comparison is an isomorphism.
/-- Lemma 15.66.3 (1): if `M` is finitely presented and `L` is flat, then the canonical map
`\operatorname{Hom}_R(M, N) \otimes_R L \to \operatorname{Hom}_R(M, N \otimes_R L)` is an
isomorphism. -/
theorem homTensorComparison_isIso_of_finitePresentation
    (M N L : ModuleCat.{u} R) [Module.FinitePresentation R M] [Module.Flat R L] :
    IsIso (homTensorComparisonHom M N L) := by
  -- Proof comment: in `ModuleCat`, bijectivity of the underlying linear map is exactly the
  -- categorical isomorphism criterion.
  exact (isIso_iff_bijective _).2 <|
    by simpa using
      (show Function.Bijective (homTensorComparisonHom M N L).hom from
        by
          let f := homTensorComparisonHom M N L
          have hRaw := rTensorHomToHomRTensor_bijective_of_finitePresentation
            (M := M) (N := N) (L := L)
          have hEq :
              f.hom =
                ((homLinearEquiv :
                    (M ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
                      (M →ₗ[R] TensorProduct R N L)).symm.toLinearMap).comp
                  (TensorProduct.rTensorHomToHomRTensor (.id R) M N L).comp
                  ((LinearEquiv.rTensor L homLinearEquiv).toLinearMap) := by
            ext x
            simp [homTensorComparisonHom, LinearMap.comp_apply]
          rw [show f.hom =
              (((homLinearEquiv :
                  (M ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
                    (M →ₗ[R] TensorProduct R N L)).symm.toLinearMap).comp
                (TensorProduct.rTensorHomToHomRTensor (.id R) M N L).comp
                ((LinearEquiv.rTensor L homLinearEquiv).toLinearMap)) from hEq]
          exact
            (homLinearEquiv :
              (M ⟶ ModuleCat.of R (TensorProduct R N L)) ≃ₗ[R]
                (M →ₗ[R] TensorProduct R N L)).symm.bijective.comp <|
              hRaw.comp (LinearEquiv.rTensor L homLinearEquiv).bijective)

-- Proof sketch: choose a finite-free resolution of the `(-m)`-pseudo-coherent module `M` in the
-- relevant range, compare the Hom complexes before and after tensoring with the flat module `L`,
-- and pass to cohomology in degree `i < m`.
/-- Lemma 15.66.3 (2): if `M` is `(-m)`-pseudo-coherent and `L` is flat, then the canonical map
`\operatorname{Ext}^i_R(M, N) \otimes_R L \to \operatorname{Ext}^i_R(M, N \otimes_R L)` is an
isomorphism for `i < m`. -/
theorem extTensorComparison_isIso_of_isMPseudoCoherent
    (M N L : ModuleCat.{u} R) (m i : ℕ) [Module.Flat R L]
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) :
    IsIso (extTensorComparisonHom M N L i) := by
  -- Proof comment: once the finite-free-resolution comparison is packaged as bijectivity on the
  -- underlying additive group, the `ModuleCat` isomorphism criterion is immediate.
  exact (isIso_iff_bijective _).2 <|
    extTensorComparison_bijective_of_isMPseudoCoherent
      (M := M) (N := N) (L := L) (m := m) (i := i) hM hi

end

end CategoryTheory
