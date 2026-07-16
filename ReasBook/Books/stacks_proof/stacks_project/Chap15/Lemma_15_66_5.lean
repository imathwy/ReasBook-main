import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import stacks_proof.stacks_project.Chap10.Proposition_10_89_2
import stacks_proof.stacks_project.Chap10.Proposition_10_89_3
import stacks_proof.stacks_project.Chap13.Remark_13_12_4
import stacks_proof.stacks_project.Chap13.Situation_13_15_1
import stacks_proof.stacks_project.Chap15.Definition_15_59_13
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14
import stacks_proof.stacks_project.Chap15.Lemma_15_65_4
import stacks_proof.stacks_project.Chap15.Lemma_15_65_5
import stacks_proof.stacks_project.Chap15.Lemma_15_65_17
import stacks_proof.stacks_project.Chap15.Lemma_15_66_1
import stacks_proof.stacks_project.Chap19.Lemma_19_13_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local instance (A : Type u) :
    HasProductsOfShape A (DerivedCategory (ModuleCat.{u} R)) :=
  derivedCategory_hasProductsOfShape

-- Domain-style sampling for pseudo-coherence via tensor-product/product comparison:
-- - primary domain: source-facing product-comparison maps for the functor
--   `Q ↦ Q[0] ⊗_R^L K`;
-- - inspected declarations:
--   * `ModuleCat.single0Functor`
--   * `CategoryTheory.derivedTensorProduct`
--   * `Limits.piComparison`
--   * constant-family specializations of `piComparison` already used elsewhere in Chapter 15;
-- - best owner abstraction:
--   in this module-category specialization, the canonical construction is the comparison morphism
--   `piComparison` for `ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj`; the
--   constant-family and free-family maps in the source are specializations of this owner.
--
-- Source/core/bridge triage:
-- - `source-facing`: the three product-comparison conditions and the TFAE statements phrased in
--   terms of those maps;
-- - `core/canonical`: `piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)`;
-- - `bridge/view`: the constant-family and `R^A` specializations of that `piComparison`.
--
-- Primitive data is the composite functor `ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj`;
-- the comparison maps and their homology conditions are derived API.

/-- Helper for Lemma 15.66.5: homology detects isomorphisms in the derived category of
`R`-modules. -/
private theorem derivedCategory_isIso_iff_homology_map_isIso_local
    {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i : ℤ, IsIso ((H^i).map f) := by
  constructor
  · intro hf i
    -- Proof comment: every homology functor preserves isomorphisms.
    let _ : IsIso f := hf
    exact Functor.map_isIso (H^i) f
  · intro hf
    -- Proof comment: pass to a homotopy-category representative and detect quasi-isomorphisms
    -- there via degreewise homology.
    obtain ⟨g, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (F := DerivedCategory.Qh.mapArrow) (Arrow.mk f)
    have hq : HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ) g.hom := by
      rw [HomotopyCategory.mem_quasiIso_iff]
      intro i
      haveI : IsIso e.hom := e.isIso_hom
      let eleft :
          (H^i).obj (DerivedCategory.Qh.obj g.left) ≅ (H^i).obj X :=
        Functor.mapIso (H^i) (Arrow.leftFunc.mapIso e)
      let eright :
          (H^i).obj (DerivedCategory.Qh.obj g.right) ≅ (H^i).obj Y :=
        Functor.mapIso (H^i) (Arrow.rightFunc.mapIso e)
      let ef : (H^i).obj X ≅ (H^i).obj Y := asIso ((H^i).map f)
      have hw :
          (H^i).map (Arrow.Hom.left e.hom) ≫ (H^i).map f =
            (H^i).map (DerivedCategory.Qh.map g.hom) ≫
              (H^i).map (Arrow.Hom.right e.hom) := by
        simpa [Functor.map_comp] using congrArg ((H^i).map) (Arrow.w e.hom)
      have hcomp :
          IsIso ((H^i).map (DerivedCategory.Qh.map g.hom) ≫
            (H^i).map (Arrow.Hom.right e.hom)) := by
        haveI : IsIso (eleft.hom ≫ ef.hom) := by infer_instance
        rw [← hw]
        simpa [eleft, ef] using (show IsIso (eleft.hom ≫ ef.hom) by infer_instance)
      have heright : eright.hom = (H^i).map (Arrow.Hom.right e.hom) := by
        simpa [eright]
      haveI :
          IsIso ((H^i).map (DerivedCategory.Qh.map g.hom) ≫ eright.hom) := by
        rw [heright]
        exact hcomp
      have hmap : IsIso ((H^i).map (DerivedCategory.Qh.map g.hom)) := by
        exact IsIso.of_isIso_comp_right ((H^i).map (DerivedCategory.Qh.map g.hom)) eright.hom
      rw [← NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh (ModuleCat R) i) g.hom]
      exact hmap
    have hQg : IsIso (DerivedCategory.Qh.map g.hom) :=
      (DerivedCategory.isIso_Qh_map_iff g.hom).2 hq
    haveI : IsIso e.hom := e.isIso_hom
    exact (Arrow.isIso_iff_isIso_of_isIso e.hom).1 hQg

/-- Helper for Lemma 15.66.5: a morphism in `D(R)` is an isomorphism exactly when every cutoff
sees cohomology isomorphisms above the cutoff together with an epimorphism in the cutoff degree. -/
private theorem comparison_iso_iff_forall_homology_upTo
    {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) :
    IsIso f ↔
      ∀ m : ℤ, (∀ i : ℤ, m < i → IsIso ((H^i).map f)) ∧ Epi ((H^m).map f) := by
  -- Proof comment: this is the degreewise conservativity statement for homology in `D(R)`. It is
  -- the clean bridge from the `m`-level criterion to the plain isomorphism criterion.
  constructor
  · intro hf m
    constructor
    · intro i hi
      -- Every cohomology functor preserves isomorphisms.
      exact (derivedCategory_isIso_iff_homology_map_isIso_local (R := R) f).1 hf i
    · -- An isomorphism in degree `m` is in particular an epimorphism.
      letI : IsIso ((H^m).map f) :=
        (derivedCategory_isIso_iff_homology_map_isIso_local (R := R) f).1 hf m
      infer_instance
  · intro h
    -- Evaluating the cutoff condition at `m = i - 1` recovers the degree-`i` isomorphism.
    refine (derivedCategory_isIso_iff_homology_map_isIso_local (R := R) f).2 ?_
    intro i
    exact (h (i - 1)).1 i (by omega)

/-- Helper for Lemma 15.66.5: pseudo-coherence is invariant under isomorphism in `D(R)`. -/
private theorem isPseudoCoherent_of_iso_local
    {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L)
    (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  -- Proof comment: reuse the same bounded-above finite-free witness and postcompose its map by
  -- the target isomorphism.
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.66.5: a derived `R`-complex is pseudo-coherent exactly when it is
`m`-pseudo-coherent for every integer `m`. -/
private theorem isPseudoCoherent_iff_forall_isMPseudoCoherent_local
    (K : DerivedCategory (ModuleCat.{u} R)) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  let E : CochainComplex (ModuleCat.{u} R) ℤ := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hTFAE := cochainComplex_pseudoCoherent_tfae (R := R) E
  have hiffE : E.IsPseudoCoherent ↔ ∀ m : ℤ, E.IsMPseudoCoherent m :=
    hTFAE.out 0 1
  constructor
  · intro hK m
    -- Proof comment: move to a chosen representative where the cochain-level TFAE applies, then
    -- transport the fixed-degree conclusion back to `K`.
    have hQE : (DerivedCategory.Q.obj E).IsPseudoCoherent :=
      isPseudoCoherent_of_iso_local e.symm hK
    have hQEm : (DerivedCategory.Q.obj E).IsMPseudoCoherent m :=
      (hiffE.mp hQE) m
    exact isMPseudoCoherent_of_iso e m hQEm
  · intro hK
    -- Proof comment: pull the degreewise hypotheses back to the chosen representative, apply the
    -- cochain-level characterization, and push the result forward along the comparison
    -- isomorphism.
    have hQEall : ∀ m : ℤ, (DerivedCategory.Q.obj E).IsMPseudoCoherent m := fun m ↦
      isMPseudoCoherent_of_iso e.symm m (hK m)
    have hQE : (DerivedCategory.Q.obj E).IsPseudoCoherent :=
      hiffE.mpr hQEall
    exact isPseudoCoherent_of_iso_local e hQE

/-- Helper for Lemma 15.66.5: a finite free module satisfies the textbook tensor/product
comparison bijection for arbitrary module families. -/
private theorem tensorProduct_piRightHom_bijective_of_module_free_finite
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M]
    {A : Type u} (Q : A → ModuleCat.{u} R) :
    Function.Bijective (TensorProduct.piRightHom R R (↑M) fun a ↦ ↥(Q a)) := by
  -- Proof comment: finite free modules are projective and finite, hence finitely presented, so
  -- Proposition `10.89.3` applies directly to the owner comparison map.
  letI : Module.Projective R M := Module.Projective.of_free
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  have howner :=
    (module_finitePresentation_tfae_tensorProduct_pi_bijective
      (R := R) (M := (↑M))).out 0 1
  exact howner.1 inferInstance A (fun a ↦ ↥(Q a))

/-- Helper for Lemma 15.66.5: the categorical module morphism underlying
`TensorProduct.piRightHom` is an isomorphism for finite free modules. -/
private theorem tensorProduct_piRightHom_isIso_of_module_free_finite
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M]
    {A : Type u} (Q : A → ModuleCat.{u} R) :
    IsIso (ModuleCat.ofHom (TensorProduct.piRightHom R R (↑M) fun a ↦ ↥(Q a))) := by
  -- Proof comment: in `ModuleCat`, a morphism is an isomorphism exactly when the underlying
  -- linear map is bijective.
  have hbij :
      Function.Bijective (TensorProduct.piRightHom R R (↑M) fun a ↦ ↥(Q a)) :=
    tensorProduct_piRightHom_bijective_of_module_free_finite (R := R) M Q
  refine (CategoryTheory.isIso_iff_bijective
      (ModuleCat.ofHom (TensorProduct.piRightHom R R (↑M) fun a ↦ ↥(Q a)))).2 ?_
  simpa using hbij

/-- Helper for Lemma 15.66.5: a finite module satisfies the free-family tensor/product
comparison surjectivity from Proposition `10.89.2`. -/
private theorem tensorProduct_piScalarRightHom_surjective_of_module_finite
    (M : ModuleCat.{u} R) [Module.Finite R M] (A : Type u) :
    Function.Surjective (TensorProduct.piScalarRightHom R R (↑M) A) := by
  -- Proof comment: the free-family clause is exactly the fourth item of Proposition `10.89.2`.
  have howner :=
    (module_finite_tfae_tensorProduct_pi_surjective
      (R := R) (M := (↑M))).out 0 3
  exact howner.1 inferInstance A

/-- Helper for Lemma 15.66.5: the categorical module morphism underlying
`TensorProduct.piScalarRightHom` is an epimorphism for finite modules. -/
private theorem tensorProduct_piScalarRightHom_epi_of_module_finite
    (M : ModuleCat.{u} R) [Module.Finite R M] (A : Type u) :
    Epi (ModuleCat.ofHom (TensorProduct.piScalarRightHom R R (↑M) A)) := by
  -- Proof comment: in `ModuleCat`, epimorphy is exactly surjectivity of the underlying linear
  -- map.
  exact (ModuleCat.epi_iff_surjective _).2
    (tensorProduct_piScalarRightHom_surjective_of_module_finite (R := R) M A)

/-- Helper for Lemma 15.66.5: a degree-zero derived module has no cohomology away from degree
`0`. -/
private theorem single_zero_complex_homology_isZero_of_ne_local
    (M : ModuleCat.{u} R) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((H^i).obj (ModuleCat.single0Functor.obj M)) := by
  -- Proof comment: a degree-zero single object lies in both `D^{≤ 0}` and `D^{≥ 0}`, so every
  -- nonzero cohomology object vanishes by the derived-category `t`-structure bounds.
  by_cases hlt : i < 0
  · exact DerivedCategory.isZero_of_isGE _ 0 i hlt
  · have hgt : 0 < i := by
      omega
    exact DerivedCategory.isZero_of_isLE _ 0 i hgt

/-- Helper for Lemma 15.66.5: the `singleFunctorIsoCompQ` comparison is the identity on zeroth
homology. -/
private theorem homology_map_singleFunctorIsoCompQ_app_zero_eq_id_local
    (M : ModuleCat.{u} R) :
    (H^0).map (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).hom) =
      𝟙 _ := by
  -- Proof comment: in the degree-zero single-complex case this comparison is definitionally the
  -- identity, so the induced map on `H^0` is also the identity.
  change
    (H^0).map
        (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M))) =
      𝟙 _
  simp

/-- Helper for Lemma 15.66.5: if postcomposing a module map with an isomorphism is epi, then the
original map is already epi. -/
private theorem epi_of_epi_comp_iso_local
    {X Y Z : ModuleCat.{u} R} (f : X ⟶ Y) (e : Y ≅ Z) [Epi (f ≫ e.hom)] :
    Epi f := by
  -- Proof comment: postcompose parallel arrows with `e.inv` and cancel the assumed epimorphism
  -- of the composite.
  rw [CategoryTheory.epi_iff_forall_injective]
  intro W
  let hcomp :=
    (CategoryTheory.epi_iff_forall_injective (f ≫ e.hom)).1
      (show Epi (f ≫ e.hom) by infer_instance) W
  intro u v huv
  have huv' : (f ≫ e.hom) ≫ (e.inv ≫ u) = (f ≫ e.hom) ≫ (e.inv ≫ v) := by
    simpa [Category.assoc] using huv
  have heq : e.inv ≫ u = e.inv ≫ v := hcomp huv'
  exact (cancel_epi e.inv).1 heq

/-- Helper for Lemma 15.66.5: postcomposing the universal tensor-object desc map by a morphism
does not change its componentwise description. -/
@[reassoc] private theorem iTensorObj_mapBifunctorDesc_assoc_local
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (n : ℤ) {A B : ModuleCat.{u} R}
    (f : ∀ p q
      (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).obj (L.X q) ⟶ A)
    (u : A ⟶ B) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat.{u} R))
          (c := ComplexShape.up ℤ) (A := A) (j := n) f ≫ u =
      f p q h ≫ u := by
  -- Proof comment: cross the `tensorObj` abbreviation once and then postcompose the owner
  -- universal-property formula.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat.{u} R))
        (c := ComplexShape.up ℤ) (A := A) (j := n) (f := f) p q h)

/-- Helper for Lemma 15.66.5: away from degree `0`, the degree-zero single complex contributes a
zero summand to the tensor totalization. -/
private theorem tensor_single0_off_diagonal_isZero_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (p q : ℤ) (hq : q ≠ 0) :
    IsZero (((curriedTensor (ModuleCat.{u} R)).obj (E.X p)).obj
      (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N).X q)) := by
  -- Proof comment: apply `tensorLeft (E.X p)` to the zero object occurring in the single complex
  -- away from degree `0`.
  exact
    Functor.map_isZero ((curriedTensor (ModuleCat.{u} R)).obj (E.X p))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) N q hq)

/-- Helper for Lemma 15.66.5: in total degree `n`, the surviving diagonal summand of
`E ⊗ N[0]` is the ordinary tensor term `E.X n ⊗ N`. -/
private noncomputable def tensor_single0_diagonal_iso_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (n : ℤ) :
    ((curriedTensor (ModuleCat.{u} R)).obj (E.X n)).obj
      (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N).X 0) ≅
      (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n :=
  Functor.mapIso ((curriedTensor (ModuleCat.{u} R)).obj (E.X n))
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N)

/-- Helper for Lemma 15.66.5: the forward component map for tensoring a cochain complex with a
degree-zero single complex keeps only the unique diagonal summand. -/
private noncomputable def tensor_single0_component_hom_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (n : ℤ) :
    (HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)).X n ⟶
      (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := E)
    (K₂ := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)
    (F := curriedTensor (ModuleCat.{u} R))
    (c := ComplexShape.up ℤ)
    (A := (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n)
    (j := n)
    (fun p q h ↦
      if hq : q = 0 then
        by
          subst hq
          have hp : p = n := by simpa using h
          subst hp
          exact (tensor_single0_diagonal_iso_local (R := R) E N n).hom
      else
        0)

/-- Helper for Lemma 15.66.5: on the surviving diagonal summand, the forward component map is
the canonical tensor identification. -/
@[reassoc] private theorem tensor_single0_component_hom_diag_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj E
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) n 0 n h ≫
      tensor_single0_component_hom_local (R := R) E N n =
        (tensor_single0_diagonal_iso_local (R := R) E N n).hom := by
  let A :
      ModuleCat.{u} R :=
    (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p q
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat.{u} R)).obj (E.X p)).obj
        (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N).X q) ⟶ A :=
    fun p q h' ↦
      if hq : q = 0 then
        by
          subst hq
          have hp : p = n := by simpa using h'
          subst hp
          exact (tensor_single0_diagonal_iso_local (R := R) E N n).hom
      else
        0
  -- Proof comment: evaluate the descended tensor map on the unique surviving `(n, 0)` summand.
  simpa [tensor_single0_component_hom_local, A, f] using
    (iTensorObj_mapBifunctorDesc_assoc_local
      (R := R)
      (K := E)
      (L := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)
      (n := n) (A := A) (B := A) f (𝟙 A) n 0 h)

/-- Helper for Lemma 15.66.5: away from the diagonal summand, the forward component map is zero. -/
@[reassoc] private theorem tensor_single0_component_hom_off_diagonal_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj E
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) p q n h ≫
      tensor_single0_component_hom_local (R := R) E N n =
        0 := by
  let A :
      ModuleCat.{u} R :=
    (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor (ModuleCat.{u} R)).obj (E.X p')).obj
        (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N).X q') ⟶ A :=
    fun p' q' h' ↦
      if hq' : q' = 0 then
        by
          subst hq'
          have hp' : p' = n := by simpa using h'
          subst hp'
          exact (tensor_single0_diagonal_iso_local (R := R) E N n).hom
      else
        0
  -- Proof comment: off the diagonal, the defining branch of the descended map is literally zero.
  simpa [tensor_single0_component_hom_local, A, f, hq] using
    (iTensorObj_mapBifunctorDesc_assoc_local
      (R := R)
      (K := E)
      (L := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)
      (n := n) (A := A) (B := A) f (𝟙 A) p q h)

/-- Helper for Lemma 15.66.5: the inverse component map reinserts the surviving diagonal summand
into the tensor totalization. -/
private noncomputable def tensor_single0_component_inv_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (n : ℤ) :
    (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n ⟶
      (HomologicalComplex.tensorObj E
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)).X n :=
  (tensor_single0_diagonal_iso_local (R := R) E N n).inv ≫
    HomologicalComplex.ιTensorObj E
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) n 0 n
      (by simpa using (show n + 0 = n by simp))

/-- Helper for Lemma 15.66.5: on each degree, the forward and inverse component maps compose to
the identity on the tensor totalization. -/
private theorem tensor_single0_component_hom_inv_id_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (n : ℤ) :
    tensor_single0_component_hom_local (R := R) E N n ≫
        tensor_single0_component_inv_local (R := R) E N n =
      𝟙 _ := by
  -- Proof comment: prove the identity summandwise; only the `(n, 0)` summand survives.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  by_cases hq : q = 0
  · subst hq
    have hp : p = n := by simpa using h
    subst hp
    change
      ((HomologicalComplex.ιTensorObj E
            ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) n 0 n h ≫
          tensor_single0_component_hom_local (R := R) E N n) ≫
        tensor_single0_component_inv_local (R := R) E N n) =
        HomologicalComplex.ιTensorObj E
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) n 0 n h ≫
            𝟙 _
    simpa [tensor_single0_component_inv_local, Category.assoc] using
      congrArg (fun k ↦ k ≫ tensor_single0_component_inv_local (R := R) E N n)
        (tensor_single0_component_hom_diag_local (R := R) E N n h)
  · change
      ((HomologicalComplex.ιTensorObj E
            ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) p q n h ≫
          tensor_single0_component_hom_local (R := R) E N n) ≫
        tensor_single0_component_inv_local (R := R) E N n) =
        HomologicalComplex.ιTensorObj E
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) p q n h ≫
            𝟙 _
    rw [tensor_single0_component_hom_off_diagonal_local (R := R) E N n p q h hq]
    simp only [zero_comp, Category.comp_id]
    symm
    exact (tensor_single0_off_diagonal_isZero_local (R := R) E N p q hq).eq_of_src _ _

/-- Helper for Lemma 15.66.5: on each degree, the inverse and forward component maps compose to
the identity on the right-tensor complex. -/
private theorem tensor_single0_component_inv_hom_id_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (n : ℤ) :
    tensor_single0_component_inv_local (R := R) E N n ≫
        tensor_single0_component_hom_local (R := R) E N n =
      𝟙 _ := by
  let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
    simpa using (show n + 0 = n by simp)
  -- Proof comment: rewrite the middle composite to the diagonal isomorphism and cancel it.
  change
    ((tensor_single0_diagonal_iso_local (R := R) E N n).inv ≫
        HomologicalComplex.ιTensorObj E
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) n 0 n h0) ≫
      tensor_single0_component_hom_local (R := R) E N n =
        𝟙 _
  calc
    ((tensor_single0_diagonal_iso_local (R := R) E N n).inv ≫
        HomologicalComplex.ιTensorObj E
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) n 0 n h0) ≫
      tensor_single0_component_hom_local (R := R) E N n
        = (tensor_single0_diagonal_iso_local (R := R) E N n).inv ≫
            (HomologicalComplex.ιTensorObj E
              ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) n 0 n h0 ≫
                tensor_single0_component_hom_local (R := R) E N n) := by
            simp [Category.assoc]
    _ = (tensor_single0_diagonal_iso_local (R := R) E N n).inv ≫
          (tensor_single0_diagonal_iso_local (R := R) E N n).hom := by
            simpa using
              congrArg
                (fun k ↦ (tensor_single0_diagonal_iso_local (R := R) E N n).inv ≫ k)
                (tensor_single0_component_hom_diag_local (R := R) E N n h0)
    _ = 𝟙 _ := by simp

/-- Helper for Lemma 15.66.5: in each total degree, tensoring with a degree-zero single complex
collapses to the unique surviving diagonal summand. -/
private noncomputable def tensor_single0_component_iso_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (n : ℤ) :
    (HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)).X n ≅
      (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).X n :=
  { hom := tensor_single0_component_hom_local (R := R) E N n
    inv := tensor_single0_component_inv_local (R := R) E N n
    hom_inv_id := tensor_single0_component_hom_inv_id_local (R := R) E N n
    inv_hom_id := tensor_single0_component_inv_hom_id_local (R := R) E N n }

/-- Helper for Lemma 15.66.5: the diagonal tensor identification is natural in the differential
of the left cochain complex. -/
private theorem tensor_single0_diagonal_iso_hom_naturality_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso_local (R := R) E N i).hom ≫
        (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j =
      (((curriedTensor (ModuleCat.{u} R)).map (E.d i j)).app
          (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N).X 0)) ≫
        (tensor_single0_diagonal_iso_local (R := R) E N j).hom := by
  -- Proof comment: the degreewise comparison comes from applying the tensor functor to
  -- `singleObjXSelf`.
  simpa [tensor_single0_diagonal_iso_local, Functor.mapHomologicalComplex_obj_d] using
    (((curriedTensor (ModuleCat.{u} R)).map (E.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N).hom)

/-- Helper for Lemma 15.66.5: the inverse diagonal tensor identification satisfies the same
naturality square rewritten on the inverse side. -/
private theorem tensor_single0_diagonal_iso_inv_naturality_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso_local (R := R) E N i).inv ≫
        (((curriedTensor (ModuleCat.{u} R)).map (E.d i j)).app
          (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N).X 0)) =
      (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j ≫
        (tensor_single0_diagonal_iso_local (R := R) E N j).inv := by
  -- Proof comment: cancel the target diagonal isomorphism and reuse the forward naturality
  -- square.
  apply (cancel_mono (tensor_single0_diagonal_iso_local (R := R) E N j).hom).1
  simpa [Category.assoc] using
    calc
      (tensor_single0_diagonal_iso_local (R := R) E N i).inv ≫
          (((curriedTensor (ModuleCat.{u} R)).map (E.d i j)).app
            (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N).X 0)) ≫
          (tensor_single0_diagonal_iso_local (R := R) E N j).hom
        = (tensor_single0_diagonal_iso_local (R := R) E N i).inv ≫
            ((tensor_single0_diagonal_iso_local (R := R) E N i).hom ≫
              (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j) := by
            rw [tensor_single0_diagonal_iso_hom_naturality_local (R := R) E N i j hij]
      _ = (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j := by
            simp [Category.assoc]

/-- Helper for Lemma 15.66.5: the inverse component comparison already respects the cochain
differential. -/
private theorem tensor_single0_component_inv_comm_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensor_single0_component_inv_local (R := R) E N i ≫
        (HomologicalComplex.tensorObj E
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)).d i j =
      (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d i j ≫
        tensor_single0_component_inv_local (R := R) E N j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Proof comment: expand the tensor differential into its horizontal and vertical pieces; the
  -- vertical part vanishes because the degree-zero single complex has zero outgoing differential.
  simp only [tensor_single0_component_inv_local, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.single_obj_d, Functor.map_zero, comp_zero, add_zero]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := E)
      (K₂ := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)
      (F := curriedTensor (ModuleCat.{u} R))
      (c := ComplexShape.up ℤ)
      (h := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))
      (i₂ := 0)
      (j := i + 1)
      (h' := by simpa using (show (i + 1) + 0 = i + 1 by simp))]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := E)
      (K₂ := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)
      (F := curriedTensor (ModuleCat.{u} R))
      (c := ComplexShape.up ℤ)
      (i₁ := i)
      (h := (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp))
      (j := i + 1)
      (h' := by simpa using (show i + (0 + 1) = i + 1 by simp))]
  have hsingle :
      (((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, zero_comp, smul_zero, comp_zero, add_zero]
  rw [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 by
      rfl, one_smul]
  rw [← Category.assoc]
  rw [tensor_single0_diagonal_iso_inv_naturality_local
      (R := R)
      (E := E)
      (N := N)
      (i := i)
      (j := i + 1)
      (hij := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))]
  simpa [HomologicalComplex.ιTensorObj, Category.assoc]

/-- Helper for Lemma 15.66.5: tensoring a cochain complex with a degree-zero single complex is
canonically the same as tensoring on the right by the underlying module. -/
private noncomputable def tensor_single0_complex_iso_local
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) :
    HomologicalComplex.tensorObj E
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) ≅
      ((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ tensor_single0_component_iso_local (R := R) E N n)
    (fun i j hij ↦ tensor_single0_component_inv_comm_local (R := R) E N i j hij)

/-- Helper for Lemma 15.66.5: right tensoring a degree-zero single complex stays degree-zero. -/
private noncomputable def single0_tensorRight_complex_iso_local
    (M N : ModuleCat.{u} R) :
    ((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
        (ModuleCat.of R (TensorProduct R (↑M) (↑N))) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (tensorRight N) (ComplexShape.up ℤ) (0 : ℤ)).app M

/-- Helper for Lemma 15.66.5: left tensoring a cochain complex by a module is canonically the
tensor object with the degree-zero single complex of that module. -/
private noncomputable def single0_tensorLeft_complex_iso_local
    (S : ModuleCat.{u} R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((tensorLeft S).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      HomologicalComplex.tensorObj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj S) P :=
  ((NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight S) (ComplexShape.up ℤ)).app P) ≪≫
    (tensor_single0_complex_iso_local (R := R) P S).symm ≪≫
      β_ P ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj S)

/-- Helper for Lemma 15.66.5: tensoring two degree-zero single complexes is canonically the
degree-zero single complex of the ordinary module tensor product. -/
private noncomputable def single0_tensor_complex_iso_local
    (M N : ModuleCat.{u} R) :
    HomologicalComplex.tensorObj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M)
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
        (ModuleCat.of R (TensorProduct R (↑M) (↑N))) :=
  tensor_single0_complex_iso_local
      (R := R)
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M)
      N ≪≫
    single0_tensorRight_complex_iso_local (R := R) M N

/-- Helper for Lemma 15.66.5: the derived tensor product of two degree-zero single objects is
canonically the degree-zero single object of the ordinary module tensor product. -/
private noncomputable def single0_derivedTensor_iso_local
    (M N : ModuleCat.{u} R) :
    (ModuleCat.single0Functor.obj M ⊗[R]^L ModuleCat.single0Functor.obj N) ≅
      ModuleCat.single0Functor.obj (ModuleCat.of R (TensorProduct R (↑M) (↑N))) :=
  (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) (0 : ℤ)).app
      (ModuleCat.of R (TensorProduct R (↑M) (↑N)))).symm) ≪≫
    (DerivedCategory.Q.mapIso
      (single0_tensor_complex_iso_local (R := R) M N).symm) ≪≫
      (Functor.Monoidal.μIso
        (DerivedCategory.Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤
          DerivedCategory (ModuleCat.{u} R))
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M)
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj N)).symm ≪≫
          (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) (0 : ℤ)).app M) ⊗ᵢ
            ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) (0 : ℤ)).app N)) ≪≫
            (derivedCategory_tensorObj_iso_derivedTensorProduct
              (ModuleCat.single0Functor.obj M)
              (ModuleCat.single0Functor.obj N)).symm

/-- Helper for Lemma 15.66.5: the ambient tensor/derived-tensor comparison is natural in the left
variable when the right factor is fixed. -/
@[reassoc] private theorem tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit
    (N : DerivedCategory (ModuleCat.{u} R))
    {K L : DerivedCategory (ModuleCat.{u} R)} (f : K ⟶ L) :
    (derivedCategory_tensorObj_iso_derivedTensorProduct K N).hom ≫
        (derivedTensorProduct N).map f =
      (f ▷ N) ≫ (derivedCategory_tensorObj_iso_derivedTensorProduct L N).hom := by
  -- Proof comment: this is exactly the componentwise naturality square of the canonical
  -- fixed-right-factor tensor/derived-tensor comparison.
  simpa using ((tensoringRightIsoDerivedTensorProduct N).hom.naturality f).symm

/-- Helper for Lemma 15.66.5: fixing a cochain complex and tensoring it on the right by a module
defines a functor from `R`-modules to cochain complexes. -/
private noncomputable def tensorRight_complex_functor_local
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj S := ((tensorRight S).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  map f :=
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map f)
      (ComplexShape.up ℤ)).app P
  map_id S := by
    -- Proof comment: on each degree, mapping the identity module map is the identity tensor map.
    ext n
    simp [tensorRight]
  map_comp f g := by
    -- Proof comment: on each degree, right tensoring respects composition strictly.
    ext n
    simp [NatTrans.mapHomologicalComplex_comp]

/-- Helper for Lemma 15.66.5: on degree `n`, mapping a module morphism through the right-tensor
chain functor is the ordinary tensor map with `P.X n` as fixed left factor. -/
private theorem tensorRight_complex_functor_map_component
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (n : ℤ) :
    ((tensorRight_complex_functor_local (R := R) P).map f).f n =
      (tensorLeft (P.X n)).map f := by
  -- Proof comment: evaluating the mapped chain morphism at degree `n` just recovers the degreewise
  -- tensor map.
  simp [tensorRight_complex_functor_local, Functor.mapHomologicalComplex_obj_X]

/-- Helper for Lemma 15.66.5: after evaluating the right-tensor chain comparison in degree `n`
and projecting to the `a`th factor, one obtains the ordinary module tensor/product comparison with
fixed left factor `P.X n`. -/
private theorem tensorRight_complex_piComparison_comp_eval_projection
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    {A : Type u} (Q : A → ModuleCat.{u} R) (n : ℤ) (a : A) :
    (piComparison (tensorRight_complex_functor_local (R := R) P) Q).f n ≫
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
          (Pi.π (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a)) a) =
      (tensorLeft (P.X n)).map (Pi.π Q a) := by
  have h :=
    piComparison_comp_π (tensorRight_complex_functor_local (R := R) P) Q a
  -- Proof comment: compute the `a`th projection in the complex category and then read off its
  -- degree-`n` component.
  change ((piComparison (tensorRight_complex_functor_local (R := R) P) Q) ≫
      Pi.π (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a)) a).f n =
    (tensorLeft (P.X n)).map (Pi.π Q a)
  have hcomp := congrArg (fun f ↦ f.f n) h
  simpa [tensorRight_complex_functor_map_component (R := R) (P := P)] using hcomp

/-- Helper for Lemma 15.66.5: after identifying evaluation with products via
`PreservesProduct.iso`, the degree-`n` right-tensor chain comparison still projects to the ordinary
module tensor/product comparison map. -/
private theorem tensorRight_complex_piComparison_comp_productIso_hom_projection
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    {A : Type u} (Q : A → ModuleCat.{u} R) (n : ℤ) (a : A) :
    (piComparison (tensorRight_complex_functor_local (R := R) P) Q).f n ≫
        (PreservesProduct.iso
          (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)
          (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a))).hom ≫
        Pi.π (fun j => P.X n ⊗ Q j) a =
      (tensorLeft (P.X n)).map (Pi.π Q a) := by
  have heval :
      (PreservesProduct.iso
          (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)
          (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a))).hom ≫
        Pi.π (fun j => P.X n ⊗ Q j) a =
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
        (Pi.π (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a)) a) := by
    -- Proof comment: the product-preservation isomorphism for evaluation is the owner
    -- `piComparison`, so its `a`th projection is the evaluated projection map.
    simpa [PreservesProduct.iso_hom, tensorRight_complex_functor_local,
      Functor.mapHomologicalComplex_obj_X] using
      (piComparison_comp_π
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)
        (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a)) a)
  have hrewrite :
      (piComparison (tensorRight_complex_functor_local (R := R) P) Q).f n ≫
          (PreservesProduct.iso
            (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)
            (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a))).hom ≫
          Pi.π (fun j => P.X n ⊗ Q j) a =
        (piComparison (tensorRight_complex_functor_local (R := R) P) Q).f n ≫
          (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
            (Pi.π (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a)) a) := by
    -- Proof comment: precompose the evaluation-side projection formula with the degree-`n`
    -- comparison component.
    simpa [Category.assoc] using
      congrArg
        (fun g ↦
          (piComparison (tensorRight_complex_functor_local (R := R) P) Q).f n ≫ g)
        heval
  exact hrewrite.trans
    (tensorRight_complex_piComparison_comp_eval_projection (R := R) (P := P) (Q := Q) n a)

/-- Helper for Lemma 15.66.5: after identifying the target product of complexes with the product
of degree-`n` tensor terms, the degree-`n` right-tensor chain comparison is exactly the module
comparison map `TensorProduct.piRightHom` packaged categorically. -/
private theorem tensorRight_complex_piComparison_component_comp_productIso_hom
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    {A : Type u} (Q : A → ModuleCat.{u} R) (n : ℤ) :
    let e := PreservesProduct.iso
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)
      (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a))
    let φ : (P.X n ⊗ ∏ᶜ Q) ⟶ ∏ᶜ fun a : A ↦ P.X n ⊗ Q a :=
      piComparison (tensorLeft (P.X n)) Q
    (piComparison (tensorRight_complex_functor_local (R := R) P) Q).f n ≫ e.hom = φ := by
  dsimp
  apply Limits.Pi.hom_ext
  intro a
  have hproj :
      (piComparison (tensorRight_complex_functor_local (R := R) P) Q).f n ≫
          (PreservesProduct.iso
            (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)
            (fun a : A ↦ (tensorRight_complex_functor_local (R := R) P).obj (Q a))).hom ≫
          Pi.π (fun j => P.X n ⊗ Q j) a =
        (tensorLeft (P.X n)).map (Pi.π Q a) :=
    tensorRight_complex_piComparison_comp_productIso_hom_projection
      (R := R) (P := P) (Q := Q) n a
  have hpi :
      (tensorLeft (P.X n)).map (Pi.π Q a) =
        (piComparison (tensorLeft (P.X n)) Q) ≫ Pi.π (fun j => P.X n ⊗ Q j) a := by
    -- Proof comment: the owner projection formula for the module tensor/product comparison gives
    -- the `a`th projection of the target module map.
    simpa [Category.assoc] using
      (piComparison_comp_π (tensorLeft (P.X n)) Q a).symm
  exact hproj.trans hpi

/-- Helper for Lemma 15.66.5: an `m`-pseudo-coherent bounded-above derived complex satisfies the
cohomological product-comparison condition for arbitrary module families. -/
private theorem isMPseudoCoherent_product_comparison_upTo
    (K : D⁻((ModuleCat.{u} R))) (m : ℤ)
    (hK : K.obj.IsMPseudoCoherent m) :
    ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
      (∀ i : ℤ, m < i →
        IsIso ((H^i).map
          (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q))) ∧
        Epi ((H^m).map
          (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q)) := by
  intro A Q
  -- Route correction: first freeze the source-faithful finite-free model of `K`; the only
  -- remaining gap is the transport from the derived `piComparison` to the ordinary tensor/product
  -- comparison on that model.
  rcases exists_projectiveMinus_finiteFree_approximation_of_isMPseudoCoherent
      (R := R) K.obj m hK with
    ⟨P, hPge, hPfree, hPfinite, α, hαgt, hαm⟩
  -- Proof comment: the forward source proof now reduces to the bounded-above termwise finite-free
  -- model `P`, together with the approximation map `α : Q.obj P ⟶ K.obj`.
  have hterm :
      ∀ n : ℤ,
        IsIso (ModuleCat.ofHom
          (TensorProduct.piRightHom R R
            (((P : CochainComplex (ModuleCat R) ℤ).X n)) fun a ↦ ↥(Q a))) := by
    intro n
    -- Proof comment: each term of the chosen model is finite free, so the ordinary module
    -- comparison is already an isomorphism in degree `n`.
    let _ : Module.Free R (((P : CochainComplex (ModuleCat R) ℤ).X n)) := hPfree n
    let _ : Module.Finite R (((P : CochainComplex (ModuleCat R) ℤ).X n)) := hPfinite n
    simpa using
      (tensorProduct_piRightHom_isIso_of_module_free_finite
        (R := R) (((P : CochainComplex (ModuleCat R) ℤ).X n)) Q)
  -- TODO: transport
  -- `piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct (DerivedCategory.Q.obj
  --   (P : CochainComplex (ModuleCat R) ℤ))) Q`
  -- to the right-tensor chain model `tensorRight_complex_functor_local P`; the projection formulas
  -- above already identify each degree-`n` component with the owner module comparison
  -- `piComparison (tensorLeft (P.X n)) Q`, whose `IsIso` input is exactly `hterm`. The remaining
  -- blocker is the whole-morphism conjugation from the derived owner map to this chain model,
  -- followed by transport across `α` using naturality of `piComparison`.
  sorry

/-- Helper for Lemma 15.66.5: the free-family cohomological product-comparison condition implies
finiteness of the corresponding cohomology module. -/
private theorem free_family_homology_epi_implies_homology_finite
    (K : D⁻((ModuleCat.{u} R))) (i : ℤ)
    (hK : ∀ A : Type u,
      Epi ((H^i).map
        (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
          fun _ : A ↦ ModuleCat.of R R))) :
    Module.Finite R ((H^i).obj K.obj) := by
  -- Proof comment: the remaining source-faithful blocker is the transport from the derived
  -- free-family comparison on `K` to the degree-zero single-complex map identified with
  -- `TensorProduct.piScalarRightHom` on `H^i(K)`.
  -- TODO: transport the assumed epimorphism through `truncLE_step_homologyTriangle`,
  -- `single0_derivedTensor_iso_local`, and the `H⁰(single₀ -)` comparison, then apply
  -- Proposition `10.89.2` backward to `((H^i).obj K.obj)`.
  sorry

/-- Helper for Lemma 15.66.5: the free-family cohomological product-comparison condition implies
`m`-pseudo-coherence for a bounded-above derived complex. -/
private theorem free_family_product_comparison_upTo_implies_isMPseudoCoherent
    (K : D⁻((ModuleCat.{u} R))) (m : ℤ)
    (hK : ∀ A : Type u,
      (∀ i : ℤ, m < i →
        IsIso ((H^i).map
          (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
            fun _ : A ↦ ModuleCat.of R R))) ∧
        Epi ((H^m).map
          (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
            fun _ : A ↦ ModuleCat.of R R))) :
    K.obj.IsMPseudoCoherent m := by
  -- Route correction: reduce the converse to the bounded-above homology-finiteness criterion, so
  -- the only remaining gap is the degreewise transport from the derived free-family comparison to
  -- the module-level `TensorProduct.piScalarRightHom` map on `H^i(K)`.
  rw [isMPseudoCoherent_iff_boundedAbove_and_homology_finite_ge]
  constructor
  · -- Proof comment: `K : D⁻(R)` already packages the bounded-above hypothesis.
    exact K.2
  · intro i hi
    -- Proof comment: for each degree `i ≥ m`, the assumed comparison is epi in degree `m` and an
    -- isomorphism above `m`; either way we obtain the epimorphism needed by the finiteness
    -- transport helper.
    apply free_family_homology_epi_implies_homology_finite (R := R) (K := K) (i := i)
    intro A
    by_cases him : i = m
    · subst him
      exact (hK A).2
    · have hm : m < i := by
        omega
      let _ : IsIso ((H^i).map
          (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
            fun _ : A ↦ ModuleCat.of R R)) := (hK A).1 i hm
      infer_instance

/-- Helper for Lemma 15.66.5: a pseudo-coherent bounded-above derived complex preserves products
under derived tensoring with arbitrary module families. -/
private theorem isPseudoCoherent_product_comparison
    (K : D⁻((ModuleCat.{u} R)))
    (hK : K.obj.IsPseudoCoherent) :
    ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
      IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q) := by
  intro A Q
  -- Proof comment: the plain comparison is an isomorphism once every cutoff sees the source
  -- `m`-pseudo-coherent criterion. Pseudo-coherence supplies those fixed-degree hypotheses for all
  -- integers `m`.
  refine (comparison_iso_iff_forall_homology_upTo (R := R) ?_).2 ?_
  intro m
  -- Proof comment: specialize the global pseudo-coherence bridge at the chosen cutoff and apply
  -- the fixed-`m` comparison theorem already isolated above.
  exact isMPseudoCoherent_product_comparison_upTo K m
    ((isPseudoCoherent_iff_forall_isMPseudoCoherent_local (R := R) K.obj).1 hK m) Q

/-- Helper for Lemma 15.66.5: the free-family product-comparison isomorphism implies
pseudo-coherence for a bounded-above derived complex. -/
private theorem free_family_product_comparison_implies_isPseudoCoherent
    (K : D⁻((ModuleCat.{u} R)))
    (hK : ∀ A : Type u,
      IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
        fun _ : A ↦ ModuleCat.of R R)) :
    K.obj.IsPseudoCoherent := by
  -- Proof comment: reduce pseudo-coherence to the fixed-degree criterion for every `m`, then
  -- extract the needed cutoff condition from the assumed isomorphism by homology detection.
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent_local]
  intro m
  apply free_family_product_comparison_upTo_implies_isMPseudoCoherent
  intro A
  -- Proof comment: the assumed free-family isomorphism gives the required degreewise
  -- isomorphisms and the degree-`m` epimorphism through the comparison/isomorphism bridge.
  exact (comparison_iso_iff_forall_homology_upTo (R := R)
    (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
      fun _ : A ↦ ModuleCat.of R R)).1 (hK A) m

-- Proof sketch: represent `K` by a bounded-above termwise finite free complex, compute derived
-- tensor products by ordinary tensor products with that complex, and use Algebra,
-- Proposition `10.89.3` together with the description of products in `D(R)` to identify the
-- three product-preservation conditions.
/-- Commutative-ring specialization of Stacks Lemma 15.66.5 (1): for a bounded-above derived
`R`-complex `K`, the following are equivalent: `K` is pseudo-coherent; for every family of
`R`-modules the canonical product comparison for `Q ↦ Q[0] ⊗_R^{\mathbf L} K` is an isomorphism;
the same holds for constant families; and the same holds for free families `R^A`. -/
theorem boundedAbove_isPseudoCoherent_tfae_derivedTensorProduct_preservesProducts
    (K : D⁻((ModuleCat.{u} R))) :
    List.TFAE [
      K.obj.IsPseudoCoherent,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
        IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) fun _ : A ↦ Q),
      ∀ A : Type u,
        IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
          fun _ : A ↦ ModuleCat.of R R)
    ] := by
  tfae_have 1 → 2 := by
    intro hK A Q
    -- Proof comment: this is the finite-free-model computation from the source proof.
    exact isPseudoCoherent_product_comparison K hK Q
  tfae_have 2 → 3 := by
    intro h Q A
    -- Proof comment: specialize the arbitrary-family clause to a constant family.
    simpa using h (fun _ : A ↦ Q)
  tfae_have 3 → 4 := by
    intro h A
    -- Proof comment: specialize the constant-family clause to the free module `R`.
    simpa using h (ModuleCat.of R R) A
  tfae_have 4 → 1 := by
    intro hK
    -- Proof comment: this is the source-proof converse, isolated as a dedicated helper.
    exact free_family_product_comparison_implies_isPseudoCoherent K hK
  tfae_finish

-- Proof sketch: the forward implications are obtained from the pseudo-coherent finite free model
-- as above. For the converse, apply the free-family criterion to the top nonvanishing cohomology
-- module, deduce finiteness from Algebra, Proposition `10.89.2`, kill that cohomology by a finite
-- free complex, and conclude by induction using Lemmas `15.65.2` and `15.65.5`.
/-- Commutative-ring specialization of Stacks Lemma 15.66.5 (2): given `m ∈ ℤ` and a bounded-
above derived `R`-complex `K`, the following are equivalent: `K` is `m`-pseudo-coherent; for
every family of `R`-modules the canonical product comparison for `Q ↦ Q[0] ⊗_R^{\mathbf L} K`
induces cohomology isomorphisms in degrees `> m` and an epimorphism in degree `m`; the same
holds for constant families; and the same holds for free families `R^A`. -/
theorem boundedAbove_isMPseudoCoherent_tfae_derivedTensorProduct_preservesProductsUpTo
    (K : D⁻((ModuleCat.{u} R))) (m : ℤ) :
    List.TFAE [
      K.obj.IsMPseudoCoherent m,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
        (∀ i : ℤ, m < i →
          IsIso ((H^i).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q))) ∧
          Epi ((H^m).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q)),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        (∀ i : ℤ, m < i →
          IsIso ((H^i).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ Q))) ∧
          Epi ((H^m).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ Q)),
      ∀ A : Type u,
        (∀ i : ℤ, m < i →
          IsIso ((H^i).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ ModuleCat.of R R))) ∧
          Epi ((H^m).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ ModuleCat.of R R))
    ] := by
  tfae_have 1 → 2 := by
    intro hK A Q
    -- Proof comment: this is the finite-free-model direction from the source proof.
    exact isMPseudoCoherent_product_comparison_upTo K m hK Q
  tfae_have 2 → 3 := by
    intro h Q A
    -- Proof comment: specialize the arbitrary-family clause to a constant family.
    simpa using h (fun _ : A ↦ Q)
  tfae_have 3 → 4 := by
    intro h A
    -- Proof comment: specialize the constant-family clause to the free module `R`.
    simpa using h (ModuleCat.of R R) A
  tfae_have 4 → 1 := by
    intro hK
    -- Proof comment: this is the source-proof induction on the top nonvanishing cohomology
    -- degree, isolated as a dedicated helper.
    exact free_family_product_comparison_upTo_implies_isMPseudoCoherent K m hK
  tfae_finish

end

end CategoryTheory
