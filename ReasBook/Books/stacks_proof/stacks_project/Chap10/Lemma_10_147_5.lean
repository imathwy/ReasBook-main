import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_3
import stacks_proof.stacks_project.Chap10.Lemma_10_127_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MorphismProperty

universe u v

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/- Domain-style sampling for Lemma 10.147.5:
* primary domain: filtered colimits of smooth commutative ring maps;
* sampled owner declarations:
  - `RingHom.Smooth`, the mathlib owner for smooth ring homomorphisms;
  - `RingHom.toMorphismProperty`, the canonical bridge from a ring-hom property to
    `CommRingCat`;
  - `CategoryTheory.MorphismProperty.ind`, the canonical filtered-colimit owner;
  - `RingHom.IsFilteredColimitOfEtale`, the project's source-facing wrapper for the analogous
    filtered-colimit-of-etale property.
* best owner abstraction: `RingHom.IsFilteredColimitOfSmooth` as the source-facing owner, with
  core/canonical content given by `ind (toMorphismProperty RingHom.Smooth)`;
* primitive data: only the ring map `f : R →+* A`;
* derived API: any chosen filtered diagram, cocone, and comparison isomorphism presenting `f` as
  a filtered colimit of smooth algebras.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsFilteredColimitOfSmooth`;
* `core/canonical`: `ind (toMorphismProperty RingHom.Smooth)`;
* `bridge/view`: the hidden same-universe `ULift` presentation of `f` used to speak to
  `CategoryTheory.MorphismProperty.ind`.

The old local `CommRingCat.smooth` abbreviation duplicated the canonical owner
`RingHom.Smooth` and its bridge `RingHom.toMorphismProperty`, so this file now exposes the
filtered-colimit hypothesis through the ring-hom owner instead.
-/

/-- An `R`-algebra map `f : R →+* A` is a filtered colimit of smooth `R`-algebras. This thin
source-facing wrapper hides the same-universe `ULift` bookkeeping needed to express the canonical
owner `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.Smooth)`. -/
abbrev IsFilteredColimitOfSmooth (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty Smooth)
    (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift A)))

/-- Helper for Chap10 Lemma 10 147 5: forget a commutative ring under a fixed base to its
underlying module over that base. -/
private abbrev underForgetToModule (R : CommRingCat.{u}) : Under R ⥤ ModuleCat R where
  obj A := ModuleCat.of R A.right
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap

/-- Helper for Chap10 Lemma 10 147 5: an object under a commutative ring carries the module
structure induced by its structure map. -/
private instance underModule (R : Type u) [CommRing R] (A : Under (CommRingCat.of R)) :
    Module R A.right := by
  let _ : Algebra R A.right := A.hom.hom.toAlgebra
  infer_instance

/-- Helper for Chap10 Lemma 10 147 5: a filtered colimit in the under-category is flat over the
base whenever every stage is flat over the base. -/
private theorem underColimit_flat_of_stagewise_flat {R : Type u} [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat R (F.obj j).right] :
    Module.Flat R c.pt.right := by
  let cM := (underForgetToModule (CommRingCat.of R)).mapCocone c
  letI : ∀ j, Module.Flat R ((F ⋙ underForgetToModule (CommRingCat.of R)).obj j) :=
    fun j ↦ by
      -- The module diagram is obtained by forgetting the same under-category objects.
      simpa [underForgetToModule] using (inferInstance : Module.Flat R (F.obj j).right)
  have hcM : IsColimit cM := by
    -- Forget to additive groups, where the relevant filtered colimit is preserved, then reflect
    -- the colimit back to `ModuleCat`.
    apply isColimitOfReflects (forget₂ (ModuleCat R) AddCommGrpCat)
    simpa [underForgetToModule] using
      (isColimitOfPreserves
        (CategoryTheory.Under.forget (CommRingCat.of R) ⋙
          forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) hc)
  -- Apply the earlier filtered-colimit flatness theorem for module diagrams.
  simpa [cM] using
    flat_of_isColimit_filtered_system
      (F := F ⋙ underForgetToModule (CommRingCat.of R)) cM hcM

/-- Helper for Chap10 Lemma 10 147 5: a filtered colimit of smooth ring maps is flat. -/
private theorem isFilteredColimitOfSmooth_flat {f : R →+* A}
    (h : f.IsFilteredColimitOfSmooth) :
    f.Flat := by
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  -- Unpack the hidden `ind` presentation as a filtered colimit in the under-category over
  -- `ULift R`.
  have hUnder :
      ObjectProperty.ind.{max u v, max u v, max u v + 1}
        (RingHom.toMorphismProperty RingHom.Smooth).underObj
        (Under.mk (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift A)))) := by
    rw [← MorphismProperty.ind_iff_ind_underMk]
    simpa [RingHom.IsFilteredColimitOfSmooth] using h
  rcases hUnder with ⟨J, _, _, pres, hpres⟩
  letI : ∀ j, Module.Flat (ULift.{v} R) (pres.diag.obj j).right :=
    fun j ↦ by
      let _ : Algebra (ULift.{v} R) (pres.diag.obj j).right :=
        (pres.diag.obj j).hom.hom.toAlgebra
      have hsmooth : (pres.diag.obj j).hom.hom.Smooth := by
        -- Each stage map in the under-presentation is smooth by construction.
        simpa [RingHom.toMorphismProperty] using hpres j
      have hflatMap :
          (algebraMap (ULift.{v} R) (pres.diag.obj j).right).Flat := by
        simpa [RingHom.algebraMap_toAlgebra] using hsmooth.flat
      exact RingHom.flat_algebraMap_iff.mp hflatMap
  have hflatULift : Module.Flat (ULift.{v} R) (ULift A) := by
    -- Stagewise smoothness gives stagewise flatness, and filtered colimits preserve flatness.
    simpa using
      underColimit_flat_of_stagewise_flat
        (R := ULift.{v} R) pres.diag pres.cocone pres.isColimit
  have hflatUp : (algebraMap (ULift.{v} R) (ULift A)).Flat :=
    RingHom.flat_algebraMap_iff.mpr hflatULift
  have hsource :
      ((ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).bijective
  have htarget :
      ((ULift.ringEquiv : ULift A ≃+* A).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv : ULift A ≃+* A).bijective
  have hcomp :
      (((ULift.ringEquiv : ULift A ≃+* A).toRingHom).comp
        ((algebraMap (ULift.{v} R) (ULift A)).comp
          ((ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom))).Flat := by
    -- Flatness is stable under the two canonical `ULift` equivalences and the lifted map.
    exact RingHom.Flat.comp (RingHom.Flat.comp hsource hflatUp) htarget
  have hEq :
      ((ULift.ringEquiv : ULift A ≃+* A).toRingHom).comp
        ((algebraMap (ULift.{v} R) (ULift A)).comp
          ((ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom)) = f := by
    ext x
    rfl
  rw [← hEq]
  exact hcomp

end

end RingHom

namespace TensorProduct

section

variable {R S : Type u} {B : Type v}
variable [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B]

/-- Helper for Chap10 Lemma 10 147 5: the module universe-lift functor preserves filtered
colimits of the stage shape used in the mixed-universe tensor descent. -/
private theorem moduleCat_uliftFunctor_preservesColimitsOfShape
    {J : Type u} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{v, u} R) := by
  -- Reflect preservation through the forgetful functor to additive groups; after forgetting,
  -- the module lift is exactly the additive-group `ULift` functor.
  haveI : PreservesColimitsOfShape J
      (ModuleCat.uliftFunctor.{v, u} R ⋙
        forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) := by
    change PreservesColimitsOfShape J
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ⋙ AddCommGrpCat.uliftFunctor.{v, u})
    infer_instance
  -- The forgetful functor from modules to additive groups reflects colimits, so preservation of
  -- the composite gives preservation by the lifted module functor itself.
  apply preservesColimitsOfShape_of_reflects_of_preserves (ModuleCat.uliftFunctor.{v, u} R)
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

/-- Helper for Chap10 Lemma 10 147 5: at each smooth stage of an ind-smooth presentation,
the integral-closure comparison map is bijective. -/
private theorem toIntegralClosure_bijective_of_smoothStage
    (hS : RingHom.Smooth (algebraMap R S)) :
    Function.Bijective (toIntegralClosure R S B) := by
  -- Convert the ring-hom smoothness carried by the presentation into the algebraic typeclass
  -- form expected by Mathlib's smooth base-change theorem.
  have hSmooth : Algebra.Smooth R S := RingHom.smooth_algebraMap.mp hS
  exact TensorProduct.toIntegralClosure_bijective_of_smooth

/-- Helper for Chap10 Lemma 10 147 5: the comparison map is injective for an ind-smooth base
change because such base changes are flat. -/
private theorem toIntegralClosure_injective_of_isFilteredColimitOfSmooth
    (hS : (algebraMap R S).IsFilteredColimitOfSmooth) :
    Function.Injective (toIntegralClosure R S B) := by
  have hflatMap : (algebraMap R S).Flat :=
    RingHom.isFilteredColimitOfSmooth_flat hS
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflatMap
  -- Mathlib already proves injectivity of the comparison map under flat base change.
  exact TensorProduct.toIntegralClosure_injective_of_flat

/-- Helper for Chap10 Lemma 10 147 5: adjoin membership of every integral tensor element
implies surjectivity of the integral-closure comparison map. -/
private theorem toIntegralClosure_surjective_of_mem_adjoin_mapIntegralClosure
    (hmem : ∀ {x : S ⊗[R] B}, IsIntegral S x →
      x ∈ Algebra.adjoin S
        ((integralClosure R B).map Algebra.TensorProduct.includeRight :
          Subalgebra R (S ⊗[R] B))) :
    Function.Surjective (toIntegralClosure R S B) := by
  -- Reduce a target subtype element to membership of its underlying tensor element in the
  -- range of the underlying tensor-product map.
  rintro ⟨x, hx⟩
  simp only [toIntegralClosure, Subtype.ext_iff, AlgHom.coe_codRestrict, ← AlgHom.mem_range]
  -- The range contains the `S`-algebra generated by the images of elements integral over `R`.
  refine Algebra.adjoin_le ?_ (hmem hx)
  rintro _ ⟨y, hy, rfl⟩
  -- Each generator is hit by the pure tensor `1 ⊗ y`.
  let yIntegral : integralClosure R B := ⟨y, hy⟩
  refine ⟨1 ⊗ₜ yIntegral, ?_⟩
  simp [yIntegral]

/-- Helper for Chap10 Lemma 10 147 5: the underlying tensor element of any comparison-map
value already lies in the subalgebra generated by the base integral closure. -/
private theorem toIntegralClosure_apply_mem_adjoin
    (z : S ⊗[R] integralClosure R B) :
    ((toIntegralClosure R S B z : integralClosure S (S ⊗[R] B)) : S ⊗[R] B) ∈
      Algebra.adjoin S
        ((integralClosure R B).map Algebra.TensorProduct.includeRight :
          Subalgebra R (S ⊗[R] B)) := by
  -- Prove the range containment on pure tensors and extend it additively across the tensor
  -- product presentation.
  induction z with
  | zero => simp
  | add x y hx hy =>
      rw [map_add]
      exact Subalgebra.add_mem _ hx hy
  | tmul s y =>
      -- A pure tensor maps to an `S`-multiple of a generator coming from `integralClosure R B`.
      have hygen : (Algebra.TensorProduct.includeRight y : S ⊗[R] B) ∈
          Algebra.adjoin S
            ((integralClosure R B).map Algebra.TensorProduct.includeRight :
              Subalgebra R (S ⊗[R] B)) := by
        exact Algebra.subset_adjoin ⟨y, y.2, rfl⟩
      convert (Algebra.adjoin S
        ((integralClosure R B).map Algebra.TensorProduct.includeRight :
          Subalgebra R (S ⊗[R] B))).smul_mem hygen s using 1
      simp [TensorProduct.toIntegralClosure, smul_tmul']

/-- Helper for Chap10 Lemma 10 147 5: at a smooth stage, every integral tensor element is in the
subalgebra generated by the base integral closure. -/
private theorem stageIntegralTensor_mem_adjoin_of_smooth
    (hS : RingHom.Smooth (algebraMap R S))
    {x : S ⊗[R] B} (hx : IsIntegral S x) :
    x ∈ Algebra.adjoin S
      ((integralClosure R B).map Algebra.TensorProduct.includeRight :
        Subalgebra R (S ⊗[R] B)) := by
  -- Use smooth-stage bijectivity to lift the integral element to the comparison-map source.
  obtain ⟨z, hz⟩ :=
    (toIntegralClosure_bijective_of_smoothStage (R := R) (S := S) (B := B) hS).2 ⟨x, hx⟩
  -- The previous helper identifies the underlying lifted image with an element of the generated
  -- subalgebra, and `hz` rewrites that image back to `x`.
  simpa [hz] using toIntegralClosure_apply_mem_adjoin (R := R) (S := S) (B := B) z

/-- Helper for Chap10 Lemma 10 147 5: adjoin membership at a stage maps to adjoin membership
in the filtered colimit tensor product. -/
private theorem map_stageAdjoin_mem_colimitAdjoin
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [HasColimit F]
    (j : J) {xj : (F.obj j) ⊗[R] B}
    (hxj : xj ∈ Algebra.adjoin (F.obj j)
      ((integralClosure R B).map Algebra.TensorProduct.includeRight :
        Subalgebra R ((F.obj j) ⊗[R] B))) :
    (Algebra.TensorProduct.map (colimit.ι F j).hom (AlgHom.id R B) xj) ∈
      Algebra.adjoin ↑(colimit F)
        ((integralClosure R B).map Algebra.TensorProduct.includeRight :
          Subalgebra R (↑(colimit F) ⊗[R] B)) := by
  -- Keep the target subalgebra and stage map named so the induction only transports the
  -- algebra-generation proof, not the surrounding colimit definitions.
  let stageGens : Set ((F.obj j) ⊗[R] B) :=
    ((integralClosure R B).map Algebra.TensorProduct.includeRight :
      Subalgebra R ((F.obj j) ⊗[R] B))
  let targetGens : Set (↑(colimit F) ⊗[R] B) :=
    ((integralClosure R B).map Algebra.TensorProduct.includeRight :
      Subalgebra R (↑(colimit F) ⊗[R] B))
  let target : Subalgebra ↑(colimit F) (↑(colimit F) ⊗[R] B) :=
    Algebra.adjoin ↑(colimit F) targetGens
  let φ := Algebra.TensorProduct.map (colimit.ι F j).hom (AlgHom.id R B)
  change xj ∈ Algebra.adjoin (F.obj j) stageGens at hxj
  change φ xj ∈ target
  -- Induct through the stage adjoin. Generators are fixed by the left tensor map, and scalar
  -- elements land in the target because it is a `colimit F`-subalgebra.
  refine Algebra.adjoin_induction
    (s := stageGens)
    (p := fun y _ ↦ φ y ∈ target) ?hgen ?halg ?hadd ?hmul hxj
  · rintro y ⟨z, hz, rfl⟩
    exact Algebra.subset_adjoin ⟨z, hz, by simp [φ]⟩
  · intro r
    simpa [φ, target] using target.algebraMap_mem ((colimit.ι F j).hom r)
  · intro y z hy hz hφy hφz
    simpa [φ] using target.add_mem hφy hφz
  · intro y z hy hz hφy hφz
    simpa [φ] using target.mul_mem hφy hφz

/-- Helper for Chap10 Lemma 10 147 5: finitely many elements of a filtered algebra colimit can
be represented at one common stage. -/
private theorem commAlgColimit_finset_lifts
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [HasColimit F]
    (s : Finset ↑(colimit F)) :
    ∃ (j : J) (repr : ↑(colimit F) → ↑(F.obj j)),
      ∀ x ∈ s, x = (colimit.ι F j).hom (repr x) := by
  classical
  refine Finset.induction_on s ?hempty ?hinsert
  · refine ⟨IsFiltered.nonempty.some, fun _ ↦ 0, ?_⟩
    -- The empty finite set imposes no representation conditions.
    intro x hx
    exact False.elim (Finset.notMem_empty x hx)
  · intro a s ha hs
    obtain ⟨j, repr, hrepr⟩ := hs
    obtain ⟨ja, aj, haj⟩ := commAlgCat_colimit_jointly_surjective (A := R) (J := J) F a
    let k := IsFiltered.max ja j
    let fa : ja ⟶ k := IsFiltered.leftToMax ja j
    let fj : j ⟶ k := IsFiltered.rightToMax ja j
    refine ⟨k,
      (fun x ↦ if x = a then (F.map fa).hom aj else (F.map fj).hom (repr x)), ?_⟩
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · have hmove :
          (colimit.ι F k).hom ((F.map fa).hom aj) = (colimit.ι F ja).hom aj := by
        -- Naturality of the colimit cocone moves the representative of the new element forward.
        change (colimit.ι F k).hom ((F.map fa).hom aj) = (colimit.ι F ja).hom aj
        simpa [fa, k] using ConcreteCategory.congr_hom ((colimit.cocone F).w fa) aj
      simpa using haj.trans hmove.symm
    · have hne : x ≠ a := by
        intro hxa
        exact ha (hxa ▸ hx)
      have hmove :
          (colimit.ι F k).hom ((F.map fj).hom (repr x)) =
            (colimit.ι F j).hom (repr x) := by
        -- Existing representatives are transported to the same common upper stage.
        change (colimit.ι F k).hom ((F.map fj).hom (repr x)) =
          (colimit.ι F j).hom (repr x)
        simpa [fj, k] using ConcreteCategory.congr_hom ((colimit.cocone F).w fj) (repr x)
      simpa [hne] using (hrepr x hx).trans hmove.symm

/-- Helper for Chap10 Lemma 10 147 5: a monic polynomial over a filtered algebra colimit lifts
to a monic polynomial over one finite stage. -/
private theorem commAlgColimit_monicPolynomial_lifts
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [HasColimit F]
    (p : Polynomial ↑(colimit F)) (hp : p.Monic) :
    ∃ (j : J) (pj : Polynomial (F.obj j)),
      pj.Monic ∧ Polynomial.map (colimit.ι F j).hom.toRingHom pj = p := by
  classical
  let coeffs : Finset ↑(colimit F) := p.support.image p.coeff
  obtain ⟨j, repr, hrepr⟩ := commAlgColimit_finset_lifts (F := F) coeffs
  have hlifts : p ∈ Polynomial.lifts (colimit.ι F j).hom.toRingHom := by
    -- Coefficients on the support use the common-stage representatives; outside the support they
    -- lift from zero.
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ p.support
    · refine ⟨repr (p.coeff n), ?_⟩
      exact (hrepr (p.coeff n) (Finset.mem_image.mpr ⟨n, hn, rfl⟩)).symm
    · refine ⟨0, ?_⟩
      rw [map_zero, Polynomial.notMem_support_iff.mp hn]
  obtain ⟨pj, hpjmap, _, hpjmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  refine ⟨j, pj, hpjmonic, ?_⟩
  simpa using hpjmap

/-- Helper for Chap10 Lemma 10 147 5: tensor commutativity conjugates a map on the left factor
to the corresponding map on the right factor. -/
private theorem tensorComm_map_left_eq_map_right
    {A A' C : Type*} [CommRing A] [CommRing A'] [CommRing C]
    [Algebra R A] [Algebra R A'] [Algebra R C]
    (f : A →ₐ[R] A') (x : A ⊗[R] C) :
    Algebra.TensorProduct.map (AlgHom.id R C) f ((Algebra.TensorProduct.comm R A C) x) =
      (Algebra.TensorProduct.comm R A' C)
        (Algebra.TensorProduct.map f (AlgHom.id R C) x) := by
  -- Prove the compatibility on the tensor generators, then extend additively over the tensor
  -- product presentation.
  refine TensorProduct.induction_on x ?hzero ?htmul ?hadd
  · simp
  · intro a c
    simp
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 147 5: for same-universe right tensor factors, every element
of the left-oriented tensor product over a filtered algebra colimit comes from a stage. -/
private theorem leftTensor_stage_lift_sameUniverse
    {B₀ : Type u} [CommRing B₀] [Algebra R B₀]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [HasColimit F]
    (x : ↑(colimit F) ⊗[R] B₀) :
    ∃ (j : J) (xj : (F.obj j) ⊗[R] B₀),
      Algebra.TensorProduct.map (colimit.ι F j).hom (AlgHom.id R B₀) xj = x := by
  -- Use the already proved right-oriented tensor colimit, then commute the tensor factors back
  -- to the left-oriented form used by the integral-descent statement.
  let xr := (Algebra.TensorProduct.comm R ↑(colimit F) B₀) x
  let rightCocone := tensor_base_change_cocone (A := R) (J := J) F B₀
  have htypes : IsColimit ((forget CommRingCat).mapCocone rightCocone) := by
    -- The imported base-change cocone is colimiting after forgetting to types.
    exact isColimitOfPreserves (forget CommRingCat)
      (tensor_base_change_cocone_isColimit (A := R) (J := J) F B₀)
  obtain ⟨j, xrj, hxrj⟩ := Types.jointly_surjective_of_isColimit htypes xr
  refine ⟨j, (Algebra.TensorProduct.comm R B₀ (F.obj j)) xrj, ?_⟩
  -- The commutativity compatibility helper identifies the stage leg after commuting factors.
  have hcommStage :
      (Algebra.TensorProduct.comm R (F.obj j) B₀)
        ((Algebra.TensorProduct.comm R B₀ (F.obj j)) xrj) = xrj := by
    exact (Algebra.TensorProduct.comm R (F.obj j) B₀).apply_symm_apply xrj
  apply (Algebra.TensorProduct.comm R ↑(colimit F) B₀).injective
  rw [← tensorComm_map_left_eq_map_right]
  rw [hcommStage]
  simpa [rightCocone, tensor_base_change_diagram, xr] using hxrj

/-- Helper for Chap10 Lemma 10 147 5: for same-universe right tensor factors, equality after
mapping to the filtered colimit descends to some later stage. -/
private theorem leftTensor_stage_eq_stabilizes_sameUniverse
    {B₀ : Type u} [CommRing B₀] [Algebra R B₀]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [HasColimit F]
    {j0 : J} {x y : (F.obj j0) ⊗[R] B₀}
    (hxy : Algebra.TensorProduct.map (colimit.ι F j0).hom (AlgHom.id R B₀) x =
      Algebra.TensorProduct.map (colimit.ι F j0).hom (AlgHom.id R B₀) y) :
    ∃ (j : J) (f : j0 ⟶ j),
      Algebra.TensorProduct.map (F.map f).hom (AlgHom.id R B₀) x =
        Algebra.TensorProduct.map (F.map f).hom (AlgHom.id R B₀) y := by
  -- Commute the left-oriented tensors into the right-oriented tensor-colimit cocone supplied by
  -- Lemma 10.127.7.
  let xr := (Algebra.TensorProduct.comm R (F.obj j0) B₀) x
  let yr := (Algebra.TensorProduct.comm R (F.obj j0) B₀) y
  let rightCocone := tensor_base_change_cocone (A := R) (J := J) F B₀
  have hright :
      Algebra.TensorProduct.map (AlgHom.id R B₀) (colimit.ι F j0).hom xr =
        Algebra.TensorProduct.map (AlgHom.id R B₀) (colimit.ι F j0).hom yr := by
    rw [tensorComm_map_left_eq_map_right, tensorComm_map_left_eq_map_right, hxy]
  have htypes : IsColimit ((forget CommRingCat).mapCocone rightCocone) := by
    -- The imported cocone is colimiting in commutative rings after forgetting.
    exact isColimitOfPreserves (forget CommRingCat)
      (tensor_base_change_cocone_isColimit (A := R) (J := J) F B₀)
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' htypes xr yr).mp hright
  refine ⟨j, f, ?_⟩
  have hstageRight :
      Algebra.TensorProduct.map (AlgHom.id R B₀) (F.map f).hom xr =
        Algebra.TensorProduct.map (AlgHom.id R B₀) (F.map f).hom yr := by
    -- Translate the equality criterion back from the forgotten cocone to the explicit tensor map.
    simpa [rightCocone, tensor_base_change_diagram, xr, yr] using hf
  -- Commute back to the original left-oriented tensor products.
  apply (Algebra.TensorProduct.comm R (F.obj j) B₀).injective
  rw [← tensorComm_map_left_eq_map_right, ← tensorComm_map_left_eq_map_right]
  exact hstageRight

/-- Helper for Chap10 Lemma 10 147 5: for same-universe right tensor factors, one polynomial
root equation over the filtered colimit descends to a later stage. -/
private theorem leftTensor_aeval_zero_stabilizes_sameUniverse
    {B₀ : Type u} [CommRing B₀] [Algebra R B₀]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [HasColimit F]
    {j0 : J} (p : Polynomial (F.obj j0)) (x : (F.obj j0) ⊗[R] B₀)
    (hroot : Polynomial.aeval
        (Algebra.TensorProduct.map (colimit.ι F j0).hom (AlgHom.id R B₀) x)
        (Polynomial.map (colimit.ι F j0).hom.toRingHom p) = 0) :
    ∃ (j : J) (f : j0 ⟶ j),
      Polynomial.aeval
        (Algebra.TensorProduct.map (F.map f).hom (AlgHom.id R B₀) x)
        (Polynomial.map (F.map f).hom.toRingHom p) = 0 := by
  have hmapRoot :
      Algebra.TensorProduct.map (colimit.ι F j0).hom (AlgHom.id R B₀)
          (Polynomial.aeval x p) = 0 := by
    -- Rewrite the image of the stage evaluation as evaluation after mapping coefficients and the
    -- root to the colimit tensor product.
    calc
      Algebra.TensorProduct.map (colimit.ι F j0).hom (AlgHom.id R B₀)
          (Polynomial.aeval x p) =
          Polynomial.aeval
            (Algebra.TensorProduct.map (colimit.ι F j0).hom (AlgHom.id R B₀) x)
            (Polynomial.map (colimit.ι F j0).hom.toRingHom p) := by
            exact Polynomial.map_aeval_eq_aeval_map (by
              ext r
              simp) p x
      _ = 0 := hroot
  obtain ⟨j, f, hf⟩ :=
    leftTensor_stage_eq_stabilizes_sameUniverse (F := F)
      (x := Polynomial.aeval x p) (y := 0) hmapRoot
  refine ⟨j, f, ?_⟩
  have hstageMap :
      Algebra.TensorProduct.map (F.map f).hom (AlgHom.id R B₀)
          (Polynomial.aeval x p) =
          Polynomial.aeval
            (Algebra.TensorProduct.map (F.map f).hom (AlgHom.id R B₀) x)
            (Polynomial.map (F.map f).hom.toRingHom p) := by
    -- Use the same evaluation-commutes-with-map identity after moving to the later stage.
    exact Polynomial.map_aeval_eq_aeval_map (by
      ext r
      simp) p x
  rw [← hstageMap]
  simpa using hf

/-- Helper for Chap10 Lemma 10 147 5: in the same-universe tensor case, integrality over a
filtered algebra colimit descends to an integral element at one finite stage. -/
private theorem leftTensorIntegral_descends_sameUniverse
    {B₀ : Type u} [CommRing B₀] [Algebra R B₀]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [HasColimit F]
    {x : ↑(colimit F) ⊗[R] B₀} (hx : IsIntegral ↑(colimit F) x) :
    ∃ (j : J) (xj : (F.obj j) ⊗[R] B₀),
      Algebra.TensorProduct.map (colimit.ι F j).hom (AlgHom.id R B₀) xj = x ∧
        IsIntegral (F.obj j) xj := by
  classical
  -- Choose a monic root equation for the integral tensor element and stage-lift both the element
  -- and the finite list of polynomial coefficients.
  obtain ⟨p, hpMonic, hroot⟩ := hx
  obtain ⟨jx, xjx, hxmap⟩ := leftTensor_stage_lift_sameUniverse (F := F) x
  obtain ⟨jp, pp, hppMonic, hppMap⟩ :=
    commAlgColimit_monicPolynomial_lifts (F := F) p hpMonic
  -- Move the tensor representative and the polynomial representative to one common filtered
  -- upper stage before stabilizing the root equation.
  let k := IsFiltered.max jx jp
  let fx : jx ⟶ k := IsFiltered.leftToMax jx jp
  let fp : jp ⟶ k := IsFiltered.rightToMax jx jp
  let xk : (F.obj k) ⊗[R] B₀ :=
    Algebra.TensorProduct.map (F.map fx).hom (AlgHom.id R B₀) xjx
  let pk : Polynomial (F.obj k) := Polynomial.map (F.map fp).hom.toRingHom pp
  have hxk_colimit :
      Algebra.TensorProduct.map (colimit.ι F k).hom (AlgHom.id R B₀) xk = x := by
    have hιx :
        (colimit.ι F k).hom.comp (F.map fx).hom = (colimit.ι F jx).hom := by
      ext a
      change (colimit.ι F k).hom ((F.map fx).hom a) = (colimit.ι F jx).hom a
      simpa [fx, k] using ConcreteCategory.congr_hom ((colimit.cocone F).w fx) a
    have hcomp :
        (Algebra.TensorProduct.map (colimit.ι F k).hom (AlgHom.id R B₀)).comp
            (Algebra.TensorProduct.map (F.map fx).hom (AlgHom.id R B₀)) =
          Algebra.TensorProduct.map (colimit.ι F jx).hom (AlgHom.id R B₀) := by
      ext a <;> simp
    calc
      Algebra.TensorProduct.map (colimit.ι F k).hom (AlgHom.id R B₀) xk =
          ((Algebra.TensorProduct.map (colimit.ι F k).hom (AlgHom.id R B₀)).comp
            (Algebra.TensorProduct.map (F.map fx).hom (AlgHom.id R B₀))) xjx := rfl
      _ = Algebra.TensorProduct.map (colimit.ι F jx).hom (AlgHom.id R B₀) xjx := by
            exact congrArg (fun φ ↦ φ xjx) hcomp
      _ = x := hxmap
  have hpk_colimit :
      Polynomial.map (colimit.ι F k).hom.toRingHom pk = p := by
    have hιp :
        (colimit.ι F k).hom.toRingHom.comp (F.map fp).hom.toRingHom =
          (colimit.ι F jp).hom.toRingHom := by
      ext a
      change (colimit.ι F k).hom ((F.map fp).hom a) = (colimit.ι F jp).hom a
      simpa [fp, k] using ConcreteCategory.congr_hom ((colimit.cocone F).w fp) a
    calc
      Polynomial.map (colimit.ι F k).hom.toRingHom pk =
          Polynomial.map ((colimit.ι F k).hom.toRingHom.comp (F.map fp).hom.toRingHom) pp := by
            simp [pk, Polynomial.map_map]
      _ = Polynomial.map (colimit.ι F jp).hom.toRingHom pp := by
            rw [hιp]
      _ = p := hppMap
  have hroot_colimit :
      Polynomial.aeval
        (Algebra.TensorProduct.map (colimit.ι F k).hom (AlgHom.id R B₀) xk)
        (Polynomial.map (colimit.ι F k).hom.toRingHom pk) = 0 := by
    -- The transported root equation is exactly the original colimit equation.
    rw [hxk_colimit, hpk_colimit]
    exact hroot
  obtain ⟨j, f, hroot_stage⟩ :=
    leftTensor_aeval_zero_stabilizes_sameUniverse (F := F) (p := pk) (x := xk)
      hroot_colimit
  let xj : (F.obj j) ⊗[R] B₀ :=
    Algebra.TensorProduct.map (F.map f).hom (AlgHom.id R B₀) xk
  refine ⟨j, xj, ?_, ?_⟩
  · have hι :
        (colimit.ι F j).hom.comp (F.map f).hom = (colimit.ι F k).hom := by
      ext a
      change (colimit.ι F j).hom ((F.map f).hom a) = (colimit.ι F k).hom a
      simpa using ConcreteCategory.congr_hom ((colimit.cocone F).w f) a
    have hcomp :
        (Algebra.TensorProduct.map (colimit.ι F j).hom (AlgHom.id R B₀)).comp
            (Algebra.TensorProduct.map (F.map f).hom (AlgHom.id R B₀)) =
          Algebra.TensorProduct.map (colimit.ι F k).hom (AlgHom.id R B₀) := by
      ext a <;> simp
    calc
      Algebra.TensorProduct.map (colimit.ι F j).hom (AlgHom.id R B₀) xj =
          ((Algebra.TensorProduct.map (colimit.ι F j).hom (AlgHom.id R B₀)).comp
            (Algebra.TensorProduct.map (F.map f).hom (AlgHom.id R B₀))) xk := rfl
      _ = Algebra.TensorProduct.map (colimit.ι F k).hom (AlgHom.id R B₀) xk := by
            exact congrArg (fun φ ↦ φ xk) hcomp
      _ = x := hxk_colimit
  · have hpkMonic : pk.Monic := hppMonic.map (F.map fp).hom.toRingHom
    refine ⟨Polynomial.map (F.map f).hom.toRingHom pk, hpkMonic.map (F.map f).hom.toRingHom, ?_⟩
    simpa [xj] using hroot_stage

/-- Helper for Chap10 Lemma 10 147 5: the remaining finite-data descent statement needed for
an integral element of a left tensor product over a filtered algebra colimit. -/
private theorem leftTensorIntegral_descends_of_commAlgColimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [HasColimit F]
    {x : ↑(colimit F) ⊗[R] B} (hx : IsIntegral ↑(colimit F) x) :
    ∃ (j : J) (xj : (F.obj j) ⊗[R] B),
      Algebra.TensorProduct.map (colimit.ι F j).hom (AlgHom.id R B) xj = x ∧
        IsIntegral (F.obj j) xj := by
  -- TODO: descend a monic integral equation for `x`. The same-universe tensor equality descent is
  -- now isolated in `leftTensor_stage_eq_stabilizes_sameUniverse`, and the same-universe root
  -- equation descent in `leftTensor_aeval_zero_stabilizes_sameUniverse`. A tempting shortcut by
  -- replacing `B` with `ULift B` fails because `ULift B : Type (max u v)` then forces the whole
  -- algebra diagram out of `CommAlgCat.{u}`. The remaining blocker is the mixed-universe
  -- tensor-colimit/finite-equation descent needed for the current `B : Type v`.
  sorry

/-- Helper for Chap10 Lemma 10 147 5: after finite integral-equation descent, smooth stages
force colimit tensor elements into the adjoin of the base integral closure. -/
private theorem commAlgColimitSmooth_mem_adjoin_mapIntegralClosure
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [HasColimit F]
    (hsm : ∀ j, RingHom.Smooth (algebraMap R (F.obj j)))
    {x : ↑(colimit F) ⊗[R] B} (hx : IsIntegral ↑(colimit F) x) :
    x ∈ Algebra.adjoin ↑(colimit F)
      ((integralClosure R B).map Algebra.TensorProduct.includeRight :
        Subalgebra R (↑(colimit F) ⊗[R] B)) := by
  -- First descend the integral element to one stage where it is still integral.
  obtain ⟨j, xj, hmap, hxjInt⟩ :=
    leftTensorIntegral_descends_of_commAlgColimit (F := F) hx
  -- Smooth-stage base change gives the adjoin membership before passing to the colimit.
  have hxjAdjoin : xj ∈ Algebra.adjoin (F.obj j)
      ((integralClosure R B).map Algebra.TensorProduct.includeRight :
        Subalgebra R ((F.obj j) ⊗[R] B)) :=
    stageIntegralTensor_mem_adjoin_of_smooth (R := R) (S := F.obj j) (B := B) (hsm j) hxjInt
  -- Push that adjoin membership through the tensor stage map and rewrite to the original element.
  have hpush := map_stageAdjoin_mem_colimitAdjoin (F := F) j hxjAdjoin
  simpa [hmap] using hpush

/-- Helper for Chap10 Lemma 10 147 5: an integral tensor element over an ind-smooth base change
lies in the algebra generated by the base integral closure. -/
private theorem mem_adjoin_mapIntegralClosure_of_isFilteredColimitOfSmooth
    (hS : (algebraMap R S).IsFilteredColimitOfSmooth)
    {x : S ⊗[R] B} (hx : IsIntegral S x) :
    x ∈ Algebra.adjoin S
      ((integralClosure R B).map Algebra.TensorProduct.includeRight :
        Subalgebra R (S ⊗[R] B)) := by
  -- Route correction: do not identify integral closures as filtered colimits. The stable prefix is
  -- the smooth-stage adjoin lemma above; the remaining work is finite polynomial-equation descent
  -- through one smooth stage and transport of that stage adjoin membership back to `S`.
  -- Expose the hidden filtered smooth presentation. The missing step is to descend the finite
  -- polynomial integrality equation for `x` to a smooth stage and push the stagewise adjoin
  -- membership back to the colimit.
  have hUlift := hS
  dsimp [RingHom.IsFilteredColimitOfSmooth] at hUlift
  -- TODO: prove finite-data descent through `hUlift`, apply
  -- `toIntegralClosure_bijective_of_smoothStage` at the smooth stage, and transport adjoin
  -- membership along the stage-to-colimit tensor map.
  sorry

-- Proof sketch: write `S` as a filtered colimit of smooth `R`-algebras. By Lemma `10.147.4`,
-- the canonical comparison map is bijective after base change to each smooth stage. Tensor
-- products commute with filtered colimits, and the integral closure on the target is obtained as
-- the filtered colimit of the stagewise integral closures, so the colimit comparison map is
-- exactly `TensorProduct.toIntegralClosure R S B`.
/-- Lemma 10.147.5: if `R → S` is a filtered colimit of smooth `R`-algebras and
`A = integralClosure R B`, then the canonical map
`S ⊗[R] A → integralClosure S (S ⊗[R] B)` is bijective, hence an isomorphism. -/
@[stacks 0CBF]
theorem toIntegralClosure_bijective_of_isFilteredColimitOfSmooth
    (hS : (algebraMap R S).IsFilteredColimitOfSmooth) :
    Function.Bijective (toIntegralClosure R S B) := by
  refine ⟨toIntegralClosure_injective_of_isFilteredColimitOfSmooth hS, ?_⟩
  -- Surjectivity is now reduced to the source-facing adjoin-membership descent statement.
  exact toIntegralClosure_surjective_of_mem_adjoin_mapIntegralClosure
    (mem_adjoin_mapIntegralClosure_of_isFilteredColimitOfSmooth hS)

end

end TensorProduct
