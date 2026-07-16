import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.stacks_project.Chap10.Definition_10_32_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_32_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_32_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_138_17
import StacksProject_2024.stacks_project.Chap10.Lemma_10_143_10
import StacksProject_2024.stacks_project.Chap10.Lemma_10_151_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CommRingCat
open Polynomial
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: étale `A`-algebras and reduction modulo an ideal;
- sampled owner declarations:
  `CommAlgCat`,
  `commAlgCatEquivUnder`,
  `CommRingCat.etale`,
  `ObjectProperty.lift`;
- best owner abstraction: the ambient category of `A`-algebras is canonically `CommAlgCat A`,
  equivalent to `Under (CommRingCat.of A)` via `commAlgCatEquivUnder`; the étale condition is
  therefore best expressed as an object property on `CommAlgCat A`, while the reduction functor is
  the base-change bridge to `CommAlgCat (A ⧸ I)`;
- primitive data: an object `B : CommAlgCat A`, equivalently an `A`-algebra with its structure
  morphism `A ⟶ B`;
- derived API: the étale object property on `CommAlgCat A`, the quotient/base-change functor
  `CommAlgCat A ⥤ CommAlgCat (A ⧸ I)`, its restriction to the étale full subcategory, its
  equivalence under a locally nilpotent ideal, and the induced henselian-ring instance.

Source/core/bridge triage:
- `source-facing`: reduction modulo `I` on the full subcategory of étale objects in
  `CommAlgCat A`;
- `core/canonical`: `CommAlgCat A`, `commAlgCatEquivUnder`, and `CommRingCat.etale`;
- `bridge/view`: the quotient/base-change functor on `CommAlgCat A`, obtained from the ordinary
  under-category base-change functor through `commAlgCatEquivUnder`.
-/

/-- The object property on `CommAlgCat A` selecting the étale `A`-algebras. -/
abbrev etaleAlgebraProperty (A : Type u) [CommRing A] : ObjectProperty (CommAlgCat A) :=
  fun B : CommAlgCat A ↦ Algebra.Etale A B

variable (I : Ideal A)

/-- Base change along `A → A ⧸ I`, formalizing the functor `B ↦ B / IB` on `A`-algebras, viewed
in the canonical owner category `CommAlgCat`. -/
abbrev quotientCommAlgFunctor : CommAlgCat A ⥤ CommAlgCat (A ⧸ I) where
  obj B := CommAlgCat.of (A ⧸ I) ((A ⧸ I) ⊗[A] B)
  map {B C} f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id _ _) f.hom)
  map_id B := by
    -- Proof comment: tensoring with the identity map fixes every simple tensor.
    ext x
    rfl
  map_comp f g := by
    -- Proof comment: tensoring with a composite equals composing the tensor maps.
    ext x
    rfl

/-- Helper for Lemma 15.11.2: the object obtained from `B` by quotient base change is the
canonical quotient algebra `B / I B`. -/
private noncomputable def quotientCommAlgFunctor_obj_algEquiv_quotient
    (B : CommAlgCat A) :
    ((quotientCommAlgFunctor I).obj B) ≃ₐ[A ⧸ I]
      B ⧸ Ideal.map (algebraMap A B) I :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm

-- Proof sketch: an étale algebra stays étale after any base change, so applying the quotient
-- functor to an étale object of `CommAlgCat A` again lands in the étale full subcategory of
-- `CommAlgCat (A ⧸ I)`.
private theorem quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty :
    ∀ B : (etaleAlgebraProperty A).FullSubcategory,
      etaleAlgebraProperty (A ⧸ I) ((quotientCommAlgFunctor I).obj B.obj) := by
  intro B
  let _ : Algebra.Etale A B.obj := by
    simpa [etaleAlgebraProperty] using B.property
  -- Proof comment: reduction modulo `I` is quotient base change on the tensor-product surface.
  let hquot :
      Algebra.Etale (A ⧸ I) (B.obj ⧸ Ideal.map (algebraMap A B.obj) I) :=
    Algebra.quotient_source_etale_over_quotient (A := A) (B := (B.obj : Type u)) I
  let _ : Algebra.Etale (A ⧸ I) (B.obj ⧸ Ideal.map (algebraMap A B.obj) I) := hquot
  exact
    Algebra.Etale.of_equiv
      (quotientCommAlgFunctor_obj_algEquiv_quotient (A := A) (I := I) B.obj).symm

/-- Helper for Lemma 15.11.2: every morphism between the canonical quotient surfaces of étale
`A`-algebras lifts across a locally nilpotent ideal. -/
private theorem lift_algHom_of_quotient_between_etale_algebras
    {B C : CommAlgCat A} (hB : etaleAlgebraProperty A B) (hI : I.IsLocallyNilpotent)
    (fbar : B ⧸ Ideal.map (algebraMap A B) I →ₐ[A ⧸ I]
      C ⧸ Ideal.map (algebraMap A C) I) :
    ∃ f : B →ₐ[A] C,
      (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A C) I)).comp f =
        (fbar.restrictScalars A).comp (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A B) I)) := by
  let _ : Algebra.Etale A B := by
    simpa [etaleAlgebraProperty] using hB
  let _ : Algebra.Smooth A B := inferInstance
  let J : Ideal C := Ideal.map (algebraMap A C) I
  have hJ : J.IsLocallyNilpotent :=
    Ideal.map_isLocallyNilpotent (algebraMap A C) hI
  let σbar : B →ₐ[A] C ⧸ J :=
    (fbar.restrictScalars A).comp (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A B) I))
  -- Proof comment: étale algebras are smooth, so formal smoothness lifts the quotient map across
  -- the locally nilpotent extension `C → C / I C`.
  obtain ⟨f, hf⟩ :=
    Algebra.smooth_exists_lift_of_quotient_by_locally_nilpotent
      (R := A) (S := B) (A := C) J hJ σbar
  refine ⟨f, ?_⟩
  simpa [J, σbar] using hf

/-- Helper for Lemma 15.11.2: every étale algebra over `A ⧸ I` has an étale lift over `A`,
already identified on the canonical quotient surface. -/
private theorem exists_etale_lift_on_canonical_surface
    {Bbar : Type u} [CommRing Bbar] [Algebra (A ⧸ I) Bbar]
    (hBbar : Algebra.Etale (A ⧸ I) Bbar) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      Nonempty (((quotientCommAlgFunctor I).obj (CommAlgCat.of A B)) ≃ₐ[A ⧸ I] Bbar) := by
  let _ : Algebra.Etale (A ⧸ I) Bbar := hBbar
  obtain ⟨B, hBCommRing, hBAlg, hBEtale, hQuot⟩ :=
    Algebra.exists_etale_lift_of_quotient (R := A) (I := I) (Sbar := Bbar)
  let _ : CommRing B := hBCommRing
  let _ : Algebra A B := hBAlg
  refine ⟨B, hBCommRing, hBAlg, hBEtale, ?_⟩
  rcases hQuot with ⟨e⟩
  -- Proof comment: the Chapter 10 lift theorem lands on the explicit quotient surface, and the
  -- canonical tensor/quotient equivalence moves it to the object of `quotientCommAlgFunctor`.
  exact ⟨(quotientCommAlgFunctor_obj_algEquiv_quotient
    (A := A) (I := I) (CommAlgCat.of A B)).trans e⟩

/-- Helper for Lemma 15.11.2: extending `I` to `B` and then mapping along an `A`-algebra morphism
lands inside the pullback of the extension of `I` to the target. -/
private theorem extendedIdeal_le_comap_extendedIdeal
    {B C : CommAlgCat A} (f : B →ₐ[A] C) :
    Ideal.map (algebraMap A B) I ≤
      Ideal.comap f.toRingHom (Ideal.map (algebraMap A C) I) := by
  -- Collapse the iterated ideal extension along the algebra tower `A → B → C`.
  simpa [Ideal.map_map, show f.toRingHom.comp (algebraMap A B) = algebraMap A C by
    ext a
    simpa using f.commutes a] using
    (Ideal.le_comap_map :
      Ideal.map (algebraMap A B) I ≤
        Ideal.comap f.toRingHom
          (Ideal.map f.toRingHom (Ideal.map (algebraMap A B) I)))

/-- Helper for Lemma 15.11.2: the canonical quotient morphism induced by an `A`-algebra map on the
explicit quotient surface `B / I B`. -/
private abbrev quotientMap_on_extended_ideal
    {B C : CommAlgCat A} (f : B →ₐ[A] C) :
    B ⧸ Ideal.map (algebraMap A B) I →ₐ[A ⧸ I]
      C ⧸ Ideal.map (algebraMap A C) I :=
  AlgHom.extendScalarsOfSurjective (Ideal.Quotient.mkₐ_surjective A I) <|
    Ideal.quotientMapₐ (Ideal.map (algebraMap A C) I) f
      (extendedIdeal_le_comap_extendedIdeal (A := A) (I := I) f)

/-- Helper for Lemma 15.11.2: the canonical quotient morphism induced by `f` sends the class of
`b` to the class of `f b`. -/
private theorem quotientMap_on_extended_ideal_mk
    {B C : CommAlgCat A} (f : B →ₐ[A] C) (b : B) :
    quotientMap_on_extended_ideal (A := A) (I := I) f
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b) =
        Ideal.Quotient.mk (Ideal.map (algebraMap A C) I) (f b) := by
  -- Evaluate the quotient map on a chosen representative.
  simp [quotientMap_on_extended_ideal]

/-- Helper for Lemma 15.11.2: the formal lifting identity against quotient maps uniquely
determines the induced morphism on the canonical quotient surface. -/
private theorem quotientMap_on_extended_ideal_eq_of_comp_mk
    {B C : CommAlgCat A} {f : B →ₐ[A] C}
    {fbar : B ⧸ Ideal.map (algebraMap A B) I →ₐ[A ⧸ I]
      C ⧸ Ideal.map (algebraMap A C) I}
    (hf :
      (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A C) I)).comp f =
        (fbar.restrictScalars A).comp
          (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A B) I))) :
    quotientMap_on_extended_ideal (A := A) (I := I) f = fbar := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro b
  -- Proof comment: both quotient maps are determined by their values on represented classes.
  have hb := congrArg (fun φ : B →ₐ[A] C ⧸ Ideal.map (algebraMap A C) I ↦ φ b) hf
  simpa [quotientMap_on_extended_ideal_mk, AlgHom.comp_apply] using hb

/-- Helper for Lemma 15.11.2: equality of the canonical quotient morphisms induced by two
`A`-algebra maps implies equality of their reductions modulo `I`. -/
private theorem comp_mk_eq_of_quotientMap_on_extended_ideal_eq
    {B C : CommAlgCat A} {f g : B →ₐ[A] C}
    (hfg :
      quotientMap_on_extended_ideal (A := A) (I := I) f =
        quotientMap_on_extended_ideal (A := A) (I := I) g) :
    (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A C) I)).comp f =
      ((Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A C) I)).comp g) := by
  ext b
  -- Proof comment: equality of the descended quotient maps immediately gives equality on every
  -- represented class.
  have hb := congrArg
    (fun φ :
      B ⧸ Ideal.map (algebraMap A B) I →ₐ[A ⧸ I]
        C ⧸ Ideal.map (algebraMap A C) I ↦
          φ (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b)) hfg
  simpa [quotientMap_on_extended_ideal_mk, AlgHom.comp_apply] using hb

/-- Helper for Lemma 15.11.2: a locally nilpotent ideal contains no nonzero idempotent. -/
private theorem idempotent_eq_zero_of_mem_locally_nilpotent_ideal
    {R : Type u} [CommRing R] {J : Ideal R} (hJ : J.IsLocallyNilpotent)
    {e : R} (he : IsIdempotentElem e) (heJ : e ∈ J) :
    e = 0 := by
  obtain ⟨e', he', huniq⟩ :=
    existsUnique_idempotent_lift_quotient_of_isLocallyNilpotent
      (I := J) hJ 0 (by
        change IsIdempotentElem (0 : R ⧸ J)
        simp [IsIdempotentElem])
  have heEq : e = e' :=
    huniq e ⟨he, Ideal.Quotient.eq_zero_iff_mem.mpr heJ⟩
  have hzeroEq : (0 : R) = e' :=
    huniq 0 ⟨by
      change IsIdempotentElem (0 : R)
      simp [IsIdempotentElem], rfl⟩
  exact heEq.trans hzeroEq.symm

/-- Helper for Lemma 15.11.2: if two maps between étale `A`-algebras agree modulo the extended
ideal `I C`, then they are equal. This is the source-faithful diagonal-idempotent argument. -/
private theorem eq_of_equal_reductions_between_etale_algebras
    {B C : CommAlgCat A} (hB : etaleAlgebraProperty A B) (hI : I.IsLocallyNilpotent)
    {f g : B →ₐ[A] C}
    (hfg :
      (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A C) I)).comp f =
        (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A C) I)).comp g) :
    f = g := by
  have hEtaleB : Algebra.Etale A B := by
    simpa [etaleAlgebraProperty] using hB
  let _ : Algebra.Etale A B := hEtaleB
  let _ : Algebra.Unramified A B := inferInstance
  let _ : Algebra (B ⊗[A] B) B := (Algebra.TensorProduct.lmul' A).toRingHom.toAlgebra
  let J : Ideal C := Ideal.map (algebraMap A C) I
  have hJ : J.IsLocallyNilpotent :=
    Ideal.map_isLocallyNilpotent (algebraMap A C) hI
  obtain ⟨e, he, hloc⟩ :=
    exists_idempotent_tensorProduct_self_isLocalization_of_unramified (R := A) (S := B)
  have hker :
      RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom =
        Ideal.span ({1 - e} : Set (B ⊗[A] B)) := by
    -- Proof comment: unramifiedness identifies the diagonal kernel with the complementary
    -- idempotent ideal.
    simpa using
      Algebra.descended_localization_kernel_eq_span_one_sub
        (R := B ⊗[A] B) (S := B) he hloc
  let q : C →ₐ[A] C ⧸ J := Ideal.Quotient.mkₐ A J
  let τ : B ⊗[A] B →ₐ[A] C := Algebra.TensorProduct.productMap f g
  have hcomp :
      q.comp τ = ((q.comp f).comp (Algebra.TensorProduct.lmul' A)) := by
    ext x y
    have hy :
        q (g y) = q (f y) := by
      simpa using congrArg (fun φ : B →ₐ[A] C ⧸ J ↦ φ y) hfg
    -- Proof comment: after quotienting by `I C`, the tensor-product map factors through
    -- multiplication because the reductions of `f` and `g` agree.
    calc
      q (τ (x ⊗ₜ[A] y)) = q (f x * g y) := by
        simp [τ, Algebra.TensorProduct.productMap_apply_tmul]
      _ = q (f x) * q (g y) := by
        simp
      _ = q (f x) * q (f y) := by
        rw [hy]
      _ = q (f (x * y)) := by
        simp
      _ = (((q.comp f).comp (Algebra.TensorProduct.lmul' A)) (x ⊗ₜ[A] y)) := by
        simp [Algebra.TensorProduct.lmul'_apply_tmul]
  have hτ_one_sub_mem : τ (1 - e) ∈ J := by
    have hkermem :
        (1 - e : B ⊗[A] B) ∈ RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom := by
      rw [hker]
      exact Ideal.subset_span (by simp)
    have hzero : q (τ (1 - e)) = 0 := by
      calc
        q (τ (1 - e)) = (q.comp τ) (1 - e) := rfl
        _ = (((q.comp f).comp (Algebra.TensorProduct.lmul' A)) (1 - e)) := by
          simpa using congrArg (fun φ : B ⊗[A] B →ₐ[A] C ⧸ J ↦ φ (1 - e)) hcomp
        _ = 0 := by
          rw [RingHom.mem_ker.mp hkermem]
          simp
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hτ_one_sub_zero : τ (1 - e) = 0 := by
    -- Proof comment: the image of `1 - e` is an idempotent inside the locally nilpotent ideal
    -- `I C`, so it must vanish.
    exact idempotent_eq_zero_of_mem_locally_nilpotent_ideal
      (hJ := hJ) (he := he.one_sub.map τ) hτ_one_sub_mem
  ext b
  have hdiff_mem :
      (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ[A] b : B ⊗[A] B) ∈
        RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom := by
    -- Proof comment: diagonal tensor differences always lie in the multiplication kernel.
    apply RingHom.mem_ker.mpr
    simp [Algebra.TensorProduct.lmul'_apply_tmul]
  have hspan :
      (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ[A] b : B ⊗[A] B) ∈
        Ideal.span ({1 - e} : Set (B ⊗[A] B)) := by
    rwa [hker] at hdiff_mem
  rw [Ideal.mem_span_singleton] at hspan
  rcases hspan with ⟨r, hr⟩
  have hτdiff : τ (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ[A] b) = 0 := by
    -- Proof comment: once `τ (1 - e)` vanishes, every diagonal difference vanishes as well.
    calc
      τ (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ[A] b) = τ ((1 - e) * r) := by
        rw [hr]
      _ = τ (1 - e) * τ r := by
        simp
      _ = 0 := by
        simp [hτ_one_sub_zero]
  simpa [τ, Algebra.TensorProduct.productMap_apply_tmul] using hτdiff

/-- Helper for Lemma 15.11.2: the explicit canonical quotient object attached to an étale
`A`-algebra in the source full subcategory. -/
private abbrev canonical_quotient_etale_obj
    (B : (etaleAlgebraProperty A).FullSubcategory) :
    (etaleAlgebraProperty (A ⧸ I)).FullSubcategory :=
  ⟨CommAlgCat.of (A ⧸ I) (B.obj ⧸ Ideal.map (algebraMap A B.obj) I), by
    -- Reuse the source étale structure and apply the quotient-etale theorem on the canonical
    -- quotient surface.
    let _ : Algebra.Etale A B.obj := by
      simpa [etaleAlgebraProperty] using B.property
    simpa [etaleAlgebraProperty] using
      (Algebra.quotient_source_etale_over_quotient (A := A) (B := (B.obj : Type u)) I :
        Algebra.Etale (A ⧸ I) (B.obj ⧸ Ideal.map (algebraMap A B.obj) I))⟩

/-- Helper for Lemma 15.11.2: the reduction functor on étale algebras, expressed directly on the
canonical quotient surface `B / I B`. -/
private noncomputable def canonical_quotient_etale_functor :
    (etaleAlgebraProperty A).FullSubcategory ⥤
      (etaleAlgebraProperty (A ⧸ I)).FullSubcategory where
  obj B := canonical_quotient_etale_obj (A := A) (I := I) B
  map {B C} f :=
    ObjectProperty.homMk <|
      CommAlgCat.ofHom (quotientMap_on_extended_ideal (A := A) (I := I) f.hom.hom)
  map_id B := by
    -- On quotient classes, the induced map of the identity algebra map is the identity.
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    refine Quotient.inductionOn' x ?_
    intro b
    simpa using
      (quotientMap_on_extended_ideal_mk
        (A := A) (I := I) (f := AlgHom.id A B.obj) b)
  map_comp {B C D} f g := by
    -- On quotient classes, functoriality is just functoriality of the induced quotient maps.
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    refine Quotient.inductionOn' x ?_
    intro b
    simp only [CommAlgCat.comp_hom, AlgHom.comp_apply]
    rw [quotientMap_on_extended_ideal_mk, quotientMap_on_extended_ideal_mk,
      quotientMap_on_extended_ideal_mk]

/-- Helper for Lemma 15.11.2: the explicit canonical quotient functor is full by lifting
quotient-surface maps between étale algebras across the locally nilpotent ideal. -/
private theorem canonical_quotient_etale_functor_full
    (hI : I.IsLocallyNilpotent) :
    (canonical_quotient_etale_functor (A := A) (I := I)).Full where
  map_surjective := by
    intro B C f
    obtain ⟨g, hg⟩ :=
      lift_algHom_of_quotient_between_etale_algebras
        (A := A) (I := I) B.property hI f.hom.hom
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom g), ?_⟩
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    -- Proof comment: the lifted map is characterized uniquely by its compatibility with the
    -- quotient maps on representatives.
    exact quotientMap_on_extended_ideal_eq_of_comp_mk (A := A) (I := I) hg

/-- Helper for Lemma 15.11.2: the explicit canonical quotient functor is faithful because two
maps of étale `A`-algebras that agree modulo the extended ideal are equal. -/
private theorem canonical_quotient_etale_functor_faithful
    (hI : I.IsLocallyNilpotent) :
    (canonical_quotient_etale_functor (A := A) (I := I)).Faithful where
  map_injective := by
    intro B C f g hfg
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    have hquot :
        quotientMap_on_extended_ideal (A := A) (I := I) f.hom.hom =
          quotientMap_on_extended_ideal (A := A) (I := I) g.hom.hom := by
      exact congrArg (fun φ => φ.hom.hom) hfg
    -- Proof comment: equality after reduction modulo `I` forces equality upstairs for étale
    -- morphisms by the diagonal-idempotent argument.
    exact eq_of_equal_reductions_between_etale_algebras
      (A := A) (I := I) B.property hI
      (comp_mk_eq_of_quotientMap_on_extended_ideal_eq (A := A) (I := I) hquot)

/-- Helper for Lemma 15.11.2: the explicit canonical quotient functor is essentially surjective by
lifting étale quotient algebras back to étale algebras over `A`. -/
private theorem canonical_quotient_etale_functor_essSurj :
    (canonical_quotient_etale_functor (A := A) (I := I)).EssSurj where
  mem_essImage := by
    intro Bbar
    obtain ⟨B, hBCommRing, hBAlg, hBEtale, hTensor⟩ :=
      exists_etale_lift_on_canonical_surface (A := A) (I := I) Bbar.property
    let sourceObj : (etaleAlgebraProperty A).FullSubcategory :=
      ⟨CommAlgCat.of A B, by
        simpa [etaleAlgebraProperty] using hBEtale⟩
    refine ⟨sourceObj, ?_⟩
    rcases hTensor with ⟨eTensor⟩
    let eQuot :
        ((canonical_quotient_etale_functor (A := A) (I := I)).obj sourceObj).obj ≃ₐ[A ⧸ I]
          Bbar.obj :=
      (quotientCommAlgFunctor_obj_algEquiv_quotient
        (A := A) (I := I) sourceObj.obj).symm.trans eTensor
    refine ⟨(etaleAlgebraProperty (A ⧸ I)).isoMk ?_⟩
    exact
      { hom := CommAlgCat.ofHom eQuot.toAlgHom
        inv := CommAlgCat.ofHom eQuot.symm.toAlgHom
        hom_inv_id := by
          apply CommAlgCat.hom_ext
          ext x
          simpa using eQuot.left_inv x
        inv_hom_id := by
          apply CommAlgCat.hom_ext
          ext x
          simpa using eQuot.apply_symm_apply x }

/-- Helper for Lemma 15.11.2: the canonical objectwise comparison sends the base-change image of
`b` to the quotient class of `b`. -/
private theorem quotientCommAlgFunctor_obj_algEquiv_quotient_algebraMap
    (B : CommAlgCat A) (b : B) :
    quotientCommAlgFunctor_obj_algEquiv_quotient (A := A) (I := I) B
      ((Algebra.TensorProduct.includeRight :
        B →ₐ[A] ((quotientCommAlgFunctor I).obj B)) b) =
        Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b := by
  -- Evaluate the quotient/tensor equivalence on the canonical tensor generator `1 ⊗ b`.
  simpa [quotientCommAlgFunctor_obj_algEquiv_quotient, quotientCommAlgFunctor,
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]

/-- Helper for Lemma 15.11.2: after passing to the quotient surface, the inverse objectwise
comparison recovers the canonical base-change map `B → (quotientCommAlgFunctor I).obj B`. -/
private theorem quotientCommAlgFunctor_obj_algEquiv_quotient_symm_comp_mk
    (B : CommAlgCat A) :
    (((quotientCommAlgFunctor_obj_algEquiv_quotient (A := A) (I := I) B).symm.toAlgHom)
      .restrictScalars A).comp
      (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A B) I)) =
        (Algebra.TensorProduct.includeRight :
          B →ₐ[A] ((quotientCommAlgFunctor I).obj B)) := by
  ext b
  apply (quotientCommAlgFunctor_obj_algEquiv_quotient (A := A) (I := I) B).injective
  -- Proof comment: apply the forward quotient/tensor equivalence to both sides and use its
  -- explicit value on `algebraMap`.
  simp [quotientCommAlgFunctor_obj_algEquiv_quotient_algebraMap, AlgHom.comp_apply]

/-- Helper for Lemma 15.11.2: under the canonical quotient-surface identifications, the reduction
functor map is exactly the quotient map induced by the original algebra morphism. -/
private theorem quotientCommAlgFunctor_obj_algEquiv_quotient_natural
    {B C : CommAlgCat A} (f : B ⟶ C) :
    ((quotientCommAlgFunctor_obj_algEquiv_quotient (A := A) (I := I) C).toAlgHom).comp
        ((quotientCommAlgFunctor I).map f).hom =
      (quotientMap_on_extended_ideal (A := A) (I := I) f.hom).comp
        ((quotientCommAlgFunctor_obj_algEquiv_quotient (A := A) (I := I) B).toAlgHom) := by
  apply Algebra.TensorProduct.ext_ring
  ext b
  -- Proof comment: both sides send the base-changed copy of `b` to the quotient class of `f b`.
  simp [quotientCommAlgFunctor, quotientCommAlgFunctor_obj_algEquiv_quotient_algebraMap,
    AlgHom.comp_apply]

/-- Helper for Lemma 15.11.2: the lifted reduction functor is naturally isomorphic to the
explicit quotient-surface functor `B ↦ B / I B`. -/
private noncomputable def quotientCommAlgFunctor_lift_iso_canonical_quotient_etale_functor :
    ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I) ≅
      canonical_quotient_etale_functor (A := A) (I := I) := by
  refine NatIso.ofComponents (fun B ↦ ?_) ?_
  · refine (etaleAlgebraProperty (A ⧸ I)).isoMk ?_
    let e := quotientCommAlgFunctor_obj_algEquiv_quotient (A := A) (I := I) B.obj
    exact
      { hom := CommAlgCat.ofHom e.toAlgHom
        inv := CommAlgCat.ofHom e.symm.toAlgHom
        hom_inv_id := by
          apply CommAlgCat.hom_ext
          ext x
          change e.symm (e x) = x
          exact e.left_inv x
        inv_hom_id := by
          apply CommAlgCat.hom_ext
          ext x
          change e (e.symm x) = x
          exact e.apply_symm_apply x }
  · intro B C f
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    -- Route correction: the final naturality check now stays on the direct tensor/quotient
    -- surface, avoiding the older under-category transport entirely.
    exact quotientCommAlgFunctor_obj_algEquiv_quotient_natural (A := A) (I := I) f.hom

-- Proof sketch: essential surjectivity comes from lifting étale `A ⧸ I`-algebras across the
-- locally nilpotent quotient. Fullness comes from lifting morphisms by formal smoothness of étale
-- algebras. Faithfulness follows from the idempotent criterion for unramified morphisms together
-- with the fact that locally nilpotent ideals contain no nonzero idempotents.
/-- Lemma 15.11.2 (1): if `I` is locally nilpotent, then reduction modulo `I`, formalized by base
change along `A → A ⧸ I`, induces an equivalence between the full subcategories of étale objects
in `CommAlgCat A` and `CommAlgCat (A ⧸ I)`. -/
theorem quotientCommAlgFunctor_isEquivalence_on_etale_of_isLocallyNilpotent
    (hI : I.IsLocallyNilpotent) :
    Functor.IsEquivalence
      (ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I)) := by
  letI : (canonical_quotient_etale_functor (A := A) (I := I)).Full :=
    canonical_quotient_etale_functor_full (A := A) (I := I) hI
  letI : (canonical_quotient_etale_functor (A := A) (I := I)).Faithful :=
    canonical_quotient_etale_functor_faithful (A := A) (I := I) hI
  letI : (canonical_quotient_etale_functor (A := A) (I := I)).EssSurj :=
    canonical_quotient_etale_functor_essSurj (A := A) (I := I)
  letI : Functor.IsEquivalence (canonical_quotient_etale_functor (A := A) (I := I)) :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  let hIso :
      ObjectProperty.lift
          (etaleAlgebraProperty (A ⧸ I))
          ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
          (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I) ≅
        canonical_quotient_etale_functor (A := A) (I := I) :=
    quotientCommAlgFunctor_lift_iso_canonical_quotient_etale_functor (A := A) (I := I)
  have hLiftEssSurj :
      (ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I)).EssSurj := by
    refine Functor.EssSurj.mk ?_
    intro Bbar
    obtain ⟨B, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (F := canonical_quotient_etale_functor (A := A) (I := I)) Bbar
    refine ⟨B, ⟨(hIso.app B) ≪≫ e⟩⟩
  have hLiftFull :
      (ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I)).Full := by
    exact Functor.Full.of_iso hIso
  have hLiftFaithful :
      (ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I)).Faithful := by
    exact Functor.Faithful.of_iso hIso
  -- Proof comment: once the explicit quotient-surface functor is known to be an equivalence, the
  -- original lifted reduction functor is equivalent to it through the objectwise quotient/tensor
  -- comparison.
  letI :
      (ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I)).EssSurj := hLiftEssSurj
  letI :
      (ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I)).Full := hLiftFull
  letI :
      (ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I)).Faithful := hLiftFaithful
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- Helper for Lemma 15.11.2: a locally nilpotent ideal is contained in the Jacobson radical. -/
private theorem isLocallyNilpotent_le_ring_jacobson
    (hI : I.IsLocallyNilpotent) :
    I ≤ Ring.jacobson A := by
  -- Local nilpotence places `I` inside the nilradical, and the nilradical lies in the Jacobson
  -- radical of any commutative ring.
  exact hI.trans (nilradical_le_jacobson A)

/-- Helper for Lemma 15.11.2: a monic polynomial of degree `1` has the expected explicit root. -/
private theorem isRoot_neg_coeff_zero_of_monic_natDegree_one
    {R : Type u} [CommRing R] {p : R[X]} (hp : p.Monic) (hdeg : p.natDegree = 1) :
    p.IsRoot (-p.coeff 0) := by
  have hcoeff : p.coeff 1 = 1 := by
    simpa [hdeg] using hp.coeff_natDegree
  have hshape : p = X + C (p.coeff 0) := by
    calc
      p = C (p.coeff 1) * X + C (p.coeff 0) := by
        exact Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
      _ = X + C (p.coeff 0) := by rw [hcoeff]; simp
  -- Proof comment: once the degree-one polynomial is normalized to `X + c`, its root is `-c`.
  rw [Polynomial.IsRoot.def, hshape]
  simp

/-- Helper for Lemma 15.11.2: if a monic polynomial maps to `X - C a`, then it already has degree
`1`. -/
private theorem natDegree_one_of_monic_map_eq_X_sub_C
    {R S : Type u} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {p : R[X]} (hp : p.Monic) {a : S}
    (hmap : p.map φ = X - C a) :
    p.natDegree = 1 := by
  have hdeg : p.degree = 1 := by
    -- Proof comment: mapping a monic polynomial preserves the degree because its leading
    -- coefficient stays nonzero.
    calc
      p.degree = (p.map φ).degree := by
        symm
        exact Polynomial.degree_map_eq_of_leadingCoeff_ne_zero φ (by
          simpa [hp.leadingCoeff] using (one_ne_zero : (1 : S) ≠ 0))
      _ = (X - C a).degree := by rw [hmap]
      _ = 1 := by simpa using Polynomial.degree_X_sub_C a
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

/-- Helper for Lemma 15.11.2: if `p(a)` is a unit, then `X - a` and `p` are coprime. -/
private theorem isCoprime_X_sub_C_of_isUnit_eval
    {R : Type u} [CommRing R] (a : R) (p : R[X]) (hp : IsUnit (p.eval a)) :
    IsCoprime (X - C a) p := by
  have hroot : (p - C (p.eval a)).IsRoot a := by
    -- Proof comment: subtracting the constant value `p(a)` forces the new polynomial to vanish
    -- at `a`.
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub]
    simp
  obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot).2 hroot
  rcases hp with ⟨u, hu⟩
  refine ⟨-q * C (((u⁻¹ : Units R) : R)), C (((u⁻¹ : Units R) : R)), ?_⟩
  -- Proof comment: the Euclidean remainder identity writes a unit-valued constant combination of
  -- `X - C a` and `p`, which is then normalized to `1`.
  calc
    (-q * C (((u⁻¹ : Units R) : R))) * (X - C a) + C (((u⁻¹ : Units R) : R)) * p =
        C (((u⁻¹ : Units R) : R)) * (p - q * (X - C a)) := by
      ring
    _ = C (((u⁻¹ : Units R) : R)) * C (p.eval a) := by
      rw [show p - q * (X - C a) = C (p.eval a) by
        calc
          p - q * (X - C a) = p - ((X - C a) * q) := by rw [mul_comm]
          _ = p - (p - C (p.eval a)) := by rw [hq]
          _ = C (p.eval a) := by ring]
    _ = 1 := by
      rw [← hu]
      rw [← Polynomial.C_mul]
      simp

/-- Helper for Lemma 15.11.2: dividing a polynomial by `X - C a` at a root `a` evaluates to the
derivative at `a`. -/
private theorem divByMonic_X_sub_C_eval_eq_derivative_eval
    {R : Type u} [CommRing R] (p : R[X]) {a : R} (ha : p.IsRoot a) :
    (p /ₘ (X - C a)).eval a = p.derivative.eval a := by
  let q : R[X] := p /ₘ (X - C a)
  have hfactor : (X - C a) * q = p := by
    simpa [q] using (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha)
  have hderiv :=
    congrArg (fun r : R[X] => r.derivative.eval a) hfactor
  -- Proof comment: after differentiating the linear factorization, the `X - C a` term vanishes
  -- at `a`, leaving only the cofactor value.
  rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul] at hderiv
  simpa [q, Polynomial.IsRoot.def.mp ha] using hderiv

/-- Helper for Lemma 15.11.2: if a locally nilpotent ideal has a subsingleton quotient, then the
base ring is already subsingleton. -/
private theorem subsingleton_of_subsingleton_quotient_of_isLocallyNilpotent
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J.IsLocallyNilpotent)
    (hquot : Subsingleton (R ⧸ J)) :
    Subsingleton R := by
  have htop : J = ⊤ := by
    ext x
    constructor
    · intro hx
      simp
    · intro _
      have hxzero : Ideal.Quotient.mk J x = 0 := Subsingleton.elim _ _
      exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero
  have hnil : IsNilpotent (1 : R) :=
    (Ideal.isLocallyNilpotent_iff J).mp hJ 1 (by simpa [htop])
  rcases hnil with ⟨n, hn⟩
  -- Proof comment: once `1` is nilpotent, the ring collapses to the zero ring.
  refine ⟨fun x y ↦ ?_⟩
  have hone : (1 : R) = 0 := by simpa using hn
  calc
    x = x * 1 := by simp
    _ = x * 0 := by rw [hone]
    _ = 0 := by simp
    _ = y * 0 := by simp
    _ = y * 1 := by rw [hone]
    _ = y := by simp

/-- Helper for Lemma 15.11.2: an étale quotient equivalence over a locally nilpotent ideal
descends to an actual section over the base ring. -/
private theorem exists_section_of_etale_quotient_equiv_of_locally_nilpotent
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (J : Ideal R) (hJ : J.IsLocallyNilpotent)
    (e : (R ⧸ J) ≃ₐ[R ⧸ J] (R' ⧸ Ideal.map (algebraMap R R') J)) :
    ∃ σ : R' →ₐ[R] R,
      (Ideal.Quotient.mkₐ R J).comp σ =
        ((e.symm.toAlgHom).restrictScalars R).comp
          (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R R') J)) := by
  let J' : Ideal R' := Ideal.map (algebraMap R R') J
  let σbar : R' →ₐ[R] R ⧸ J :=
    ((e.symm.toAlgHom).restrictScalars R).comp (Ideal.Quotient.mkₐ R J')
  obtain ⟨σ, hσ⟩ :=
    Algebra.smooth_exists_lift_of_quotient_by_locally_nilpotent
      (R := R) (S := R') (A := R) J hJ σbar
  -- Proof comment: the smooth lifting theorem produces exactly the desired section after
  -- packaging the quotient equivalence as a map into `R ⧸ J`.
  exact ⟨σ, by simpa [J', σbar] using hσ⟩

/-- Helper for Lemma 15.11.2: over a nontrivial quotient, a monic polynomial reducing to
`X - C b` already has a root lifting `b`. -/
private theorem exists_root_of_monic_mod_X_sub_C
    {R : Type u} [CommRing R] (J : Ideal R) [Nontrivial (R ⧸ J)]
    {g : R[X]} (hg : g.Monic) {b : R ⧸ J}
    (hmap : g.map (Ideal.Quotient.mk J) = X - C b) :
    ∃ a : R, g.IsRoot a ∧ Ideal.Quotient.mk J a = b := by
  refine ⟨-g.coeff 0, ?_, ?_⟩
  · -- Proof comment: the quotient identity forces `g` to have degree `1`, so its explicit root
    -- is the negated constant coefficient.
    exact
      isRoot_neg_coeff_zero_of_monic_natDegree_one hg
        (natDegree_one_of_monic_map_eq_X_sub_C (Ideal.Quotient.mk J) hg hmap)
  · -- Proof comment: comparing constant coefficients identifies the lifted root with the chosen
    -- residue class `b`.
    have hcoeff0 : Ideal.Quotient.mk J (g.coeff 0) = -b := by
      simpa using congrArg (fun p : (R ⧸ J)[X] ↦ p.coeff 0) hmap
    calc
      Ideal.Quotient.mk J (-g.coeff 0) = -Ideal.Quotient.mk J (g.coeff 0) := by simp
      _ = -(-b) := by rw [hcoeff0]
      _ = b := by simp

/-- Helper for Lemma 15.11.2: a locally nilpotent ideal satisfies the Hensel root-lifting field
by the textbook factorization-and-descent route. -/
private theorem exists_hensel_root_of_locally_nilpotent_ideal
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J.IsLocallyNilpotent)
    {f : R[X]} (hf : f.Monic) (a₀ : R) (ha₀ : f.eval a₀ ∈ J)
    (hderiv : IsUnit ((Ideal.Quotient.mk J) (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ J := by
  classical
  by_cases hquot : Subsingleton (R ⧸ J)
  · let _ : Subsingleton R :=
      subsingleton_of_subsingleton_quotient_of_isLocallyNilpotent J hJ hquot
    refine ⟨0, ?_, ?_⟩
    · -- Proof comment: in the zero ring every evaluation vanishes, so any element is a root.
      exact (Polynomial.IsRoot.def).2 (Subsingleton.elim _ _)
    · -- Proof comment: the congruence condition is automatic in a subsingleton ring.
      have hdiff : (0 : R) - a₀ = 0 := Subsingleton.elim _ _
      simpa [hdiff] using (J.zero_mem : (0 : R) ∈ J)
  · let _ : Nontrivial (R ⧸ J) := not_subsingleton_iff_nontrivial.mp hquot
    let abar : R ⧸ J := Ideal.Quotient.mk J a₀
    let fbar : (R ⧸ J)[X] := f.map (Ideal.Quotient.mk J)
    let gbar : (R ⧸ J)[X] := X - C abar
    let hbar : (R ⧸ J)[X] := fbar /ₘ gbar
    have hrootbar : fbar.IsRoot abar := by
      -- Proof comment: reducing `f(a₀)` modulo `J` gives the simple residue root `ā`.
      exact (Polynomial.IsRoot.def).2 <| by
        simpa [fbar, abar, Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_at_apply] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr ha₀ :
            Ideal.Quotient.mk J (Polynomial.eval a₀ f) = 0)
    have hfactorbar : fbar = gbar * hbar := by
      -- Proof comment: the residue root forces the standard linear factorization by `X - C ā`.
      simpa [fbar, gbar, hbar] using
        (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hrootbar).symm
    have hgbar : gbar.Monic := by
      simpa [gbar] using (monic_X_sub_C abar)
    have hhbar : hbar.Monic := by
      -- Proof comment: the cofactor stays monic because `f̄` and `X - C ā` are both monic.
      have hfbar : fbar.Monic := by
        simpa [fbar] using hf.map (Ideal.Quotient.mk J)
      rw [hfactorbar] at hfbar
      exact (monic_X_sub_C abar).of_mul_monic_left hfbar
    have hderivbar :
        IsUnit (hbar.eval abar) := by
      -- Proof comment: at the residue root, the cofactor value is exactly the residue derivative.
      rw [show hbar.eval abar = fbar.derivative.eval abar by
            simpa [fbar, gbar, hbar] using
              divByMonic_X_sub_C_eval_eq_derivative_eval fbar hrootbar]
      have hmap_deriv :
          fbar.derivative.eval abar =
            (Ideal.Quotient.mk J) (f.derivative.eval a₀) := by
        simpa [fbar, abar, Polynomial.derivative_map, Polynomial.eval₂_eq_eval_map,
          Polynomial.eval₂_at_apply]
      rw [hmap_deriv]
      exact hderiv
    have hcoprime : IsCoprime gbar hbar := by
      simpa [gbar] using isCoprime_X_sub_C_of_isUnit_eval abar hbar hderivbar
    obtain ⟨R', _, _, _, e, g', h', hg', hh', hfactor', hgred, _⟩ :=
      Algebra.exists_etale_lift_factorization_of_monic_mod_ideal
        (A := R) J f gbar hbar hf hgbar hhbar hfactorbar hcoprime
    let J' : Ideal R' := Ideal.map (algebraMap R R') J
    let _ : Nontrivial (R' ⧸ J') := Function.Injective.nontrivial e.injective
    have hgred' : g'.map (Ideal.Quotient.mk J') = X - C (e abar) := by
      calc
        g'.map (Ideal.Quotient.mk J') = gbar.map e.toRingHom := hgred.symm
        _ = X - C (e abar) := by simp [gbar]
    obtain ⟨σ, hσ⟩ :=
      exists_section_of_etale_quotient_equiv_of_locally_nilpotent
        (J := J) hJ e
    obtain ⟨a', ha'root, ha'quot⟩ :=
      exists_root_of_monic_mod_X_sub_C (J := J') hg' hgred'
    let a : R := σ a'
    refine ⟨a, ?_, ?_⟩
    · have hmapRoot : (f.map (algebraMap R R')).IsRoot a' := by
        -- Proof comment: the lifted linear factor `g'` divides the lifted polynomial `f`.
        rw [Polynomial.IsRoot.def, hfactor', Polynomial.eval_mul, Polynomial.IsRoot.def.mp ha'root]
        simp
      have hrootMap :
          (Polynomial.map σ.toRingHom (f.map (algebraMap R R'))).IsRoot (σ a') :=
        Polynomial.IsRoot.map (f := σ.toRingHom) hmapRoot
      -- Proof comment: restricting scalars along the section collapses the coefficient map back
      -- to the original polynomial `f`.
      simpa [a, Polynomial.map_map] using hrootMap
    · have hσ_apply :
          Ideal.Quotient.mk J (σ a') = e.symm (Ideal.Quotient.mk J' a') := by
        have hσ_eval :=
          congrArg (fun φ : R' →ₐ[R] R ⧸ J ↦ φ a') hσ
        simpa [J'] using hσ_eval
      -- Route correction: rather than descending through the categorical equivalence package,
      -- descend the actual lifted root along the explicit section `σ : R' →ₐ[R] R`.
      -- Proof comment: evaluating the descended section on the lifted residue root shows that the
      -- final root is congruent to `a₀` modulo `J`.
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hσ_apply, ha'quot, AlgEquiv.symm_apply_apply]
      simp [abar]

-- Proof sketch: locally nilpotent ideals lie in the Jacobson radical, giving the Jacobson part of
-- henselianity. The factorization-lifting criterion is obtained by applying the étale
-- factorization lift of Lemma `15.9.5` and then using the equivalence from part `(1)` to descend
-- the resulting étale extension back to `A`.
/-- Lemma 15.11.2 (2): if `I` is locally nilpotent, then the pair `(A, I)` is henselian, i.e.
`A` is henselian at the ideal `I`. -/
instance henselianRing_of_isLocallyNilpotent
    (hI : I.IsLocallyNilpotent) : HenselianRing A I := by
  -- Route correction: the source-faithful proof does not need more functor transport from part
  -- `(1)`. It factors `f mod I`, lifts that factorization étale-locally via Lemma `15.9.5`, and
  -- then descends the resulting root along an explicit section produced by formal smoothness.
  refine
    { jac := ?_
      is_henselian := ?_ }
  · simpa [Ideal.jacobson_bot] using
      isLocallyNilpotent_le_ring_jacobson (A := A) (I := I) hI
  · -- Proof comment: the exact Hensel lifting statement is already packaged in the local helper
    -- above, which follows the source proof verbatim.
    intro f hf a₀ ha₀ hderiv
    exact exists_hensel_root_of_locally_nilpotent_ideal I hI hf a₀ ha₀ hderiv

end
