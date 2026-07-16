import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_81_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_81_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_82_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]
variable [Algebra.FiniteType R A]

/- Domain-style sampling:
- primary domain: relative pseudo-coherence for modules over a finite type algebra;
- sampled owner declarations:
  `Module.IsMPseudoCoherentRelativeTo`,
  `Module.IsPseudoCoherentRelativeTo`,
  `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `Module.FinitePresentationRelativeTo`,
  `Module.HasLengthFiniteFreeResolution`;
- best owner abstraction: the thin unbundled module bridge owners
  `Module.IsMPseudoCoherentRelativeTo R A M` and
  `Module.IsPseudoCoherentRelativeTo R A M`, which reuse the chapter owners on `ModuleCat`;
- primitive data: the bundled module object `ModuleCat.of A M` together with the existing relative
  pseudo-coherence owner from `Definition_15_82_4`;
- derived API: finite / finitely presented / finite-free-resolution criteria obtained by testing
  the restricted module over every surjective polynomial presentation of `A`.

Source/core/bridge triage:
- `source-facing`: the four equivalences of Lemma `15.82.7`;
- `core/canonical`: `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `Module.FinitePresentationRelativeTo`,
  `Module.HasLengthFiniteFreeResolution`,
  and Lemma `15.65.4`;
- `bridge/view`: the presentationwise finite-free-resolution criteria on the right-hand sides of
  parts `(3)` and `(4)`.

The canonical owner remains the chapter predicate on `ModuleCat`, but the ordinary theorem surface
for unbundled modules should use the thin bridge `Module.IsMPseudoCoherentRelativeTo` /
`Module.IsPseudoCoherentRelativeTo` rather than repeating `ModuleCat.of A M`. -/

namespace Module

/-- Helper for Lemma 15.82.7: the unbundled module owner for relative `m`-pseudo-coherence, kept
local to this item so the proof can reuse the compiled presentationwise owners from
`Lemma_15_82_10`. -/
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : Type w) [AddCommGroup M] [Module A M] (m : ℤ) : Prop :=
  (ModuleCat.of A M).IsMPseudoCoherentRelativeTo R m

/-- Helper for Lemma 15.82.7: the unbundled module owner for relative pseudo-coherence, kept
local to this item so the proof can stay on the `15.65.4 + definitions` route despite the missing
compiled `Definition_15_82_4` owner file. -/
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : Type w) [AddCommGroup M] [Module A M] : Prop :=
  (ModuleCat.of A M).IsPseudoCoherentRelativeTo R

end Module

omit [Algebra.FiniteType R A] in
/-- Helper for Lemma 15.82.7: restricting the degree-zero single complex of `M` along a
polynomial presentation identifies its `m`-pseudo-coherence with the `m`-pseudo-coherence of the
restricted module. -/
lemma presentation_restriction_isMPseudoCoherent_iff {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (m : ℤ) :
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    (CochainComplex.polynomialPresentationRestriction
      ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj MA) α).IsMPseudoCoherent m ↔
      MP.IsMPseudoCoherent m := by
  let MA : ModuleCat A := ModuleCat.of A M
  let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
  let E :
      CochainComplex (ModuleCat (MvPolynomial (Fin n) R)) ℤ :=
    CochainComplex.polynomialPresentationRestriction
      ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj MA) α
  let e :
      ModuleCat.single0Functor.obj MP ≅ DerivedCategory.Q.obj E :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (MvPolynomial (Fin n) R)) (0 : ℤ)).app MP) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars α.toRingHom)
          (0 : ℤ)).app MA).symm
  constructor
  · intro hE
    -- Proof comment: transport the presentationwise pseudo-coherence statement across the
    -- canonical comparison between the restricted single complex and the restricted module.
    simpa [E, MP, ModuleCat.IsMPseudoCoherent, CochainComplex.polynomialPresentationRestriction] using
      isMPseudoCoherent_of_iso e.symm m hE
  · intro hMP
    -- Proof comment: the same comparison isomorphism converts the restricted module back into the
    -- restricted degree-zero single complex.
    simpa [E, MP, ModuleCat.IsMPseudoCoherent, CochainComplex.polynomialPresentationRestriction] using
      isMPseudoCoherent_of_iso e m hMP

/-- Helper for Lemma 15.82.7: a bundled module is pseudo-coherent exactly when it is
`m`-pseudo-coherent for every integer `m`. -/
lemma moduleCat_isPseudoCoherent_iff_forall_isMPseudoCoherent_local
    {S : Type u} [Ring S] (N : ModuleCat S) :
    N.IsPseudoCoherent ↔ ∀ m : ℤ, N.IsMPseudoCoherent m := by
  -- Proof comment: this is the remaining universe-polymorphic bridge between absolute
  -- pseudo-coherence and degreewise `m`-pseudo-coherence for module objects.
  sorry

/-- Helper for Lemma 15.82.7: relative `m`-pseudo-coherence of an ordinary module is exactly the
pointwise absolute `m`-pseudo-coherence of its restrictions along surjective polynomial
presentations. -/
lemma module_isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
    (m : ℤ) :
    Module.IsMPseudoCoherentRelativeTo R A M m ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          (ModuleCat.of P M).IsMPseudoCoherent m := by
  constructor
  · intro hM
    intro n α hα
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    -- Proof comment: unfold the relative module predicate to the degree-zero single complex and
    -- identify restriction of scalars of that single complex with the single complex of the
    -- restricted module.
    have hPresentation :
        (CochainComplex.polynomialPresentationRestriction
          ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj MA) α).IsMPseudoCoherent m := by
      simpa [Module.IsMPseudoCoherentRelativeTo, ModuleCat.IsMPseudoCoherentRelativeTo,
        CochainComplex.IsMPseudoCoherentRelativeTo, MA] using hM n α hα
    have hMP : MP.IsMPseudoCoherent m :=
      (presentation_restriction_isMPseudoCoherent_iff
        (R := R) (A := A) (M := M) α m).1 hPresentation
    simpa [MP, MA] using hMP
  · intro hM
    intro n α hα
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    -- Proof comment: the presentationwise absolute module condition is exactly the relative
    -- condition specialized to the chosen presentation.
    have hMP : MP.IsMPseudoCoherent m := by
      simpa [MP, MA] using hM n α hα
    have hPresentation :
        (CochainComplex.polynomialPresentationRestriction
          ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj MA) α).IsMPseudoCoherent m :=
      (presentation_restriction_isMPseudoCoherent_iff
        (R := R) (A := A) (M := M) α m).2 hMP
    simpa [Module.IsMPseudoCoherentRelativeTo, ModuleCat.IsMPseudoCoherentRelativeTo,
      CochainComplex.IsMPseudoCoherentRelativeTo, MA] using hPresentation

/-- Helper for Lemma 15.82.7: relative pseudo-coherence of an ordinary module is exactly the
pointwise absolute pseudo-coherence of its restrictions along surjective polynomial
presentations. -/
lemma module_isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation :
    Module.IsPseudoCoherentRelativeTo R A M ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          (ModuleCat.of P M).IsPseudoCoherent := by
  constructor
  · intro hM
    intro n α hα
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    have hAll : ∀ m : ℤ, MP.IsMPseudoCoherent m := by
      intro m
      have hPresentation :
          (CochainComplex.polynomialPresentationRestriction
            ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj MA) α).IsMPseudoCoherent m := by
        simpa [Module.IsPseudoCoherentRelativeTo, Module.IsMPseudoCoherentRelativeTo,
          ModuleCat.IsPseudoCoherentRelativeTo, CochainComplex.IsPseudoCoherentRelativeTo,
          ModuleCat.IsMPseudoCoherentRelativeTo, CochainComplex.IsMPseudoCoherentRelativeTo, MA] using
          hM m n α hα
      exact
        (presentation_restriction_isMPseudoCoherent_iff
          (R := R) (A := A) (M := M) α m).1 hPresentation
    have hPseudo : MP.IsPseudoCoherent := by
      exact (moduleCat_isPseudoCoherent_iff_forall_isMPseudoCoherent_local MP).2 hAll
    -- Proof comment: identify the restricted degree-zero complex with the module over the
    -- presentation ring.
    simpa [MP, MA] using hPseudo
  · intro hM
    intro m
    exact
      (module_isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
        (R := R) (A := A) (M := M) m).2 <| by
          intro n α hα
          let MA : ModuleCat A := ModuleCat.of A M
          let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
          have hPresentation : MP.IsPseudoCoherent := by
            exact hM n α hα
          have hMP : MP.IsMPseudoCoherent m := by
            exact
              (moduleCat_isPseudoCoherent_iff_forall_isMPseudoCoherent_local MP).1 hPresentation m
          simpa [MP, MA] using hMP

omit [Algebra.FiniteType R A] in
/-- Helper for Lemma 15.82.7: finite generation over a surjective presentation ring descends to
finite generation over the quotient algebra. -/
lemma module_finite_of_compHom_surjective
    {S : Type u} [CommRing S] [Algebra R S]
    (α : S →ₐ[R] A) (_hα : Function.Surjective α)
    (hM :
      let _ : Module S M := Module.compHom M α.toRingHom
      Module.Finite S M) :
    Module.Finite A M := by
  letI : Algebra S A := α.toAlgebra
  letI : Module S M := Module.compHom M α.toRingHom
  letI : IsScalarTower S A M := IsScalarTower.of_compHom S A M
  letI : Module.Finite S M := by
    simpa using hM
  rcases (Module.Finite.iff_exists_surjective_free S M).1 (inferInstance : Module.Finite S M) with
    ⟨n, f, hf⟩
  let g : (Fin n → A) →ₗ[A] M :=
    Module.piEquiv (Fin n) A M (fun i ↦ f (Pi.single i (1 : S)))
  have hg : Function.Surjective g := by
    -- Proof comment: the chosen `S`-linear generators remain generators after composing with the
    -- surjection `S → A`.
    intro m
    rcases hf m with ⟨x, rfl⟩
    refine ⟨fun i ↦ α (x i), ?_⟩
    have hx : x = ∑ i, x i • (Pi.single i (1 : S) : Fin n → S) := by
      -- Proof comment: decompose the source vector against the standard basis of `S^n`.
      ext i
      simp [Pi.single_apply]
    -- Proof comment: the same generators in `M` now define an `A`-linear free cover.
    calc
      g (fun i ↦ α (x i)) =
          ∑ i, α (x i) • f (Pi.single i (1 : S)) := by
            simpa only [g] using
              (Module.piEquiv_apply_apply (Fin n) A M
                (fun i ↦ f (Pi.single i (1 : S))) (fun i ↦ α (x i)))
      _ = ∑ i, x i • f (Pi.single i (1 : S)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rfl
      _ = ∑ i, f (x i • (Pi.single i (1 : S) : Fin n → S)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (f.map_smul (x i) (Pi.single i (1 : S) : Fin n → S)).symm
      _ = f (∑ i, x i • (Pi.single i (1 : S) : Fin n → S)) := by
            symm
            simp only [map_sum]
      _ = f x := by
            rw [← hx]
  exact Module.Finite.of_surjective g hg

/-- Helper for Lemma 15.82.7: a finite module admits a surjective finite free cover whose source
lives in the ambient module universe. -/
lemma exists_surjective_shrink_free_cover
    {S : Type u} [Ring S] {N : Type w} [AddCommGroup N] [Module S N]
    [Module.Finite S N] :
    ∃ (F : Type w) (_ : AddCommGroup F) (_ : Module S F),
      Module.Free S F ∧ Module.Finite S F ∧
      ∃ f : F →ₗ[S] N, Function.Surjective f := by
  rcases (Module.Finite.iff_exists_surjective_free S N).1 inferInstance with ⟨n, f, hf⟩
  let e : Shrink.{w} (Fin n → S) ≃ₗ[S] (Fin n → S) := Shrink.linearEquiv S (Fin n → S)
  refine ⟨Shrink.{w} (Fin n → S), inferInstance, inferInstance, ?_, ?_, f.comp e.toLinearMap, ?_⟩
  · exact Module.Free.of_equiv e.symm
  · exact Module.Finite.equiv e.symm
  · intro x
    rcases hf x with ⟨y, rfl⟩
    refine ⟨e.symm y, ?_⟩
    simp [e]

/-- Helper for Lemma 15.82.7: the degree-zero homology of the single complex is the original
module object in the current module universe. -/
noncomputable abbrev single_zero_complex_homology_iso_univ_local
    {S : Type u} [Ring S] (N : ModuleCat.{w} S) :
    (((CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj N).homology 0) ≅ N :=
  HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) N

/-- Helper for Lemma 15.82.7: the single complex on a finite free module is termwise finite free
in the ambient module universe. -/
lemma single_zero_complex_isTermwiseFiniteFree_univ_local
    {S : Type u} [Ring S] (F : ModuleCat.{w} S) [Module.Free S F] [Module.Finite S F] :
    ((CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F).IsTermwiseFiniteFree := by
  -- Proof comment: degree `0` is `F`, and every other term is the zero module.
  refine ⟨fun i ↦ ?_⟩
  by_cases hi : i = 0
  · let e :
        (((CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F).X i) ≅ F := by
        subst hi
        simpa using HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) F
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩
  · let E : CochainComplex (ModuleCat.{w} S) ℤ :=
      (CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F
    let hzero : IsZero (E.X i) := by
      simpa [E] using
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) F i hi)
    letI : Subsingleton ↥(E.X i) := ModuleCat.subsingleton_of_isZero hzero
    have hfree : Module.Free S (E.X i) :=
      Module.Free.of_subsingleton (R := S) (N := ↥(E.X i))
    have hfinite : Module.Finite S (E.X i) := by
      let e : ModuleCat.of S PUnit ≅ E.X i :=
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of S PUnit)).isoZero ≪≫ hzero.isoZero.symm
      exact Module.Finite.equiv e.toLinearEquiv
    exact ⟨hfree, hfinite⟩

/-- Helper for Lemma 15.82.7: a degree-zero module object has vanishing derived homology away from
degree `0` in the current module universe. -/
lemma single_zero_complex_homology_isZero_of_ne_univ_local
    {S : Type u} [Ring S] (N : ModuleCat.{w} S) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj (ModuleCat.single0Functor.obj N)) := by
  -- Proof comment: degree-zero objects lie in both truncation halves at degree `0`.
  by_cases hlt : i < 0
  · exact DerivedCategory.isZero_of_isGE _ 0 i hlt
  · have hgt : 0 < i := by
      omega
    exact DerivedCategory.isZero_of_isLE _ 0 i hgt

/-- Helper for Lemma 15.82.7: the `Q(single -)` comparison induces the identity on zeroth
homology in the current module universe. -/
lemma homology_map_singleFunctorIsoCompQ_app_zero_eq_id_univ_local
    {S : Type u} [Ring S] (N : ModuleCat.{w} S) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app N).hom) =
      𝟙 _ := by
  change
    (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
        (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj N))) =
      𝟙 _
  simp

/-- Helper for Lemma 15.82.7: if `f ≫ e.hom` is epi and `e` is an isomorphism, then `f` is epi,
in the current module universe. -/
lemma epi_of_epi_comp_iso_univ_local
    {S : Type u} [Ring S] {X Y Z : ModuleCat.{w} S} (f : X ⟶ Y) (e : Y ≅ Z) [Epi (f ≫ e.hom)] :
    Epi f := by
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

/-- Helper for Lemma 15.82.7: after the canonical zeroth-homology identifications, the homology
map induced by a degree-zero cover is the original module map in the current module universe. -/
lemma single_zero_cover_homology_map_eq_univ_local
    {S : Type u} [Ring S] {F N : ModuleCat.{w} S} (f : F ⟶ N) :
    let α :
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F) ⟶
          ModuleCat.single0Functor.obj N :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom ≫
        ModuleCat.single0Functor.map f
    (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map α ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} S) (0 : ℤ)).app N).hom =
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} S) (0 : ℤ)).app F).hom ≫
        f := by
  let α :
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F) ⟶
        ModuleCat.single0Functor.obj N :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom ≫
      ModuleCat.single0Functor.map f
  let eF :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} S) (0 : ℤ)).app F
  let eN :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} S) (0 : ℤ)).app N
  have hnat :=
    NatIso.naturality_1
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} S) (0 : ℤ)) f
  have hnat' :
      (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
          (ModuleCat.single0Functor.map f) ≫
        eN.hom =
      eF.hom ≫ f := by
    have hstep1 :
        (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
            (ModuleCat.single0Functor.map f) ≫ eN.hom =
          eF.hom ≫
            (eF.inv ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
                (ModuleCat.single0Functor.map f) ≫
                eN.hom) := by
      simpa [Category.assoc] using
        (Iso.hom_inv_id_assoc eF
          ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
            (ModuleCat.single0Functor.map f) ≫
              eN.hom)).symm
    have hstep2 :
        eF.hom ≫
            (eF.inv ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
                (ModuleCat.single0Functor.map f) ≫
                eN.hom) =
          eF.hom ≫ f := by
      simpa [eF, eN, Category.assoc] using congrArg (fun k ↦ eF.hom ≫ k) hnat
    exact hstep1.trans hstep2
  have hsplit :
      (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map α ≫ eN.hom =
        (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom) ≫
          ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
              (ModuleCat.single0Functor.map f) ≫
            eN.hom) := by
    dsimp [α]
    rw [Functor.map_comp]
    rfl
  have hmid :
      (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map α ≫ eN.hom =
        (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom) ≫
          eF.hom ≫ f := by
    have hstep3 :
        (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
              (ModuleCat.single0Functor.map f) ≫
            eN.hom =
          (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom) ≫
              eF.hom ≫ f := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
                (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom) ≫
              k)
          hnat'
    exact hsplit.trans hstep3
  have hfinal :
      (DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map
          (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom) ≫
        eF.hom ≫ f =
      eF.hom ≫ f := by
    rw [homology_map_singleFunctorIsoCompQ_app_zero_eq_id_univ_local (S := S) F]
    change
      𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F)) ≫
          (eF.hom ≫ f) =
        eF.hom ≫ f
    simpa using Category.id_comp (eF.hom ≫ f)
  exact hmid.trans hfinal

/-- Helper for Lemma 15.82.7: a surjective degree-zero finite free cover induces an epimorphism
on zeroth homology in the current module universe. -/
lemma single_zero_cover_homology_epi_of_surjective_univ_local
    {S : Type u} [Ring S] {F N : ModuleCat.{w} S} (f : F ⟶ N) (hf : Function.Surjective f.hom) :
    let α :
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F) ⟶
          ModuleCat.single0Functor.obj N :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom ≫
        ModuleCat.single0Functor.map f
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map α) := by
  let α :
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F) ⟶
        ModuleCat.single0Functor.obj N :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom ≫
      ModuleCat.single0Functor.map f
  let eF :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} S) (0 : ℤ)).app F
  have hcomp :
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map α ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} S) (0 : ℤ)).app N).hom) := by
    rw [single_zero_cover_homology_map_eq_univ_local (S := S) f]
    exact
      (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [eF, Category.assoc] using hf.comp eF.toLinearEquiv.surjective
  exact
    epi_of_epi_comp_iso_univ_local
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) (0 : ℤ)).map α)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} S) (0 : ℤ)).app N)

/-- Helper for Lemma 15.82.7: a finite free module object is `m`-pseudo-coherent in the current
module universe. -/
lemma finite_free_module_isMPseudoCoherent_univ_local
    {S : Type u} [Ring S] (F : ModuleCat.{w} S) (m : ℤ) [Module.Free S F] [Module.Finite S F] :
    F.IsMPseudoCoherent m := by
  let E : CochainComplex (ModuleCat.{w} S) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F
  let hEfree : E.IsTermwiseFiniteFree := single_zero_complex_isTermwiseFiniteFree_univ_local (S := S) F
  let α : DerivedCategory.Q.obj E ⟶ ModuleCat.single0Functor.obj F :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F).hom
  refine ⟨E, ⟨0, 0, inferInstance, inferInstance⟩, hEfree, α, ?_, ?_⟩
  · intro i hi
    letI : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).map α) :=
      Functor.map_isIso (DerivedCategory.homologyFunctor (ModuleCat.{w} S) i) α
    infer_instance
  · letI : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) m).map α) :=
      Functor.map_isIso (DerivedCategory.homologyFunctor (ModuleCat.{w} S) m) α
    infer_instance

/-- Helper for Lemma 15.82.7: the kernel inclusion followed by the original map is zero in the
current module universe. -/
lemma kernel_subtype_comp_eq_zero_univ_local
    {S : Type u} [Ring S] {F N : ModuleCat.{w} S} (f : F ⟶ N) :
    f.hom.comp (LinearMap.ker f.hom).subtype = 0 := by
  ext x
  simpa [LinearMap.comp_apply, LinearMap.mem_ker] using x.2

/-- Helper for Lemma 15.82.7: the kernel sequence of a surjective map is short exact in the
current module universe. -/
theorem kernel_cover_shortExact_univ_local
    {S : Type u} [Ring S] {F N : ModuleCat.{w} S} (f : F ⟶ N) (hf : Function.Surjective f.hom) :
    (ShortComplex.moduleCatMk (LinearMap.ker f.hom).subtype f.hom
      (kernel_subtype_comp_eq_zero_univ_local (S := S) f)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa using LinearMap.exact_subtype_ker_map f.hom
  · exact (ModuleCat.mono_iff_injective _).2 (LinearMap.ker f.hom).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).2 hf

/-- Helper for Lemma 15.82.7: the kernel of a surjective finite free cover of a
`(-(d + 1))`-pseudo-coherent module is `(-d)`-pseudo-coherent in the current module universe. -/
lemma kernel_of_surjective_finite_free_cover_isMPseudoCoherent_univ_local
    {S : Type u} [Ring S] {F N : ModuleCat.{w} S} (f : F ⟶ N) (hf : Function.Surjective f.hom)
    (d : ℕ) [Module.Free S F] [Module.Finite S F]
    (hN : N.IsMPseudoCoherent (-(d + 1 : ℤ))) :
    (ModuleCat.of S (LinearMap.ker f.hom)).IsMPseudoCoherent (-(d : ℤ)) := by
  let SC : ShortComplex (ModuleCat.{w} S) :=
    ShortComplex.moduleCatMk (LinearMap.ker f.hom).subtype f.hom
      (kernel_subtype_comp_eq_zero_univ_local (S := S) f)
  have hSC : SC.ShortExact := by
    simpa [SC] using kernel_cover_shortExact_univ_local (S := S) f hf
  let T : Triangle (DerivedCategory (ModuleCat.{w} S)) := hSC.singleTriangle
  have hF : T.obj₂.IsMPseudoCoherent (-(d : ℤ)) := by
    simpa [T, SC, ModuleCat.IsMPseudoCoherent] using
      finite_free_module_isMPseudoCoherent_univ_local (S := S) F (-(d : ℤ))
  have hF' : T.obj₂.IsMPseudoCoherent ((-(d + 1 : ℤ)) + 1) := by
    simpa using hF
  have hN' : T.obj₃.IsMPseudoCoherent (-(d + 1 : ℤ)) := by
    simpa [T, SC, ModuleCat.IsMPseudoCoherent] using hN
  have hK :
      T.obj₁.IsMPseudoCoherent ((-(d + 1 : ℤ)) + 1) :=
    isMPseudoCoherent_obj₁_of_distinguishedTriangle
      (R := S) T hSC.singleTriangle_distinguished hF' hN'
  simpa [T, SC, ModuleCat.IsMPseudoCoherent] using hK

/-- Helper for Lemma 15.82.7: the absolute degree-zero criterion holds in the current module
universe. -/
lemma moduleCat_isZeroPseudoCoherent_iff_finite_univ_local
    {S : Type u} [Ring S] (N : ModuleCat.{w} S) :
    N.IsMPseudoCoherent 0 ↔ Module.Finite S N := by
  constructor
  · intro hN
    let E : CochainComplex (ModuleCat.{w} S) ℤ :=
      (CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj N
    have hE : E.IsMPseudoCoherent 0 := by
      exact
        isMPseudoCoherent_of_iso
          (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app N).symm) 0 hN
    have hfiniteH : Module.Finite S (E.homology 0) := by
      exact CochainComplex.homology_finite_of_isMPseudoCoherent
        (R := S) hE
        (fun i hi ↦ HomologicalComplex.isZero_single_obj_homology
          (ComplexShape.up ℤ) (0 : ℤ) N i (by omega))
    letI : Module.Finite S (E.homology 0) := hfiniteH
    exact Module.Finite.equiv (single_zero_complex_homology_iso_univ_local (S := S) N).toLinearEquiv
  · intro hN
    letI : Module.Finite S N := hN
    rcases exists_surjective_shrink_free_cover (S := S) (N := N) with
      ⟨F, _hFadd, _hFmod, hFfree, hFfinite, f, hf⟩
    let F₀ : ModuleCat.{w} S := ModuleCat.of S F
    let g : F₀ ⟶ N := ModuleCat.ofHom f
    letI : Module.Free S F := hFfree
    letI : Module.Finite S F := hFfinite
    let E : CochainComplex (ModuleCat.{w} S) ℤ :=
      (CochainComplex.singleFunctor (ModuleCat.{w} S) (0 : ℤ)).obj F₀
    let hEfree : E.IsTermwiseFiniteFree :=
      single_zero_complex_isTermwiseFiniteFree_univ_local (S := S) F₀
    let α : DerivedCategory.Q.obj E ⟶ ModuleCat.single0Functor.obj N :=
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F₀).hom ≫
        ModuleCat.single0Functor.map g
    refine ⟨E, ⟨0, 0, inferInstance, inferInstance⟩, hEfree, α, ?_, ?_⟩
    · intro i hi
      have hi0 : i ≠ 0 := by
        omega
      let hsrcSingle :
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj
            (ModuleCat.single0Functor.obj F₀)) :=
        single_zero_complex_homology_isZero_of_ne_univ_local (S := S) F₀ i hi0
      let hsrc :
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj (DerivedCategory.Q.obj E)) := by
        exact
          ((((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) (0 : ℤ)).app F₀)).isZero_iff).2
            hsrcSingle)
      let htgt :
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj
            (ModuleCat.single0Functor.obj N)) :=
        single_zero_complex_homology_isZero_of_ne_univ_local (S := S) N i hi0
      exact hsrc.isIso htgt ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).map α)
    · exact single_zero_cover_homology_epi_of_surjective_univ_local (S := S) g hf

/-- Helper for Lemma 15.82.7: the absolute `(-1)` criterion holds in the current module
universe. -/
lemma moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation_univ_local
    {S : Type u} [Ring S] (N : ModuleCat.{w} S) :
    N.IsMPseudoCoherent (-1) ↔ Module.FinitePresentation S N := by
  constructor
  · intro hN
    have hN0 : N.IsMPseudoCoherent 0 := by
      rw [ModuleCat.IsMPseudoCoherent] at hN ⊢
      exact isMPseudoCoherent_mono (R := S) (show (-1 : ℤ) ≤ 0 by omega) hN
    have hfiniteN : Module.Finite S N :=
      (moduleCat_isZeroPseudoCoherent_iff_finite_univ_local (S := S) N).1 hN0
    letI : Module.Finite S N := hfiniteN
    rcases exists_surjective_shrink_free_cover (S := S) (N := N) with
      ⟨F, _hFadd, _hFmod, hFfree, hFfinite, f, hf⟩
    let F₀ : ModuleCat.{w} S := ModuleCat.of S F
    let g : F₀ ⟶ N := ModuleCat.ofHom f
    letI : Module.Free S F := hFfree
    letI : Module.Finite S F := hFfinite
    have hkerPc :
        (ModuleCat.of S (LinearMap.ker g.hom)).IsMPseudoCoherent 0 :=
      kernel_of_surjective_finite_free_cover_isMPseudoCoherent_univ_local (S := S) g hf 0 hN
    have hkerFinite :
        Module.Finite S (LinearMap.ker g.hom) :=
      (moduleCat_isZeroPseudoCoherent_iff_finite_univ_local (S := S)
        (ModuleCat.of S (LinearMap.ker g.hom))).1 hkerPc
    letI : Module.Finite S (LinearMap.ker g.hom) := hkerFinite
    have hkerFG : (LinearMap.ker g.hom).FG := by
      have hkerEq :
          LinearMap.ker g.hom = LinearMap.range (LinearMap.ker g.hom).subtype := by
        ext x
        constructor
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact x.2
      rw [hkerEq]
      exact Submodule.fg_range (LinearMap.ker g.hom).subtype
    exact Module.finitePresentation_of_surjective g.hom hf hkerFG
  · intro hN
    letI : Module.FinitePresentation S N := hN
    letI : Module.Finite S N := inferInstance
    rcases exists_surjective_shrink_free_cover (S := S) (N := N) with
      ⟨F, _hFadd, _hFmod, hFfree, hFfinite, f, hf⟩
    let F₀ : ModuleCat.{w} S := ModuleCat.of S F
    let q : F₀ ⟶ N := ModuleCat.ofHom f
    letI : Module.Free S F := hFfree
    letI : Module.Finite S F := hFfinite
    have hkerFinite : Module.Finite S (LinearMap.ker f) := by
      exact Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
    have hkerPc :
        (ModuleCat.of S (LinearMap.ker f)).IsMPseudoCoherent 0 :=
      (moduleCat_isZeroPseudoCoherent_iff_finite_univ_local (S := S)
        (ModuleCat.of S (LinearMap.ker f))).2 hkerFinite
    let SC : ShortComplex (ModuleCat.{w} S) :=
      ShortComplex.moduleCatMk (LinearMap.ker q.hom).subtype q.hom
        (kernel_subtype_comp_eq_zero_univ_local (S := S) q)
    have hSC : SC.ShortExact := by
      simpa [SC] using kernel_cover_shortExact_univ_local (S := S) q hf
    let T : Triangle (DerivedCategory (ModuleCat.{w} S)) := hSC.singleTriangle
    have hleft : T.obj₁.IsMPseudoCoherent 0 := by
      simpa [T, SC, ModuleCat.IsMPseudoCoherent] using hkerPc
    have hmiddle : T.obj₂.IsMPseudoCoherent (-1) := by
      simpa [T, SC, ModuleCat.IsMPseudoCoherent] using
        finite_free_module_isMPseudoCoherent_univ_local (S := S) F₀ (-1)
    simpa [T, SC, ModuleCat.IsMPseudoCoherent] using
      (isMPseudoCoherent_obj₃_of_distinguishedTriangle
        (R := S) T hSC.singleTriangle_distinguished hleft hmiddle)

/-- Helper for Lemma 15.82.7: the absolute negative-degree finite-free-resolution criterion holds
in the current module universe. -/
lemma moduleCat_isNegPseudoCoherent_iff_hasFiniteFreeResolutionLength_univ_local
    {S : Type u} [Ring S] (N : ModuleCat.{w} S) (d : ℕ) :
    N.IsMPseudoCoherent (-(d : ℤ)) ↔ Module.HasLengthFiniteFreeResolution S N d := by
  induction d generalizing N with
  | zero =>
      simpa [Module.HasLengthFiniteFreeResolution] using
        (moduleCat_isZeroPseudoCoherent_iff_finite_univ_local (S := S) N)
  | succ d ih =>
      constructor
      · intro hN
        have hN0 : N.IsMPseudoCoherent 0 := by
          rw [ModuleCat.IsMPseudoCoherent] at hN ⊢
          exact isMPseudoCoherent_mono (R := S) (show (-(d + 1 : ℤ)) ≤ 0 by omega) hN
        have hfiniteN : Module.Finite S N :=
          (moduleCat_isZeroPseudoCoherent_iff_finite_univ_local (S := S) N).1 hN0
        letI : Module.Finite S N := hfiniteN
        rcases exists_surjective_shrink_free_cover (S := S) (N := N) with
          ⟨F, _hFadd, _hFmod, hFfree, hFfinite, f, hf⟩
        let F₀ : ModuleCat.{w} S := ModuleCat.of S F
        let g : F₀ ⟶ N := ModuleCat.ofHom f
        letI : Module.Free S F := hFfree
        letI : Module.Finite S F := hFfinite
        have hkerPc :
            (ModuleCat.of S (LinearMap.ker g.hom)).IsMPseudoCoherent (-(d : ℤ)) :=
          kernel_of_surjective_finite_free_cover_isMPseudoCoherent_univ_local (S := S) g hf d hN
        have hkerRes :
            Module.HasLengthFiniteFreeResolution S (LinearMap.ker g.hom) d :=
          (ih (ModuleCat.of S (LinearMap.ker g.hom))).1 hkerPc
        exact
          (Module.hasLengthFiniteFreeResolution_succ_iff (R := S) (M := N) d).2
            ⟨F, inferInstance, inferInstance, hFfree, hFfinite, f, hf, hkerRes⟩
      · intro hN
        rcases (Module.hasLengthFiniteFreeResolution_succ_iff (R := S) (M := N) d).1 hN with
          ⟨F, _hFadd, _hFmod, hfree, hfinite, f, hf, hker⟩
        let F₀ : ModuleCat.{w} S := ModuleCat.of S F
        let q : F₀ ⟶ N := ModuleCat.ofHom f
        letI : Module.Free S F := hfree
        letI : Module.Finite S F := hfinite
        have hkerPc :
            (ModuleCat.of S (LinearMap.ker f)).IsMPseudoCoherent (-(d : ℤ)) :=
          (ih (ModuleCat.of S (LinearMap.ker f))).2 hker
        let SC : ShortComplex (ModuleCat.{w} S) :=
          ShortComplex.moduleCatMk (LinearMap.ker q.hom).subtype q.hom
            (kernel_subtype_comp_eq_zero_univ_local (S := S) q)
        have hSC : SC.ShortExact := by
          simpa [SC] using kernel_cover_shortExact_univ_local (S := S) q hf
        let T : Triangle (DerivedCategory (ModuleCat.{w} S)) := hSC.singleTriangle
        have hleft : T.obj₁.IsMPseudoCoherent (-(d : ℤ)) := by
          simpa [T, SC, ModuleCat.IsMPseudoCoherent] using hkerPc
        have hmiddle : T.obj₂.IsMPseudoCoherent (-(d + 1 : ℤ)) := by
          simpa [T, SC, ModuleCat.IsMPseudoCoherent] using
            finite_free_module_isMPseudoCoherent_univ_local (S := S) F₀ (-(d + 1 : ℤ))
        have hleft' : T.obj₁.IsMPseudoCoherent ((-(d + 1 : ℤ)) + 1) := by
          simpa using hleft
        simpa [T, SC, ModuleCat.IsMPseudoCoherent] using
          (isMPseudoCoherent_obj₃_of_distinguishedTriangle
            (R := S) T hSC.singleTriangle_distinguished hleft' hmiddle)

/-- Helper for Lemma 15.82.7: an infinite finite free resolution gives pseudo-coherence in the
current module universe. -/
lemma isPseudoCoherent_of_finite_free_resolution_univ_local
    {S : Type u} [Ring S] {N : ModuleCat.{w} S} {F : ChainComplex (ModuleCat.{w} S) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat.{w} S)).obj N)
    [ChainComplex.IsFiniteFreeResolution π] :
    N.IsPseudoCoherent := by
  let E : CochainComplex (ModuleCat.{w} S) ℤ := F.extend ComplexShape.embeddingDownNat
  have hE : E.IsTermwiseFiniteFree :=
    extend_embeddingDownNat_isTermwiseFiniteFree (R := S) π
  obtain ⟨e⟩ := extend_resolution_single0_iso (R := S) π
  rw [ModuleCat.IsPseudoCoherent]
  exact ⟨E, ⟨0, inferInstance⟩, hE, e.hom, by infer_instance⟩

/-- Helper for Lemma 15.82.7: the absolute pseudo-coherent versus infinite-resolution criterion
holds in the current module universe. -/
lemma moduleCat_isPseudoCoherent_iff_exists_infiniteFiniteFreeResolution_univ_local
    {S : Type u} [Ring S] (N : ModuleCat.{w} S) :
    N.IsPseudoCoherent ↔
      ∃ (F : ChainComplex (ModuleCat.{w} S) ℕ)
        (π : F ⟶ (ChainComplex.single₀ (ModuleCat.{w} S)).obj N),
        ChainComplex.IsFiniteFreeResolution π := by
  constructor
  · intro hN
    rw [ModuleCat.IsPseudoCoherent] at hN
    rcases hN with ⟨E, ⟨b, hEb⟩, hEfree, α, hα⟩
    letI : E.IsTermwiseFiniteFree := hEfree
    letI : IsIso α := hα
    obtain ⟨β, hβ, _hQβ⟩ :=
      exists_strict_single0_map_of_pseudoCoherent_witness
        (R := S) (E := E) (M := N) b hEb α
    let F : ChainComplex (ModuleCat.{w} S) ℕ := E.restriction ComplexShape.embeddingDownNat
    let π :
        F ⟶ (ChainComplex.single₀ (ModuleCat.{w} S)).obj N :=
      HomologicalComplex.restrictionMap β ComplexShape.embeddingDownNat ≫
        (Classical.choice (restriction_single0_iso (R := S) N)).hom
    have hπ : ChainComplex.IsFiniteFreeResolution π :=
      restriction_single_quasiIso_isFiniteFreeResolution (R := S) β hβ
    exact ⟨F, π, hπ⟩
  · rintro ⟨F, π, hπ⟩
    letI : ChainComplex.IsFiniteFreeResolution π := hπ
    exact isPseudoCoherent_of_finite_free_resolution_univ_local (S := S) π

-- Proof sketch: for each surjective polynomial presentation `α`, apply Lemma `15.65.4 (1)` over
-- `MvPolynomial (Fin n) R` to identify `0`-pseudo-coherence with finite generation. Finite
-- generation descends and ascends along the surjection `α`, so the pointwise condition is
-- equivalent to finite generation over `A`.
/-- Lemma 15.82.7 (1): an `A`-module is `0`-pseudo-coherent relative to `R` exactly when it is a
finite `A`-module. -/
theorem Module.isZeroPseudoCoherentRelativeTo_iff_finite :
    Module.IsMPseudoCoherentRelativeTo R A M 0 ↔ Module.Finite A M := by
  constructor
  · intro hM
    obtain ⟨n, α, hα⟩ :=
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
    let P := MvPolynomial (Fin n) R
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    letI : Module P M := Module.compHom M α.toRingHom
    have hMP : MP.IsMPseudoCoherent 0 := by
      -- Proof comment: test the relative predicate on one chosen surjective polynomial
      -- presentation of `A`.
      exact
        (module_isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
          (R := R) (A := A) (M := M) 0).1 hM n α hα
    have hfiniteP : Module.Finite P M := by
      -- Proof comment: over the presentation ring, Lemma `15.65.4 (1)` identifies the restricted
      -- module with a finite module.
      simpa [MP, MA] using
        (moduleCat_isZeroPseudoCoherent_iff_finite_univ_local (S := P) MP).1 hMP
    -- Proof comment: finite generation descends from the chosen surjective presentation to `A`.
    exact module_finite_of_compHom_surjective (R := R) (A := A) (M := M) α hα <| by
      simpa [P] using hfiniteP
  · intro hM
    refine
      (module_isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
        (R := R) (A := A) (M := M) 0).2 ?_
    intro n α hα
    let P := MvPolynomial (Fin n) R
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    letI : Algebra P A := α.toAlgebra
    letI : Module P M := Module.compHom M α.toRingHom
    letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
    letI : Module.Finite P A := Module.Finite.of_surjective (Algebra.linearMap P A) hα
    letI : Module.Finite P M := Module.Finite.trans A M
    -- Proof comment: every presentation ring sees `M` as finite because `A` is finite over that
    -- ring and `M` is finite over `A`.
    simpa [MP, MA] using
      (moduleCat_isZeroPseudoCoherent_iff_finite_univ_local (S := P) MP).2 inferInstance

-- Proof sketch: apply Lemma `15.65.4 (2)` to each surjective polynomial presentation of `A` over
-- `R`. Then use Lemma `15.81.1` to pass between finite presentation over one presentation and over
-- every presentation.
/-- Lemma 15.82.7 (2): an `A`-module is `(-1)`-pseudo-coherent relative to `R` exactly when it is
finitely presented relative to `R`. -/
theorem Module.isMinusOnePseudoCoherentRelativeTo_iff_finitePresentationRelativeTo :
    Module.IsMPseudoCoherentRelativeTo R A M (-1) ↔
      Module.FinitePresentationRelativeTo R A M := by
  constructor
  · intro hM
    refine
      (Module.FinitePresentationRelativeTo.iff_overEveryPolynomialPresentation
        (R := R) (A := A) (M := M)).2 ?_
    intro n α hα
    let P := MvPolynomial (Fin n) R
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    have hMP : MP.IsMPseudoCoherent (-1) := by
      -- Proof comment: evaluate the relative `(-1)`-pseudo-coherent condition on the chosen
      -- polynomial presentation.
      exact
        (module_isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
          (R := R) (A := A) (M := M) (-1)).1 hM n α hα
    -- Proof comment: the absolute `(-1)`-criterion over the presentation ring is finite
    -- presentation.
    exact
      (moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation_univ_local
        (S := P) MP).1 <| by
          simpa [MP, MA] using hMP
  · intro hM
    refine
      (module_isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
        (R := R) (A := A) (M := M) (-1)).2 ?_
    intro n α hα
    let P := MvPolynomial (Fin n) R
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    have hfinitePresentationP : Module.FinitePresentation P M := by
      -- Proof comment: finite presentation relative to `R` can be checked over every surjective
      -- polynomial presentation by Lemma `15.81.1`.
      exact
        (Module.FinitePresentationRelativeTo.iff_overEveryPolynomialPresentation
          (R := R) (A := A) (M := M)).1 hM n α hα
    have hMP : MP.IsMPseudoCoherent (-1) :=
      (moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation_univ_local
        (S := P) MP).2 <| by
          simpa [MP, MA] using hfinitePresentationP
    simpa [MP, MA] using hMP

-- Proof sketch: for each surjective polynomial presentation `α`, apply Lemma `15.65.4 (3)` over
-- the polynomial ring `MvPolynomial (Fin n) R`; this identifies `(-(d : ℤ))`-pseudo-coherence
-- with the existence of a length-`d` finite free resolution over that presentation ring.
/-- Lemma 15.82.7 (3): for `d : ℕ`, an `A`-module is `(-d)`-pseudo-coherent relative to `R`
exactly when for every surjective polynomial presentation of `A` over `R`, the induced module
admits a length-`d` finite free resolution. -/
theorem Module.isNegPseudoCoherentRelativeTo_iff_hasLengthFiniteFreeResolutionRelativeTo
    (d : ℕ) :
    Module.IsMPseudoCoherentRelativeTo R A M (-(d : ℤ)) ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          Module.HasLengthFiniteFreeResolution P M d := by
  constructor
  · intro hM
    intro n α hα
    let P := MvPolynomial (Fin n) R
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    have hMP : MP.IsMPseudoCoherent (-(d : ℤ)) := by
      -- Proof comment: evaluate the relative `(-d)`-pseudo-coherent condition on the given
      -- presentation.
      exact
        (module_isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
          (R := R) (A := A) (M := M) (-(d : ℤ))).1 hM n α hα
    -- Proof comment: Lemma `15.65.4 (3)` turns this pointwise pseudo-coherence statement into the
    -- desired finite free resolution.
    exact
      (moduleCat_isNegPseudoCoherent_iff_hasFiniteFreeResolutionLength_univ_local
        (S := P) MP d).1 <| by
          simpa [MP, MA] using hMP
  · intro hM
    refine
      (module_isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
        (R := R) (A := A) (M := M) (-(d : ℤ))).2 ?_
    intro n α hα
    let P := MvPolynomial (Fin n) R
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    have hMP : MP.IsMPseudoCoherent (-(d : ℤ)) :=
      (moduleCat_isNegPseudoCoherent_iff_hasFiniteFreeResolutionLength_univ_local
        (S := P) MP d).2 <| by
          simpa [MP, MA] using hM n α hα
    simpa [MP, MA] using hMP

-- Proof sketch: apply Lemma `15.65.4 (4)` over each surjective polynomial presentation of `A`
-- over `R`; the pointwise pseudo-coherence condition is equivalent to the existence of an infinite
-- finite free resolution over every such presentation ring.
/-- Lemma 15.82.7 (4): an `A`-module is pseudo-coherent relative to `R` exactly when for every
surjective polynomial presentation of `A` over `R`, the induced module admits an infinite
resolution by finite free modules. -/
theorem Module.isPseudoCoherentRelativeTo_iff_hasInfiniteFiniteFreeResolutionRelativeTo :
    Module.IsPseudoCoherentRelativeTo R A M ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          ∃ (F : ChainComplex (ModuleCat P) ℕ)
            (π : F ⟶ (ChainComplex.single₀ (ModuleCat P)).obj (ModuleCat.of P M)),
            ChainComplex.IsFiniteFreeResolution π := by
  constructor
  · intro hM
    intro n α hα
    let P := MvPolynomial (Fin n) R
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    have hMP : MP.IsPseudoCoherent := by
      -- Proof comment: relative pseudo-coherence is tested presentationwise on the restricted
      -- module.
      exact
        (module_isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
          (R := R) (A := A) (M := M)).1 hM n α hα
    exact
      (moduleCat_isPseudoCoherent_iff_exists_infiniteFiniteFreeResolution_univ_local
        (S := P) MP).1 <| by
          simpa [MP, MA] using hMP
  · intro hM
    refine
      (module_isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
        (R := R) (A := A) (M := M)).2 ?_
    intro n α hα
    let P := MvPolynomial (Fin n) R
    let MA : ModuleCat A := ModuleCat.of A M
    let MP := (ModuleCat.restrictScalars α.toRingHom).obj MA
    have hMP : MP.IsPseudoCoherent :=
      (moduleCat_isPseudoCoherent_iff_exists_infiniteFiniteFreeResolution_univ_local
        (S := P) MP).2 <| by
          simpa [MP, MA] using hM n α hα
    simpa [MP, MA] using hMP

end
