import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_134_3
import stacks_proof.stacks_project.Chap10.Lemma_10_134_10
import stacks_proof.stacks_project.Chap10.Lemma_10_134_12
import stacks_proof.stacks_project.Chap10.Lemma_10_134_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Algebra.Generators
open Algebra.Extension
open CategoryTheory
open CategoryTheory.Limits

universe u v w

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {g : S} {n m : ℕ}

attribute [local instance] SMulCommClass.of_commMonoid
attribute [local instance] TensorProduct.rightAlgebra

/-- Helper for Chap10 Lemma 10 134 16: extension of scalars is additive on module morphisms. -/
private instance extendScalarsFunctorAdditive
    {T : Type w} [CommRing T] (f : S →+* T) :
    (ModuleCat.extendScalars f).Additive where
  map_add {X Y} p q := by
    -- It is enough to test equality on pure tensors `1 ⊗ x`.
    letI : Algebra S T := f.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext (f := f)
    intro x
    change (LinearMap.baseChange T (ModuleCat.Hom.hom (p + q))) (1 ⊗ₜ[S] x) =
      (LinearMap.baseChange T (ModuleCat.Hom.hom p)) (1 ⊗ₜ[S] x) +
        (LinearMap.baseChange T (ModuleCat.Hom.hom q)) (1 ⊗ₜ[S] x)
    rw [ModuleCat.hom_add, LinearMap.baseChange_add]
    rfl

/- Domain-style sampling:
* primary domain: cotangent modules of finite algebra presentations under localization away from
  one element.
* sampled owner declarations:
  - `presentation_cotangent_stable_equiv`, the chapter owner for stable presentation-independence
    of conormal modules;
  - `Generators.cotangentCompLocalizationAwayEquiv`, the localization-away splitting of the
    cotangent module after adjoining an inverse;
  - `LocalizedModule.equivTensorProduct`, the canonical bridge between a localized module and the
    tensor-product base-change model;
  - `Generators.basisCotangentAway`, the canonical rank-one basis for the localization-away
    presentation.
* best owner abstraction: the source-facing object is the localized conormal module itself,
  modeled canonically as `LocalizedModule.Away g P.toExtension.Cotangent`; the tensor-product
  description is only the bridge used to connect this owner to
  `Generators.cotangentCompLocalizationAwayEquiv`.
* primitive data vs. derived API:
  - primitive data: the presentations `P` and `Q`, together with the away-localized cotangent
    module of `P`;
  - derived API: the stabilized isomorphism with the cotangent module of `Q`;
  - bridge/view: the tensor-product model and the extra rank-one summand coming from adjoining an
    inverse of `g`.
* layer triage:
  - `source-facing`: the stable isomorphism
    `(I / I²)_g ⊕ S_g^{⊕ m} ≅ J / J² ⊕ S_g^{⊕ n}`;
  - `core/canonical`: `presentation_cotangent_stable_equiv`;
  - `bridge/view`: `Generators.cotangentCompLocalizationAwayEquiv` together with
    `LocalizedModule.equivTensorProduct`.
-/

-- Proof sketch: let `P' := (Generators.localizationAway (Localization.Away g) g).comp P`, so
-- `P'` is the canonical presentation of `S_g` obtained from `P` by adjoining one inverse for `g`.
-- `Generators.cotangentCompLocalizationAwayEquiv` identifies `P'.toExtension.Cotangent` with the
-- tensor-product model `Localization.Away g ⊗[S] P.toExtension.Cotangent` plus one free rank-one
-- summand, and `LocalizedModule.equivTensorProduct` rewrites that tensor product as the source-
-- facing localized conormal module `LocalizedModule.Away g P.toExtension.Cotangent`.
-- Lemma `10.134.15` compares `P'` with the arbitrary presentation `Q`. Rewriting the
-- localization-away cotangent summand by its canonical rank-one basis yields the source-facing
-- stable equivalence promised by the Stacks lemma, so the clean public statement here is
-- existence rather than a non-canonical chosen witness.
/-- Helper for Lemma 10.134.16: the lifted degree-`1` term in the naive cotangent complex. -/
private abbrev LiftCotangent (P : Extension.{w} R S) :=
  ULift.{v, w} P.Cotangent

/-- Helper for Lemma 10.134.16: the `ULift` in degree `1` is canonically equivalent to the
actual cotangent module. -/
private noncomputable abbrev liftCotangentEquiv
    (P : Extension.{w} R S) :
    LiftCotangent P ≃ₗ[S] P.Cotangent :=
  ULift.moduleEquiv

/-- Helper for Lemma 10.134.16: the scalar extension of the naive cotangent complex attached to a
presentation `P`. -/
private noncomputable abbrev scalarExtendedPresentationNaiveCotangent
    (P : Generators R S (Fin n)) :
    ChainComplex (ModuleCat (Localization.Away g)) ℕ :=
  ((ModuleCat.extendScalars (algebraMap S (Localization.Away g))).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj P.toExtension.naiveCotangentChainComplex

/-- Helper for Lemma 10.134.16: the standard localization-away presentation is reindexed into the
ambient universe so that presentation-independence can compare it to the owner self-presentation
of `Localization.Away g` over `S`. -/
private noncomputable abbrev localizedPresentationAwayGenerators :
    Generators S (Localization.Away g) (ULift.{v} Unit) :=
  (Generators.localizationAway (Localization.Away g) g).reindex Equiv.ulift

/-- Helper for Lemma 10.134.16: every degree `i + 2` term of a presentation-level naive
cotangent complex is canonically zero. -/
private theorem naiveCotangentChainComplex_isZero_of_succ_succ
    (P : Extension.{w} R S) (i : ℕ) :
    IsZero (P.naiveCotangentChainComplex.X (i + 2)) := by
  -- The naive cotangent complex is literally built as a two-term complex, so all higher degrees
  -- identify with `PUnit`.
  let e :
      P.naiveCotangentChainComplex.X (i + 2) ≅ ModuleCat.of.{max w v} S PUnit := by
    let succZero :
        ∀ {X₀ X₁ : ModuleCat.{max w v} S} (f : X₁ ⟶ X₀),
          Σ' (X₂ : ModuleCat.{max w v} S) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
      fun {_ _} _ ↦ ⟨ModuleCat.of.{max w v} S PUnit, 0, by simp⟩
    simpa [Algebra.Extension.naiveCotangentChainComplex] using
      (ChainComplex.mk'XIso
        (ModuleCat.of.{max w v} S P.CotangentSpace)
        (ModuleCat.of.{max w v} S (LiftCotangent P))
        (ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftCotangentEquiv P).toLinearMap))
        succZero i)
  letI : Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) :=
    ⟨fun x y ↦ by
      have hx : e.hom.hom x = 0 := by
        cases e.hom.hom x
        rfl
      have hy : e.hom.hom y = 0 := by
        cases e.hom.hom y
        rfl
      apply_fun e.inv.hom at hx
      apply_fun e.inv.hom at hy
      simpa using hx.trans hy.symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Chap10 Lemma 10 134 16: every element in a higher term of a presentation-level
naive cotangent complex is zero. -/
private theorem naiveCotangentChainComplex_eq_zero_of_succ_succ
    (P : Extension.{w} R S) (i : ℕ)
    (x : P.naiveCotangentChainComplex.X (i + 2)) :
    x = 0 := by
  -- Compare the higher term with the explicit `PUnit` term of the two-term model.
  let e :
      P.naiveCotangentChainComplex.X (i + 2) ≅ ModuleCat.of.{max w v} S PUnit := by
    let succZero :
        ∀ {X₀ X₁ : ModuleCat.{max w v} S} (f : X₁ ⟶ X₀),
          Σ' (X₂ : ModuleCat.{max w v} S) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
      fun {_ _} _ ↦ ⟨ModuleCat.of.{max w v} S PUnit, 0, by simp⟩
    simpa [Algebra.Extension.naiveCotangentChainComplex] using
      (ChainComplex.mk'XIso
        (ModuleCat.of.{max w v} S P.CotangentSpace)
        (ModuleCat.of.{max w v} S (LiftCotangent P))
        (ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftCotangentEquiv P).toLinearMap))
        succZero i)
  have h : e.hom.hom x = e.hom.hom 0 := by
    cases e.hom.hom x
    rfl
  apply_fun e.inv.hom at h
  simpa using h

/-- Helper for Chap10 Lemma 10 134 16: higher terms in a presentation-level naive cotangent
complex are subsingletons. -/
private theorem naiveCotangentChainComplex_subsingleton_of_succ_succ
    (P : Extension.{w} R S) (i : ℕ) :
    Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) := by
  -- The previous zero-element lemma turns equality of any two elements into equality with zero.
  refine ⟨fun x y ↦ ?_⟩
  rw [naiveCotangentChainComplex_eq_zero_of_succ_succ P i x,
    naiveCotangentChainComplex_eq_zero_of_succ_succ P i y]

/-- Helper for Lemma 10.134.16: the naive cotangent complex of a presentation is concentrated in
degrees `0` and `1`. -/
private theorem naiveCotangentChainComplex_concentrated_away_from_zero_one
    (P : Extension.{w} R S) (k : ℕ) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    IsZero (P.naiveCotangentChainComplex.X k) := by
  -- Only the `k = i + 2` branch survives the case split.
  cases k with
  | zero =>
      exact False.elim (hk0 rfl)
  | succ k =>
      cases k with
      | zero =>
          exact False.elim (hk1 rfl)
      | succ i =>
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            naiveCotangentChainComplex_isZero_of_succ_succ P i

/-- Helper for Chap10 Lemma 10 134 16: the degree-`0` to degree-`1` homotopy component comparing
two extension-induced maps on naive cotangent complexes. -/
private noncomputable abbrev liftCotangentHomotopyMap
    {P Q : Extension.{w} R S} (f g : P.Hom Q) :
    P.CotangentSpace →ₗ[S] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ f.sub g

/-- Helper for Chap10 Lemma 10 134 16: the relation from degree `1` to degree `0` in the downward
complex shape. -/
private theorem naiveCotangent_rel10 : (ComplexShape.down ℕ).Rel 1 0 := by
  -- This is the basic successor relation for the two-term naive cotangent complex.
  simp [ComplexShape.down]

/-- Helper for Chap10 Lemma 10 134 16: the relation from degree `2` to degree `1` in the downward
complex shape. -/
private theorem naiveCotangent_rel21 : (ComplexShape.down ℕ).Rel 2 1 := by
  -- This higher relation is needed only to spell out the null-homotopy formula.
  simp [ComplexShape.down]

/-- Helper for Chap10 Lemma 10 134 16: no differential in the downward complex shape targets a
degree from `0`. -/
private theorem naiveCotangent_not_rel0 (j : ℕ) : ¬ (ComplexShape.down ℕ).Rel 0 j := by
  -- Downward complexes have no outgoing relation from their lowest displayed degree.
  simp [ComplexShape.down]

/-- Helper for Chap10 Lemma 10 134 16: the raw homotopy matrix between two extension-induced maps
on naive cotangent complexes. -/
private noncomputable def naiveCotangentChainHomotopyHomAnyUniverse
    {P Q : Extension.{w} R S} (f g : P.Hom Q)
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    P.naiveCotangentChainComplex.X i ⟶ Q.naiveCotangentChainComplex.X j := by
  -- Only the component from degree `0` to degree `1` is nonzero; all other entries vanish.
  rcases i with _ | i
  · rcases j with _ | j
    · exact 0
    · cases j with
      | zero =>
          exact ModuleCat.ofHom (liftCotangentHomotopyMap f g)
      | succ j =>
          exact 0
  · exact 0

/-- Helper for Chap10 Lemma 10 134 16: two extension-induced maps on naive cotangent complexes
differ by the null-homotopic map attached to the raw homotopy matrix. -/
private theorem naiveCotangentChainMap_sub_eq_nullHomotopicMap_anyUniverse
    {P Q : Extension.{w} R S} (f g : P.Hom Q) :
    Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g =
      Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHomAnyUniverse f g) := by
  -- Check the equality degree by degree; degrees above `1` are subsingleton.
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 0 =
        (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHomAnyUniverse f g)).f 0
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left naiveCotangent_rel10
        naiveCotangent_not_rel0 (naiveCotangentChainHomotopyHomAnyUniverse f g)]
      ext x
      simpa [Extension.naiveCotangentChainMap, naiveCotangentChainHomotopyHomAnyUniverse,
        Algebra.Extension.naiveCotangentChainComplex, liftCotangentHomotopyMap,
        LinearMap.comp_assoc] using
        LinearMap.congr_fun (Extension.CotangentSpace.map_sub_map f g) x
  | succ i =>
      cases i with
      | zero =>
          change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 1 =
            (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHomAnyUniverse f g)).f 1
          rw [Homotopy.nullHomotopicMap'_f naiveCotangent_rel21 naiveCotangent_rel10
            (naiveCotangentChainHomotopyHomAnyUniverse f g)]
          ext x
          rcases x with ⟨x⟩
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            (ModuleCat.Hom.hom
                (P.naiveCotangentChainComplex.d 1 0 ≫
                  naiveCotangentChainHomotopyHomAnyUniverse f g 0 1 naiveCotangent_rel10 +
                naiveCotangentChainHomotopyHomAnyUniverse f g 1 2 naiveCotangent_rel21 ≫
                  Q.naiveCotangentChainComplex.d 2 1))
              { down := x }
          rw [Extension.naiveCotangentChainComplex_d_succ_succ Q 0,
            Extension.naiveCotangentChainComplex_d_1_0 P]
          simp only [naiveCotangentChainHomotopyHomAnyUniverse, liftCotangentHomotopyMap,
            LinearMap.sub_apply, comp_zero, add_zero, ModuleCat.hom_comp, LinearMap.coe_comp,
            Function.comp_apply]
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            ULift.up ((f.sub g) (P.cotangentComplex x))
          rw [LinearMap.congr_fun (Extension.Cotangent.map_sub_map f g) x]
          rfl
      | succ i =>
          letI : Subsingleton (Q.naiveCotangentChainComplex.X (i + 2)) :=
            naiveCotangentChainComplex_subsingleton_of_succ_succ Q i
          ext x
          exact Subsingleton.elim _ _

/-- Helper for Chap10 Lemma 10 134 16: any two maps of extensions induce homotopic maps on the
naive cotangent complexes. -/
private noncomputable def naiveCotangentChainMapHomotopyAnyUniverse
    {P Q : Extension.{w} R S} (f g : P.Hom Q) :
    Homotopy (Extension.naiveCotangentChainMap f) (Extension.naiveCotangentChainMap g) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (naiveCotangentChainMap_sub_eq_nullHomotopicMap_anyUniverse f g)).trans
      (Homotopy.nullHomotopy' (naiveCotangentChainHomotopyHomAnyUniverse f g)))

/-- Helper for Chap10 Lemma 10 134 16: the default comparison map between presentations, viewed at
the extension level. -/
private noncomputable abbrev defaultExtensionHomAnyUniverse
    {ι ι' : Type v} (P : Generators R S ι) (Q : Generators R S ι') :
    P.toExtension.Hom Q.toExtension :=
  (Generators.defaultHom P Q).toExtensionHom

/-- Helper for Chap10 Lemma 10 134 16: arbitrary presentations of the same algebra have homotopy
equivalent naive cotangent complexes, without requiring the generator universes to match the ring
universes. -/
private noncomputable def generatorsNaiveCotangentChainHomotopyEquivAnyUniverse
    {ι ι' : Type v} (P : Generators R S ι) (Q : Generators R S ι') :
    HomotopyEquiv P.toExtension.naiveCotangentChainComplex Q.toExtension.naiveCotangentChainComplex where
  hom := Extension.naiveCotangentChainMap (defaultExtensionHomAnyUniverse P Q)
  inv := Extension.naiveCotangentChainMap (defaultExtensionHomAnyUniverse Q P)
  homotopyHomInvId := by
    -- Compose the two default maps, then contract the result to the identity-induced chain map.
    let f := defaultExtensionHomAnyUniverse P Q
    let g := defaultExtensionHomAnyUniverse Q P
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp f g).symm).trans
        ((naiveCotangentChainMapHomotopyAnyUniverse (g.comp f) (.id P.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id P.toExtension)))
  homotopyInvHomId := by
    -- The inverse-side homotopy is the same argument with the two presentations interchanged.
    let f := defaultExtensionHomAnyUniverse P Q
    let g := defaultExtensionHomAnyUniverse Q P
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp g f).symm).trans
        ((naiveCotangentChainMapHomotopyAnyUniverse (f.comp g) (.id Q.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id Q.toExtension)))

/-- Helper for Chap10 Lemma 10 134 16: reindex the finite presentation into the ambient universe
before comparing it to the owner self-presentation. -/
private noncomputable abbrev reindexedFinitePresentation
    (P : Generators R S (Fin n)) :
    Generators R S (ULift.{v} (Fin n)) :=
  P.reindex Equiv.ulift

/-- Helper for Chap10 Lemma 10 134 16: the forward reindex map sends each finite generator to the
corresponding lifted variable. -/
private theorem reindexedFinitePresentationHomAeval
    (P : Generators R S (Fin n)) (i : Fin n) :
    MvPolynomial.aeval (reindexedFinitePresentation (R := R) (S := S) P).val
        (MvPolynomial.X (ULift.up i) : MvPolynomial (ULift.{v} (Fin n)) R) =
      P.val i := by
  -- The lifted variable evaluates to the original generator after unfolding the reindexing.
  simp [reindexedFinitePresentation, Generators.reindex]

/-- Helper for Chap10 Lemma 10 134 16: the finite presentation maps to its `ULift` reindex by
renaming each variable to its lifted copy. -/
private noncomputable def reindexedFinitePresentationHom
    (P : Generators R S (Fin n)) :
    P.Hom (reindexedFinitePresentation (R := R) (S := S) P) :=
  { val := fun i ↦ MvPolynomial.X (ULift.up i)
    aeval_val := reindexedFinitePresentationHomAeval (R := R) (S := S) P }

/-- Helper for Chap10 Lemma 10 134 16: the backward reindex map lowers each lifted generator to
the original finite variable. -/
private theorem reindexedFinitePresentationInvHomAeval
    (P : Generators R S (Fin n)) (i : ULift.{v} (Fin n)) :
    MvPolynomial.aeval P.val (MvPolynomial.X i.down : MvPolynomial (Fin n) R) =
      (reindexedFinitePresentation (R := R) (S := S) P).val i := by
  -- Lowering the lifted index recovers exactly the reindexed generator.
  cases i
  simp [reindexedFinitePresentation, Generators.reindex]

/-- Helper for Chap10 Lemma 10 134 16: the `ULift` reindex maps back to the original finite
presentation by lowering lifted variables. -/
private noncomputable def reindexedFinitePresentationInvHom
    (P : Generators R S (Fin n)) :
    (reindexedFinitePresentation (R := R) (S := S) P).Hom P :=
  { val := fun i ↦ MvPolynomial.X i.down
    aeval_val := reindexedFinitePresentationInvHomAeval (R := R) (S := S) P }

/-- Helper for Chap10 Lemma 10 134 16: lowering after lifting the finite reindex is the identity
on the original presentation. -/
private theorem reindexedFinitePresentationInvHom_comp_hom
    (P : Generators R S (Fin n)) :
    (reindexedFinitePresentationInvHom (R := R) (S := S) P).comp
        (reindexedFinitePresentationHom (R := R) (S := S) P) =
      Generators.Hom.id P := by
  -- Both renamings cancel on each original generator.
  ext i
  simp [reindexedFinitePresentationHom, reindexedFinitePresentationInvHom]

/-- Helper for Chap10 Lemma 10 134 16: lifting after lowering the finite reindex is the identity
on the ambient-universe copy. -/
private theorem reindexedFinitePresentationHom_comp_invHom
    (P : Generators R S (Fin n)) :
    (reindexedFinitePresentationHom (R := R) (S := S) P).comp
        (reindexedFinitePresentationInvHom (R := R) (S := S) P) =
      Generators.Hom.id (reindexedFinitePresentation (R := R) (S := S) P) := by
  -- The lifted variables are unchanged after lowering and lifting again.
  ext i
  cases i
  simp [reindexedFinitePresentationHom, reindexedFinitePresentationInvHom]

/-- Helper for Chap10 Lemma 10 134 16: the forward-then-backward reindex comparison becomes the
identity extension morphism. -/
private theorem reindexedFinitePresentationInvHom_comp_hom_toExtensionHom
    (P : Generators R S (Fin n)) :
    (reindexedFinitePresentationInvHom (R := R) (S := S) P).toExtensionHom.comp
        (reindexedFinitePresentationHom (R := R) (S := S) P).toExtensionHom =
      .id P.toExtension := by
  -- Transport the generator-level cancellation through `toExtensionHom`.
  simpa [Generators.Hom.toExtensionHom_comp, Generators.Hom.toExtensionHom_id] using
    congrArg (fun f => f.toExtensionHom)
      (reindexedFinitePresentationInvHom_comp_hom (R := R) (S := S) P)

/-- Helper for Chap10 Lemma 10 134 16: the forward reindex map at the extension level. -/
private noncomputable abbrev reindexedFinitePresentationToExtensionHom
    (P : Generators R S (Fin n)) :
    P.toExtension.Hom (reindexedFinitePresentation (R := R) (S := S) P).toExtension :=
  (reindexedFinitePresentationHom (R := R) (S := S) P).toExtensionHom

/-- Helper for Chap10 Lemma 10 134 16: the backward-then-forward reindex comparison becomes the
identity extension morphism on the reindexed presentation. -/
private theorem reindexedFinitePresentationHom_comp_invHom_toExtensionHom
    (P : Generators R S (Fin n)) :
    (reindexedFinitePresentationHom (R := R) (S := S) P).toExtensionHom.comp
        (reindexedFinitePresentationInvHom (R := R) (S := S) P).toExtensionHom =
      .id (reindexedFinitePresentation (R := R) (S := S) P).toExtension := by
  -- Transport the ambient-universe cancellation through `toExtensionHom`.
  simpa [Generators.Hom.toExtensionHom_comp, Generators.Hom.toExtensionHom_id] using
    congrArg (fun f => f.toExtensionHom)
      (reindexedFinitePresentationHom_comp_invHom (R := R) (S := S) P)

/-- Helper for Chap10 Lemma 10 134 16: the backward reindex map at the extension level. -/
private noncomputable abbrev reindexedFinitePresentationInvToExtensionHom
    (P : Generators R S (Fin n)) :
    (reindexedFinitePresentation (R := R) (S := S) P).toExtension.Hom P.toExtension :=
  (reindexedFinitePresentationInvHom (R := R) (S := S) P).toExtensionHom

/-- Helper for Chap10 Lemma 10 134 16: the finite presentation and its `ULift` reindex have
identical naive cotangent complexes degreewise, hence are isomorphic as chain complexes. -/
private noncomputable def reindexedFinitePresentationNaiveCotangentIso
    (P : Generators R S (Fin n)) :
    P.toExtension.naiveCotangentChainComplex ≅
      (reindexedFinitePresentation (R := R) (S := S) P).toExtension.naiveCotangentChainComplex := by
  let P' := reindexedFinitePresentation (R := R) (S := S) P
  let C := P.toExtension.naiveCotangentChainComplex
  let D := P'.toExtension.naiveCotangentChainComplex
  let f := reindexedFinitePresentationToExtensionHom (R := R) (S := S) P
  let g := reindexedFinitePresentationInvToExtensionHom (R := R) (S := S) P
  have hgf :
      g.comp f = .id P.toExtension := by
    simpa [f, g] using
      reindexedFinitePresentationInvHom_comp_hom_toExtensionHom (R := R) (S := S) P
  have hfg :
      f.comp g = .id P'.toExtension := by
    simpa [f, g] using
      reindexedFinitePresentationHom_comp_invHom_toExtensionHom (R := R) (S := S) P
  have hspaceLeft :
      (Extension.CotangentSpace.map g).restrictScalars S ∘ₗ Extension.CotangentSpace.map f =
        LinearMap.id := by
    apply LinearMap.ext
    intro x
    calc
      ((Extension.CotangentSpace.map g).restrictScalars S ∘ₗ Extension.CotangentSpace.map f) x =
          Extension.CotangentSpace.map (g.comp f) x := by
            simpa using (Extension.CotangentSpace.map_comp_apply f g x).symm
      _ = x := by
        rw [hgf, Extension.CotangentSpace.map_id]
        simpa using (LinearMap.id_apply x)
  have hspaceRight :
      (Extension.CotangentSpace.map f).restrictScalars S ∘ₗ Extension.CotangentSpace.map g =
        LinearMap.id := by
    apply LinearMap.ext
    intro x
    calc
      ((Extension.CotangentSpace.map f).restrictScalars S ∘ₗ Extension.CotangentSpace.map g) x =
          Extension.CotangentSpace.map (f.comp g) x := by
            simpa using (Extension.CotangentSpace.map_comp_apply g f x).symm
      _ = x := by
        rw [hfg, Extension.CotangentSpace.map_id]
        simpa using (LinearMap.id_apply x)
  have hcotLeft :
      Extension.Cotangent.map g ∘ₗ Extension.Cotangent.map f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    calc
      (Extension.Cotangent.map g ∘ₗ Extension.Cotangent.map f) x =
          Extension.Cotangent.map (g.comp f) x := by
            exact
              (DFunLike.congr_fun
                (Extension.Cotangent.map_comp
                  (P := P.toExtension)
                  (P' := P'.toExtension)
                  (P'' := P.toExtension) f g)
                x).symm
      _ = x := by
        rw [hgf, Extension.Cotangent.map_id]
        rfl
  have hcotRight :
      Extension.Cotangent.map f ∘ₗ Extension.Cotangent.map g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    calc
      (Extension.Cotangent.map f ∘ₗ Extension.Cotangent.map g) x =
          Extension.Cotangent.map (f.comp g) x := by
            exact
              (DFunLike.congr_fun
                (Extension.Cotangent.map_comp
                  (P := P'.toExtension)
                  (P' := P.toExtension)
                  (P'' := P'.toExtension) g f)
                x).symm
      _ = x := by
        rw [hfg, Extension.Cotangent.map_id]
        rfl
  let e0 :
      P.toExtension.CotangentSpace ≃ₗ[S] P'.toExtension.CotangentSpace :=
    LinearEquiv.ofLinear
      (Extension.CotangentSpace.map f)
      (Extension.CotangentSpace.map g)
      hspaceRight
      hspaceLeft
  let e1 :
      C.X 1 ≃ₗ[S] D.X 1 := by
    -- Degree `1` is the lifted cotangent term, so lift the conormal maps directly.
    refine LinearEquiv.ofLinear ?_ ?_ ?_ ?_
    · exact
        { toFun := fun x ↦ ⟨Extension.Cotangent.map f x.down⟩
          map_add' := by
            rintro ⟨x⟩ ⟨y⟩
            change ULift.up (Extension.Cotangent.map f (x + y)) =
              ULift.up (Extension.Cotangent.map f x + Extension.Cotangent.map f y)
            simpa using congrArg ULift.up ((Extension.Cotangent.map f).map_add x y)
          map_smul' := by
            rintro a ⟨x⟩
            change ULift.up (Extension.Cotangent.map f (a • x)) =
              ULift.up (a • Extension.Cotangent.map f x)
            simpa using congrArg ULift.up ((Extension.Cotangent.map f).map_smul a x) }
    · exact
        { toFun := fun x ↦ ⟨Extension.Cotangent.map g x.down⟩
          map_add' := by
            rintro ⟨x⟩ ⟨y⟩
            change ULift.up (Extension.Cotangent.map g (x + y)) =
              ULift.up (Extension.Cotangent.map g x + Extension.Cotangent.map g y)
            simpa using congrArg ULift.up ((Extension.Cotangent.map g).map_add x y)
          map_smul' := by
            rintro a ⟨x⟩
            change ULift.up (Extension.Cotangent.map g (a • x)) =
              ULift.up (a • Extension.Cotangent.map g x)
            simpa using congrArg ULift.up ((Extension.Cotangent.map g).map_smul a x) }
    · apply LinearMap.ext
      rintro ⟨x⟩
      change ULift.up ((Extension.Cotangent.map f) ((Extension.Cotangent.map g) x)) =
        ULift.up x
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcotRight x
    · apply LinearMap.ext
      rintro ⟨x⟩
      change ULift.up ((Extension.Cotangent.map g) ((Extension.Cotangent.map f) x)) =
        ULift.up x
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcotLeft x
  let e : ∀ i : ℕ, C.X i ≅ D.X i
    | 0 => e0.toModuleIso
    | 1 => e1.toModuleIso
    | n + 2 =>
        (naiveCotangentChainComplex_isZero_of_succ_succ P.toExtension n).isoZero ≪≫
          (naiveCotangentChainComplex_isZero_of_succ_succ P'.toExtension n).isoZero.symm
  exact HomologicalComplex.Hom.isoOfComponents e <| by
    intro i j hij
    subst i
    cases j with
    | zero =>
        change (e 1).hom ≫ D.d 1 0 = C.d 1 0 ≫ (e 0).hom
        ext x
        rcases x with ⟨x⟩
        simpa [e, e0, e1, C, D, P', LinearEquiv.trans_apply, LinearMap.comp_assoc,
          Extension.naiveCotangentChainComplex] using
          LinearMap.congr_fun (Extension.CotangentSpace.map_comp_cotangentComplex f).symm x
    | succ j =>
        have hC : C.d (j + 2) (j + 1) = 0 := by
          simpa [C] using Extension.naiveCotangentChainComplex_d_succ_succ P.toExtension j
        have hD : D.d (j + 2) (j + 1) = 0 := by
          simpa [D] using Extension.naiveCotangentChainComplex_d_succ_succ P'.toExtension j
        change (e (j + 2)).hom ≫ D.d (j + 2) (j + 1) =
          C.d (j + 2) (j + 1) ≫ (e (j + 1)).hom
        rw [hC, hD]
        simp

/-- Helper for Chap10 Lemma 10 134 16: the finite presentation and its `ULift` reindex have
identical naive cotangent complexes up to homotopy. -/
private noncomputable def reindexedFinitePresentationNaiveCotangentChainHomotopyEquiv
    (P : Generators R S (Fin n)) :
    HomotopyEquiv
      P.toExtension.naiveCotangentChainComplex
      (reindexedFinitePresentation (R := R) (S := S) P).toExtension.naiveCotangentChainComplex :=
  HomotopyEquiv.ofIso (reindexedFinitePresentationNaiveCotangentIso (R := R) (S := S) P)

/-- Helper for Chap10 Lemma 10 134 16: a finite presentation has the same naive cotangent complex,
up to homotopy, as the owner self-presentation of the same algebra. -/
private noncomputable def finitePresentationSelfNaiveCotangentChainHomotopyEquiv
    (P : Generators R S (Fin n)) :
    HomotopyEquiv
      P.toExtension.naiveCotangentChainComplex
      (Generators.self R S).toExtension.naiveCotangentChainComplex :=
  -- Route correction: the direct finite-to-self comparison factors through the `ULift` reindex,
  -- where the existing any-universe presentation-independence bridge already applies.
  let eReindex :=
    reindexedFinitePresentationNaiveCotangentChainHomotopyEquiv (R := R) (S := S) P
  let eSelf :
      HomotopyEquiv
        (reindexedFinitePresentation (R := R) (S := S) P).toExtension.naiveCotangentChainComplex
        (Generators.self R S).toExtension.naiveCotangentChainComplex :=
    generatorsNaiveCotangentChainHomotopyEquivAnyUniverse
      (reindexedFinitePresentation (R := R) (S := S) P) (Generators.self R S)
  -- Compose the explicit reindex equivalence with presentation-independence at ambient universe
  -- level.
  eReindex.trans eSelf

/-- Helper for Lemma 10.134.16: scalar extension preserves the concentration of the naive
cotangent complex away from degrees `0` and `1`. -/
private theorem scalarExtendedPresentationNaiveCotangent_concentrated_away_from_zero_one
    (P : Generators R S (Fin n)) (k : ℕ) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    IsZero ((scalarExtendedPresentationNaiveCotangent (g := g) P).X k) := by
  -- The underlying degree object is just the scalar extension of the original degree object, so
  -- the zero-object statement transports through the functor.
  let F := ModuleCat.extendScalars (algebraMap S (Localization.Away g))
  have hP :
      IsZero (P.toExtension.naiveCotangentChainComplex.X k) :=
    naiveCotangentChainComplex_concentrated_away_from_zero_one P.toExtension k hk0 hk1
  simpa [scalarExtendedPresentationNaiveCotangent,
    CategoryTheory.Functor.mapHomologicalComplex_obj_X] using F.map_isZero hP

/-- Helper for Lemma 10.134.16: the reindexed localization-away presentation has contractible
naive cotangent complex because it is presentation-independent from the owner localization
complex `NL_{S_g⁄S}`, and Lemma `10.134.10` shows that owner complex is null-homotopic. -/
private noncomputable def localizedPresentationAway_naiveCotangent_homotopyEquiv_zero :
    HomotopyEquiv
      (localizedPresentationAwayGenerators (S := S) (g := g)).toExtension.naiveCotangentChainComplex
      (HomologicalComplex.zero :
        ChainComplex (ModuleCat (Localization.Away g)) ℕ) := by
  -- First compare the reindexed localization-away presentation to the owner self-presentation.
  let e₁ :
      HomotopyEquiv
        (localizedPresentationAwayGenerators (S := S) (g := g)).toExtension.naiveCotangentChainComplex
        (Generators.self S (Localization.Away g)).toExtension.naiveCotangentChainComplex :=
    Generators.naiveCotangentChainHomotopyEquiv
      (localizedPresentationAwayGenerators (S := S) (g := g))
      (Generators.self S (Localization.Away g))
  -- Then contract the owner localization complex using Lemma `10.134.10`.
  let e₂ :
      HomotopyEquiv
        (Generators.self S (Localization.Away g)).toExtension.naiveCotangentChainComplex
        (HomologicalComplex.zero :
          ChainComplex (ModuleCat (Localization.Away g)) ℕ) := by
    simpa [Algebra.naiveCotangent] using
      (localization_naiveCotangentComplex_homotopyEquiv_zero
        (A := S) (Aₛ := Localization.Away g) (S := Submonoid.powers g))
  exact e₁.trans e₂

/-- Helper for Lemma 10.134.16: the reindexed localization-away summand is contractible. -/
private noncomputable def localizedPresentationAway_naiveCotangent_contractible :
    Homotopy
      (𝟙 (localizedPresentationAwayGenerators (S := S) (g := g)).toExtension.naiveCotangentChainComplex)
      0 := by
  -- The homotopy equivalence to the zero complex makes the identity map null-homotopic.
  let e := localizedPresentationAway_naiveCotangent_homotopyEquiv_zero (S := S) (g := g)
  have hzero : e.hom ≫ e.inv = 0 := by
    ext i
    have hhom : e.hom.f i = 0 := by
      exact (Limits.isZero_zero (ModuleCat (Localization.Away g))).eq_of_tgt _ _
    simp [hhom]
  exact e.homotopyHomInvId.symm.trans (Homotopy.ofEq hzero)

/-- Helper for Lemma 10.134.16: Lemma `10.134.12` already supplies the owner-level localization
comparison `NL_{S⁄R} ⊗_S S_g ≃ NL_{S_g⁄R}`. -/
private noncomputable def localized_owner_naiveCotangent_homotopyEquiv :
    HomotopyEquiv
      (((ModuleCat.extendScalars (algebraMap S (Localization.Away g))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj ((Generators.self R S).toExtension.naiveCotangentChainComplex))
      ((Generators.self R (Localization.Away g)).toExtension.naiveCotangentChainComplex) := by
  -- This is exactly Lemma `10.134.12`, rewritten away from the owner naive cotangent notation.
  simpa [Algebra.naiveCotangent] using
    (naiveCotangent_tensor_comparison_of_isLocalizationAway_homotopyEquiv
      R S (Localization.Away g) g)

/-- Helper for Chap10 Lemma 10 134 16: after scalar extension to `S_g`, a finite presentation
complex is homotopy equivalent to the scalar-extended owner self-presentation complex. -/
private noncomputable def scalarExtendedFinitePresentationSelfNaiveCotangentChainHomotopyEquiv
    (P : Generators R S (Fin n)) :
    HomotopyEquiv
      (scalarExtendedPresentationNaiveCotangent (g := g) P)
      (((ModuleCat.extendScalars (algebraMap S (Localization.Away g))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
          (Generators.self R S).toExtension.naiveCotangentChainComplex) := by
  -- Map the finite-to-self presentation homotopy equivalence through scalar extension.
  let F : ModuleCat S ⥤ ModuleCat (Localization.Away g) :=
    ModuleCat.extendScalars (algebraMap S (Localization.Away g))
  letI : F.Additive := inferInstance
  let eRaw :
      HomotopyEquiv
        (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.toExtension.naiveCotangentChainComplex))
        (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Generators.self R S).toExtension.naiveCotangentChainComplex)) :=
    F.mapHomotopyEquiv (finitePresentationSelfNaiveCotangentChainHomotopyEquiv P)
  simpa [F, scalarExtendedPresentationNaiveCotangent] using eRaw

/-- Helper for Lemma 10.134.16: the scalar-extended naive cotangent complex of `P` is homotopy
equivalent to the naive cotangent complex of `Q` by passing through the owner complexes before and
after localization. -/
private noncomputable def localized_presentation_naiveCotangent_homotopyEquiv
    (P : Generators R S (Fin n)) (Q : Generators R (Localization.Away g) (Fin m)) :
    HomotopyEquiv
      (scalarExtendedPresentationNaiveCotangent (g := g) P)
      Q.toExtension.naiveCotangentChainComplex := by
  -- Route correction: keep the textbook chain-level route
  -- `P -> Generators.self R S -> Generators.self R S_g -> Q`.
  let eP :
      HomotopyEquiv
        (scalarExtendedPresentationNaiveCotangent (g := g) P)
        ((((ModuleCat.extendScalars (algebraMap S (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
          (Generators.self R S).toExtension.naiveCotangentChainComplex)) :=
    scalarExtendedFinitePresentationSelfNaiveCotangentChainHomotopyEquiv (g := g) P
  let eOwner :
      HomotopyEquiv
        ((((ModuleCat.extendScalars (algebraMap S (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
          (Generators.self R S).toExtension.naiveCotangentChainComplex))
        ((Generators.self R (Localization.Away g)).toExtension.naiveCotangentChainComplex) :=
    localized_owner_naiveCotangent_homotopyEquiv (g := g)
  let eQ :
      HomotopyEquiv
        ((Generators.self R (Localization.Away g)).toExtension.naiveCotangentChainComplex)
        Q.toExtension.naiveCotangentChainComplex :=
    (finitePresentationSelfNaiveCotangentChainHomotopyEquiv
      (R := R) (S := Localization.Away g) Q).symm
  exact (eP.trans eOwner).trans eQ

/-- Helper for Lemma 10.134.16: the scalar-extended degree-`1` term of `P` rewrites to the
localized conormal module `(I / I²)_g`. -/
private noncomputable def scalarExtendedPresentationDegreeOneEquiv
    (P : Generators R S (Fin n)) :
    (scalarExtendedPresentationNaiveCotangent (g := g) P).X 1 ≃ₗ[Localization.Away g]
      LocalizedModule.Away g P.toExtension.Cotangent := by
  -- First rewrite the scalar-extended degree term as a tensor product, then pass to the canonical
  -- localized-module model.
  let eTensor :
      (scalarExtendedPresentationNaiveCotangent (g := g) P).X 1 ≃ₗ[Localization.Away g]
        (Localization.Away g ⊗[S] P.toExtension.Cotangent) := by
    simpa [scalarExtendedPresentationNaiveCotangent, ModuleCat.extendScalars,
      ModuleCat.ExtendScalars.obj', Extension.naiveCotangentChainComplex] using
      (TensorProduct.AlgebraTensorModule.congr
        (restrictScalarsSelfEquiv S (Localization.Away g))
        (liftCotangentEquiv P.toExtension))
  simpa [LocalizedModule.Away, Localization.Away] using
    eTensor.trans (LocalizedModule.equivTensorProduct (Submonoid.powers g) P.toExtension.Cotangent).symm

/-- Helper for Lemma 10.134.16: the scalar-extended degree-`0` term of `P` rewrites to the free
module `S_g^{⊕ n}` via the canonical cotangent-space basis. -/
private noncomputable def scalarExtendedPresentationDegreeZeroEquiv
    (P : Generators R S (Fin n)) :
    (scalarExtendedPresentationNaiveCotangent (g := g) P).X 0 ≃ₗ[Localization.Away g]
      (Fin n →₀ Localization.Away g) := by
  -- The degree-`0` term is the scalar extension of the cotangent-space term, and the base-changed
  -- cotangent-space basis gives the desired finite free coordinates.
  let eTensor :
      (scalarExtendedPresentationNaiveCotangent (g := g) P).X 0 ≃ₗ[Localization.Away g]
        (Localization.Away g ⊗[S] P.toExtension.CotangentSpace) := by
    simpa [scalarExtendedPresentationNaiveCotangent, ModuleCat.extendScalars,
      ModuleCat.ExtendScalars.obj', Extension.naiveCotangentChainComplex] using
      (TensorProduct.AlgebraTensorModule.congr
        (restrictScalarsSelfEquiv S (Localization.Away g))
        (LinearEquiv.refl S P.toExtension.CotangentSpace))
  exact eTensor.trans (P.cotangentSpaceBasis.baseChange (Localization.Away g)).repr

/-- Helper for Lemma 10.134.16: the degree-`1` term of the naive cotangent complex of `Q`
identifies with its cotangent module. -/
private noncomputable def presentationDegreeOneEquiv
    (Q : Generators R (Localization.Away g) (Fin m)) :
    Q.toExtension.naiveCotangentChainComplex.X 1 ≃ₗ[Localization.Away g]
      Q.toExtension.Cotangent := by
  -- This is the standard `ULift` normalization of the degree-`1` term.
  simpa [Extension.naiveCotangentChainComplex] using
    (liftCotangentEquiv Q.toExtension)

/-- Helper for Lemma 10.134.16: the degree-`0` term of the naive cotangent complex of `Q`
identifies with the free module `S_g^{⊕ m}` by the canonical basis. -/
private noncomputable def presentationDegreeZeroEquiv
    (Q : Generators R (Localization.Away g) (Fin m)) :
    Q.toExtension.naiveCotangentChainComplex.X 0 ≃ₗ[Localization.Away g]
      (Fin m →₀ Localization.Away g) := by
  -- The cotangent-space basis is exactly the coordinate system needed for the textbook summand.
  simpa [Extension.naiveCotangentChainComplex] using Q.cotangentSpaceBasis.repr

/-- Chap10 Lemma 10 134 16: for a presentation `P : R[x₁, …, xₙ] → S` and a presentation
`Q : R[y₁, …, yₘ] → S_g`, there exists a `Localization.Away g`-linear equivalence between the
localized conormal module of `P`, stabilized by `S_g^{⊕ m}`, and the conormal module of `Q`,
stabilized by `S_g^{⊕ n}`. This is the source-facing existence form of the textbook isomorphism
`(I / I²)_g ⊕ S_g^{⊕ m} ≅ J / J² ⊕ S_g^{⊕ n}`; the tensor-product base-change model is only the
bridge to the canonical localization APIs used in the proof. -/
@[stacks 00S6]
theorem localized_presentation_cotangent_stable_equiv
    (P : Generators R S (Fin n)) (Q : Generators R (Localization.Away g) (Fin m)) :
    Nonempty
      ((LocalizedModule.Away g P.toExtension.Cotangent × (Fin m →₀ Localization.Away g)) ≃ₗ[Localization.Away g]
        (Q.toExtension.Cotangent × (Fin n →₀ Localization.Away g))) := by
  -- The chain-level route is: compare `P` to the self-presentation of `S`, localize the owner
  -- naive cotangent complex, compare with `Q`, and then extract the degree-`1`/`0` stable block.
  let A := scalarExtendedPresentationNaiveCotangent (g := g) P
  let B := Q.toExtension.naiveCotangentChainComplex
  let e := localized_presentation_naiveCotangent_homotopyEquiv (g := g) P Q
  have hA :
      ∀ k : ℕ, k ≠ 0 → k ≠ 1 → IsZero (A.X k) :=
    fun k hk0 hk1 ↦
      scalarExtendedPresentationNaiveCotangent_concentrated_away_from_zero_one P k hk0 hk1
  have hB :
      ∀ k : ℕ, k ≠ 0 → k ≠ 1 → IsZero (B.X k) :=
    fun k hk0 hk1 ↦
      naiveCotangentChainComplex_concentrated_away_from_zero_one Q.toExtension k hk0 hk1
  letI : IsIso (term_complex_biprod_hom e) :=
    term_complex_biprod_hom_isIso hA hB e
  let i :
      A.X 1 ⊞ B.X 0 ≅ B.X 1 ⊞ A.X 0 :=
    asIso (term_complex_biprod_hom e)
  let leftProdEquiv :
      (LocalizedModule.Away g P.toExtension.Cotangent × (Fin m →₀ Localization.Away g)) ≃ₗ[Localization.Away g]
        (A.X 1 × B.X 0) :=
    LinearEquiv.prodCongr
      (scalarExtendedPresentationDegreeOneEquiv (g := g) P).symm
      (presentationDegreeZeroEquiv (g := g) Q).symm
  let rightProdEquiv :
      (B.X 1 × A.X 0) ≃ₗ[Localization.Away g]
        (Q.toExtension.Cotangent × (Fin n →₀ Localization.Away g)) :=
    LinearEquiv.prodCongr
      (presentationDegreeOneEquiv (g := g) Q)
      (scalarExtendedPresentationDegreeZeroEquiv (g := g) P)
  refine ⟨((((leftProdEquiv.toModuleIso) ≪≫
      (ModuleCat.biprodIsoProd (A.X 1) (B.X 0)).symm) ≪≫ i) ≪≫
        (ModuleCat.biprodIsoProd (B.X 1) (A.X 0)) ≪≫
          rightProdEquiv.toModuleIso).toLinearEquiv⟩

end
