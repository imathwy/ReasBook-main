import Mathlib
import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap10.Lemma_10_134_14

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open Algebra.Generators
open Algebra.Extension
open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {n m : ℕ}
variable {ι ι' : Type u}

/- Domain-style sampling:
* primary domain: finite algebra presentations and their two-term cotangent complexes.
* sampled owner declarations:
  - `Generators.defaultHom`, the canonical comparison between two presentations;
  - `Extension.Cotangent.map_sub_map`, the homotopy identity on the conormal term;
  - `Extension.CotangentSpace.map_sub_map`, the parallel homotopy identity on the cotangent-space
    term;
  - `term_complex_biprod_hom`, the chapter owner extracting the stable block isomorphism from a
    two-term chain-complex homotopy equivalence.
* best owner abstraction: the primitive data are the extension-level naive cotangent complexes;
  the stable block equivalence is derived from the homotopy equivalence between those owner
  complexes, and the free-module surface is only a basis rewrite.
* primitive data vs. derived API:
  - primitive data: `P.naiveCotangentChainComplex` for `P : Extension.{u} R S`;
  - derived API: the stable equivalence between cotangent and cotangent-space summands;
  - bridge/view: the basis rewrite identifying cotangent spaces with finite free modules.
* layer triage:
  - `source-facing`: the textbook stabilization
    `I / I² ⊕ S^{⊕ m} ≃ J / J² ⊕ S^{⊕ n}`;
  - `core/canonical`: the stable block isomorphism for the two-term cotangent complexes;
  - `bridge/view`: the canonical basis coordinates on cotangent spaces.
-/

private abbrev LiftCotangent (P : Extension.{u} R S) :=
  ULift.{v, u} P.Cotangent

private noncomputable abbrev liftCotangentEquiv
    (P : Extension.{u} R S) :
    LiftCotangent P ≃ₗ[S] P.Cotangent :=
  ULift.moduleEquiv

private noncomputable def liftCotangentMap
    {P Q : Extension.{u} R S} (f : P.Hom Q) :
    LiftCotangent P →ₗ[S] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ Cotangent.map f ∘ₗ
    (liftCotangentEquiv P).toLinearMap

private noncomputable def liftCotangentHomotopyMap
    {P Q : Extension.{u} R S} (f g : P.Hom Q) :
    P.CotangentSpace →ₗ[S] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ f.sub g

private theorem liftCotangentMap_id (P : Extension.{u} R S) :
    liftCotangentMap (.id P) = LinearMap.id := by
  ext x
  rcases x with ⟨x⟩
  simp [liftCotangentMap]

private theorem liftCotangentMap_comp
    {P Q T : Extension.{u} R S} (f : P.Hom Q) (g : Q.Hom T) :
    liftCotangentMap (g.comp f) = (liftCotangentMap g).restrictScalars S ∘ₗ liftCotangentMap f := by
  ext x
  rcases x with ⟨x⟩
  simp [liftCotangentMap, Cotangent.map_comp, LinearMap.comp_assoc]

private theorem naiveCotangent_rel10 : (ComplexShape.down ℕ).Rel 1 0 := by
  simp [ComplexShape.down]

private theorem naiveCotangent_rel21 : (ComplexShape.down ℕ).Rel 2 1 := by
  simp [ComplexShape.down]

private theorem naiveCotangent_not_rel0 (j : ℕ) : ¬ (ComplexShape.down ℕ).Rel 0 j := by
  simp [ComplexShape.down]

private noncomputable def naiveCotangentChainComplexXIsoPUnit
    (P : Extension.{u} R S) (i : ℕ) :
    P.naiveCotangentChainComplex.X (i + 2) ≅ ModuleCat.of.{max u v} S PUnit := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat.{max u v} S} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat.{max u v} S) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of.{max u v} S PUnit, 0, zero_comp⟩
  simpa [Algebra.Extension.naiveCotangentChainComplex] using
    (ChainComplex.mk'XIso
      (ModuleCat.of.{max u v} S P.CotangentSpace)
      (ModuleCat.of.{max u v} S (LiftCotangent P))
      (ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftCotangentEquiv P).toLinearMap))
      succZero i)

private theorem naiveCotangentChainComplex_eq_zero_of_succ_succ
    (P : Extension.{u} R S) (i : ℕ)
    (x : P.naiveCotangentChainComplex.X (i + 2)) :
    x = 0 := by
  let e := naiveCotangentChainComplexXIsoPUnit P i
  have h : e.hom.hom x = e.hom.hom 0 := by
    cases e.hom.hom x
    rfl
  apply_fun e.inv.hom at h
  simpa using h

private theorem naiveCotangentChainComplex_subsingleton_of_succ_succ
    (P : Extension.{u} R S) (i : ℕ) :
    Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) := by
  refine ⟨fun x y ↦ ?_⟩
  rw [naiveCotangentChainComplex_eq_zero_of_succ_succ P i x,
    naiveCotangentChainComplex_eq_zero_of_succ_succ P i y]

private theorem naiveCotangentChainMap_id
    (P : Extension.{u} R S) :
    Extension.naiveCotangentChainMap (.id P) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change ModuleCat.ofHom (CotangentSpace.map (.id P)) =
        ModuleCat.ofHom (LinearMap.id : P.CotangentSpace →ₗ[S] P.CotangentSpace)
      congr
      exact Extension.CotangentSpace.map_id
  | succ i =>
      cases i with
      | zero =>
          ext x
          rcases x with ⟨x⟩
          change (ULift.up (Cotangent.map (.id P) x) : LiftCotangent P) =
            ULift.up x
          congr 1
          simp
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ P i
          ext x
          exact Subsingleton.elim _ _

private theorem naiveCotangentChainMap_comp
    {P Q T : Extension.{u} R S} (f : P.Hom Q) (g : Q.Hom T) :
    Extension.naiveCotangentChainMap (g.comp f) =
      Extension.naiveCotangentChainMap f ≫ Extension.naiveCotangentChainMap g := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change ModuleCat.ofHom (CotangentSpace.map (g.comp f)) =
        ModuleCat.ofHom ((CotangentSpace.map g).restrictScalars S ∘ₗ CotangentSpace.map f)
      congr
      exact Extension.CotangentSpace.map_comp f g
  | succ i =>
      cases i with
      | zero =>
          ext x
          rcases x with ⟨x⟩
          change (ULift.up (Cotangent.map (g.comp f) x) : LiftCotangent T) =
            ULift.up (Cotangent.map g (Cotangent.map f x))
          simp [Cotangent.map_comp]
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ T i
          ext x
          exact Subsingleton.elim _ _

private noncomputable def naiveCotangentChainHomotopyHom
    {P Q : Extension.{u} R S} (f g : P.Hom Q)
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    P.naiveCotangentChainComplex.X i ⟶ Q.naiveCotangentChainComplex.X j := by
  rcases i with _ | i
  · rcases j with _ | j
    · exact 0
    · cases j with
      | zero =>
          exact ModuleCat.ofHom (liftCotangentHomotopyMap f g)
      | succ j =>
          exact 0
  · exact 0

private theorem naiveCotangentChainMap_sub_eq_nullHomotopicMap
    {P Q : Extension.{u} R S} (f g : P.Hom Q) :
    Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g =
      Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g) := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 0 =
        (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g)).f 0
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left naiveCotangent_rel10
        naiveCotangent_not_rel0 (naiveCotangentChainHomotopyHom f g)]
      ext x
      simpa [Extension.naiveCotangentChainMap, naiveCotangentChainHomotopyHom,
        Algebra.Extension.naiveCotangentChainComplex, liftCotangentHomotopyMap,
        LinearMap.comp_assoc] using
        LinearMap.congr_fun (Extension.CotangentSpace.map_sub_map f g) x
  | succ i =>
      cases i with
      | zero =>
          change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 1 =
            (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g)).f 1
          rw [Homotopy.nullHomotopicMap'_f naiveCotangent_rel21 naiveCotangent_rel10
            (naiveCotangentChainHomotopyHom f g)]
          ext x
          rcases x with ⟨x⟩
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            (ModuleCat.Hom.hom
                (P.naiveCotangentChainComplex.d 1 0 ≫
                  naiveCotangentChainHomotopyHom f g 0 1 naiveCotangent_rel10 +
                naiveCotangentChainHomotopyHom f g 1 2 naiveCotangent_rel21 ≫
                  Q.naiveCotangentChainComplex.d 2 1))
              { down := x }
          rw [Extension.naiveCotangentChainComplex_d_succ_succ Q 0,
            Extension.naiveCotangentChainComplex_d_1_0 P]
          simp [naiveCotangentChainHomotopyHom, liftCotangentHomotopyMap]
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            ULift.up ((f.sub g) (P.cotangentComplex x))
          rw [LinearMap.congr_fun (Extension.Cotangent.map_sub_map f g) x]
          rfl
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ Q i
          ext x
          exact Subsingleton.elim _ _

private noncomputable def naiveCotangentChainMapHomotopy
    {P Q : Extension.{u} R S} (f g : P.Hom Q) :
    Homotopy (Extension.naiveCotangentChainMap f) (Extension.naiveCotangentChainMap g) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (naiveCotangentChainMap_sub_eq_nullHomotopicMap f g)).trans
      (Homotopy.nullHomotopy' (naiveCotangentChainHomotopyHom f g)))

private noncomputable def defaultNaiveCotangentChainHomotopyEquiv
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    HomotopyEquiv P.toExtension.naiveCotangentChainComplex Q.toExtension.naiveCotangentChainComplex where
  hom := Extension.naiveCotangentChainMap (Generators.defaultHom P Q).toExtensionHom
  inv := Extension.naiveCotangentChainMap (Generators.defaultHom Q P).toExtensionHom
  homotopyHomInvId := by
    let f := (Generators.defaultHom P Q).toExtensionHom
    let g := (Generators.defaultHom Q P).toExtensionHom
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp f g).symm).trans
        ((naiveCotangentChainMapHomotopy (g.comp f) (.id P.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id P.toExtension)))
  homotopyInvHomId := by
    let f := (Generators.defaultHom P Q).toExtensionHom
    let g := (Generators.defaultHom Q P).toExtensionHom
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp g f).symm).trans
        ((naiveCotangentChainMapHomotopy (f.comp g) (.id Q.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id Q.toExtension)))

/-- The canonical basis equivalence identifying the cotangent space of a finite presentation with
its free module of generators. -/
private noncomputable abbrev presentationCotangentSpaceBasisEquiv
    {k : ℕ} (P : Generators R S (Fin k)) :
    P.toExtension.CotangentSpace ≃ₗ[S] (Fin k →₀ S) :=
  P.cotangentSpaceBasis.repr

/-- Helper for Lemma 10.134.15: the naive cotangent complex of an extension is zero in every
degree `i + 2`. -/
private theorem naiveCotangentChainComplex_isZero_of_succ_succ
    (P : Extension.{u} R S) (i : ℕ) :
    IsZero (P.naiveCotangentChainComplex.X (i + 2)) := by
  -- The higher terms are already known to be subsingletons, so the module object is zero.
  letI := naiveCotangentChainComplex_subsingleton_of_succ_succ P i
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 10.134.15: the naive cotangent complex of an extension is concentrated in
degrees `0` and `1`. -/
private theorem naiveCotangentChainComplex_concentrated_away_from_zero_one
    (P : Extension.{u} R S) (n : ℕ) (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    IsZero (P.naiveCotangentChainComplex.X n) := by
  -- Only the `n = i + 2` branch survives the case split; the other two are excluded by
  -- hypothesis.
  cases n with
  | zero =>
      exact False.elim (hn0 rfl)
  | succ n =>
      cases n with
      | zero =>
          exact False.elim (hn1 rfl)
      | succ i =>
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            naiveCotangentChainComplex_isZero_of_succ_succ P i

/-- Helper for Lemma 10.134.15: a homotopy equivalence between naive cotangent complexes induces
an isomorphism on the stabilized degree-`1/0` block map from Lemma 10.134.14. -/
private theorem naiveCotangent_term_complex_biprod_hom_isIso
    {P Q : Extension.{u} R S}
    (e : HomotopyEquiv P.naiveCotangentChainComplex Q.naiveCotangentChainComplex) :
    IsIso (term_complex_biprod_hom e) := by
  -- Route correction: apply Lemma 10.134.14 through the explicit concentration API now required
  -- for the naive cotangent complexes.
  exact term_complex_biprod_hom_isIso
    (fun n hn0 hn1 ↦ naiveCotangentChainComplex_concentrated_away_from_zero_one P n hn0 hn1)
    (fun n hn0 hn1 ↦ naiveCotangentChainComplex_concentrated_away_from_zero_one Q n hn0 hn1)
    e

private noncomputable def naiveCotangentLiftCotangentSpaceStableEquiv
    {P Q : Extension.{u} R S}
    (e : HomotopyEquiv P.naiveCotangentChainComplex Q.naiveCotangentChainComplex) :
    (LiftCotangent P × Q.CotangentSpace) ≃ₗ[S]
      (LiftCotangent Q × P.CotangentSpace) := by
  -- The stable block isomorphism is exactly Lemma 10.134.14 applied to the concentrated naive
  -- cotangent complexes.
  letI : IsIso (term_complex_biprod_hom e) :=
    naiveCotangent_term_complex_biprod_hom_isIso e
  simpa [Algebra.Extension.naiveCotangentChainComplex] using
    (((ModuleCat.biprodIsoProd
        (P.naiveCotangentChainComplex.X 1)
        (Q.naiveCotangentChainComplex.X 0)).symm ≪≫
      asIso (term_complex_biprod_hom e) ≪≫
      ModuleCat.biprodIsoProd
        (Q.naiveCotangentChainComplex.X 1)
        (P.naiveCotangentChainComplex.X 0))).toLinearEquiv

-- Proof sketch: compare the two naive cotangent complexes by the canonical default maps between
-- the presentations. The `map_sub_map` identities give the chain homotopies showing those maps
-- are homotopy inverse. Applying `term_complex_biprod_hom` yields the stable block isomorphism,
-- and the `ULift` bridge is immediately removed.
private noncomputable def presentation_cotangentSpace_stable_equiv_aux
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    (P.toExtension.Cotangent × Q.toExtension.CotangentSpace) ≃ₗ[S]
      (Q.toExtension.Cotangent × P.toExtension.CotangentSpace) :=
    (LinearEquiv.prodCongr
      (liftCotangentEquiv P.toExtension).symm
      (LinearEquiv.refl S Q.toExtension.CotangentSpace)).trans <|
    (naiveCotangentLiftCotangentSpaceStableEquiv
      (defaultNaiveCotangentChainHomotopyEquiv P Q)).trans <|
      LinearEquiv.prodCongr
        (liftCotangentEquiv Q.toExtension)
        (LinearEquiv.refl S P.toExtension.CotangentSpace)

/-- Core/canonical companion: before rewriting the cotangent-space summands by their free bases,
the stable presentation-independence statement is the linear equivalence
`P.toExtension.Cotangent × Q.toExtension.CotangentSpace ≃ₗ[S]
  Q.toExtension.Cotangent × P.toExtension.CotangentSpace`. -/
noncomputable abbrev presentation_cotangentSpace_stable_equiv
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    (P.toExtension.Cotangent × Q.toExtension.CotangentSpace) ≃ₗ[S]
      (Q.toExtension.Cotangent × P.toExtension.CotangentSpace) :=
  presentation_cotangentSpace_stable_equiv_aux P Q

-- Proof sketch: transport the cotangent-space summands of
-- `presentation_cotangentSpace_stable_equiv` along the canonical basis equivalences
-- `Q.cotangentSpaceBasis.repr` and `P.cotangentSpaceBasis.repr`.
/-- Lemma 10.134.15: for two finite presentations of the same `R`-algebra `S`, rewriting the
cotangent spaces by their canonical free bases yields the textbook stabilization
`I / I² ⊕ S^{⊕ m} ≃ J / J² ⊕ S^{⊕ n}`. -/
noncomputable def presentation_cotangent_stable_equiv
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    (P.toExtension.Cotangent × (Fin m →₀ S)) ≃ₗ[S]
      (Q.toExtension.Cotangent × (Fin n →₀ S)) := by
  let eQ := presentationCotangentSpaceBasisEquiv Q
  let eP := presentationCotangentSpaceBasisEquiv P
  exact
    (LinearEquiv.prodCongr
        (LinearEquiv.refl S P.toExtension.Cotangent)
        eQ.symm).trans <|
      (presentation_cotangentSpace_stable_equiv P Q).trans <|
        LinearEquiv.prodCongr
          (LinearEquiv.refl S Q.toExtension.Cotangent)
          eP

-- Proof sketch: this is the defining basis-change decomposition of
-- `presentation_cotangent_stable_equiv`, so the statement is immediate by unfolding the
-- definition.
/-- Companion `_def` lemma: `presentation_cotangent_stable_equiv` is obtained by transporting
`presentation_cotangentSpace_stable_equiv` along the canonical cotangent-space basis
equivalences. -/
theorem presentation_cotangent_stable_equiv_def
    (P : Generators R S (Fin n)) (Q : Generators R S (Fin m)) :
    presentation_cotangent_stable_equiv P Q =
      ((LinearEquiv.prodCongr
          (LinearEquiv.refl S P.toExtension.Cotangent)
          (presentationCotangentSpaceBasisEquiv Q).symm).trans <|
        (presentation_cotangentSpace_stable_equiv P Q).trans <|
          LinearEquiv.prodCongr
            (LinearEquiv.refl S Q.toExtension.Cotangent)
            (presentationCotangentSpaceBasisEquiv P)) := by
  rfl

end
