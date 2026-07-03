import stacks_project.Chap10.Definition_10_134_1

open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent

universe u

noncomputable section

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: naive cotangent complexes attached to polynomial presentations of an
  `A`-algebra `B`;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the canonical owner `NL_{B⁄A}`;
  - `Algebra.Generators.self`, the canonical self-presentation underlying `NL_{B⁄A}`;
  - `Algebra.Generators.defaultHom`, the canonical comparison between two presentations of the
    same algebra;
  - `Algebra.Extension.toKaehler`, the canonical map from the degree-`0` term of a presentation
    complex to `Ω[B⁄A]`.
* best owner abstraction: the source-facing public statement should be about the canonical owner
  `NL_{B⁄A}`. A chosen polynomial algebra structure is bridge/view data used only to compare that
  owner with a presentation whose algebra map is bijective.
* primitive vs. derived:
  - primitive data: the algebra map `A → B` and, for the polynomial case, a chosen equivalence
    `MvPolynomial ι A ≃ₐ[A] B`;
  - derived API: the presentationwise naive cotangent complexes and the homotopy comparison
    between different presentations.
* layer triage:
  - `source-facing`: the homotopy equivalence `NL_{B⁄A} ≃ single₀ Ω[B⁄A]` for polynomial
    `A`-algebras;
  - `core/canonical`: `Algebra.naiveCotangent A B`;
  - `bridge/view`: the chosen polynomial presentation and the generic bijective-presentation
    comparison below.
-/

private abbrev LiftCotangent (P : Extension.{u} A B) :=
  ULift P.Cotangent

private noncomputable abbrev liftCotangentEquiv
    (P : Extension.{u} A B) :
    LiftCotangent P ≃ₗ[B] P.Cotangent :=
  ULift.moduleEquiv

private noncomputable def liftCotangentMap
    {P Q : Extension.{u} A B} (f : P.Hom Q) :
    LiftCotangent P →ₗ[B] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ
    Cotangent.map f ∘ₗ (liftCotangentEquiv P).toLinearMap

private noncomputable def liftCotangentHomotopyMap
    {P Q : Extension.{u} A B} (f g : P.Hom Q) :
    P.CotangentSpace →ₗ[B] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ f.sub g

private theorem liftCotangentMap_id
    (P : Extension.{u} A B) :
    liftCotangentMap (.id P) = LinearMap.id := by
  ext x
  rcases x with ⟨x⟩
  simp [liftCotangentMap]

private theorem liftCotangentMap_comp
    {P Q T : Extension.{u} A B} (f : P.Hom Q) (g : Q.Hom T) :
    liftCotangentMap (g.comp f) =
      (liftCotangentMap g).restrictScalars B ∘ₗ liftCotangentMap f := by
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
    (P : Extension.{u} A B) (i : ℕ) :
    P.naiveCotangentChainComplex.X (i + 2) ≅ ModuleCat.of.{u} B PUnit := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat.{u} B} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat.{u} B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of.{u} B PUnit, 0, zero_comp⟩
  simpa [naiveCotangentChainComplex] using
    (ChainComplex.mk'XIso
      (ModuleCat.of.{u} B P.CotangentSpace)
      (ModuleCat.of.{u} B (LiftCotangent P))
      (ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftCotangentEquiv P).toLinearMap))
      succZero i)

private theorem naiveCotangentChainComplex_eq_zero_of_succ_succ
    (P : Extension.{u} A B) (i : ℕ)
    (x : P.naiveCotangentChainComplex.X (i + 2)) :
    x = 0 := by
  let e := naiveCotangentChainComplexXIsoPUnit P i
  have h : e.hom.hom x = e.hom.hom 0 := by
    cases e.hom.hom x
    rfl
  apply_fun e.inv.hom at h
  simpa using h

private theorem naiveCotangentChainComplex_subsingleton_of_succ_succ
    (P : Extension.{u} A B) (i : ℕ) :
    Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) := by
  refine ⟨fun x y ↦ ?_⟩
  rw [naiveCotangentChainComplex_eq_zero_of_succ_succ P i x,
    naiveCotangentChainComplex_eq_zero_of_succ_succ P i y]

private noncomputable def naiveCotangentChainHomotopyHom
    {P Q : Extension.{u} A B} (f g : P.Hom Q)
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
    {P Q : Extension.{u} A B} (f g : P.Hom Q) :
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
        naiveCotangentChainComplex, liftCotangentHomotopyMap, LinearMap.comp_assoc] using
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
          rw [naiveCotangentChainComplex_d_succ_succ Q 0,
            naiveCotangentChainComplex_d_1_0 P]
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
    {P Q : Extension.{u} A B} (f g : P.Hom Q) :
    Homotopy (Extension.naiveCotangentChainMap f) (Extension.naiveCotangentChainMap g) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (naiveCotangentChainMap_sub_eq_nullHomotopicMap f g)).trans
      (Homotopy.nullHomotopy' (naiveCotangentChainHomotopyHom f g)))

private noncomputable abbrev defaultExtensionHom
    {ι ι' : Type u} (P : Generators A B ι) (Q : Generators A B ι') :
    P.toExtension.Hom Q.toExtension :=
  (Generators.defaultHom P Q).toExtensionHom

namespace Algebra.Generators

/-- Presentation-independence bridge: the naive cotangent complexes attached to any two
presentations of the same `A`-algebra `B` are canonically homotopy equivalent. -/
noncomputable def naiveCotangentChainHomotopyEquiv
    {ι ι' : Type u}
    (P : Generators A B ι) (Q : Generators A B ι') :
    HomotopyEquiv P.toExtension.naiveCotangentChainComplex Q.toExtension.naiveCotangentChainComplex where
  hom := Extension.naiveCotangentChainMap (defaultExtensionHom P Q)
  inv := Extension.naiveCotangentChainMap (defaultExtensionHom Q P)
  homotopyHomInvId := by
    let f := defaultExtensionHom P Q
    let g := defaultExtensionHom Q P
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp f g).symm).trans
        ((naiveCotangentChainMapHomotopy (g.comp f) (.id P.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id P.toExtension)))
  homotopyInvHomId := by
    let f := defaultExtensionHom P Q
    let g := defaultExtensionHom Q P
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp g f).symm).trans
        ((naiveCotangentChainMapHomotopy (f.comp g) (.id Q.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id Q.toExtension)))

end Algebra.Generators

private theorem cotangent_subsingleton_of_bijective
    (P : Extension.{u} A B) (hP : Function.Bijective (algebraMap P.Ring B)) :
    Subsingleton P.Cotangent := by
  letI : Subsingleton ↥P.ker := by
    refine ⟨fun x y ↦ ?_⟩
    apply Subtype.ext
    exact hP.1 <| by
      simpa [RingHom.mem_ker] using x.2.trans y.2.symm
  exact Cotangent.mk_surjective.subsingleton

private theorem cotangentComplex_eq_zero_of_subsingleton_cotangent
    (P : Extension.{u} A B) [Subsingleton P.Cotangent] :
    P.cotangentComplex = 0 := by
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

private theorem toKaehler_bijective_of_bijective
    (P : Extension.{u} A B) (hP : Function.Bijective (algebraMap P.Ring B)) :
    Function.Bijective P.toKaehler := by
  letI : Subsingleton P.Cotangent := cotangent_subsingleton_of_bijective P hP
  refine ⟨?_, P.toKaehler_surjective⟩
  intro x y hxy
  have hxy' : P.toKaehler (x - y) = 0 := by
    simpa using sub_eq_zero.mpr hxy
  have hexact := (LinearMap.exact_iff).mp P.exact_cotangentComplex_toKaehler
  have hmem : x - y ∈ LinearMap.range P.cotangentComplex := by
    rw [← hexact]
    exact hxy'
  rcases hmem with ⟨z, hz⟩
  rw [cotangentComplex_eq_zero_of_subsingleton_cotangent P] at hz
  exact sub_eq_zero.mp <| by simpa using hz.symm

/-- Bridge/view comparison: if a presentation `P` has bijective algebra map `P.Ring ≃ B`, then
its naive cotangent complex is already concentrated in degree `0` and is isomorphic to the chain
complex `single₀ Ω[B⁄A]`. -/
noncomputable def extension_naiveCotangentChainComplex_iso_single₀_kaehler_of_bijective
    (P : Extension.{u} A B) (hP : Function.Bijective (algebraMap P.Ring B)) :
    P.naiveCotangentChainComplex ≅
      ((ChainComplex.single₀ (ModuleCat.{u} B)).obj
        (ModuleCat.of.{u} B Ω[B⁄A])) := by
  letI : Subsingleton P.Cotangent := cotangent_subsingleton_of_bijective P hP
  let succZero :
      ∀ {X₀ X₁ : ModuleCat.{u} B} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat.{u} B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of.{u} B PUnit, 0, zero_comp⟩
  let C := P.naiveCotangentChainComplex
  let D := (ChainComplex.single₀ (ModuleCat.{u} B)).obj
    (ModuleCat.of.{u} B Ω[B⁄A])
  let e₀ : P.CotangentSpace ≃ₗ[B] Ω[B⁄A] :=
    LinearEquiv.ofBijective P.toKaehler (toKaehler_bijective_of_bijective P hP)
  let e : ∀ n : ℕ, C.X n ≅ D.X n
    | 0 => by
        simpa [C, D, naiveCotangentChainComplex] using e₀.toModuleIso
    | 1 => by
        simpa [C, D, naiveCotangentChainComplex] using
          ((ModuleCat.isZero_of_subsingleton
              (ModuleCat.of B (ULift P.Cotangent))).isoZero ≪≫
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
              (ModuleCat.of B Ω[B⁄A]) 1 (by decide)).isoZero.symm)
    | n + 2 => by
        have hs : (succZero (C.d (n + 1) n)).1 = ModuleCat.of B PUnit := rfl
        have hX :
            C.X (n + 2) ≅ (succZero (C.d (n + 1) n)).1 := by
          simpa [C, naiveCotangentChainComplex] using
            (ChainComplex.mk'XIso
              (ModuleCat.of.{u} B P.CotangentSpace)
              (ModuleCat.of.{u} B (ULift P.Cotangent))
              (ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))
              succZero n)
        simpa [D] using
          (hX ≪≫ eqToIso hs ≪≫
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of B PUnit)).isoZero ≪≫
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
              (ModuleCat.of B Ω[B⁄A]) (n + 2) (by simp)).isoZero.symm)
  exact HomologicalComplex.Hom.isoOfComponents e <| by
    intro i j hij
    subst i
    cases j with
    | zero =>
        have hcot :
            ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) = 0 := by
          rw [cotangentComplex_eq_zero_of_subsingleton_cotangent P]
          rfl
        have hC : C.d 1 0 = 0 := by
          simpa [C] using (naiveCotangentChainComplex_d_1_0 P).trans hcot
        have hD : D.d 1 0 = 0 := by
          simp [D]
        change (e 1).hom ≫ D.d 1 0 = C.d 1 0 ≫ (e 0).hom
        rw [hC, hD]
        simp
    | succ j =>
        have hC : C.d (j + 2) (j + 1) = 0 := by
          simpa [C] using naiveCotangentChainComplex_d_succ_succ P j
        have hD : D.d (j + 2) (j + 1) = 0 := by
          simp [D]
        change (e (j + 2)).hom ≫ D.d (j + 2) (j + 1) =
          C.d (j + 2) (j + 1) ≫ (e (j + 1)).hom
        rw [hC, hD]
        simp

/-- Bridge/view comparison: if a presentation `P` has bijective algebra map `P.Ring ≃ B`, then
its naive cotangent complex is homotopy equivalent to the chain complex concentrated in degree `0`
with value `Ω[B⁄A]`. -/
noncomputable def extension_naiveCotangentChainComplex_homotopyEquiv_single₀_kaehler_of_bijective
    (P : Extension.{u} A B) (hP : Function.Bijective (algebraMap P.Ring B)) :
    HomotopyEquiv
      P.naiveCotangentChainComplex
      ((ChainComplex.single₀ (ModuleCat.{u} B)).obj
        (ModuleCat.of.{u} B Ω[B⁄A])) :=
  HomotopyEquiv.ofIso
    (extension_naiveCotangentChainComplex_iso_single₀_kaehler_of_bijective P hP)

private noncomputable def polynomialPresentation
    {ι : Type u} (e : MvPolynomial ι A ≃ₐ[A] B) :
    Generators A B ι where
  val := fun i ↦ e (.X i)
  σ' := e.symm
  aeval_val_σ' b := by
    let h :
        MvPolynomial.aeval (fun i ↦ e (.X i)) = e.toAlgHom :=
      (MvPolynomial.aeval_unique e.toAlgHom).symm
    simp [h]

private theorem polynomialPresentation_algebraMap_bijective
    {ι : Type u} (e : MvPolynomial ι A ≃ₐ[A] B) :
    Function.Bijective (algebraMap (polynomialPresentation e).Ring B) := by
  change Function.Bijective (MvPolynomial.aeval (fun i ↦ e (.X i)))
  let h :
      MvPolynomial.aeval (fun i ↦ e (.X i)) = e.toAlgHom :=
    (MvPolynomial.aeval_unique e.toAlgHom).symm
  simpa [h] using e.bijective

-- Proof sketch: compare the canonical owner `NL_{B/A}` with the chosen polynomial presentation
-- attached to `e` by the default-presentation homotopy equivalence, then use the bijective-ring
-- bridge above to collapse the chosen presentation to `single₀ Ω[B⁄A]`.
/-- Lemma 10.134.3: if `B` is a polynomial algebra over `A`, witnessed by an `A`-algebra
equivalence `MvPolynomial ι A ≃ₐ[A] B`, then the canonical naive cotangent complex `NL_{B⁄A}` is
homotopy equivalent to the chain complex concentrated in degree `0` with value `Ω[B⁄A]`. -/
noncomputable def naiveCotangent_homotopyEquiv_single₀_kaehler_of_mvPolynomial
    {ι : Type u} (e : MvPolynomial ι A ≃ₐ[A] B) :
    HomotopyEquiv
      (NL_{B⁄A})
      ((ChainComplex.single₀ (ModuleCat.{u} B)).obj
        (ModuleCat.of.{u} B Ω[B⁄A])) := by
  let P := polynomialPresentation e
  exact
    (Generators.naiveCotangentChainHomotopyEquiv (Generators.self A B) P).trans
      (extension_naiveCotangentChainComplex_homotopyEquiv_single₀_kaehler_of_bijective
        P.toExtension (polynomialPresentation_algebraMap_bijective e))

end
