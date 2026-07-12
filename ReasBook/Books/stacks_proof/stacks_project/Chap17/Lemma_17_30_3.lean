import Mathlib
import StacksProject_2024.Chap10.Lemma_10_133_10
import StacksProject_2024.Chap17.Definition_17_29_1
import StacksProject_2024.Chap17.Definition_17_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open TopCat.Sheaf
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/- Domain-style sampling for Lemma 17.30.3:
- primary domain: relative de Rham differentials for a morphism of sheaves of rings on a fixed
  topological space;
- sampled owner declarations:
  `TopCat.Sheaf.deRhamComplex`,
  `CochainComplex.d`,
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`,
  `de_rham_differentials_are_order_one_differential_operators`;
- best owner abstraction: the canonical degree-`p` differential
  `(Ω^•(φ)).d p (p + 1)` in the source-facing owner `TopCat.Sheaf.deRhamComplex φ`;
- primitive data: only the morphism `φ : O₁ ⟶ O₂` and the degree `p`;
- derived API: the order-one differential-operator property of that canonical differential.

Source/core/bridge triage:
- `source-facing`: the order-one statement for the actual de Rham differential
  `d : \Omega^p_{O₂/O₁} \to \Omega^{p + 1}_{O₂/O₁}`;
- `core/canonical`: `TopCat.Sheaf.deRhamComplex φ` together with
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`;
- `bridge/view`: evaluation on opens inside the ringed-site owner. -/

/-- Helper for Lemma 17.30.3: on each open set, the algebraic de Rham differential attached to the
section ring map `O₁(U) → O₂(U)` is an order-one differential operator. -/
private theorem sectionwise_algebraic_de_rham_order_one
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ) :
    (deRhamDifferentialFamily (O₁.obj.obj U) (O₂.obj.obj U) p).IsDifferentialOperatorOfOrder
      (O₂.obj.obj U) 1 := by
  -- Proof comment: this is exactly the algebraic dependency from Lemma `10.133.10`, specialized
  -- to the ring map on sections over the open set `U`.
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := (φ.hom.app U).hom.toAlgebra
  simpa using
    de_rham_differentials_are_order_one_differential_operators
      (A := O₁.obj.obj U) (B := O₂.obj.obj U) p

/-- Helper for Lemma 17.30.3: an `A`-derivation into a `B`-module is a first-order differential
operator over `A → B`. -/
private theorem derivation_isDifferentialOperatorOfOrder_one
    {A B N : Type _} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (δ : Derivation A B N) :
    δ.toLinearMap.IsDifferentialOperatorOfOrder B 1 := by
  -- Proof comment: the commutator with multiplication by `g` is the `B`-linear map
  -- `m ↦ m • δ g`, so every commutator has order `0`.
  rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
  intro g
  rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
  intro h m
  -- Expand the Leibniz rule twice and collect the surviving term `h * m • δ g`.
  simp [LinearMap.scalarCommutator_apply, δ.leibniz, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 17.30.3: on each open set, the degree-`0` de Rham differential is the
universal derivation `d : O₂(U) → Ω_{O₂/O₁}(U)`. -/
private theorem de_rham_differential_zero_app
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    (((Ω^•(φ)).d 0 1).val.app U).hom = ((relativeDifferential φ).app U).d := by
  -- Proof comment: evaluate the public basic-form rule on the unique degree-`0` basic form.
  ext b
  simpa [basicFormSection, differentialTargetSection] using
    (deRhamComplex_d_basicForm φ U 0 b (fun i ↦ Fin.elim0 i))

/-- Helper for Lemma 17.30.3: the universal relative derivation on sections satisfies Leibniz. -/
private theorem relative_differential_app_leibniz
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) (b₀ b₁ : O₂.obj.obj U) :
    ((relativeDifferential φ).app U).d (b₀ * b₁) =
      b₀ • ((relativeDifferential φ).app U).d b₁ +
        b₁ • ((relativeDifferential φ).app U).d b₀ := by
  -- Proof comment: this is the sectionwise Leibniz rule of the universal derivation.
  simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
    (((relativeDifferential φ).app U).leibniz b₀ b₁)

/-- Helper for Lemma 17.30.3: a section of the sheafification of a presheaf of
`(ringSheaf O₂)`-modules comes from a genuine presheaf section after shrinking to a neighborhood of
the chosen point. -/
private theorem module_sheafification_unit_section_lifts_near_point
    (P : PresheafOfModules (ringSheaf O₂).obj) {U : Opens X} (x : X) (hxU : x ∈ U)
    (s : ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U) (z : P.obj (op V)),
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app P).app
          (op V)) z =
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.map
          (homOfLE ‹V ≤ U›).op s := by
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app P)
  have hη :
      (PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η =
        CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
    -- Proof comment: rewrite the module-sheafification unit as the additive sheafification unit.
    simpa [η] using
      (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 (ringSheaf O₂).obj) P)
  have hη_iso :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)) := by
    -- Proof comment: on stalks, the sheafification unit is an isomorphism, so it is locally
    -- surjective on sections.
    rw [hη]
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P.presheaf)
  have hη_surj :
      Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)) :=
    (CategoryTheory.isIso_iff_bijective _).1 hη_iso |>.2
  -- Proof comment: lift the germ of `s` through the stalk isomorphism and shrink to make the
  -- chosen representative agree with `s`.
  obtain ⟨m, hm⟩ :=
    hη_surj (TopCat.Presheaf.germ
      (((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.presheaf)
      U x hxU s)
  obtain ⟨V₀, hxV₀, z₀, hz₀⟩ := TopCat.Presheaf.germ_exist P.presheaf x m
  have hgerm :
      TopCat.Presheaf.germ
          (((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.presheaf)
          V₀ x hxV₀ ((η.app (op V₀)) z₀) =
        TopCat.Presheaf.germ
          (((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.presheaf)
          U x hxU s := by
    -- Proof comment: replace the abstract lifted stalk element by its local section
    -- representative.
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply V₀ x hxV₀
      ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η) z₀, hz₀, hm]
  obtain ⟨V, hxV, iV₀, iU, hsec⟩ :=
    TopCat.Presheaf.germ_eq
      (((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.presheaf)
      x hxV₀ hxU ((η.app (op V₀)) z₀) s hgerm
  let hVU : V ≤ U := iU.le
  let z : P.obj (op V) := P.map iV₀.op z₀
  refine ⟨V, hxV, hVU, z, ?_⟩
  have hnat :
      (η.app (op V)) z =
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.map iV₀.op
          ((η.app (op V₀)) z₀) := by
    -- Proof comment: naturality of the unit identifies restriction of the lifted section.
    simpa [η, z, FunctorToTypes.map_comp_apply] using
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (η.val.naturality iV₀.op)) z₀
  have hsec' :
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.map iV₀.op
          ((η.app (op V₀)) z₀) =
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.map iU.op s := by
    simpa using hsec
  rw [hnat, hsec']
  rfl

/-- Helper for Lemma 17.30.3: if a presheaf section maps to zero in the sheafification, then
after shrinking around any chosen point its restriction is already zero in the presheaf. -/
private theorem module_sheafification_unit_zero_near_point
    (P : PresheafOfModules (ringSheaf O₂).obj) {U : Opens X} (x : X) (hxU : x ∈ U)
    (z : P.obj (op U))
    (hz :
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app P).app
          (op U)) z = 0) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
      P.map (homOfLE ‹V ≤ U›).op z = 0 := by
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app P)
  have hη :
      (PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η =
        CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
    -- Proof comment: rewrite the module-sheafification unit as the additive sheafification unit.
    simpa [η] using
      (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 (ringSheaf O₂).obj) P)
  have hη_iso :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)) := by
    -- Proof comment: on stalks the sheafification unit is an isomorphism, so its stalk map is
    -- injective.
    rw [hη]
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P.presheaf)
  have hη_inj :
      Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)) :=
    (CategoryTheory.isIso_iff_bijective _).1 hη_iso |>.1
  have hgerm_zero :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)
          (TopCat.Presheaf.germ P.presheaf U x hxU z) = 0 := by
    -- Proof comment: push the source germ forward and use the assumed vanishing upstairs.
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η) z, hz]
    exact map_zero _
  have hgerm :
      TopCat.Presheaf.germ P.presheaf U x hxU z =
        TopCat.Presheaf.germ P.presheaf U x hxU (0 : P.obj (op U)) := by
    exact hη_inj (by simpa using hgerm_zero)
  obtain ⟨V, hxV, i₁, i₂, hsec⟩ :=
    TopCat.Presheaf.germ_eq P.presheaf x hxU hxU z 0 hgerm
  let hVU : V ≤ U := i₁.le
  refine ⟨V, hxV, hVU, ?_⟩
  -- Proof comment: equality of germs gives equality of restrictions on a smaller neighborhood.
  simpa using hsec

/-- Helper for Lemma 17.30.3: any higher-degree de Rham form section lifts locally to the
exterior-power presheaf on one-forms. -/
private theorem higher_form_section_lifts_near_point
    (φ : O₁ ⟶ O₂) (n : ℕ) {U : Opens X} (x : X) (hxU : x ∈ U)
    (s : (Ω^[n + 2](φ)).val.obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U)
      (z : (exteriorPowerPresheaf (Ω(φ)) (n + 2)).obj (op V)),
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
          (exteriorPowerPresheaf (Ω(φ)) (n + 2))).app (op V)) z =
        (Ω^[n + 2](φ)).val.map (homOfLE ‹V ≤ U›).op s := by
  -- Proof comment: this is exactly the generic sheafification lift specialized to the higher-form
  -- sheaf `Ω^[n + 2](φ) = Λ^[n + 2] Ω(φ)`.
  simpa [deRhamForm] using
    module_sheafification_unit_section_lifts_near_point
      (O₂ := O₂) (P := exteriorPowerPresheaf (Ω(φ)) (n + 2)) x hxU s

/-- Helper for Lemma 17.30.3: after shrinking around a chosen point, any one-form section lies in
the span of exact differentials. -/
private theorem one_form_section_mem_span_exact_near_point
    (φ : O₁ ⟶ O₂) {U : Opens X} (x : X) (hxU : x ∈ U)
    (ω : (Ω(φ)).val.obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
      (Ω(φ)).val.map (homOfLE ‹V ≤ U›).op ω ∈
        Submodule.span (O₂.obj.obj (op V))
          (Set.range (exactOneFormSection φ (op V))) := by
  obtain ⟨V, hxV, hVU, z, hz⟩ :=
    module_sheafification_unit_section_lifts_near_point
      (O₂ := O₂) (P := relativeDifferentials' φ.hom) x hxU ω
  refine ⟨V, hxV, hVU, ?_⟩
  let R := O₂.obj.obj (op V)
  have hzspan :
      z ∈ Submodule.span R
        (Set.range (KaehlerDifferential.D (O₁.obj.obj (op V)) (O₂.obj.obj (op V)))) := by
    -- Proof comment: the raw Kähler differentials are generated by exact one-forms on each open.
    rw [KaehlerDifferential.span_range_derivation (R := O₁.obj.obj (op V))
      (S := O₂.obj.obj (op V))]
    trivial
  have himage :
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
          (relativeDifferentials' φ.hom)).app (op V)) z ∈
        Submodule.span R (Set.range (exactOneFormSection φ (op V))) := by
    -- Proof comment: push the spanning relation forward through the universal one-form map.
    refine Submodule.span_induction hzspan ?_ ?_ ?_ ?_
    · rintro _ ⟨b, rfl⟩
      exact Submodule.subset_span ⟨b, rfl⟩
    · simpa using (Submodule.zero_mem (Submodule.span R (Set.range (exactOneFormSection φ (op V)))))
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
    · intro a b hb
      exact Submodule.smul_mem _ a hb
  simpa [exactOneFormSection, relativeDifferential] using (hz ▸ himage)

/-- Helper for Lemma 17.30.3: two higher-form sections are equal once their restrictions agree on
a neighborhood of every point of the ambient open set. -/
private theorem higher_form_section_eq_of_locally_equal
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (s t : (Ω^[n + 2](φ)).val.obj U)
    (hlocal : ∀ x : X, x ∈ U.unop →
      ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U.unop),
        (Ω^[n + 2](φ)).val.map (homOfLE ‹V ≤ U.unop›).op s =
          (Ω^[n + 2](φ)).val.map (homOfLE ‹V ≤ U.unop›).op t) :
    s = t := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨(Ω^[n + 2](φ)).val.presheaf, (Ω^[n + 2](φ)).isSheaf⟩
  -- Proof comment: sheaf sections are determined by their germs, so it suffices to compare
  -- the germs after shrinking to a neighborhood where the two restrictions coincide.
  apply TopCat.Presheaf.section_ext F U.unop s t
  intro x hxU
  obtain ⟨V, hxV, hVU, hst⟩ := hlocal x hxU
  calc
    TopCat.Presheaf.germ F.presheaf U.unop x hxU s =
        TopCat.Presheaf.germ F.presheaf V x hxV
          ((Ω^[n + 2](φ)).val.map (homOfLE hVU).op s) := by
            symm
            exact TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVU) x hxV s
    _ = TopCat.Presheaf.germ F.presheaf V x hxV
          ((Ω^[n + 2](φ)).val.map (homOfLE hVU).op t) := by
            rw [hst]
    _ = TopCat.Presheaf.germ F.presheaf U.unop x hxU t := by
          exact TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVU) x hxV t

/-- Helper for Lemma 17.30.3: a higher-form section is zero once it vanishes on a neighborhood of
every point. -/
private theorem higher_form_section_eq_zero_of_locally_zero
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (s : (Ω^[n + 2](φ)).val.obj U)
    (hlocal : ∀ x : X, x ∈ U.unop →
      ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U.unop),
        (Ω^[n + 2](φ)).val.map (homOfLE ‹V ≤ U.unop›).op s = 0) :
    s = 0 := by
  -- Proof comment: apply the local-equality criterion with the zero section as the comparison
  -- target.
  apply higher_form_section_eq_of_locally_equal (φ := φ) (n := n) (U := U) (s := s) (t := 0)
  intro x hxU
  obtain ⟨V, hxV, hVU, hsV⟩ := hlocal x hxU
  exact ⟨V, hxV, hVU, hsV⟩

/-- Helper for Lemma 17.30.3: on a basic form, the second scalar commutator of the de Rham
differential vanishes objectwise. -/
private theorem secondScalarCommutator_basicForm_eq_zero
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (g h b₀ : O₂.obj.obj U) (b : Fin (n + 1) → O₂.obj.obj U) :
    let D := (((Ω^•(φ)).d (n + 1) (n + 2)).val.app U).hom
    LinearMap.scalarCommutator (LinearMap.scalarCommutator D g) h
      (basicFormSection φ (n + 1) U b₀ b) = 0 := by
  let D := (((Ω^•(φ)).d (n + 1) (n + 2)).val.app U).hom
  -- Proof comment: expand both scalar commutators, rewrite each de Rham differential on a basic
  -- form, and use Leibniz to cancel the mixed terms.
  simp only [LinearMap.scalarCommutator_apply]
  rw [deRhamComplex_d_basicForm, deRhamComplex_d_basicForm, deRhamComplex_d_basicForm,
    deRhamComplex_d_basicForm]
  simp only [basicFormSection, differentialTargetSection, relative_differential_app_leibniz,
    map_add, map_smul, mul_smul, smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm,
    add_comm, add_left_comm, add_assoc, sub_eq_add_neg, add_left_neg, add_right_neg, zero_add,
    add_zero]

/-- Helper for Lemma 17.30.3: the `O₂(U)`-submodule of one-form sections spanned by exact
differentals on the open set `U`. -/
private abbrev exactOneFormSpan
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    Submodule (O₂.obj.obj U) ((Ω(φ)).val.obj U) :=
  Submodule.span (O₂.obj.obj U) (Set.range (exactOneFormSection φ U))

/-- Helper for Lemma 17.30.3: the degree-`n + 2` exterior-power generators built from exact
one-forms on the open set `U`. -/
private abbrev exactWedgeGenerator
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    (Fin (n + 2) → O₂.obj.obj U) →
      (exteriorPowerPresheaf (Ω(φ)) (n + 2)).obj U :=
  fun b ↦ exteriorPower.ιMulti (O₂.obj.obj U) (n + 2)
    (fun i ↦ exactOneFormSection φ U (b i))

/-- Helper for Lemma 17.30.3: the `O₂(U)`-submodule generated by exact wedge sections in degree
`n + 2`. -/
private abbrev exactWedgeSpan
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    Submodule (O₂.obj.obj U) ((exteriorPowerPresheaf (Ω(φ)) (n + 2)).obj U) :=
  Submodule.span (O₂.obj.obj U) (Set.range (exactWedgeGenerator φ n U))

/-- Helper for Lemma 17.30.3: restriction in the exterior-power presheaf sends an `ιMulti`
generator to the entrywise restricted generator. -/
private theorem exteriorPowerPresheaf_map_apply_ιMulti
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (m : Fin n → (Ω(φ)).val.obj U) :
    ((exteriorPowerPresheaf (Ω(φ)) n).map i).hom
        (exteriorPower.ιMulti (O₂.obj.obj U) n m) =
      exteriorPower.ιMulti (O₂.obj.obj V) n
        (fun j ↦ ((Ω(φ)).val.map i).hom (m j)) := by
  -- Proof comment: this is the Chapter 17 exterior-power restriction formula specialized to
  -- the one-form sheaf `Ω(φ)`.
  let R := O₂.obj.obj U
  let S := O₂.obj.obj V
  let M := (Ω(φ)).val.obj U
  let N := (Ω(φ)).val.obj V
  letI : Algebra R S := (O₂.val.map i).hom.toAlgebra
  letI : Module R N := Module.compHom N (O₂.val.map i).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R ↥(⋀[S]^n N) := Module.compHom _ (algebraMap R S)
  let f : M →ₗ[R] N := (Ω(φ)).val.map i |>.hom
  let ιN : N [⋀^Fin n]→ₗ[S] ↥(⋀[S]^n N) := exteriorPower.ιMulti S n
  let ιN' : N [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) :=
    { toMultilinearMap :=
        { toFun := ιN
          map_update_add' := by
            intro _ m j x y
            simpa using ιN.map_update_add m j x y
          map_update_smul' := by
            intro _ m j r x
            simpa only [algebraMap_smul S] using ιN.map_update_smul m j (algebraMap R S r) x }
      map_eq_zero_of_eq' := by
        intro m j k hjk hne
        exact ιN.map_eq_zero_of_eq m hjk hne }
  let A : M [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) := ιN'.compLinearMap f
  change (exteriorPower.alternatingMapLinearEquiv A)
      (exteriorPower.ιMulti R n m) =
    exteriorPower.ιMulti S n (fun j ↦ f (m j))
  calc
    (exteriorPower.alternatingMapLinearEquiv A) (exteriorPower.ιMulti R n m)
        = (exteriorPower.alternatingMapLinearEquiv.symm
            (exteriorPower.alternatingMapLinearEquiv A)) m := by
            symm
            simpa using
              (exteriorPower.alternatingMapLinearEquiv_symm_apply
                (F := exteriorPower.alternatingMapLinearEquiv A) m)
    _ = A m := by
          simpa using
            congrArg (fun F : M [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) ↦ F m)
              (exteriorPower.alternatingMapLinearEquiv.symm_apply_apply A)
    _ = exteriorPower.ιMulti S n (f ∘ m) := rfl

/-- Helper for Lemma 17.30.3: restricting an exact one-form span element keeps it inside the
exact one-form span on the smaller open. -/
private theorem exactOneFormSpan_map_mem
    (φ : O₁ ⟶ O₂) {U V : Opens X} (i : V ⟶ U)
    {ω : (Ω(φ)).val.obj (op U)} (hω : ω ∈ exactOneFormSpan φ (op U)) :
    (Ω(φ)).val.map i.op ω ∈ exactOneFormSpan φ (op V) := by
  -- Proof comment: restriction preserves exact generators by naturality of the universal
  -- differential, so it preserves their span.
  refine Submodule.span_induction hω ?_ ?_ ?_ ?_
  · rintro _ ⟨b, rfl⟩
    have hnat :
        (Ω(φ)).val.map i.op (exactOneFormSection φ (op U) b) =
          exactOneFormSection φ (op V) ((O₂.val.map i.op).hom b) := by
      simpa [exactOneFormSection, relativeDifferential, FunctorToTypes.map_comp_apply] using
        congrArg ModuleCat.Hom.hom ((relativeDifferential φ).naturality i.op)
    rw [hnat]
    exact Submodule.subset_span ⟨(O₂.val.map i.op).hom b, rfl⟩
  · simpa using (Submodule.zero_mem (exactOneFormSpan φ (op V)))
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb
  · intro a b hb
    exact Submodule.smul_mem _ ((O₂.val.map i.op).hom a) hb

/-- Helper for Lemma 17.30.3: the exact one-forms span the exact-one-form submodule even after
viewing them as subtype-valued generators. -/
private theorem exactOneFormSubtype_span_eq_top
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    Submodule.span (O₂.obj.obj U)
      (Set.range fun b : O₂.obj.obj U ↦
        (⟨exactOneFormSection φ U b, Submodule.subset_span ⟨b, rfl⟩⟩ :
          exactOneFormSpan φ U)) = ⊤ := by
  -- Proof comment: this is the same span as `exactOneFormSpan`, just rewritten inside its
  -- subtype carrier.
  apply top_unique
  intro x hx
  clear hx
  let S : Submodule (O₂.obj.obj U) (exactOneFormSpan φ U) :=
    Submodule.span (O₂.obj.obj U)
      (Set.range fun b : O₂.obj.obj U ↦
        (⟨exactOneFormSection φ U b, Submodule.subset_span ⟨b, rfl⟩⟩ :
          exactOneFormSpan φ U))
  have hxS :
      x ∈ S := by
    have hyS :
        ∀ {y : (Ω(φ)).val.obj U} (hy : y ∈ exactOneFormSpan φ U),
          (⟨y, hy⟩ : exactOneFormSpan φ U) ∈ S := by
      intro y hy
      refine Submodule.span_induction hy ?_ ?_ ?_ ?_
      · rintro _ ⟨b, rfl⟩
        exact Submodule.subset_span ⟨b, rfl⟩
      · simpa [S] using (Submodule.zero_mem S)
      · intro a b ha hb
        simpa [S] using Submodule.add_mem S ha hb
      · intro a b hb
        simpa [S] using Submodule.smul_mem S a hb
    exact hyS x.property
  simpa [S] using hxS

/-- Helper for Lemma 17.30.3: if every entry of an alternating generator lies in the exact
one-form span, then the whole generator lies in the exact-wedge span. -/
private theorem iMulti_mem_exactWedgeSpan_of_mem_exactOneFormSpan
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (m : Fin (n + 2) → (Ω(φ)).val.obj U)
    (hm : ∀ i, m i ∈ exactOneFormSpan φ U) :
    exteriorPower.ιMulti (O₂.obj.obj U) (n + 2) m ∈ exactWedgeSpan φ n U := by
  classical
  let R := O₂.obj.obj U
  let P := exactOneFormSpan φ U
  let mP : Fin (n + 2) → P := fun i ↦ ⟨m i, hm i⟩
  let sP : Set P := Set.range fun b : R ↦
    (⟨exactOneFormSection φ U b, Submodule.subset_span ⟨b, rfl⟩⟩ : P)
  have hsP : Submodule.span R sP = ⊤ := exactOneFormSubtype_span_eq_top (φ := φ) U
  have hspanP :
      Submodule.span R (exteriorPower.ιMulti R (n + 2) '' {a | Set.range a ⊆ sP}) =
        (⋀[R]^(n + 2) P : Submodule R (ExteriorAlgebra R P)) := by
    simpa using
      (exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top
        (R := R) (n := n + 2) (M := P) (s := sP) hsP)
  have hmemP :
      (exteriorPower.ιMulti R (n + 2) mP : ↥(⋀[R]^(n + 2) P)) ∈
        Submodule.span R (exteriorPower.ιMulti R (n + 2) '' {a | Set.range a ⊆ sP}) := by
    -- Proof comment: inside the exact-one-form submodule, the exact generators span the whole
    -- module, so the fixed-degree exterior power is spanned by exact tuples.
    rw [hspanP]
    exact (exteriorPower.ιMulti R (n + 2) mP).property
  let f : P →ₗ[R] (Ω(φ)).val.obj U := P.subtype
  have hmap_mem :
      exteriorPower.map (n + 2) f (exteriorPower.ιMulti R (n + 2) mP) ∈
        Submodule.map (exteriorPower.map (n + 2) f)
          (Submodule.span R (exteriorPower.ιMulti R (n + 2) '' {a | Set.range a ⊆ sP})) := by
    exact Submodule.map_mem _ hmemP
  have hmap_le :
      Submodule.map (exteriorPower.map (n + 2) f)
          (Submodule.span R (exteriorPower.ιMulti R (n + 2) '' {a | Set.range a ⊆ sP})) ≤
        exactWedgeSpan φ n U := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨a, ha, rfl⟩
    let b : Fin (n + 2) → R := fun i ↦ Classical.choose (ha ⟨i, rfl⟩)
    have hb : ∀ i, a i =
        (⟨exactOneFormSection φ U (b i), Submodule.subset_span ⟨b i, rfl⟩⟩ : P) := by
      intro i
      exact Classical.choose_spec (ha ⟨i, rfl⟩)
    have htuple : f ∘ a = fun i ↦ exactOneFormSection φ U (b i) := by
      funext i
      exact congrArg Subtype.val (hb i)
    rw [show exteriorPower.map (n + 2) f (exteriorPower.ιMulti R (n + 2) a) =
        exteriorPower.ιMulti R (n + 2) (f ∘ a) by
          rw [exteriorPower.map_apply_ιMulti]]
    rw [htuple]
    exact Submodule.subset_span ⟨b, rfl⟩
  have htarget :
      exteriorPower.map (n + 2) f (exteriorPower.ιMulti R (n + 2) mP) ∈ exactWedgeSpan φ n U :=
    hmap_le hmap_mem
  simpa [mP, f] using htarget

/-- Helper for Lemma 17.30.3: restriction preserves the exact-wedge span on higher-form
presheaf sections. -/
private theorem exactWedgeSpan_map_mem
    (φ : O₁ ⟶ O₂) (n : ℕ) {U V : Opens X} (i : V ⟶ U)
    {z : (exteriorPowerPresheaf (Ω(φ)) (n + 2)).obj (op U)}
    (hz : z ∈ exactWedgeSpan φ n (op U)) :
    (exteriorPowerPresheaf (Ω(φ)) (n + 2)).map i.op z ∈ exactWedgeSpan φ n (op V) := by
  -- Proof comment: restriction sends each exact wedge generator to the corresponding exact wedge
  -- generator on the smaller open, so it preserves the generated span.
  refine Submodule.span_induction hz ?_ ?_ ?_ ?_
  · rintro _ ⟨b, rfl⟩
    have hmap :
        (exteriorPowerPresheaf (Ω(φ)) (n + 2)).map i.op
            (exactWedgeGenerator φ n (op U) b) =
          exactWedgeGenerator φ n (op V) (fun j ↦ (O₂.val.map i.op).hom (b j)) := by
      rw [show exactWedgeGenerator φ n (op U) b =
          exteriorPower.ιMulti (O₂.obj.obj (op U)) (n + 2)
            (fun j ↦ exactOneFormSection φ (op U) (b j)) by rfl]
      rw [exteriorPowerPresheaf_map_apply_ιMulti (φ := φ) (i := i.op) (n := n + 2)]
      congr
      funext j
      simpa [exactOneFormSection, relativeDifferential, FunctorToTypes.map_comp_apply] using
        congrArg ModuleCat.Hom.hom ((relativeDifferential φ).naturality i.op)
    rw [hmap]
    exact Submodule.subset_span ⟨fun j ↦ (O₂.val.map i.op).hom (b j), rfl⟩
  · simpa using (Submodule.zero_mem (exactWedgeSpan φ n (op V)))
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb
  · intro a b hb
    exact Submodule.smul_mem _ ((O₂.val.map i.op).hom a) hb

/-- Helper for Lemma 17.30.3: a finite tuple of one-form sections can be made simultaneously
exact-span after shrinking around a chosen point. -/
private theorem finiteFamily_oneFormSections_memSpanExact_near_point
    (φ : O₁ ⟶ O₂) :
    ∀ (n : ℕ) {U : Opens X} (x : X) (hxU : x ∈ U)
      (ω : Fin n → (Ω(φ)).val.obj (op U)),
      ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
        ∀ i : Fin n,
          (Ω(φ)).val.map (homOfLE ‹V ≤ U›).op (ω i) ∈ exactOneFormSpan φ (op V)
  | 0, U, x, hxU, ω => by
      refine ⟨U, hxU, le_rfl, ?_⟩
      intro i
      exact (Fin.elim0 i)
  | n + 1, U, x, hxU, ω => by
      obtain ⟨V₀, hxV₀, hV₀U, hω₀⟩ :=
        one_form_section_mem_span_exact_near_point (φ := φ) x hxU (ω 0)
      let i₀ : V₀ ⟶ U := homOfLE hV₀U
      obtain ⟨V, hxV, hVV₀, htail⟩ :=
        finiteFamily_oneFormSections_memSpanExact_near_point (φ := φ) n x hxV₀
          (fun j ↦ (Ω(φ)).val.map i₀.op (ω j.succ))
      refine ⟨V, hxV, hVV₀.trans hV₀U, ?_⟩
      intro i
      cases i using Fin.cases with
      | zero =>
          have hrestrict :
              (Ω(φ)).val.map (homOfLE hVV₀).op
                  ((Ω(φ)).val.map i₀.op (ω 0)) ∈
                exactOneFormSpan φ (op V) :=
            exactOneFormSpan_map_mem (φ := φ) (i := homOfLE hVV₀) hω₀
          simpa [FunctorToTypes.map_comp_apply] using hrestrict
      | succ j =>
          simpa [FunctorToTypes.map_comp_apply] using htail j

/-- Helper for Lemma 17.30.3: after shrinking around a chosen point, a lifted higher-form section
lies in the span of exact wedge generators. -/
private theorem localLiftedHigherForm_memSpanExactWedges_near_point
    (φ : O₁ ⟶ O₂) (n : ℕ) {U : Opens X} (x : X) (hxU : x ∈ U)
    (z : (exteriorPowerPresheaf (Ω(φ)) (n + 2)).obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
      (exteriorPowerPresheaf (Ω(φ)) (n + 2)).map (homOfLE ‹V ≤ U›).op z ∈
        exactWedgeSpan φ n (op V) := by
  let R := O₂.obj.obj (op U)
  have hz :
      z ∈ Submodule.span R
        (Set.range (exteriorPower.ιMulti R (n + 2) :
          (Fin (n + 2) → (Ω(φ)).val.obj (op U)) →
            (exteriorPowerPresheaf (Ω(φ)) (n + 2)).obj (op U))) := by
    -- Proof comment: the exterior-power presheaf object is generated by its `ιMulti` sections.
    rw [← exteriorPower.ιMulti_span_fixedDegree
      (R := R) (n := n + 2) (M := (Ω(φ)).val.obj (op U))]
    exact z.property
  refine Submodule.span_induction hz ?_ ?_ ?_ ?_
  · intro y hy
    rcases hy with ⟨m, rfl⟩
    obtain ⟨V, hxV, hVU, hmV⟩ :=
      finiteFamily_oneFormSections_memSpanExact_near_point (φ := φ) (n + 2) x hxU m
    refine ⟨V, hxV, hVU, ?_⟩
    rw [exteriorPowerPresheaf_map_apply_ιMulti (φ := φ) (i := (homOfLE hVU).op) (n := n + 2)]
    exact iMulti_mem_exactWedgeSpan_of_mem_exactOneFormSpan (φ := φ) n (op V)
      (fun j ↦ ((Ω(φ)).val.map (homOfLE hVU).op).hom (m j)) hmV
  · refine ⟨U, hxU, le_rfl, ?_⟩
    simpa using (Submodule.zero_mem (exactWedgeSpan φ n (op U)))
  · intro a b ha hb
    rcases ha with ⟨V₁, hxV₁, hV₁U, haV₁⟩
    rcases hb with ⟨V₂, hxV₂, hV₂U, hbV₂⟩
    let V : Opens X := V₁ ⊓ V₂
    have hxV : x ∈ V := ⟨hxV₁, hxV₂⟩
    have hVU : V ≤ U := fun y hy ↦ hV₁U hy.1
    let i₁ : V ⟶ V₁ := homOfLE inf_le_left
    let i₂ : V ⟶ V₂ := homOfLE inf_le_right
    refine ⟨V, hxV, hVU, ?_⟩
    have haV :
        (exteriorPowerPresheaf (Ω(φ)) (n + 2)).map i₁.op
            ((exteriorPowerPresheaf (Ω(φ)) (n + 2)).map (homOfLE hV₁U).op a) ∈
          exactWedgeSpan φ n (op V) :=
      exactWedgeSpan_map_mem (φ := φ) n i₁ haV₁
    have hbV :
        (exteriorPowerPresheaf (Ω(φ)) (n + 2)).map i₂.op
            ((exteriorPowerPresheaf (Ω(φ)) (n + 2)).map (homOfLE hV₂U).op b) ∈
          exactWedgeSpan φ n (op V) :=
      exactWedgeSpan_map_mem (φ := φ) n i₂ hbV₂
    have haV' :
        (exteriorPowerPresheaf (Ω(φ)) (n + 2)).map (homOfLE hVU).op a ∈
          exactWedgeSpan φ n (op V) := by
      simpa [FunctorToTypes.map_comp_apply] using haV
    have hbV' :
        (exteriorPowerPresheaf (Ω(φ)) (n + 2)).map (homOfLE hVU).op b ∈
          exactWedgeSpan φ n (op V) := by
      simpa [FunctorToTypes.map_comp_apply] using hbV
    simpa [map_add] using Submodule.add_mem _ haV' hbV'
  · intro a b hb
    rcases hb with ⟨V, hxV, hVU, hbV⟩
    refine ⟨V, hxV, hVU, ?_⟩
    simpa [FunctorToTypes.map_smul] using
      Submodule.smul_mem (exactWedgeSpan φ n (op V))
        ((O₂.val.map (homOfLE hVU).op).hom a) hbV

/-- Helper for Lemma 17.30.3: after composing with the higher-form sheafification unit, the local
second scalar commutator kills the span of exact wedge generators. -/
private theorem liftedHigherFormSecondScalarCommutator_unit_eq_zero_of_memSpanExactWedges
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ) (g h : O₂.obj.obj U)
    (z : (exteriorPowerPresheaf (Ω(φ)) (n + 2)).obj U)
    (hz : z ∈ exactWedgeSpan φ n U) :
    let D := (((Ω^•(φ)).d (n + 1) (n + 2)).val.app U).hom
    let η :=
      ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
        (exteriorPowerPresheaf (Ω(φ)) (n + 2))).app U)).hom
    (LinearMap.scalarCommutator (LinearMap.scalarCommutator D g) h).comp η z = 0 := by
  let D := (((Ω^•(φ)).d (n + 1) (n + 2)).val.app U).hom
  let η :=
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
      (exteriorPowerPresheaf (Ω(φ)) (n + 2))).app U)).hom
  -- Proof comment: exact wedge generators are precisely the basic forms with leading coefficient
  -- `1`, and the earlier basic-form computation kills the commutator on those generators.
  refine Submodule.span_induction hz ?_ ?_ ?_ ?_
  · rintro _ ⟨b, rfl⟩
    have hbasic :
        η (exactWedgeGenerator φ n U b) =
          basicFormSection φ (n + 1) U 1 (fun j ↦ b j.succ) := by
      -- Proof comment: unpack the definition of a higher basic form as the image of the exact
      -- wedge generator under the sheafification unit.
      dsimp [exactWedgeGenerator, η, basicFormSection, higherExteriorPowerSection,
        wedgeOneFormsSection]
      congr
      funext i
      cases i using Fin.cases with
      | zero =>
          simp [exactOneFormSection]
      | succ j =>
          simp [exactOneFormSection]
    rw [LinearMap.comp_apply, hbasic]
    simpa [D, LinearMap.scalarCommutator_apply] using
      secondScalarCommutator_basicForm_eq_zero
        (φ := φ) (n := n) (U := U) (g := g) (h := h) (b₀ := 1)
        (b := fun j ↦ b j.succ)
  · simp
  · intro a b ha hb
    simp [ha, hb]
  · intro a b hb
    simp [hb]

/-- Helper for Lemma 17.30.3: a chosen higher-form lift rewrites the restricted double scalar
commutator as the corresponding local commutator evaluated on that lift. -/
private theorem restrictSecondScalarCommutator_eq_of_higherFormLift
    (φ : O₁ ⟶ O₂) (n : ℕ) {U V : Opens X} (hVU : V ≤ U)
    (g h : O₂.obj.obj (op U)) (s : (Ω^[n + 2](φ)).val.obj (op U))
    (z : (exteriorPowerPresheaf (Ω(φ)) (n + 2)).obj (op V))
    (hz :
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
          (exteriorPowerPresheaf (Ω(φ)) (n + 2))).app (op V)) z =
        (Ω^[n + 2](φ)).val.map (homOfLE hVU).op s) :
    let i : V ⟶ U := homOfLE hVU
    let D := (((Ω^•(φ)).d (n + 1) (n + 2)).val.app (op U)).hom
    let DV := (((Ω^•(φ)).d (n + 1) (n + 2)).val.app (op V)).hom
    let gV : O₂.obj.obj (op V) := (O₂.val.map i.op).hom g
    let hV : O₂.obj.obj (op V) := (O₂.val.map i.op).hom h
    let η :=
      ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
        (exteriorPowerPresheaf (Ω(φ)) (n + 2))).app (op V))).hom
    (Ω^[n + 2](φ)).val.map i.op
        (LinearMap.scalarCommutator D g (h • s) -
          h • LinearMap.scalarCommutator D g s) =
      ((LinearMap.scalarCommutator (LinearMap.scalarCommutator DV gV) hV).comp η) z := by
  let i : V ⟶ U := homOfLE hVU
  let D := (((Ω^•(φ)).d (n + 1) (n + 2)).val.app (op U)).hom
  let DV := (((Ω^•(φ)).d (n + 1) (n + 2)).val.app (op V)).hom
  let gV : O₂.obj.obj (op V) := (O₂.val.map i.op).hom g
  let hV : O₂.obj.obj (op V) := (O₂.val.map i.op).hom h
  let η :=
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
      (exteriorPowerPresheaf (Ω(φ)) (n + 2))).app (op V))).hom
  have hnatD (t : (Ω^[n + 2](φ)).val.obj (op U)) :
      (Ω^[n + 2](φ)).val.map i.op (D t) = DV ((Ω^[n + 2](φ)).val.map i.op t) := by
    -- Proof comment: the de Rham differential is a morphism of sheaves, so restricting after
    -- applying it agrees with applying the restricted differential.
    simpa [D, DV, FunctorToTypes.map_comp_apply] using
      congrArg ModuleCat.Hom.hom (((Ω^•(φ)).d (n + 1) (n + 2)).val.naturality i.op)
  -- Proof comment: expand the restricted commutator and replace the restricted higher-form
  -- section by the chosen lift equality `hz`.
  simp only [LinearMap.comp_apply, LinearMap.scalarCommutator_apply, map_sub]
  rw [hnatD, hnatD, hz]
  simp only [gV, hV, η, FunctorToTypes.map_smul]

/-- Lemma 17.30.3: for a morphism of sheaves of rings `φ : O₁ ⟶ O₂`, each differential
`d : \Omega^p_{O₂/O₁} \to \Omega^{p + 1}_{O₂/O₁}` in the canonical de Rham complex `Ω^•(φ)` is a
differential operator of order `1` relative to `φ`. -/
-- Proof sketch: evaluate the canonical de Rham differential on each open set, identify it with
-- the sectionwise algebraic de Rham differential, and apply the algebraic order-one result of
-- Lemma `10.133.10`.
theorem deRhamDifferential_isDifferentialOperatorOfOrder
    (φ : O₁ ⟶ O₂) (p : ℕ) :
    IsDifferentialOperatorOfOrder φ ((Ω^•(φ)).d p (p + 1)) 1 := by
  cases p with
  | zero =>
      intro U
      -- Proof comment: in degree `0`, the de Rham differential is the universal derivation on
      -- sections, so the general first-order fact for derivations applies directly.
      let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := (φ.hom.app U).hom.toAlgebra
      simpa [de_rham_differential_zero_app (φ := φ) (U := U)] using
        derivation_isDifferentialOperatorOfOrder_one (((relativeDifferential φ).app U))
  | succ p =>
      cases p with
      | zero =>
          intro U
          let D := (((Ω^•(φ)).d 1 2).val.app U).hom
          -- Route correction: degree `1` is simpler than the higher-form case. After shrinking to
          -- a neighborhood where the one-form section is a span of exact forms, the local double
          -- commutator vanishes by span induction on exact generators.
          -- Proof comment: as in the general order-one criterion, it suffices to show that the
          -- double scalar commutator vanishes locally on every one-form section.
          change D.IsDifferentialOperatorOfOrder (O₂.obj.obj U) 1
          rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
          intro g
          rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
          intro h s
          change
            LinearMap.scalarCommutator D g (h • s) -
                h • LinearMap.scalarCommutator D g s = 0
          apply higher_form_section_eq_zero_of_locally_zero (φ := φ) (n := 0) (U := U)
          intro x hxU
          obtain ⟨V, hxV, hVU, hsV⟩ :=
            one_form_section_mem_span_exact_near_point (φ := φ) x hxU s
          refine ⟨V, hxV, hVU, ?_⟩
          let i : V ⟶ U.unop := homOfLE hVU
          let DV := (((Ω^•(φ)).d 1 2).val.app (op V)).hom
          let gV : O₂.obj.obj (op V) := (O₂.val.map i.op).hom g
          let hV : O₂.obj.obj (op V) := (O₂.val.map i.op).hom h
          let sV : (Ω(φ)).val.obj (op V) := (Ω(φ)).val.map i.op s
          have hnatD (t : (Ω(φ)).val.obj (op U.unop)) :
              (Ω^[2](φ)).val.map i.op (D t) = DV ((Ω(φ)).val.map i.op t) := by
            -- Proof comment: naturality of the de Rham differential identifies restriction of
            -- `D t` with application of the restricted differential to the restricted section.
            simpa [D, DV, FunctorToTypes.map_comp_apply] using
              congrArg ModuleCat.Hom.hom
                (((Ω^•(φ)).d 1 2).val.naturality i.op)
          have hlocal :
              (Ω^[2](φ)).val.map i.op
                  (LinearMap.scalarCommutator D g (h • s) -
                    h • LinearMap.scalarCommutator D g s) =
                LinearMap.scalarCommutator DV gV (hV • sV) -
                  hV • LinearMap.scalarCommutator DV gV sV := by
            -- Proof comment: restrict the global commutator expression to `V` and rewrite it
            -- using naturality of the differential and linearity of the restriction maps.
            simp only [LinearMap.scalarCommutator_apply, map_sub]
            rw [hnatD, hnatD]
            simp only [gV, hV, sV, i, FunctorToTypes.map_smul, map_sub]
          -- Proof comment: on `V`, the restricted one-form section is a span of exact forms, and
          -- the generator case is exactly the basic-form computation for degree `1`.
          rw [hlocal]
          let L := LinearMap.scalarCommutator (LinearMap.scalarCommutator DV gV) hV
          change L sV = 0
          refine Submodule.span_induction hsV ?_ ?_ ?_ ?_
          · rintro _ ⟨b, rfl⟩
            -- Proof comment: exact one-forms are the basic generators `1 · db`, so the earlier
            -- basic-form commutator computation applies directly.
            simpa [L, DV, gV, hV, sV, exactOneFormSection, basicFormSection, relativeDifferential,
              LinearMap.scalarCommutator_apply] using
              secondScalarCommutator_basicForm_eq_zero
                (φ := φ) (n := 0) (U := op V) (g := gV) (h := hV) (b₀ := 1)
                (b := fun _ ↦ b)
          · simp [L]
          · intro a b ha hb
            simp [L, ha, hb]
          · intro a b hb
            simp [L, hb]
      | succ q =>
          intro U
          let D := (((Ω^•(φ)).d (q + 2) (q + 3)).val.app U).hom
          -- Route correction: the old direct objectwise-identification route fails because the
          -- public Chapter 17 API exposes the higher de Rham differential only through its
          -- basic-form rule on sheafified exterior powers, not as a literal algebraic
          -- sectionwise map.
          -- Proof comment: for source degree at least `2`, the remaining task is the genuinely
          -- higher-form local span argument on a lifted exterior-power section.
          change D.IsDifferentialOperatorOfOrder (O₂.obj.obj U) 1
          rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff]
          intro g
          rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
          intro h s
          change
            LinearMap.scalarCommutator D g (h • s) -
                h • LinearMap.scalarCommutator D g s = 0
          apply higher_form_section_eq_zero_of_locally_zero (φ := φ) (n := q + 1) (U := U)
          intro x hxU
          obtain ⟨V, hxV, hVU, z, hz⟩ :=
            higher_form_section_lifts_near_point (φ := φ) (n := q + 1) x hxU s
          obtain ⟨W, hxW, hWV, hzW⟩ :=
            localLiftedHigherForm_memSpanExactWedges_near_point
              (φ := φ) (n := q + 1) x hxV z
          refine ⟨W, hxW, hWV.trans hVU, ?_⟩
          let iWV : W ⟶ V := homOfLE hWV
          let iWU : W ⟶ U.unop := homOfLE (hWV.trans hVU)
          let zW : (exteriorPowerPresheaf (Ω(φ)) (q + 3)).obj (op W) :=
            (exteriorPowerPresheaf (Ω(φ)) (q + 3)).map iWV.op z
          have hzW' :
              (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
                  (exteriorPowerPresheaf (Ω(φ)) (q + 3))).app (op W)) zW =
                (Ω^[q + 3](φ)).val.map iWU.op s := by
            -- Proof comment: restrict the chosen lift equality `hz` from `V` down to `W`.
            have hnatη :
                (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
                    (exteriorPowerPresheaf (Ω(φ)) (q + 3))).app (op W)) zW =
                  (Ω^[q + 3](φ)).val.map iWV.op
                    ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
                      (exteriorPowerPresheaf (Ω(φ)) (q + 3))).app (op V)) z) := by
              simpa [zW, FunctorToTypes.map_comp_apply] using
                congrArg ModuleCat.Hom.hom
                  ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
                    (exteriorPowerPresheaf (Ω(φ)) (q + 3))).naturality iWV.op))
            rw [hnatη, hz]
            simpa [iWU, iWV, FunctorToTypes.map_comp_apply]
          rw [restrictSecondScalarCommutator_eq_of_higherFormLift
            (φ := φ) (n := q + 1) (hVU := hWV.trans hVU)
            (g := g) (h := h) (s := s) (z := zW) hzW']
          simpa using
            liftedHigherFormSecondScalarCommutator_unit_eq_zero_of_memSpanExactWedges
              (φ := φ) (n := q + 1) (U := op W)
              ((O₂.val.map iWU.op).hom g) ((O₂.val.map iWU.op).hom h) zW hzW

end TopCat.Sheaf
