import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory
open HomologicalComplex

universe t w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {T : Type t}
variable {I : T → CochainComplex 𝒜 ℤ} {P : CochainComplex 𝒜 ℤ}

local notation "Q" => DerivedCategory.Q

/-
Domain-style sampling for Lemma 13.31.5:
- primary domain: K-injective cochain complexes and products in the derived category;
- inspected owner declarations:
  * `CochainComplex.IsKInjective`
  * `CochainComplex.IsKInjective.Qh_map_bijective`
  * `CategoryTheory.Limits.PreservesLimit`
  * `HomologicalComplex.isLimitOfEval`
  * `CategoryTheory.Limits.Fan.IsLimit.lift`
  * `CategoryTheory.Limits.Fan.IsLimit.hom_ext`
  `IsLimit (Fan.mk P π)`; for the concrete termwise product family the canonical derived-category
  owner is the preservation statement `PreservesLimit (Discrete.functor I) Q`; the `Q.obj`-level
  universal morphisms are only a private bridge from an arbitrary chosen product cone to that
  owner;
- primitive data:
  * a family of complexes `I t`
  * a comparison family `π : ∀ t, P ⟶ I t`
- derived API:
  * the complex-level product witness `IsLimit (Fan.mk P π)`
  * the ambient instances `∀ t, (I t).IsKInjective`
  * `P.IsKInjective`
  * for a termwise product family `I`, the preservation witness
    `PreservesLimit (Discrete.functor I) Q`
  * the recoverable `IsLimit` witness in `DerivedCategory 𝒜` via
    `isLimitOfHasProductOfPreservesLimit`
  * the unique lift in `DerivedCategory 𝒜` for source objects of the form `Q.obj K`, together
    with the localization representative bridge from an arbitrary derived object via
    `Q.objPreimage`.

Source/core/bridge triage:
- source-facing: `isKInjective_of_product`, expressing the lemma through the complex-level product
  cone `Fan.mk P π`;
- core/canonical: `Fan.IsLimit` for the cochain-complex product cone `Fan.mk P π`, and for
  concrete termwise products the preservation owner `PreservesLimit (Discrete.functor I) Q`;
- bridge/view: `HomologicalComplex.isLimitOfEval` upgrades internal termwise product cones to
  `Fan.mk P π`, while `Q.objPreimage` and `Q.objObjPreimageIso` transport the `Q.obj`-level
  lift/uniqueness statement to an arbitrary derived object; this bridge stays private because the
  public owner is the preservation theorem.
-/

-- Proof sketch: for any acyclic complex `K`, the source proof studies the Hom-complex
-- `HomComplex K P`; we record the postcomposition map here because that is the canonical bridge
-- from the product cone on complexes to a product cone on Hom-complexes.
/-- Helper for Lemma 13.31.5: postcomposition by a morphism of complexes induces an additive map
on cochains of fixed degree in the Hom-complex. -/
private theorem homComplex_postcomp_map_zero
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) (n : ℤ) :
    (0 : CochainComplex.HomComplex.Cochain K L n).comp
        (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) = 0 := by
  simpa only using
    (CochainComplex.HomComplex.Cochain.zero_comp
      (n₁ := n) (n₂ := 0) (n₁₂ := n) (h := add_zero n)
      (CochainComplex.HomComplex.Cochain.ofHom σ))

/-- Helper for Lemma 13.31.5: postcomposition on cochains is additive. -/
private theorem homComplex_postcomp_map_add
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) (n : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain K L n) :
    (z + z').comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) =
      z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) +
        z'.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) := by
  simpa only using
    (CochainComplex.HomComplex.Cochain.add_comp
      (n₁ := n) (n₂ := 0) (n₁₂ := n) (h := add_zero n) z z'
      (CochainComplex.HomComplex.Cochain.ofHom σ))

/-- Helper for Lemma 13.31.5: postcomposition by a morphism of complexes gives an additive
endomorphism on each Hom-complex degree. -/
private def homComplex_postcompAddMonoidHom
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) (n : ℤ) :
    CochainComplex.HomComplex.Cochain K L n →+ CochainComplex.HomComplex.Cochain K M n :=
  { toFun := fun z ↦ z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n)
    map_zero' := homComplex_postcomp_map_zero σ n
    map_add' := homComplex_postcomp_map_add σ n }

/-- Helper for Lemma 13.31.5: the postcomposition maps on cochains commute with the Hom-complex
differential. -/
private theorem homComplex_postcomp_comm
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel i j) :
    AddCommGrpCat.ofHom (homComplex_postcompAddMonoidHom σ i) ≫
        (CochainComplex.HomComplex K M).d i j =
      (CochainComplex.HomComplex K L).d i j ≫
        AddCommGrpCat.ofHom (homComplex_postcompAddMonoidHom σ j) := by
  -- This is the chain-level compatibility needed for the Hom-complex product cone.
  ext z
  change
    CochainComplex.HomComplex.δ i j
        (z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero i)) =
      (CochainComplex.HomComplex.δ i j z).comp
        (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero j)
  simpa only using
    (CochainComplex.HomComplex.δ_comp_ofHom (n := i) z σ j)

/-- Helper for Lemma 13.31.5: postcomposition by a morphism of complexes induces a morphism of
Hom-complexes. -/
private def homComplex_postcomp
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) :
    CochainComplex.HomComplex K L ⟶ CochainComplex.HomComplex K M :=
  { f := fun n ↦ AddCommGrpCat.ofHom (homComplex_postcompAddMonoidHom σ n)
    comm' := homComplex_postcomp_comm σ }

/-- Helper for Lemma 13.31.5: after evaluating a product cone of complexes in a fixed degree and
applying coyoneda, the resulting cone of types still admits a limiting structure. -/
private theorem evaluated_product_coyoneda_nonempty
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (n : ℤ) (X : 𝒜) :
    Nonempty
      (IsLimit
      ((HomologicalComplex.eval 𝒜 (up ℤ) n ⋙ coyoneda.obj (Opposite.op X)).mapCone
        (Fan.mk P π))) := by
  let F := HomologicalComplex.eval 𝒜 (up ℤ) n ⋙ coyoneda.obj (Opposite.op X)
  haveI : F.IsCorepresentable :=
    (HomologicalComplex.evalCompCoyonedaCorepresentable (C := 𝒜) (c := up ℤ) X n).isCorepresentable
  exact ⟨by simpa [F] using isLimitOfPreserves F hP⟩

/-- Helper for Lemma 13.31.5: a product cone of cochain complexes gives products in each
degree. -/
private theorem degreewise_product_isLimit_nonempty
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (n : ℤ) :
    Nonempty (IsLimit (Fan.mk (P.X n) fun t ↦ (π t).f n)) := by
  classical
  let c : Fan fun t ↦ (I t).X n := Fan.mk (P.X n) fun t ↦ (π t).f n
  refine ⟨((Limits.Cone.isLimitCoyonedaEquiv c).symm ?_)⟩
  intro X
  let hX := Classical.choice (evaluated_product_coyoneda_nonempty π hP n X.unop)
  -- The coyoneda image of the degreewise fan is the same mapped product cone seen through
  -- evaluation and then `coyoneda`.
  exact
    (Fan.isLimitMapConeEquiv (coyoneda.obj X) (fun t ↦ (I t).X n) c).symm
      ((CategoryTheory.Limits.isLimitMapConeFanMkEquiv
        (HomologicalComplex.eval 𝒜 (up ℤ) n ⋙ coyoneda.obj X) I π) hX)

/-- Helper for Lemma 13.31.5: a chosen degreewise product structure induced by the product cone of
complexes. -/
private noncomputable def degreewise_product_isLimit
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (n : ℤ) :
    IsLimit (Fan.mk (P.X n) fun t ↦ (π t).f n) :=
  Classical.choice (degreewise_product_isLimit_nonempty π hP n)

/-- Helper for Lemma 13.31.5: if all projections of a morphism to a product complex are
null-homotopic, then the morphism itself is null-homotopic. -/
private theorem null_homotopy_of_factorwise_null_homotopy
    {K : CochainComplex 𝒜 ℤ}
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (f : K ⟶ P)
    (hf : ∀ t, Nonempty (Homotopy (f ≫ π t) 0)) :
    Nonempty (Homotopy f 0) := by
  classical
  let αt : ∀ t, CochainComplex.HomComplex.Cochain K (I t) (-1) := fun t ↦
    ((CochainComplex.HomComplex.Cochain.equivHomotopy (f ≫ π t) 0)
      (Classical.choice (hf t))).1
  have hαt :
      ∀ t,
        CochainComplex.HomComplex.Cochain.ofHom (f ≫ π t) =
          CochainComplex.HomComplex.δ (-1) 0 (αt t) := by
    intro t
    -- Each chosen factorwise homotopy identifies `f ≫ π t` with a coboundary in degree `-1`.
    simpa only [αt, CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero] using
      ((CochainComplex.HomComplex.Cochain.equivHomotopy (f ≫ π t) 0)
        (Classical.choice (hf t))).2
  let α : CochainComplex.HomComplex.Cochain K P (-1) :=
    CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
      (degreewise_product_isLimit π hP q).lift
        (Fan.mk (K.X p) fun t ↦ (αt t).v p q hpq)
  have hα_fac (t : T) :
      α.comp (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero (-1)) = αt t := by
    ext p q hpq
    -- The assembled cochain has the prescribed factorwise components by the degreewise product
    -- universal property.
    simpa [α] using
      (Fan.IsLimit.fac (degreewise_product_isLimit π hP q)
        (fun s ↦ (αt s).v p q hpq) t)
  have hα_eq :
      CochainComplex.HomComplex.Cochain.ofHom f =
        CochainComplex.HomComplex.δ (-1) 0 α := by
    apply CochainComplex.HomComplex.Cochain.ext₀
    intro p
    -- Equality of degreewise components is checked after composing with every product projection.
    apply Fan.IsLimit.hom_ext (degreewise_product_isLimit π hP p)
    intro t
    have hcomp :
        (CochainComplex.HomComplex.Cochain.ofHom f).comp
            (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero 0) =
          (CochainComplex.HomComplex.δ (-1) 0 α).comp
            (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero 0) := by
      calc
        (CochainComplex.HomComplex.Cochain.ofHom f).comp
            (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero 0) =
          CochainComplex.HomComplex.Cochain.ofHom (f ≫ π t) := by
            simpa only using (CochainComplex.HomComplex.Cochain.ofHom_comp f (π t)).symm
        _ = CochainComplex.HomComplex.δ (-1) 0 (αt t) := hαt t
        _ = CochainComplex.HomComplex.δ (-1) 0
              (α.comp (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero (-1))) := by
            rw [hα_fac t]
        _ = (CochainComplex.HomComplex.δ (-1) 0 α).comp
              (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero 0) := by
            symm
            simpa only using
              (CochainComplex.HomComplex.δ_comp_ofHom (n := -1) α (π t) 0).symm
    have hcomp_v :=
      CochainComplex.HomComplex.Cochain.congr_v hcomp p p (add_zero p)
    simpa using hcomp_v
  -- The assembled `-1`-cochain is exactly the datum of a null-homotopy of `f`.
  refine ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy f 0).symm ?_⟩
  refine ⟨α, ?_⟩
  rw [hα_eq, CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]

/-- Helper for Lemma 13.31.5: a product cone of complexes induces the corresponding product cone
in the homotopy category. -/
private theorem homotopyCategory_product_existsUnique_of_product_cone
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (u : ∀ t,
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj (I t)) :
    ∃! v : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P,
      ∀ t, v ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map (π t) = u t := by
  classical
  let KQ := HomotopyCategory.quotient 𝒜 (up ℤ)
  let u' : ∀ t, K ⟶ I t := fun t ↦ (KQ.map_surjective (u t)).choose
  have hu' : ∀ t, KQ.map (u' t) = u t := fun t ↦ (KQ.map_surjective (u t)).choose_spec
  let v' : K ⟶ P := hP.lift (Fan.mk K u')
  have hv' : ∀ t, KQ.map v' ≫ KQ.map (π t) = u t := by
    intro t
    -- The chosen lift in complexes already has the correct projections in the homotopy category.
    simpa [v', hu' t, Functor.map_comp] using
      congrArg (fun m ↦ KQ.map m) (Fan.IsLimit.fac hP u' t)
  refine ⟨KQ.map v', hv', ?_⟩
  intro m hm
  obtain ⟨m', hm'⟩ := KQ.map_surjective m
  have hfactor :
      ∀ t, Nonempty (Homotopy ((m' - v') ≫ π t) 0) := by
    intro t
    -- Equality of projections in the homotopy category means each factor of the difference is
    -- null-homotopic.
    apply (HomotopyCategory.quotient_map_eq_zero_iff ((m' - v') ≫ π t)).1
    rw [Functor.map_comp, Functor.map_sub, Preadditive.sub_comp, hm', hm t, hv' t, sub_self]
  have hnull :
      Nonempty (Homotopy (m' - v') 0) :=
    null_homotopy_of_factorwise_null_homotopy π hP (m' - v') hfactor
  have hzero : KQ.map (m' - v') = 0 :=
    (HomotopyCategory.quotient_map_eq_zero_iff (m' - v')).2 hnull
  have hm_eq : KQ.map m' = KQ.map v' := by
    apply sub_eq_zero.mp
    simpa using hzero
  calc
    m = KQ.map m' := hm'.symm
    _ = KQ.map v' := hm_eq

/-- Core product form of Lemma 13.31.5: a product of K-injective cochain complexes is
K-injective. -/
theorem isKInjective_of_product
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π)) :
    P.IsKInjective := by
  -- Route correction: instead of a bespoke cone isomorphism, use evaluation to get degreewise
  -- products and then assemble the factorwise null-homotopies into one homotopy on the product.
  refine ⟨fun {K} f hK ↦ ?_⟩
  exact null_homotopy_of_factorwise_null_homotopy π hP f fun t ↦
    CochainComplex.IsKInjective.nonempty_homotopy_zero (f ≫ π t) hK

section

variable [HasDerivedCategory.{w} 𝒜]

/-- Helper for Lemma 13.31.5: conjugating a `Qh`-image along `quotientCompQhIso` recovers the
corresponding `Q`-image. -/
private theorem quotientCompQhIso_homCongr_map
    {K L : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) :
    (Iso.homCongr ((quotientCompQhIso 𝒜).app K) ((quotientCompQhIso 𝒜).app L))
      (Qh.map ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f)) = Q.map f := by
  -- This is the naturality square for the comparison isomorphism `quotient ⋙ Qh ≅ Q`.
  change
    (quotientCompQhIso 𝒜).inv.app K ≫
        Qh.map ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) ≫
          (quotientCompQhIso 𝒜).hom.app L =
      Q.map f
  have hnat :
      Qh.map ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) ≫
          (quotientCompQhIso 𝒜).hom.app L =
        (quotientCompQhIso 𝒜).hom.app K ≫ Q.map f := by
    simpa [Functor.comp_map] using (quotientCompQhIso 𝒜).hom.naturality f
  calc
    (quotientCompQhIso 𝒜).inv.app K ≫
        Qh.map ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) ≫
          (quotientCompQhIso 𝒜).hom.app L =
      (quotientCompQhIso 𝒜).inv.app K ≫
        ((quotientCompQhIso 𝒜).hom.app K ≫ Q.map f) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (quotientCompQhIso 𝒜).inv.app K ≫ k) hnat
    _ = Q.map f := by
          simpa using
            (Iso.inv_hom_id_assoc ((quotientCompQhIso 𝒜).app K) (Q.map f))

-- Proof sketch: use the previous K-injectivity statement together with the characterization of
-- morphisms into a K-injective complex in the derived category, first for source objects of the
-- form `Q.obj K`; the intermediate owner-level statement is existence and uniqueness of the lift
-- to `Q.obj P` against the product fan. The final product cone in `DerivedCategory 𝒜` is then
-- obtained for an arbitrary source object by transporting along `Q.objObjPreimageIso`.
private theorem qObjProduct_existsUnique
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (f : ∀ t, Q.obj K ⟶ Q.obj (I t)) :
    ∃! g : Q.obj K ⟶ Q.obj P, ∀ t, g ≫ Q.map (π t) = f t := by
  classical
  let KQ := HomotopyCategory.quotient 𝒜 (up ℤ)
  let eP := Iso.homCongr ((quotientCompQhIso 𝒜).app K) ((quotientCompQhIso 𝒜).app P)
  let eI : ∀ t, (Qh.obj (KQ.obj K) ⟶ Qh.obj (KQ.obj (I t))) ≃ (Q.obj K ⟶ Q.obj (I t)) := fun t ↦
    Iso.homCongr ((quotientCompQhIso 𝒜).app K) ((quotientCompQhIso 𝒜).app (I t))
  haveI : P.IsKInjective := isKInjective_of_product π hP
  let u : ∀ t, KQ.obj K ⟶ KQ.obj (I t) := fun t ↦
    ((CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj K) (I t)).surjective
      ((eI t).symm (f t))).choose
  have hu : ∀ t, Qh.map (u t) = (eI t).symm (f t) := by
    intro t
    exact
      ((CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj K) (I t)).surjective
        ((eI t).symm (f t))).choose_spec
  obtain ⟨v, hv, hvuniq⟩ := homotopyCategory_product_existsUnique_of_product_cone π hP K u
  have huQ : ∀ t, eI t (Qh.map (u t)) = f t := by
    intro t
    rw [hu t]
    exact (eI t).apply_symm_apply (f t)
  have htransport (g : KQ.obj K ⟶ KQ.obj P) (t : T) :
      eP (Qh.map g) ≫ Q.map (π t) = eI t (Qh.map (g ≫ KQ.map (π t))) := by
    -- This is the naturality square of `quotientCompQhIso`, written after conjugating the
    -- homotopy-category morphism.
    have hnat :
        (quotientCompQhIso 𝒜).hom.app P ≫ Q.map (π t) =
          Qh.map (KQ.map (π t)) ≫ (quotientCompQhIso 𝒜).hom.app (I t) := by
      simpa [Functor.comp_map] using ((quotientCompQhIso 𝒜).hom.naturality (π t)).symm
    calc
      eP (Qh.map g) ≫ Q.map (π t) =
          (quotientCompQhIso 𝒜).inv.app K ≫ Qh.map g ≫
            (quotientCompQhIso 𝒜).hom.app P ≫ Q.map (π t) := by
              show
                (((quotientCompQhIso 𝒜).app K).inv ≫ Qh.map g ≫ ((quotientCompQhIso 𝒜).app P).hom) ≫
                    Q.map (π t) =
                  (quotientCompQhIso 𝒜).inv.app K ≫ Qh.map g ≫
                    (quotientCompQhIso 𝒜).hom.app P ≫ Q.map (π t)
              simp [Category.assoc]
      _ =
          (quotientCompQhIso 𝒜).inv.app K ≫ Qh.map g ≫
            (Qh.map (KQ.map (π t)) ≫ (quotientCompQhIso 𝒜).hom.app (I t)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ (quotientCompQhIso 𝒜).inv.app K ≫ Qh.map g ≫ k)
                  hnat
      _ =
          (quotientCompQhIso 𝒜).inv.app K ≫
            (Qh.map g ≫ Qh.map (KQ.map (π t))) ≫ (quotientCompQhIso 𝒜).hom.app (I t) := by
              simp [Category.assoc]
      _ =
          (quotientCompQhIso 𝒜).inv.app K ≫
            Qh.map (g ≫ KQ.map (π t)) ≫ (quotientCompQhIso 𝒜).hom.app (I t) := by
              simp [Functor.map_comp, Category.assoc]
      _ = eI t (Qh.map (g ≫ KQ.map (π t))) := by
            show
              (quotientCompQhIso 𝒜).inv.app K ≫
                  Qh.map (g ≫ KQ.map (π t)) ≫ (quotientCompQhIso 𝒜).hom.app (I t) =
                (((quotientCompQhIso 𝒜).app K).homCongr ((quotientCompQhIso 𝒜).app (I t)))
                  (Qh.map (g ≫ KQ.map (π t)))
            rfl
  refine ⟨eP (Qh.map v), ?_, ?_⟩
  · intro t
    -- The homotopy-category lift transports to the required derived-category projection formula.
    have hvQh : Qh.map (v ≫ KQ.map (π t)) = Qh.map (u t) := by
      simpa [Functor.map_comp] using congrArg (fun m ↦ Qh.map m) (hv t)
    calc
      eP (Qh.map v) ≫ Q.map (π t) =
        eI t (Qh.map (v ≫ KQ.map (π t))) := htransport v t
      _ = eI t (Qh.map (u t)) := by
          rw [hvQh]
      _ = f t := huQ t
  · intro m hm
    obtain ⟨m', hm'⟩ :=
      (CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj K) P).surjective ((eP).symm m)
    have hmQ : eP (Qh.map m') = m := by
      rw [hm']
      exact eP.apply_symm_apply m
    have hm'fac : ∀ t, m' ≫ KQ.map (π t) = u t := by
      intro t
      have hderived :
          eI t (Qh.map (m' ≫ KQ.map (π t))) = eI t (Qh.map (u t)) := by
        calc
          eI t (Qh.map (m' ≫ KQ.map (π t))) =
              eP (Qh.map m') ≫ Q.map (π t) := by
                simpa using (htransport m' t).symm
          _ = m ≫ Q.map (π t) := by rw [hmQ]
          _ = f t := hm t
          _ = eI t (Qh.map (u t)) := by symm; exact huQ t
      have hQh :
          Qh.map (m' ≫ KQ.map (π t)) = Qh.map (u t) :=
        (eI t).injective hderived
      exact (CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj K) (I t)).injective hQh
    have hmv : m' = v := hvuniq _ hm'fac
    calc
      m = eP (Qh.map m') := hmQ.symm
      _ = eP (Qh.map v) := by rw [hmv]

private noncomputable def qObjProductLift
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (f : ∀ t, Q.obj K ⟶ Q.obj (I t)) :
    Q.obj K ⟶ Q.obj P :=
  Classical.choose (ExistsUnique.exists (qObjProduct_existsUnique π hP K f))

private theorem qObjProductLift_fac
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (f : ∀ t, Q.obj K ⟶ Q.obj (I t))
    (t : T) :
    qObjProductLift π hP K f ≫ Q.map (π t) = f t :=
  (Classical.choose_spec (ExistsUnique.exists (qObjProduct_existsUnique π hP K f))) t

private theorem qObjProductLift_uniq
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (f : ∀ t, Q.obj K ⟶ Q.obj (I t))
    (m : Q.obj K ⟶ Q.obj P)
    (hm : ∀ t, m ≫ Q.map (π t) = f t) :
    m = qObjProductLift π hP K f :=
  (qObjProduct_existsUnique π hP K f).unique hm (qObjProductLift_fac π hP K f)

-- Proof sketch: specialize the source-facing product theorem to the canonical product cone
-- `Fan.mk (∏ᶜ I) (Pi.π I)`, build the mapped fan from the private unique-lift API above, and
-- package the result with `preservesLimit_of_preserves_limit_cone`.
/-- The localization functor `DerivedCategory.Q` preserves the product of any family of
K-injective cochain complexes. -/
theorem derivedCategory_Q_preserves_product_of_kInjective
    (I : T → CochainComplex 𝒜 ℤ)
    [HasProduct I]
    [∀ t, (I t).IsKInjective] :
    PreservesLimit (Discrete.functor I) Q := by
  classical
  let π : ∀ t, ∏ᶜ I ⟶ I t := fun t ↦ Pi.π I t
  let hπ : IsLimit (Fan.mk (∏ᶜ I) π) := by
    simpa [π] using productIsProduct I
  let hQ' : IsLimit (Fan.mk (Q.obj (∏ᶜ I)) fun t ↦ Q.map (π t)) := by
    refine mkFanLimit (Fan.mk (Q.obj (∏ᶜ I)) fun t ↦ Q.map (π t)) (fun s ↦ ?_) ?_ ?_
    · let e := Q.objObjPreimageIso s.pt
      exact e.inv ≫ qObjProductLift π hπ (Q.objPreimage s.pt) (fun t ↦ e.hom ≫ s.proj t)
    · intro s t
      let e := Q.objObjPreimageIso s.pt
      simpa [Category.assoc] using
        congrArg (fun k ↦ e.inv ≫ k)
          (qObjProductLift_fac π hπ (Q.objPreimage s.pt) (fun j ↦ e.hom ≫ s.proj j) t)
    · intro s m hm
      let e := Q.objObjPreimageIso s.pt
      have hm' :
          e.hom ≫ m =
            qObjProductLift π hπ (Q.objPreimage s.pt) (fun t ↦ e.hom ≫ s.proj t) :=
        qObjProductLift_uniq π hπ (Q.objPreimage s.pt) (fun t ↦ e.hom ≫ s.proj t) (e.hom ≫ m)
          fun t ↦ by
            simpa [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) (hm t)
      simpa [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) hm'
  let hQ : IsLimit (Q.mapCone (Fan.mk (∏ᶜ I) π)) :=
    (isLimitMapConeFanMkEquiv Q I π).symm hQ'
  exact preservesLimit_of_preserves_limit_cone hπ hQ

/-- Lemma 13.31.5: if the termwise product of a family of K-injective cochain complexes exists,
then the product complex is K-injective, and its image in the derived category represents the
product of the family. -/
theorem product_of_kInjective_isKInjective_and_preserves_limit
    (I : T → CochainComplex 𝒜 ℤ)
    [HasProduct I]
    [∀ t, (I t).IsKInjective] :
    (∏ᶜ I).IsKInjective ∧ PreservesLimit (Discrete.functor I) Q := by
  let π : ∀ t, ∏ᶜ I ⟶ I t := fun t ↦ Pi.π I t
  have hπ : IsLimit (Fan.mk (∏ᶜ I) π) := by
    simpa [π] using productIsProduct I
  constructor
  · exact isKInjective_of_product π hπ
  · exact derivedCategory_Q_preserves_product_of_kInjective I

end

end

end CategoryTheory
