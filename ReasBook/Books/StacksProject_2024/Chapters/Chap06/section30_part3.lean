import Mathlib
import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_6_30_16 (from Chap06) -/
open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits

universe u

section

variable {C : Type u} [Category.{u} C]
variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (BX : Set (Opens X)) (BY : Set (Opens Y))
variable (𝒢 : TopCat.Sheaf C Y) (ℱ : TopCat.Sheaf C X)

private instance basisOpenInclusion_isContinuous (hBX : Opens.IsBasis BX) :
    Functor.IsContinuous (basisOpenInclusion BX)
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X) := by
  letI : (basisOpenInclusion BX).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hBX
  exact
    Functor.IsCoverDense.isContinuous
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X) (basisOpenInclusion BX)
      (Functor.inducedTopology_coverPreserving (basisOpenInclusion BX)
        (Opens.grothendieckTopology X))

-- The ambient inclusion of opens underlying a morphism in a basis-open full subcategory.
private theorem basisOpenHomLE {Z : TopCat.{u}} {B : Set (Opens Z)}
    {U V : BasisOpen B} (i : U ⟶ V) :
    U.obj ≤ V.obj :=
  i.hom.le

/- Domain-style sampling for Lemma 6.30.16:
- primary domain: basis-indexed pushforward morphisms of sheaves, with source-facing section data
  on basis opens of both `X` and `Y`;
- sampled owner declarations:
  `BasisOpen`,
  `basisOpenInclusion`,
  `Functor.sheafPushforwardContinuous`,
  `existsUnique_pushforward_hom_of_basis_restriction`;
- best owner abstraction: the canonical owner of the resulting map is the pushforward morphism
  `𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ`, while the basis-indexed section family is source-facing
  input data and the induced morphism between basis restrictions is derived API;
- primitive data: the section components `app` together with naturality in the source basis open
  and the target basis open;
- derived API: under the basis-restriction equivalences from Lemma `6.30.14`, such a family
  determines a unique morphism `𝒢 ⟶ f_* ℱ`.

Source/core/bridge triage:
- `source-facing`: `BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ`;
- `core/canonical`: `𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ`;
- `bridge/view`: the morphism between the basis restrictions of `𝒢` and `f_* ℱ` obtained from the
  section family via the basis-site equivalence.
-/
/-- A family of section morphisms on basis opens of `Y` and `X` over a continuous map `f`,
compatible with restriction in both variables. -/
structure BasisContinuousMapSectionFamily where
  app (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj) :
    𝒢.presheaf.obj (op V.obj) ⟶ ℱ.presheaf.obj (op U.obj)
  source_naturality {U U' : BasisOpen BX} (i : U' ⟶ U) {V : BasisOpen BY}
      (h : U.obj ≤ (Opens.map f).obj V.obj) :
    app U V h ≫ ℱ.presheaf.map (homOfLE (basisOpenHomLE i)).op =
      app U' V ((basisOpenHomLE i).trans h)
  target_naturality {U : BasisOpen BX} {V V' : BasisOpen BY} (j : V ⟶ V')
      (h : U.obj ≤ (Opens.map f).obj V.obj) :
    𝒢.presheaf.map (homOfLE (basisOpenHomLE j)).op ≫ app U V h =
      app U V'
        (h.trans ((Opens.map f).map (homOfLE (basisOpenHomLE j))).le)

/-- Helper for Lemma 6.30.16: on a basis open `V` of `Y`, the pushforward sheaf evaluates to the
section object of `ℱ` on the preimage open `f⁻¹(V)`. -/
lemma pushforward_obj_on_basis_open (V : BasisOpen BY) :
    ((Sheaf.pushforward C f).obj ℱ).presheaf.obj (op V.obj) =
      ℱ.presheaf.obj (op ((Opens.map f).obj V.obj)) :=
  rfl

/-- Helper for Lemma 6.30.16: for a fixed basis open `V` of `Y`, the maps
`φ.app U V h : 𝒢(V) ⟶ ℱ(U)` over basis neighborhoods `U ⊆ f⁻¹(V)` form a cone on the
structured-arrow diagram computing the right Kan extension over `f⁻¹(V)`. -/
noncomputable def section_family_structured_arrow_cone
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    (V : BasisOpen BY) :
    Cone (StructuredArrow.proj (op ((Opens.map f).obj V.obj)) (basisOpenInclusion BX).op ⋙
      (((basisOpenInclusion BX).sheafPushforwardContinuous C
        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj ℱ).obj) where
  pt := 𝒢.presheaf.obj (op V.obj)
  π :=
    { app := fun g ↦
        φ.app g.right.unop V
          (show g.right.unop.obj ≤ (Opens.map f).obj V.obj from g.hom.unop.le)
      naturality := by
        intro g g' i
        -- The structured-arrow morphism reverses the basis inclusion, exactly matching the
        -- `U`-naturality built into the source family.
        simpa using
          (φ.source_naturality (V := V) i.right.unop
            (show g.right.unop.obj ≤ (Opens.map f).obj V.obj from g.hom.unop.le)).symm }

/-- Helper for Lemma 6.30.16: the universal morphism from `𝒢(V)` into the limit of the basis
neighborhood diagram over `f⁻¹(V)`. This is the categorical replacement for the source proof's
stalkwise construction on a fixed basis open `V`. -/
noncomputable def section_family_limit_lift
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (V : BasisOpen BY) :
    𝒢.presheaf.obj (op V.obj) ⟶
      limit (StructuredArrow.proj (op ((Opens.map f).obj V.obj)) (basisOpenInclusion BX).op ⋙
        (((basisOpenInclusion BX).sheafPushforwardContinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj ℱ).obj) :=
  limit.lift _ (section_family_structured_arrow_cone (f := f) (BX := BX) (BY := BY)
    (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V)

/-- Helper for Lemma 6.30.16: the universal lift to the limit recovers the given basis component
after projecting to any basis neighborhood of `f⁻¹(V)`. -/
lemma section_family_limit_lift_π
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (V : BasisOpen BY)
    (g : StructuredArrow (op ((Opens.map f).obj V.obj)) (basisOpenInclusion BX).op) :
    section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
        limit.π _ g =
      φ.app g.right.unop V
        (show g.right.unop.obj ≤ (Opens.map f).obj V.obj from g.hom.unop.le) := by
  -- Evaluate the limit lift on the cone leg indexed by `g`.
  simpa [section_family_limit_lift, section_family_structured_arrow_cone] using
    limit.lift_π
      (section_family_structured_arrow_cone (f := f) (BX := BX) (BY := BY)
        (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V)
      g

/-- Helper for Lemma 6.30.16: the universal limit lift specializes to the original prescribed
map when one evaluates at the structured-arrow object corresponding to a basis inclusion
`U ⊆ f⁻¹(V)`. -/
lemma section_family_limit_lift_π_basis
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj) :
    section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
        limit.π _ (StructuredArrow.mk (homOfLE h).op) =
      φ.app U V h := by
  -- The structured-arrow object `StructuredArrow.mk (homOfLE h).op` is exactly the basis
  -- neighborhood `U ⊆ f⁻¹(V)`.
  simpa using
    section_family_limit_lift_π (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V
      (StructuredArrow.mk (homOfLE h).op)

/-- Helper for Lemma 6.30.16: the comparison unit from a sheaf on `X` to the extension of its
basis restriction, followed by the canonical limit identification, restricts on a basis inclusion
`U ⊆ W` to the usual restriction map `ℱ(W) ⟶ ℱ(U)`. -/
lemma basis_restriction_unit_app_comp_π
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (W : Opens X) (U : BasisOpen BX) (h : U.obj ≤ W) :
    (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ).hom.app
        (op W) ≫
        ((basisOpenInclusion BX).op.ranObjObjIsoLimit
            ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)
            (op W)).hom ≫
        limit.π
          (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
            (((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)
          (StructuredArrow.mk (homOfLE h).op) =
      ℱ.presheaf.map (homOfLE h).op := by
  -- Rewrite the sheaf-side unit into the raw right Kan extension unit.
  rw [Functor.sheafAdjunctionCocontinuous_unit_app_hom]
  have hπ :=
    Functor.ranObjObjIsoLimit_hom_π (L := (basisOpenInclusion BX).op)
      (F := (((basisOpenInclusion BX).sheafPushforwardContinuous C
        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj ℱ).obj)
      (X := op W) (f := StructuredArrow.mk (homOfLE h).op)
  have hrewrite₁ :
      (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op W) ≫
          ((basisOpenInclusion BX).op.ranObjObjIsoLimit
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)
              (op W)).hom ≫
          limit.π
            (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
              (((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)
            (StructuredArrow.mk (homOfLE h).op)
        = (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op W) ≫
            ((basisOpenInclusion BX).op.ran.obj
                ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)).map
              (homOfLE h).op ≫
            (((basisOpenInclusion BX).op.ranCounit.app
                ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)).app
              (op U)) := by
    simpa [Category.assoc] using congrArg
      (fun k => (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op W) ≫ k) hπ
  have hnat :=
    NatTrans.naturality (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj)
      (homOfLE h).op
  have hrewrite₂ :
      (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op W) ≫
          ((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
            (homOfLE h).op ≫
          (((basisOpenInclusion BX).op.ranCounit.app
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).app
            (op U)) =
        (ℱ.presheaf.map (homOfLE h).op ≫
            (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op U.obj)) ≫
          (((basisOpenInclusion BX).op.ranCounit.app
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).app
            (op U)) := by
    have h₂raw := congrArg
      (fun k => k ≫
        (((basisOpenInclusion BX).op.ranCounit.app
          ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                  (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
              ℱ).obj)).app (op U))) hnat.symm
    simpa [Functor.sheafPushforwardContinuous, Category.assoc] using h₂raw
  refine hrewrite₁.trans ?_
  refine hrewrite₂.trans ?_
  -- The remaining composite is the triangle identity for the right Kan extension adjunction.
  rw [Category.assoc]
  simpa using congrArg
    (fun k => ℱ.presheaf.map (homOfLE h).op ≫ k)
    (Functor.ranCounit_app_app_ranAdjunction_unit_app_app
      (L := (basisOpenInclusion BX).op) (H := C) ℱ.obj (op U))

/-- Helper for Lemma 6.30.16: restriction to the basis `BX` is an equivalence on `C`-valued
sheaves once `BX` is a basis and the needed right Kan extension limits exist. -/
private noncomputable instance basisOpenRestriction_isEquivalence
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C] :
    Functor.IsEquivalence
      ((basisOpenInclusion BX).sheafPushforwardContinuous C
        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)) := by
  letI : (basisOpenInclusion BX).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hBX
  let G := (basisOpenInclusion BX).sheafPushforwardContinuous C
    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)
  simpa using inferInstanceAs (G.IsEquivalence)

/-- Helper for Lemma 6.30.16: the basis-restriction unit formula may be read against any
structured-arrow object over `W`, not only the canonical one built from an explicit inclusion. -/
lemma basis_restriction_unit_app_comp_π_structured_arrow
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (W : Opens X)
    (g : StructuredArrow (op W) (basisOpenInclusion BX).op) :
    (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ).hom.app
        (op W) ≫
        ((basisOpenInclusion BX).op.ranObjObjIsoLimit
            ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)
            (op W)).hom ≫
        limit.π
          (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
            (((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)
          g =
      ℱ.presheaf.map g.hom := by
  -- Every structured-arrow object is the canonical basis inclusion carried by its arrow.
  have hg : g = StructuredArrow.mk g.hom :=
    StructuredArrow.eq_mk g
  have hh : (homOfLE g.hom.unop.le).op = g.hom :=
    Subsingleton.elim _ _
  simpa [hg, hh] using
    basis_restriction_unit_app_comp_π (C := C) (X := X) (BX := BX) (ℱ := ℱ)
      hBX W g.right.unop g.hom.unop.le

/-- Helper for Lemma 6.30.16: on a basis open `U`, the forward unit component followed by the
right Kan extension counit is the identity. -/
lemma basis_restriction_unit_component_hom_inv_id
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (U : BasisOpen BX) :
    (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ).hom.app
        (op U.obj) ≫
      (((basisOpenInclusion BX).op.ranCounit.app
            ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)).app
          (op U)) =
        𝟙 _ := by
  let η :=
    ((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ
  let ρ :=
    (basisOpenInclusion BX).op.ranObjObjIsoLimit
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj)
      (op U.obj)
  let κ :=
    ((basisOpenInclusion BX).op.ranCounit.app
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj))
  have hπ :
      ρ.hom ≫
          limit.π
            (StructuredArrow.proj (op U.obj) (basisOpenInclusion BX).op ⋙
              (((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)
            (StructuredArrow.mk (homOfLE (show U.obj ≤ U.obj from le_rfl)).op) =
        κ.app (op U) := by
    -- The identity basis inclusion projects from the limit to the counit component at `U`.
    simpa [ρ, κ] using
      (Functor.ranObjObjIsoLimit_hom_π (L := (basisOpenInclusion BX).op)
        (F := ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj))
        (X := op U.obj)
        (f := StructuredArrow.mk (homOfLE (show U.obj ≤ U.obj from le_rfl)).op))
  have hunit :
      η.hom.app (op U.obj) ≫ ρ.hom ≫
          limit.π
            (StructuredArrow.proj (op U.obj) (basisOpenInclusion BX).op ⋙
              (((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)
            (StructuredArrow.mk (homOfLE (show U.obj ≤ U.obj from le_rfl)).op) =
        ℱ.presheaf.map (homOfLE (show U.obj ≤ U.obj from le_rfl)).op := by
    -- This is the basis-restriction unit formula at the identity inclusion `U ⊆ U`.
    simpa [η, ρ] using
      basis_restriction_unit_app_comp_π (C := C) (X := X) (BX := BX) (ℱ := ℱ)
        hBX U.obj U (show U.obj ≤ U.obj from le_rfl)
  -- Specialize the basis-restriction unit formula to the identity inclusion `U ⊆ U`.
  rw [← hπ]
  exact hunit.trans (by simp)

/-- Helper for Lemma 6.30.16: on a basis open `U`, the inverse of the sheaf-side comparison unit
is the corresponding right Kan extension counit component. -/
lemma basis_restriction_unit_component_inv
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (U : BasisOpen BX) :
    ((asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
            (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app
          ℱ)).inv).hom.app (op U.obj) =
      (((basisOpenInclusion BX).op.ranCounit.app
            ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)).app
          (op U)) := by
  let η :=
    asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ)
  let κ :=
    ((basisOpenInclusion BX).op.ranCounit.app
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj))
  let ηp : ℱ.presheaf ≅
      (((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X) ⋙
            (basisOpenInclusion BX).sheafPushforwardCocontinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj :=
    ⟨η.hom.hom, η.inv.hom,
      congrArg (fun ψ ↦ ψ.hom) η.hom_inv_id,
      congrArg (fun ψ ↦ ψ.hom) η.inv_hom_id⟩
  -- The basis-open triangle identity identifies the counit as the inverse component.
  have htri :
      η.hom.hom.app (op U.obj) ≫ κ.app (op U) = 𝟙 _ := by
    simpa [η, κ] using
      basis_restriction_unit_component_hom_inv_id
        (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX U
  have hinv :
      η.inv.hom.app (op U.obj) ≫ η.hom.hom.app (op U.obj) = 𝟙 _ := by
    simpa [η, ηp] using ηp.inv_hom_id_app (op U.obj)
  have hcomp :
      η.inv.hom.app (op U.obj) =
        η.inv.hom.app (op U.obj) ≫ (η.hom.hom.app (op U.obj) ≫ κ.app (op U)) := by
    rw [htri]
    simp
  have hassoc :
      η.inv.hom.app (op U.obj) ≫ (η.hom.hom.app (op U.obj) ≫ κ.app (op U)) =
        (η.inv.hom.app (op U.obj) ≫ η.hom.hom.app (op U.obj)) ≫ κ.app (op U) := by
    rw [Category.assoc]
  have hcancel :
      (η.inv.hom.app (op U.obj) ≫ η.hom.hom.app (op U.obj)) ≫ κ.app (op U) =
        κ.app (op U) := by
    rw [hinv, Category.id_comp]
  exact hcomp.trans (hassoc.trans hcancel)

/-- Helper for Lemma 6.30.16: a morphism into `ℱ(W)` is determined by all of its basis
restrictions to basis opens `U ⊆ W`. -/
lemma basis_restriction_hom_ext
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    {A : C} {W : Opens X}
    {α β : A ⟶ ℱ.presheaf.obj (op W)}
    (hαβ : ∀ (U : BasisOpen BX) (h : U.obj ≤ W),
      α ≫ ℱ.presheaf.map (homOfLE h).op =
        β ≫ ℱ.presheaf.map (homOfLE h).op) :
    α = β := by
  let η :=
    asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ)
  let ρ :=
    (basisOpenInclusion BX).op.ranObjObjIsoLimit
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj)
      (op W)
  let μ :
      ℱ.presheaf.obj (op W) ⟶
        ((basisOpenInclusion BX).op.ran.obj
          ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                  (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
              ℱ).obj)).obj
          (op W) :=
    (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app
      ℱ).hom.app (op W)
  let ηp : ℱ.presheaf ≅
      (((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X) ⋙
            (basisOpenInclusion BX).sheafPushforwardCocontinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj :=
    ⟨η.hom.hom, η.inv.hom,
      congrArg (fun ψ ↦ ψ.hom) η.hom_inv_id,
      congrArg (fun ψ ↦ ψ.hom) η.inv_hom_id⟩
  -- Route correction: transport both maps forward into the basis-neighborhood limit and prove
  -- equality there, so no transport-back helper is needed.
  have hforward :
      α ≫ μ ≫ ρ.hom =
        β ≫ μ ≫ ρ.hom := by
    apply limit.hom_ext
    intro g
    -- Each structured-arrow object records a basis inclusion `g.right.unop ⊆ W`, so the
    -- projected forward transport is exactly that basis restriction.
    have hαg :
        (α ≫ μ ≫ ρ.hom) ≫
            limit.π
              (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
                (((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)
              g =
          α ≫ ℱ.presheaf.map g.hom := by
      simpa [μ, ρ, Category.assoc] using congrArg
        (fun k ↦ α ≫ k)
        (basis_restriction_unit_app_comp_π_structured_arrow
          (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX W g)
    have hβg :
        (β ≫ μ ≫ ρ.hom) ≫
            limit.π
              (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
                (((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)
              g =
          β ≫ ℱ.presheaf.map g.hom := by
      simpa [μ, ρ, Category.assoc] using congrArg
        (fun k ↦ β ≫ k)
        (basis_restriction_unit_app_comp_π_structured_arrow
          (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX W g)
    exact hαg.trans ((hαβ g.right.unop g.hom.unop.le).trans hβg.symm)
  -- Postcompose with the inverse comparison maps to return from the limit object to `ℱ(W)`.
  have hback :
      α ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) =
        β ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ ρ.inv ≫ η.inv.hom.app (op W)) hforward
  have hρ : ρ.hom ≫ ρ.inv = 𝟙 _ := by
    simp [ρ]
  have hη :
      μ ≫ η.inv.hom.app (op W) = 𝟙 _ := by
    simpa [η, ηp, μ] using ηp.hom_inv_id_app (op W)
  have hαρ :
      α ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) =
        α ≫ μ ≫ η.inv.hom.app (op W) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ α ≫ k ≫ η.inv.hom.app (op W)) hρ
  have hαη :
      α ≫ μ ≫ η.inv.hom.app (op W) = α := by
    simpa [Category.assoc] using congrArg (fun k ↦ α ≫ k) hη
  have hα :
      α = α ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) := by
    exact (hαρ.trans hαη).symm
  have hβρ :
      β ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) =
        β ≫ μ ≫ η.inv.hom.app (op W) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ β ≫ k ≫ η.inv.hom.app (op W)) hρ
  have hβη :
      β ≫ μ ≫ η.inv.hom.app (op W) = β := by
    simpa [Category.assoc] using congrArg (fun k ↦ β ≫ k) hη
  have hβ :
      β ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) = β := by
    exact hβρ.trans hβη
  exact hα.trans (hback.trans hβ)

/-- Helper for Lemma 6.30.16: for a fixed basis open `V` of `Y`, transport the compatible family
`φ.app _ V _` back from the basis-neighborhood limit to a section over `f⁻¹(V)`. -/
noncomputable def basis_section_map_of_family
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (V : BasisOpen BY) :
    𝒢.presheaf.obj (op V.obj) ⟶
      ℱ.presheaf.obj (op ((Opens.map f).obj V.obj)) :=
  section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
    ((basisOpenInclusion BX).op.ranObjObjIsoLimit
        ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
            ℱ).obj)
        (op ((Opens.map f).obj V.obj))).inv ≫
    ((asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
            (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app
          ℱ)).inv).hom.app (op ((Opens.map f).obj V.obj))

/-- Helper for Lemma 6.30.16: the fixed-`V` section map recovers the prescribed basis-pair map
after restricting from `f⁻¹(V)` to a basis open `U ⊆ f⁻¹(V)`. -/
lemma basis_section_map_of_family_restrict
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj) :
    basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
        ℱ.presheaf.map (homOfLE h).op =
      φ.app U V h := by
  let η :=
    asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ)
  let ρ :=
    (basisOpenInclusion BX).op.ranObjObjIsoLimit
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj)
      (op ((Opens.map f).obj V.obj))
  let κ :=
    ((basisOpenInclusion BX).op.ranCounit.app
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj))
  have hη :
      ρ.inv ≫ η.inv.hom.app (op ((Opens.map f).obj V.obj)) ≫ ℱ.presheaf.map (homOfLE h).op =
        ρ.inv ≫
          (((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
              (homOfLE h).op) ≫
          η.inv.hom.app (op U.obj) := by
    -- Move the restriction past the inverse unit while keeping the preceding `ρ.inv` fixed.
    simpa [η, Category.assoc] using
      congrArg (fun k ↦ ρ.inv ≫ k) ((η.inv.hom.naturality (homOfLE h).op).symm)
  have hκ :
      ρ.inv ≫
          (((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
              (homOfLE h).op) ≫
          η.inv.hom.app (op U.obj) =
        ρ.inv ≫
          (((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
              (homOfLE h).op) ≫
          κ.app (op U) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          ρ.inv ≫
            (((basisOpenInclusion BX).op.ran.obj
                ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)).map
                (homOfLE h).op) ≫
            k)
        (basis_restriction_unit_component_inv (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX U)
  have hρ :
      ρ.inv ≫
          (((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
              (homOfLE h).op) ≫
          κ.app (op U) =
        limit.π _ (StructuredArrow.mk (homOfLE h).op) := by
    -- The inverse right-Kan comparison sends the relevant restriction map to the matching limit
    -- projection.
    simpa [ρ, κ] using
      (Functor.ranObjObjIsoLimit_inv_π (L := (basisOpenInclusion BX).op)
        (F := ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj))
        (X := op ((Opens.map f).obj V.obj))
        (f := StructuredArrow.mk (homOfLE h).op))
  -- Rewrite the transported restriction map until only the canonical limit projection remains.
  have htransport :
      basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
          ℱ.presheaf.map (homOfLE h).op =
        section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
          ρ.inv ≫
            (((basisOpenInclusion BX).op.ran.obj
                ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)).map
                (homOfLE h).op) ≫
            κ.app (op U) := by
    simpa [basis_section_map_of_family, Category.assoc] using
      congrArg
        (fun k ↦
          section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
            k)
        (hη.trans hκ)
  have hπ :
    basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
          ℱ.presheaf.map (homOfLE h).op =
        section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
          limit.π _ (StructuredArrow.mk (homOfLE h).op) := by
      rw [htransport]
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
              k) hρ
  exact hπ.trans <| by
    simpa using
      section_family_limit_lift_π_basis (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
        hBX φ U V h

/-- Helper for Lemma 6.30.16: the fixed-`V` section maps are natural in the basis open `V` of
`Y`, so they assemble into the basis-restriction morphism required for Lemma `6.30.14`. -/
lemma basis_section_map_of_family_natural
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    {V V' : BasisOpen BY} (j : V ⟶ V') :
    𝒢.presheaf.map (homOfLE (basisOpenHomLE j)).op ≫
        basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
          hBX φ V =
      basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
          hBX φ V' ≫
        ℱ.presheaf.map ((Opens.map f).map (homOfLE (basisOpenHomLE j))).op := by
  -- Compare the two maps after restricting to every basis open inside `f⁻¹(V)`.
  apply basis_restriction_hom_ext (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX
  intro U hU
  let hU' : U.obj ≤ (Opens.map f).obj V'.obj :=
    hU.trans ((Opens.map f).map (homOfLE (basisOpenHomLE j))).le
  have hcomp :
      ((Opens.map f).map (homOfLE (basisOpenHomLE j))).op ≫ (homOfLE hU).op =
        (homOfLE hU').op :=
    Subsingleton.elim _ _
  have hmap :
      ℱ.presheaf.map ((Opens.map f).map (homOfLE (basisOpenHomLE j))).op ≫
          ℱ.presheaf.map (homOfLE hU).op =
        ℱ.presheaf.map (homOfLE hU').op := by
    -- The preimage restriction followed by the basis restriction is the single composite
    -- restriction to `U ⊆ f⁻¹(V')`.
    simpa [Functor.map_comp] using congrArg ℱ.presheaf.map hcomp
  -- Both sides reduce to the prescribed target-naturality square for `φ`.
  calc
    (𝒢.presheaf.map (homOfLE (basisOpenHomLE j)).op ≫
          basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
            hBX φ V) ≫
          ℱ.presheaf.map (homOfLE hU).op =
        𝒢.presheaf.map (homOfLE (basisOpenHomLE j)).op ≫ φ.app U V hU := by
      rw [Category.assoc, basis_section_map_of_family_restrict
        (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ U V hU]
    _ = φ.app U V' hU' := by
      simpa [hU'] using φ.target_naturality (U := U) (j := j) (h := hU)
    _ = basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
          hBX φ V' ≫
        ℱ.presheaf.map (homOfLE hU').op := by
      symm
      exact basis_section_map_of_family_restrict
        (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ U V' hU'
    _ = (basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
          hBX φ V' ≫
        ℱ.presheaf.map ((Opens.map f).map (homOfLE (basisOpenHomLE j))).op) ≫
          ℱ.presheaf.map (homOfLE hU).op := by
      rw [Category.assoc, hmap]

-- Proof sketch: for each basis open `V` of `Y`, the `U`-naturality makes the family
-- `φ.app _ V _` into a compatible basis restriction datum on the open `f⁻¹(V)` of `X`, so the
-- basis-site equivalence on `X` yields a unique section map `𝒢(V) ⟶ ℱ(f⁻¹(V))` in `C`. The
-- `V`-naturality then assembles these maps into a morphism between the basis restrictions of `𝒢`
-- and `f_* ℱ` on `BY`, and Lemma `6.30.14` upgrades that canonical basis-restriction morphism to
-- a unique global morphism `𝒢 ⟶ f_* ℱ`.
/-- Lemma 6.30.16: a family of morphisms `𝒢(V) ⟶ ℱ(U)` given for basis opens `V` of `Y` and `U`
of `X` with `U ⊆ f⁻¹(V)` (equivalently `f(U) ⊆ V`), and compatible with restriction in both
variables, comes from a unique morphism `𝒢 ⟶ f_* ℱ` recovering the given maps after restricting
from `f⁻¹(V)` to `U`. -/
theorem existsUnique_pushforward_hom_of_basis_section_family
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    [∀ V : (Opens Y)ᵒᵖ, HasLimitsOfShape (StructuredArrow V (basisOpenInclusion BY).op) C]
    (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ) :
    ∃! Φ : 𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ,
      ∀ (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.presheaf.map (homOfLE h).op = φ.app U V h := by
  let φB :
      ((basisOpenInclusion BY).sheafPushforwardContinuous C
          (basisGrothendieckTopology BY hBY) (Opens.grothendieckTopology Y)).obj 𝒢 ⟶
        ((basisOpenInclusion BY).sheafPushforwardContinuous C
          (basisGrothendieckTopology BY hBY) (Opens.grothendieckTopology Y)).obj
          ((Sheaf.pushforward C f).obj ℱ) :=
    CategoryTheory.ObjectProperty.homMk
      { app := fun V ↦
          basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
            hBX φ V.unop
        naturality := by
          intro V V' i
          -- The fixed-`V` construction is natural in the `Y`-basis variable.
          simpa using
            basis_section_map_of_family_natural (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢)
              (ℱ := ℱ) hBX φ i.unop }
  rcases existsUnique_pushforward_hom_of_basis_restriction
      (C := C) (f := f) (ℱ := ℱ) (𝒢 := 𝒢) (B := BY) hBY φB with
    ⟨Φ, hΦ, hΦ_unique⟩
  refine ⟨Φ, ?_, ?_⟩
  · intro U V h
    have hΦV :
        Φ.hom.app (op V.obj) =
          basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
            hBX φ V := by
      -- The global extension agrees with the basis-restriction morphism on each basis open.
      simpa [φB] using congrArg (fun ψ ↦ ψ.hom.app (op V)) hΦ
    -- The component formula is exactly the fixed-`V` restriction lemma after identifying
    -- `Φ` with the basis extension on `V`.
    simpa [hΦV] using
      basis_section_map_of_family_restrict
        (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ U V h
  · intro Ψ hΨ
    apply hΦ_unique
    apply CategoryTheory.Sheaf.hom_ext
    ext V
    change Ψ.hom.app (op V.unop.obj) =
      basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
        hBX φ V.unop
    -- Route correction: uniqueness is proved by fixed-open basis extensionality on `X`, not by
    -- a second dense-subsite transport argument on `Y`.
    apply basis_restriction_hom_ext (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX
    intro U hU
    calc
      Ψ.hom.app (op V.unop.obj) ≫ ℱ.presheaf.map (homOfLE hU).op = φ.app U V.unop hU := by
        exact hΨ U V.unop hU
      _ = basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
            hBX φ V.unop ≫
          ℱ.presheaf.map (homOfLE hU).op := by
        symm
        exact basis_section_map_of_family_restrict
          (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ U V.unop hU

end

/-! ### Lemma_6_30_17 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable {BX : Set (Opens X)} {BY : Set (Opens Y)}
variable (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
variable (𝒢 : SheafOfModules ((RingedSpace.ringCatSheaf Y)))

local notation "BasisOpenX" => ObjectProperty.FullSubcategory fun U : Opens X ↦ U ∈ BX
local notation "BasisOpenY" => ObjectProperty.FullSubcategory fun V : Opens Y ↦ V ∈ BY

/-
Domain-style sampling for Lemma 6.30.17:
- primary domain: pushforward of sheaves of modules on a morphism of ringed spaces, expressed via
  basis-indexed section families on the underlying sheaves of abelian groups;
- sampled owner declarations:
  `RingedSpace.Hom.pushforward`,
  `RingedSpace.Hom.toRingCatSheafHom`,
  `BasisContinuousMapSectionFamily`,
  `existsUnique_pushforward_hom_of_basis_section_family`,
  `SheafOfModules.toSheaf`;
- owner abstraction: the canonical target owner is `(f _*).obj ℱ`,
  while the source-facing basis data are already owned by
  `BasisContinuousMapSectionFamily f.hom.base BX BY`;
- primitive data: the only extra primitive input beyond the basis family is the
  `\mathcal O_Y(V)`-linearity condition on sections;
- derived API: the unique module morphism whose underlying sheaf morphism recovers the given basis
  family on basis opens.

Source/core/bridge triage:
- `source-facing`: the basis-pair family `η` and its linearity condition;
- `core/canonical`: the module pushforward owner `(f _*).obj ℱ`;
- `bridge/view`: `SheafOfModules.toSheaf`, used only to compare the source family with the
  underlying sheaf morphism of the resulting module map.
-/

-- Proof sketch: forget the module structure to obtain a compatible basis-indexed family of maps
-- of sheaves of abelian groups, apply Lemma `6.30.16` to extend it uniquely to the underlying
-- pushforward morphism, and then use the pointwise linearity hypothesis to view the resulting
-- morphism as a morphism of sheaves of modules.
/-- Helper for Lemma 6.30.17: once the additive sheaf lift is known, its section map on a basis
open `V` of `Y` is `\mathcal O_Y(V)`-linear because its restrictions to all basis opens of
`f^{-1}(V)` agree with the given linear basis-pair maps. -/
theorem underlying_basis_pair_lift_is_linear
    (hBX : Opens.IsBasis BX) (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    {Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ))}
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    ∀ (V : BasisOpenY)
      (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj))
      (s : 𝒢.val.obj (op V.obj)),
      (show ((f _*).obj ℱ).val.obj (op V.obj) from
          Φ.hom.app (op V.obj) (r • s)) =
        r • (show ((f _*).obj ℱ).val.obj (op V.obj) from Φ.hom.app (op V.obj) s) := by
  intro V r s
  change (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from
      Φ.hom.app (op V.obj) (r • s)) =
    (show ((RingedSpace.ringCatSheaf X)).obj.obj
        (op ((Opens.map f.hom.base).obj V.obj)) from
      (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) r) •
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s)
  -- Compare the two sections after restricting to basis neighborhoods of each point of `f⁻¹(V)`.
  apply TopCat.Presheaf.IsSheaf.section_ext ℱ.isSheaf
  intro x hx
  obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, hWV⟩ :=
    hBX.exists_subset_of_mem_open hx ((Opens.map f.hom.base).obj V.obj).2
  let U : BasisOpenX := ⟨W, hWB⟩
  refine ⟨W, hWV, hxW, ?_⟩
  have hleft : ℱ.val.presheaf.map (homOfLE hWV).op
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) (r • s)) =
        (show ℱ.val.obj (op U.obj) from η.app U V hWV (r • s)) := by
    simpa using ConcreteCategory.congr_hom (hΦ U V hWV) (r • s)
  have hright : ℱ.val.presheaf.map (homOfLE hWV).op
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s) =
        (show ℱ.val.obj (op U.obj) from η.app U V hWV s) := by
    simpa using ConcreteCategory.congr_hom (hΦ U V hWV) s
  have hmiddle :
      (show ℱ.val.obj (op U.obj) from η.app U V hWV (r • s)) =
        (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
            (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) •
          (show ℱ.val.obj (op U.obj) from η.app U V hWV s) := by
    simpa using hη U V hWV r s
  have hrewrite :
      (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) •
        (show ℱ.val.obj (op U.obj) from η.app U V hWV s) =
          (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
            (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) •
            ℱ.val.presheaf.map (homOfLE hWV).op
              (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s) := by
    exact congrArg
      (fun t ↦
        (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
            (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) • t)
      hright.symm
  have hsmul :
      (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hWV).op
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)) •
        ℱ.val.presheaf.map (homOfLE hWV).op
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s) =
          ℱ.val.presheaf.map (homOfLE hWV).op
            ((show ((RingedSpace.ringCatSheaf X)).obj.obj
                (op ((Opens.map f.hom.base).obj V.obj)) from
              (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) r) •
              (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s)) := by
    symm
    simpa using
      (ℱ.val.map_smul (homOfLE hWV).op
        (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj)) r)
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj V.obj)) from Φ.hom.app (op V.obj) s))
  exact hleft.trans (hmiddle.trans (hrewrite.trans hsmul))

/-- Helper for Lemma 6.30.17: the additive lift is linear on arbitrary opens of `Y` once one
refines both the source open and its preimage by basis neighborhoods and then applies the
basis-local linearity statement. -/
theorem basis_pair_lift_is_linear_on_opens
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    {Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ))}
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    ∀ (W : Opens Y)
      (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op W))
      (s : 𝒢.val.obj (op W)),
      (show ((f _*).obj ℱ).val.obj (op W) from Φ.hom.app (op W) (r • s)) =
        r • (show ((f _*).obj ℱ).val.obj (op W) from Φ.hom.app (op W) s) := by
  intro W r s
  change (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) (r • s)) =
    (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
      (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r) •
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s)
  -- Route correction: localize from `W` to a basis open `V ⊆ W` in `Y`; after transport to
  -- `f⁻¹(V)`, the existing basis-open linearity theorem closes the argument directly.
  apply TopCat.Presheaf.IsSheaf.section_ext ℱ.isSheaf
  intro x hx
  have hyW : f.hom.base x ∈ W := hx
  obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVW⟩ :=
    hBY.exists_subset_of_mem_open (a := f.hom.base x) hyW W.2
  let Vb : BasisOpenY := ⟨V, hVB⟩
  have hpre : (Opens.map f.hom.base).obj Vb.obj ≤ (Opens.map f.hom.base).obj W := by
    intro y hy
    exact hVW hy
  refine ⟨(Opens.map f.hom.base).obj Vb.obj, hpre, hxV, ?_⟩
  -- Transport the left-hand side from `W` down to the basis open `V`.
  have hleft_nat :
      ℱ.val.presheaf.map (homOfLE hpre).op
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) (r • s)) =
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op (r • s))) := by
    simpa [Vb] using
      (NatTrans.naturality_apply Φ.hom (homOfLE hVW).op (r • s)).symm
  have hleft_smul :
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op (r • s))) =
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj)
            ((((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r) •
              (𝒢.val.map (homOfLE hVW).op s))) := by
    exact congrArg
      (fun t ↦
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj) t))
      (𝒢.val.map_smul (homOfLE hVW).op r s)
  have hleft :
      ℱ.val.presheaf.map (homOfLE hpre).op
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) (r • s)) =
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj)
            ((((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r) •
              (𝒢.val.map (homOfLE hVW).op s))) := by
    exact hleft_nat.trans hleft_smul
  -- Transport the scalar and the section on the right-hand side to `f⁻¹(V)`.
  have hring :
      ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hpre).op
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r) =
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) := by
    simpa [Vb] using
      (NatTrans.naturality_apply ((RingedSpace.Hom.toRingCatSheafHom f).hom)
        (homOfLE hVW).op r).symm
  have hsection :
      ℱ.val.presheaf.map (homOfLE hpre).op
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) =
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op s)) := by
    simpa [Vb] using
      (NatTrans.naturality_apply Φ.hom (homOfLE hVW).op s).symm
  have hright_smul :
      ℱ.val.presheaf.map (homOfLE hpre).op
        ((show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
            (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s)) =
        (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hpre).op
            (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
              (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r)) •
          ℱ.val.presheaf.map (homOfLE hpre).op
            (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) := by
    simpa using
      (ℱ.val.map_smul (homOfLE hpre).op
        ((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r)
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s))
  have hright :
      ℱ.val.presheaf.map (homOfLE hpre).op
        ((show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
            (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s)) =
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op s)) := by
    have hright_scalar :
        (((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hpre).op
            (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj W)) from
              (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op W) r)) •
          ℱ.val.presheaf.map (homOfLE hpre).op
            (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) =
          (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
              (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
            ℱ.val.presheaf.map (homOfLE hpre).op
              (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) := by
      exact congrArg (fun t ↦ t • ℱ.val.presheaf.map (homOfLE hpre).op
        (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s)) hring
    have hright_section :
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
          ℱ.val.presheaf.map (homOfLE hpre).op
            (show ℱ.val.obj (op ((Opens.map f.hom.base).obj W)) from Φ.hom.app (op W) s) =
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op s)) := by
      exact congrArg
        (fun t ↦
          (show ((RingedSpace.ringCatSheaf X)).obj.obj
              (op ((Opens.map f.hom.base).obj Vb.obj)) from
            (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
              (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) • t)
        hsection
    exact hright_smul.trans (hright_scalar.trans hright_section)
  -- The localized equality is exactly the basis-open linearity statement already proved.
  have hlinear :
      (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          Φ.hom.app (op Vb.obj)
            ((((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r) •
              (𝒢.val.map (homOfLE hVW).op s))) =
        (show ((RingedSpace.ringCatSheaf X)).obj.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
          (RingedSpace.Hom.toRingCatSheafHom f).hom.app (op Vb.obj)
            (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)) •
          (show ℱ.val.obj (op ((Opens.map f.hom.base).obj Vb.obj)) from
            Φ.hom.app (op Vb.obj) (𝒢.val.map (homOfLE hVW).op s)) := by
    simpa [Vb] using
      underlying_basis_pair_lift_is_linear (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
        hBX η hη hΦ Vb
        (((RingedSpace.ringCatSheaf Y)).obj.map (homOfLE hVW).op r)
        (𝒢.val.map (homOfLE hVW).op s)
  exact hleft.trans (hlinear.trans hright.symm)

/-- Helper for Lemma 6.30.17: once the additive lift is linear on every open of `Y`, it upgrades
to a morphism of presheaves of modules. -/
noncomputable def basis_pair_lift_to_presheaf_module_hom
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    (Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)))
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    𝒢.val ⟶ ((f _*).obj ℱ).val :=
  PresheafOfModules.homMk Φ.hom
    (fun W r s ↦ basis_pair_lift_is_linear_on_opens (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη hΦ W.unop r s)

/-- Helper for Lemma 6.30.17: packaging the presheaf-level module morphism as a morphism of sheaves
of modules introduces no extra data. -/
noncomputable def basis_pair_lift_to_module_hom
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    (Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)))
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    𝒢 ⟶ (f _*).obj ℱ :=
  ⟨basis_pair_lift_to_presheaf_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
    hBX hBY η hη Φ hΦ⟩

/-- Helper for Lemma 6.30.17: the packaged module morphism still recovers the original basis-pair
family after restricting from `f^{-1}(V)` to `U`. -/
theorem basis_pair_lift_restrict_eq_eta
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    (Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)))
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    ∀ (U : BasisOpenX) (V : BasisOpenY)
      (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
      (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map
          (basis_pair_lift_to_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
            hBX hBY η hη Φ hΦ)).hom.app (op V.obj)) ≫
          ℱ.val.presheaf.map (homOfLE hUV).op =
        η.app U V hUV := by
  intro U V hUV
  -- The module lift was built from the additive lift `Φ`, so the recovery equation is unchanged.
  simpa [basis_pair_lift_to_module_hom, basis_pair_lift_to_presheaf_module_hom] using hΦ U V hUV

/-- Helper for Lemma 6.30.17: uniqueness of the module lift follows by forgetting to sheaves of
abelian groups and reusing the uniqueness from Lemma `6.30.16`. -/
theorem basis_pair_lift_unique
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s))
    (Φ :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)))
    (hΦ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV)
    (hΦ_unique :
      ∀ Ψ :
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢) ⟶
          ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj ((f _*).obj ℱ)),
        (∀ (U : BasisOpenX) (V : BasisOpenY)
          (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
          Ψ.hom.app (op V.obj) ≫ ℱ.val.presheaf.map (homOfLE hUV).op =
            η.app U V hUV) →
          Ψ = Φ)
    (ψ : 𝒢 ⟶ (f _*).obj ℱ)
    (hψ :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map ψ).hom.app (op V.obj)) ≫
            ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV) :
    ψ = basis_pair_lift_to_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη Φ hΦ := by
  have hψ_underlying :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map ψ) = Φ := by
    apply hΦ_unique
    intro U V hUV
    simpa using hψ U V hUV
  have hconstructed_underlying :
      ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map
          (basis_pair_lift_to_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
            hBX hBY η hη Φ hΦ)) = Φ := by
    apply hΦ_unique
    intro U V hUV
    simpa using
      basis_pair_lift_restrict_eq_eta (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
        hBX hBY η hη Φ hΦ U V hUV
  exact Functor.Faithful.map_injective
    (F := SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y)))
    (hψ_underlying.trans hconstructed_underlying.symm)

/-- Lemma 6.30.17: a compatible family of `\mathcal O_Y(V)`-linear maps
`\mathcal G(V) → \mathcal F(U)` for basis opens `V ∈ BY`, `U ∈ BX`, and `U ⊆ f⁻¹(V)` comes from
exactly one morphism of sheaves of `\mathcal O_Y`-modules `𝒢 ⟶ f_* ℱ`, and on basis opens it
recovers the given maps after restricting from `f⁻¹(V)` to `U`. -/
theorem existsUnique_module_pushforward_hom_of_basis_pair_sections
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s)) :
    ∃! φ : 𝒢 ⟶ (f _*).obj ℱ,
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map φ).hom.app (op V.obj)) ≫
            ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV := by
  -- First forget the module structures and apply the additive pushforward extension theorem.
  obtain ⟨Φ, hΦ, hΦ_unique⟩ :=
    existsUnique_pushforward_hom_of_basis_section_family
      (f := f.hom.base) (BX := BX) (BY := BY)
      (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢))
      (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
      hBX hBY η
  refine ⟨basis_pair_lift_to_module_hom (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη Φ hΦ, ?_, ?_⟩
  · -- The wrapped module morphism still restricts to the given basis-pair family.
    intro U V hUV
    exact basis_pair_lift_restrict_eq_eta (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη Φ hΦ U V hUV
  · -- Uniqueness is inherited from the additive uniqueness after forgetting module structures.
    intro ψ hψ
    exact basis_pair_lift_unique (f := f) (ℱ := ℱ) (𝒢 := 𝒢)
      hBX hBY η hη Φ hΦ hΦ_unique ψ hψ

end AlgebraicGeometry
