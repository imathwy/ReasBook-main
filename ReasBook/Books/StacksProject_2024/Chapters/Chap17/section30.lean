import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_30_1 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open TopCat.Sheaf
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

private abbrev ringedSpaceOfSheaf (O : TopCat.Sheaf CommRingCat.{u} X) : RingedSpace :=
  { carrier := X
    presheaf := O.presheaf
    IsSheaf := O.2 }

local notation "ModO₂" => RingedSpace.Modules (ringedSpaceOfSheaf O₂)
local notation "𝒪₂" => (SheafOfModules.unit (ringSheaf O₂) : ModO₂)

private abbrev deRhamRestrictScalars (φ : O₁ ⟶ O₂) :=
  SheafOfModules.restrictScalars (ringSheafMap φ)

private abbrev higherDeRhamFormPresheaf (φ : O₁ ⟶ O₂) (n : ℕ) :
    PresheafOfModules (ringSheaf O₂).obj :=
  exteriorPowerPresheaf (Ω(φ) : ModO₂) (n + 2)

/- Domain-style sampling for Definition 17.30.1:
- primary domain: relative de Rham complexes for a morphism of sheaves of rings on a fixed
  topological space;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferential`,
  `RingedSpace.Modules`,
  `Λ^[n]`,
  `IsExteriorPowerDeRhamDifferential`;
- best owner abstraction: the source-facing owner is the sheaf-level de Rham complex
  `TopCat.Sheaf.deRhamComplex φ`, attached directly to a morphism `φ : O₁ ⟶ O₂`;
- primitive data: the graded sheaves `\Omega^n_{O₂/O₁}` and the unique de Rham differential family
  on them;
- derived API: the source-facing notation `Ω^[n](φ)` for the graded form sheaves, the
  restriction-of-scalars view `deRhamComplexTerm`, the specification predicate `IsDeRhamComplex`,
  and the ringed-space specialization obtained by taking
  `φ = RingedSpace.Hom.inverseImageStructureSheafHomComm f`.

Source/core/bridge triage:
- `source-facing`: `deRhamComplex φ`;
- `core/canonical`: `Ω(φ)`, `relativeDifferential φ`, `RingedSpace.Modules`, and `Λ^[n]`;
- `bridge/view`: `deRhamComplexTerm`, `IsDeRhamComplex`, and the ringed-space specialization at the
  end of the file. -/

/-- The graded sheaf `\Omega^n_{O₂/O₁}` underlying the relative de Rham complex of a morphism
`φ : O₁ ⟶ O₂` of sheaves of rings. -/
noncomputable def deRhamFormSheaf (φ : O₁ ⟶ O₂) (n : ℕ) :
    SheafOfModules (ringSheaf O₂) :=
  match n with
  | 0 => 𝒪₂
  | 1 => Ω(φ)
  | n + 2 => Λ^[n + 2] (Ω(φ) : ModO₂)

scoped[AlgebraicGeometry] notation3:max "Ω^[" n "](" φ ")" =>
  TopCat.Sheaf.deRhamFormSheaf φ n

/-- The degree-`n` object in the relative de Rham complex of `φ`, viewed as an `O₁`-module sheaf
by restriction of scalars along `φ`. -/
noncomputable abbrev deRhamComplexTerm (φ : O₁ ⟶ O₂) (n : ℕ) :
    SheafOfModules (ringSheaf O₁) :=
  (deRhamRestrictScalars φ).obj Ω^[n](φ)

/-- The exact one-form `db` on an open set, relative to the morphism `φ : O₁ ⟶ O₂`. -/
private noncomputable abbrev exactOneFormSection
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    O₂.presheaf.obj U → (Ω(φ)).val.obj U :=
  fun b ↦ ((relativeDifferential φ).app U).d b

/-- The canonical map from objectwise exterior-power sections to the sheafified higher de Rham
term. -/
private noncomputable def higherExteriorPowerSection
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    (higherDeRhamFormPresheaf φ n).obj U →
      (deRhamFormSheaf φ (n + 2)).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
    (higherDeRhamFormPresheaf φ n)).app U

/-- The canonical basic `p`-form `b₀ \, db₁ ∧ \cdots ∧ dbₚ` on an open set of `X`. -/
noncomputable def basicFormSection
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ) :
    O₂.presheaf.obj U → (Fin p → O₂.presheaf.obj U) → (deRhamComplexTerm φ p).val.obj U :=
  match p with
  | 0 => fun b₀ _ ↦ by
      simpa [deRhamComplexTerm, deRhamRestrictScalars, deRhamFormSheaf] using b₀
  | 1 => fun b₀ b ↦ by
      simpa [deRhamComplexTerm, deRhamRestrictScalars, deRhamFormSheaf] using
        (b₀ • exactOneFormSection φ U (b 0))
  | n + 2 => fun b₀ b ↦ by
      let Rsh := ringSheaf O₂
      letI : CommRing ↑(Rsh.obj.obj U) := by
        change CommRing ↑(O₂.presheaf.obj U)
        infer_instance
      simpa [deRhamComplexTerm, deRhamRestrictScalars, deRhamFormSheaf] using
        higherExteriorPowerSection φ n U
          (ModuleCat.exteriorPower.mk fun i : Fin (n + 2) ↦
            Fin.cases
              (b₀ • exactOneFormSection φ U (b 0))
              (fun j ↦ exactOneFormSection φ U (b j.succ))
              i)

/-- The target form `db₀ ∧ db₁ ∧ \cdots ∧ dbₚ` on the right-hand side of the de Rham rule. -/
noncomputable def differentialTargetSection
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ) :
    O₂.presheaf.obj U → (Fin p → O₂.presheaf.obj U) →
      (deRhamComplexTerm φ (p + 1)).val.obj U :=
  match p with
  | 0 => fun b₀ _ ↦ by
      simpa [deRhamComplexTerm, deRhamRestrictScalars, deRhamFormSheaf] using
        exactOneFormSection φ U b₀
  | n + 1 => fun b₀ b ↦ by
      let Rsh := ringSheaf O₂
      letI : CommRing ↑(Rsh.obj.obj U) := by
        change CommRing ↑(O₂.presheaf.obj U)
        infer_instance
      simpa [deRhamComplexTerm, deRhamRestrictScalars, deRhamFormSheaf] using
        higherExteriorPowerSection φ n U
          (ModuleCat.exteriorPower.mk fun i : Fin (n + 2) ↦
            Fin.cases
              (exactOneFormSection φ U b₀)
              (fun j ↦ exactOneFormSection φ U (b j))
              i)

-- Proof sketch: degree `0` is forced by the universal derivation
-- `O₂ \to Ω_{O₂/O₁}`, and in higher degrees the local basic forms generate the exterior powers of
-- `Ω_{O₂/O₁}`, so there is a unique compatible differential family satisfying the usual de Rham
-- rule on those generators.
/-- A morphism of sheaves of rings carries a unique differential family on the graded forms
`Ω^•_{O₂/O₁}` whose degree-`0` part is the universal derivation and whose higher-degree parts send
`b₀ \, db₁ ∧ \cdots ∧ dbₚ` to `db₀ ∧ db₁ ∧ \cdots ∧ dbₚ`. -/
private theorem existsUnique_deRhamDifferentialFamily
    (φ : O₁ ⟶ O₂) :
    ∃! δ : ∀ p : ℕ, deRhamComplexTerm φ p ⟶ deRhamComplexTerm φ (p + 1),
      (∀ (p : ℕ) (U : (Opens X)ᵒᵖ) (b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U),
        ((δ p).val.app U) (basicFormSection φ p U b₀ b) =
          differentialTargetSection φ p U b₀ b) ∧
      ∀ p : ℕ, δ p ≫ δ (p + 1) = 0 := by
  sorry

/-- The canonical differential family on the graded forms `Ω^•_{O₂/O₁}`. -/
private noncomputable def deRhamDifferentialFamily
    (φ : O₁ ⟶ O₂) :
    ∀ p : ℕ, deRhamComplexTerm φ p ⟶ deRhamComplexTerm φ (p + 1) :=
  Classical.choose (ExistsUnique.exists (existsUnique_deRhamDifferentialFamily φ))

/-- The chosen de Rham differential family satisfies the de Rham rule and squares to zero. -/
private theorem deRhamDifferentialFamily_spec
    (φ : O₁ ⟶ O₂) :
    (∀ (p : ℕ) (U : (Opens X)ᵒᵖ) (b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U),
      ((deRhamDifferentialFamily φ p).val.app U) (basicFormSection φ p U b₀ b) =
        differentialTargetSection φ p U b₀ b) ∧
      ∀ p : ℕ, deRhamDifferentialFamily φ p ≫ deRhamDifferentialFamily φ (p + 1) = 0 := by
  simpa [deRhamDifferentialFamily] using
    (Classical.choose_spec (ExistsUnique.exists (existsUnique_deRhamDifferentialFamily φ)))

-- Proof sketch: extract the basic-form clause from the chosen differential family.
/-- The chosen de Rham differentials satisfy the basic-form rule on local sections. -/
private theorem deRhamDifferentialFamily_basicForm
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U) :
    ((deRhamDifferentialFamily φ p).val.app U) (basicFormSection φ p U b₀ b) =
      differentialTargetSection φ p U b₀ b :=
  (deRhamDifferentialFamily_spec φ).1 p U b₀ b

-- Proof sketch: extract the square-zero clause from the chosen differential family.
/-- Consecutive chosen de Rham differentials compose to zero. -/
private theorem deRhamDifferentialFamily_sq_zero
    (φ : O₁ ⟶ O₂) (p : ℕ) :
    deRhamDifferentialFamily φ p ≫ deRhamDifferentialFamily φ (p + 1) = 0 := by
  exact (deRhamDifferentialFamily_spec φ).2 p

/-- Definition 17.30.1: for a morphism `φ : O₁ ⟶ O₂` of sheaves of rings on a topological space,
the de Rham complex of `φ` is the cochain complex of `O₁`-module sheaves whose degree-`n` term is
`\Omega^n_{O₂/O₁}` and whose differential is the canonical de Rham differential on local basic
forms. -/
noncomputable def deRhamComplex
    (φ : O₁ ⟶ O₂) :
    CochainComplex (SheafOfModules (ringSheaf O₁)) ℕ :=
  CochainComplex.of
    (deRhamComplexTerm φ)
    (deRhamDifferentialFamily φ)
    (deRhamDifferentialFamily_sq_zero φ)

scoped[AlgebraicGeometry] notation3:max "Ω^•(" φ ")" =>
  TopCat.Sheaf.deRhamComplex φ

/-- The degree-`n` object of the relative de Rham complex is the expected relative de Rham term. -/
theorem deRhamComplex_obj
    (φ : O₁ ⟶ O₂) (n : ℕ) :
    (Ω^•(φ)).X n = deRhamComplexTerm φ n :=
  rfl

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- The canonical de Rham term is obtained from the de Rham form sheaf by restriction of scalars
along `φ : O₁ ⟶ O₂`. -/
theorem deRhamComplexTerm_eq_restrictScalars
    (φ : O₁ ⟶ O₂) (n : ℕ) :
    deRhamComplexTerm φ n =
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj Ω^[n](φ) :=
  rfl

/-- A companion specification predicate: a cochain complex of `O₁`-module sheaves is a de Rham
complex for `φ : O₁ ⟶ O₂` if its terms are the expected relative de Rham form sheaves `Ω^[n](φ)`,
viewed by
restriction of scalars along `φ`, and its differential satisfies the usual de Rham rule on the
canonical basic forms. -/
class IsDeRhamComplex
    (φ : O₁ ⟶ O₂)
    (K : CochainComplex (SheafOfModules (ringSheaf O₁)) ℕ) where
  /-- Every degree of the complex is the expected relative de Rham form sheaf. -/
  term_iso (n : ℕ) :
    K.X n ≅ deRhamComplexTerm φ n
  /-- On every open set, the differential of `K` sends canonical basic forms to their de Rham
  target forms. -/
  basicForm (U : (Opens X)ᵒᵖ) (p : ℕ) (b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U) :
    (((term_iso p).inv ≫ K.d p (p + 1) ≫ (term_iso (p + 1)).hom).val.app U)
        (basicFormSection φ p U b₀ b) =
      differentialTargetSection φ p U b₀ b

-- Proof sketch: the complex was defined with the canonical owner terms `deRhamComplexTerm φ`, and
-- the de Rham formulas on sections are exactly the basic-form formulas required by
-- `IsDeRhamComplex`.
/-- The canonical relative de Rham complex satisfies the companion specification predicate
`IsDeRhamComplex`. -/
instance instIsDeRhamComplexDeRhamComplex
    (φ : O₁ ⟶ O₂) :
    IsDeRhamComplex φ (deRhamComplex φ) where
  term_iso n := eqToIso <| deRhamComplex_obj φ n
  basicForm U p b₀ b := by
    simpa [deRhamComplex] using
      deRhamDifferentialFamily_basicForm φ p U b₀ b

end TopCat.Sheaf

namespace AlgebraicGeometry.RingedSpace

variable {X S : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/-- The de Rham complex of a morphism of ringed spaces is the specialization of the sheaf-level
de Rham complex to the inverse-image structure-sheaf morphism
`f^{-1}\mathcal O_S \to \mathcal O_X`. -/
abbrev deRhamComplex
    (f : X ⟶ S) :=
  TopCat.Sheaf.deRhamComplex (RingedSpace.Hom.inverseImageStructureSheafHomComm f)

scoped[AlgebraicGeometry] notation3:max "Ω^•[" f "]" =>
  AlgebraicGeometry.RingedSpace.deRhamComplex f

scoped[AlgebraicGeometry] notation3:max "Ω^[" n "][" f "]" =>
  TopCat.Sheaf.deRhamFormSheaf
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f) n

/-- The degree-`n` object of the relative de Rham complex of a morphism of ringed spaces is the
sheaf `\Omega^n_{X/S}`, viewed by restriction of scalars along
`f^\sharp : f^{-1}\mathcal O_S \to \mathcal O_X`. -/
theorem deRhamComplex_X
    (f : X ⟶ S) (n : ℕ) :
    (Ω^•[f]).X n =
      (SheafOfModules.restrictScalars
        (ringSheafMap (RingedSpace.Hom.inverseImageStructureSheafHomComm f))).obj
        Ω^[n][f] :=
  rfl

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_30_2 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace ComplexShape
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}
variable {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/- Domain-style sampling for Lemma 17.30.2:
- primary domain: inverse-image compatibility for relative de Rham complexes of sheaves of rings
  on a topological space;
- sampled owner declarations:
  `TopCat.Sheaf.deRhamComplex`,
  `Ω^•(φ)`,
  `TopCat.Sheaf.deRhamComplexTerm_eq_restrictScalars`,
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`,
  `CategoryTheory.Functor.mapHomologicalComplex`,
  `HomologicalComplex.Hom.isoOfComponents`;
- best owner abstraction: the source-facing owner remains the relative de Rham complex `Ω^•(φ)`,
  with raw owner `TopCat.Sheaf.deRhamComplex φ`, and the
  inverse-image comparison should be exposed by an actual complex isomorphism between the inverse
  image of `Ω^•(φ)` and the pulled-back de Rham complex;
- primitive data: the morphism `φ : O₁ ⟶ O₂`, the actual inverse-image functor on
  `O₁`-module sheaves, and the pulled-back morphism `(pullback CommRingCat f).map φ`;
- derived API: the named complex isomorphism `inverseImage_deRhamComplexIso` and its
  theorem-level `IsIsomorphic` companion.

Source/core/bridge triage:
- `source-facing`: the canonical identification
  `f^{-1}\Omega^\bullet_{O₂/O₁} = \Omega^\bullet_{f^{-1}O₂/f^{-1}O₁}`;
- `core/canonical`: `Ω^•(φ)`, `inverseImage_relativeDifferentialsIso`, and
  `Functor.mapHomologicalComplex`;
- `bridge/view`: this file packages that identification as a complex isomorphism transported across
  `pullbackRingSheafIso f O₁`.

The bridge should therefore live at the complex-isomorphism layer, with `IsIsomorphic` retained
only as the thin theorem companion, and its public type should mention the actual source and target
complexes rather than file-local wrapper aliases. -/

/-- Lemma 17.30.2: the inverse image of the relative de Rham complex
`\Omega^\bullet_{O₂/O₁}` is canonically isomorphic, as a cochain complex, to the relative de Rham
complex of the pulled-back morphism
`f^{-1}\mathcal O_1 \to f^{-1}\mathcal O_2`, expressed over the raw pulled-back
`RingCat`-valued structure sheaf via `pullbackRingSheafIso f O₁`. -/
noncomputable def inverseImage_deRhamComplexIso
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (((SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₁))).mapHomologicalComplex
      (up ℕ)).obj
      Ω^•(φ)) ≅
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₁).inv).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•((pullback CommRingCat.{u} f).map φ)) := by
  sorry

/-- The inverse image of the relative de Rham complex is canonically identified with the relative
de Rham complex of the pulled-back morphism. This is the theorem-level `IsIsomorphic` companion to
`inverseImage_deRhamComplexIso`. -/
theorem inverseImage_deRhamComplex_isIsomorphic
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      (((SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₁))).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•(φ))
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₁).inv).mapHomologicalComplex
        (up ℕ)).obj
        Ω^•((pullback CommRingCat.{u} f).map φ)) := by
  exact ⟨inverseImage_deRhamComplexIso f φ⟩

end TopCat.Sheaf

/-! ### Lemma_17_30_3 (from Chap17) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open TopCat.Sheaf

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
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`,
  `de_rham_differentials_are_order_one_differential_operators`;
- best owner abstraction: the canonical degree-`p` differential
  `(deRhamComplex φ).d p (p + 1)` in the source-facing owner `TopCat.Sheaf.deRhamComplex φ`;
- primitive data: only the morphism `φ : O₁ ⟶ O₂` and the degree `p`;
- derived API: the order-one differential-operator property of that canonical differential.

Source/core/bridge triage:
- `source-facing`: the order-one statement for the actual de Rham differential
  `d : \Omega^p_{O₂/O₁} \to \Omega^{p + 1}_{O₂/O₁}`;
- `core/canonical`: `TopCat.Sheaf.deRhamComplex φ` together with
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`;
- `bridge/view`: evaluation on opens inside the ringed-site owner. -/

/-- Lemma 17.30.3: for a morphism of sheaves of rings `φ : O₁ ⟶ O₂`, each differential
`d : \Omega^p_{O₂/O₁} \to \Omega^{p + 1}_{O₂/O₁}` in the canonical de Rham complex is a
differential operator of order `1` relative to `φ`. -/
-- Proof sketch: evaluate the canonical de Rham differential on each open set, identify it with
-- the sectionwise algebraic de Rham differential, and apply the algebraic order-one result of
-- Lemma `10.133.10`.
theorem deRhamDifferential_isDifferentialOperatorOfOrder
    (φ : O₁ ⟶ O₂) (p : ℕ) :
    IsDifferentialOperatorOfOrder φ ((deRhamComplex φ).d p (p + 1)) 1 := by
  sorry

end TopCat.Sheaf

/-! ### Definition_17_30_4 (from Chap17) -/
open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
variable (f : X ⟶ Y) (i : ℕ)

/- Domain-style sampling for Definition 17.30.4:
- primary domain: relative de Rham complexes on a morphism of ringed spaces;
- sampled owner declarations:
  `deRhamComplex`,
  `deRhamComplex_X`,
  `IsDeRhamComplex`,
  `CochainComplex.d`;
- best owner abstraction: the source-facing differential already lives as the degree-`i`
  differential of the canonical owner `deRhamComplex f` from `Definition_17_30_1`;
- primitive data in this file: none;
- derived API in this file: none.

Source/core/bridge triage:
- `source-facing`: the differential `d : Ω^i_{X/Y} → Ω^{i + 1}_{X/Y}`;
- `core/canonical`: `deRhamComplex f` and its differential field `.d`;
- `bridge/view`: this file is recall-only, so it keeps no parallel bridge owner. -/

/- Definition 17.30.4: the degree-`i` relative de Rham differential
`d : Ω^i_{X/Y} → Ω^{i + 1}_{X/Y}` is the degree-`i` differential of the canonical relative de Rham
complex `deRhamComplex f`. -/
#check (deRhamComplex f).d i (i + 1)

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_30_5 (from Chap17) -/
open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open TopCat.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/- Domain-style sampling for Lemma 17.30.5:
- primary domain: relative de Rham differentials on a morphism of ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.inverseImageStructureSheafHomComm`,
  `ringSheafMap`,
  `deRhamComplex`,
  `TopCat.Sheaf.deRhamComplex`,
  `TopCat.Sheaf.deRhamDifferential_isDifferentialOperatorOfOrder`,
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`;
- best owner abstraction: the sheaf-level owner theorem
  `TopCat.Sheaf.deRhamDifferential_isDifferentialOperatorOfOrder`, specialized along
  `RingedSpace.Hom.inverseImageStructureSheafHomComm f`, with the ringed-space notation
  `deRhamComplex f` used only as a thin bridge;
- primitive data here: only the morphism `f : X ⟶ Y` and the degree `i`;
- derived API: the order-one differential-operator statement for the degree-`i` owner
  differential.

Source/core/bridge triage:
- `source-facing`: the order-one differential-operator statement for the relative de Rham
  differential;
- `core/canonical`: `TopCat.Sheaf.deRhamComplex` and
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`;
- `bridge/view`: the ringed-space specialization `deRhamComplex f`.

This item is therefore a direct bridge/view recall: the ringed-space statement is exactly the
sheaf-level owner theorem specialized along `RingedSpace.Hom.inverseImageStructureSheafHomComm f`,
so the file should reuse that owner directly rather than introduce a parallel theorem wrapper. -/

variable (f : X ⟶ Y) (i : ℕ)

/- Lemma 17.30.5: for a morphism of ringed spaces `f : X ⟶ Y`, each differential
`d : \Omega^i_{X/Y} \to \Omega^{i + 1}_{X/Y}` in the relative de Rham complex is a differential
operator of order `1` on `X/Y`. This is the sheaf-level owner theorem of Lemma `17.30.3`,
specialized to the inverse-image structure-sheaf morphism of `f`. -/
#check
  (TopCat.Sheaf.deRhamDifferential_isDifferentialOperatorOfOrder
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f) i :
    IsDifferentialOperatorOfOrder
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f)
      ((deRhamComplex f).d i (i + 1)) 1)

end AlgebraicGeometry.RingedSpace
