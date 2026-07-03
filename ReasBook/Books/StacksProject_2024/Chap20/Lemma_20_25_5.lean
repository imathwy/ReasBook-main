import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopologicalSpace.SheafCohomology

variable {X : Type u} [TopologicalSpace X]

abbrev TopologicalSpaceSite (X : Type u) [TopologicalSpace X] : GrothendieckTopology (Opens X) :=
  Opens.grothendieckTopology X

/-- The underlying `RingCat`-valued sheaf of a sheaf of commutative rings on `X`. -/
abbrev ringSheaf (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}) :
    Sheaf (TopologicalSpaceSite X) RingCat.{u} :=
  (sheafCompose (TopologicalSpaceSite X) (forget₂ CommRingCat RingCat.{u})).obj O

/-- The underlying sheaf of abelian groups of a sheaf of commutative rings on `X`. -/
abbrev additiveSheaf (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}) :
    Sheaf (TopologicalSpaceSite X) AddCommGrpCat.{u} :=
  (sheafCompose (TopologicalSpaceSite X)
    (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).obj O

/-- The additive-sheaf morphism underlying a morphism of sheaves of commutative rings on `X`. -/
abbrev additiveSheafMap
    {O' O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}} (π : O' ⟶ O) :
    additiveSheaf O' ⟶ additiveSheaf O :=
  (sheafCompose (TopologicalSpaceSite X)
    (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).map π

/-- The underlying sheaf of abelian groups of a sheaf of modules over `O`. -/
abbrev moduleUnderlyingSheaf
    {O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}}
    (I : SheafOfModules (ringSheaf O)) :
    Sheaf (TopologicalSpaceSite X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringSheaf O)).obj I

/-- The maximal open subset of `X`. -/
abbrev topOpen : Opens X :=
  ⟨Set.univ, isOpen_univ⟩

/-- The ring of global sections of a sheaf of commutative rings on `X`. -/
abbrev globalSectionsRing (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}) :=
  O.obj.obj (op topOpen)

/-- Every open subset of `X` is contained in the maximal open. -/
theorem le_topOpen (U : Opens X) : U ≤ topOpen := by
  intro x hx
  simp [topOpen]

/-- A square-zero extension setup for the boundary derivation statement on a topological space. -/
structure SquareZeroBoundarySetup
    (O' O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}) where
  /-- The kernel ideal, viewed as a sheaf of `O`-modules. -/
  idealModule : SheafOfModules (ringSheaf O)
  /-- The surjection of sheaves of commutative rings `\mathcal O' \twoheadrightarrow \mathcal O`. -/
  quotient : O' ⟶ O
  /-- The inclusion of the underlying additive sheaf of the kernel ideal into `\mathcal O'`. -/
  idealInclusion :
    moduleUnderlyingSheaf idealModule ⟶ additiveSheaf O'
  /-- The inclusion lands in the kernel of the quotient map on underlying additive sheaves. -/
  zero_comp : idealInclusion ≫ additiveSheafMap quotient = 0
  /-- The additive short complex `0 ⟶ \mathcal I ⟶ \mathcal O' ⟶ \mathcal O` is short exact. -/
  shortExact :
    (ShortComplex.mk idealInclusion (additiveSheafMap quotient) zero_comp).ShortExact
  /-- The quotient map is an epimorphism of sheaves of commutative rings. -/
  quotient_epi : Epi quotient
  /-- Sectionwise, products of two local sections from the ideal vanish in `\mathcal O'`. -/
  square_zero :
    ∀ U : (Opens X)ᵒᵖ, ∀ x y : idealModule.val.obj U,
      ((show ↑(O'.obj.obj U) from idealInclusion.hom.app U x) *
        (show ↑(O'.obj.obj U) from idealInclusion.hom.app U y)) = 0
  /-- Multiplication by a lift in `\mathcal O'` induces the given `\mathcal O`-module structure on
  the kernel ideal via the quotient map. -/
  scalar_compat :
    ∀ U : (Opens X)ᵒᵖ, ∀ a : O'.obj.obj U, ∀ x : idealModule.val.obj U,
      (show ↑(O'.obj.obj U) from
        idealInclusion.hom.app U (((quotient.hom.app U) a) • x)) =
          a * (show ↑(O'.obj.obj U) from idealInclusion.hom.app U x)
  /-- A chosen `Γ(X, \mathcal O)`-module structure on `H^1(X, \mathcal I)`. -/
  cohomologyModule : ModuleCat (globalSectionsRing O)
  /-- The chosen module object has the correct underlying additive group. -/
  cohomologyIso :
    AddCommGrpCat.of cohomologyModule ≅
      AddCommGrpCat.of ((moduleUnderlyingSheaf idealModule).H 1)

/-- The additive map from `\mathbb Z` to an abelian-group object determined by a chosen element. -/
theorem uliftIntToAddCommGrp_map_add
    {A : Type u} [AddCommGroup A] (a : A) (m n : ULift ℤ) :
    (m + n).down • a = m.down • a + n.down • a := by
  simp [add_zsmul]

/-- The presheaf morphism classified by a chosen global section of a sheaf of commutative rings. -/
-- Proof sketch: both sides of the naturality identity are obtained by restricting the same global
-- section `r` from the maximal open to `U`, and scalar multiplication by `n.down` commutes with
-- the restriction morphisms in the underlying additive presheaf.
theorem sectionToConstantPresheafHom_naturality
    (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u})
    (r : globalSectionsRing O)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))).map f ≫
      AddCommGrpCat.ofHom
        (AddMonoidHom.mk'
          (fun n : ULift ℤ ↦ n.down •
            (additiveSheaf O).obj.map (homOfLE (le_topOpen V.unop)).op r)
          (uliftIntToAddCommGrp_map_add
            ((additiveSheaf O).obj.map (homOfLE (le_topOpen V.unop)).op r))) =
      AddCommGrpCat.ofHom
        (AddMonoidHom.mk'
          (fun n : ULift ℤ ↦ n.down •
            (additiveSheaf O).obj.map (homOfLE (le_topOpen U.unop)).op r)
          (uliftIntToAddCommGrp_map_add
              ((additiveSheaf O).obj.map (homOfLE (le_topOpen U.unop)).op r))) ≫
        (additiveSheaf O).obj.map f := sorry

/-- The presheaf morphism classified by a chosen global section of a sheaf of commutative rings. -/
def sectionToConstantPresheafHom
    (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u})
    (r : globalSectionsRing O) :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
      (additiveSheaf O).obj where
  app U :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun n : ULift ℤ ↦ n.down •
          (additiveSheaf O).obj.map (homOfLE (le_topOpen U.unop)).op r)
        (uliftIntToAddCommGrp_map_add
          ((additiveSheaf O).obj.map (homOfLE (le_topOpen U.unop)).op r))
  naturality _ _ f := sectionToConstantPresheafHom_naturality O r f

/-- The morphism from the constant abelian sheaf on `\mathbb Z` classified by a global section of
`O`. -/
noncomputable def sectionToConstantSheafHom
    (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u})
    (r : globalSectionsRing O) :
    (constantSheaf (TopologicalSpaceSite X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶
    additiveSheaf O :=
  ((sheafificationAdjunction (TopologicalSpaceSite X) AddCommGrpCat.{u}).homEquiv _ _).symm
    (sectionToConstantPresheafHom O r)

variable [HasSheafify (TopologicalSpaceSite X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (TopologicalSpaceSite X) AddCommGrpCat.{u})]

/-- The boundary class in `H^1(X, \mathcal I)` attached to a global section of `\mathcal O`. -/
noncomputable def squareZeroBoundaryClass
    {O' O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}}
    (S : SquareZeroBoundarySetup O' O)
    (r : globalSectionsRing O) :
    (moduleUnderlyingSheaf S.idealModule).H 1 :=
  let extClass := S.shortExact.extClass
  let constantZ := (constantSheaf (TopologicalSpaceSite X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))
  (extClass.postcomp constantZ (rfl : 0 + 1 = 1))
    ((Abelian.Ext.addEquiv₀).symm (sectionToConstantSheafHom O r))

-- Proof sketch: view the short exact sequence
-- `0 ⟶ \mathcal I ⟶ \mathcal O' ⟶ \mathcal O ⟶ 0` in the abelian category of sheaves of
-- abelian groups. The connecting morphism sends a global section of `\mathcal O` to a class in
-- `H^1(X, \mathcal I)`. The square-zero hypothesis and the compatibility of the quotient action
-- with the `\mathcal O`-module structure on `\mathcal I` give the Leibniz rule after transporting
-- the codomain through the chosen `Γ(X, \mathcal O)`-module structure.
/-- Lemma 20.25.5: let `X` be a topological space, let `\mathcal O' \twoheadrightarrow \mathcal O`
be a surjection of sheaves of rings whose kernel ideal `\mathcal I` has square zero, and let
`R = \Gamma(X, \mathcal O)`. After choosing the induced `R`-module structure on `H^1(X,
\mathcal I)` as a bundled `R`-module `M`, the boundary map associated to
`0 \to \mathcal I \to \mathcal O' \to \mathcal O \to 0` is represented by a derivation
`R \to M`. -/
theorem exists_derivation_of_square_zero_boundary_map
    {O' O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}}
    (S : SquareZeroBoundarySetup O' O) :
    ∃ D : Derivation ℤ (globalSectionsRing O) S.cohomologyModule,
      ∀ r : globalSectionsRing O,
        S.cohomologyIso.hom (D r) = squareZeroBoundaryClass S r := sorry

end TopologicalSpace.SheafCohomology
