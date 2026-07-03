import Mathlib
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_15_1 (from Chap06) -/
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

universe w v u

/- Domain-style sampling for Definition 6.15.1:
- primary domain: concrete-category forgetful functors to `Type` whose behavior on limits,
  filtered colimits, and isomorphisms drives the sheaf and stalk API for algebraic structures;
- inspected owner declarations:
  `CategoryTheory.ConcreteCategory`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`,
  `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`;
- owner abstraction:
  the source fixes a pair `(C, F)` with `F : C ⥤ Type w`, so the right public owner here is a
  bundled `Prop`-valued predicate on that pair, while the primitive data are the six canonical
  mathlib classes
  `F.Faithful`, `HasLimits C`, `PreservesLimits F`, `HasFilteredColimits C`,
  `PreservesFilteredColimits F`, and `F.ReflectsIsomorphisms`;
- bridge/view:
  `CategoryTheory.ConcreteCategory` is only a view induced by the faithful functor `F`, not the
  owner abstraction itself, because the source does not start from a pre-existing concrete-category
  structure on `C`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project predicate saying that the fixed pair `(C, F)` is a type of
  algebraic structures;
- `core/canonical`: the six existing mathlib classes listed above;
- `bridge/view`: any concrete-category structure induced from the faithful functor `F`.

Primitive data are exactly those six owner classes, so this definition should bundle them directly
and add no auxiliary wrapper data.
-/
/-- Definition 6.15.1: once the category `C` and the functor `F : C ⥤ Type w` are fixed, the
remaining axioms for a type of algebraic structure form a property of the pair `(C, F)`. -/
class IsAlgebraicStructure (C : Type u) [Category.{v} C] (F : C ⥤ Type w) : Prop
    extends F.Faithful, HasLimits C, PreservesLimits F, HasFilteredColimits C,
      PreservesFilteredColimits F, F.ReflectsIsomorphisms

section

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

instance [F.Faithful] [HasLimits C] [PreservesLimits F] [HasFilteredColimits C]
    [PreservesFilteredColimits F] [F.ReflectsIsomorphisms] : IsAlgebraicStructure C F where

instance [IsAlgebraicStructure C F] (X : TopCat.{w}) :
    (Opens.grothendieckTopology X).HasSheafCompose F := by
  exact hasSheafCompose_of_preservesLimitsOfSize (Opens.grothendieckTopology X)

end

/-! ### Lemma_6_15_2 (from Chap06) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

private abbrev pointedBase : Type u := ULift.{u} PUnit

private noncomputable def pointedEquivUnder : Pointed.{u} ≌ Under (pointedBase.{u}) where
  functor :=
    { obj := fun X ↦ Under.mk (fun _ : pointedBase ↦ X.point)
      map := fun {X Y} f ↦ Under.homMk f.toFun (by
        funext x
        exact f.map_point) }
  inverse :=
    { obj := fun X ↦ Pointed.of (X.hom (ULift.up PUnit.unit))
      map := fun {X Y} f ↦ ⟨f.right, by
        simpa using congr_fun (Under.w f) (ULift.up PUnit.unit)⟩ }
  unitIso := NatIso.ofComponents (fun X ↦ Pointed.Iso.mk (Equiv.refl _) rfl)
  counitIso := NatIso.ofComponents (fun X ↦ Under.isoMk (Iso.refl _))

/-- The category of pointed sets has all limits. -/
instance : HasLimits Pointed :=
  Adjunction.has_limits_of_equivalence pointedEquivUnder.functor

/-- The forgetful functor from pointed sets to types preserves limits. -/
instance : PreservesLimits (forget Pointed) :=
  typeToPointedForgetAdjunction.rightAdjoint_preservesLimits

/-- The category of pointed sets has all colimits. -/
instance : HasColimits Pointed :=
  HasColimitsOfSize.mk (C := Pointed) fun J [Category J] ↦ by
    letI : HasColimits (Under pointedBase) := inferInstance
    letI : HasColimitsOfShape J (Under pointedBase) := inferInstance
    exact Adjunction.hasColimitsOfShape_of_equivalence pointedEquivUnder.functor

/-- The category of pointed sets has filtered colimits. -/
instance : HasFilteredColimits Pointed := by
  let h : HasColimits (Under pointedBase) := inferInstance
  letI : HasFilteredColimits (Under pointedBase) :=
    { HasColimitsOfShape := fun J _ _ ↦ h.has_colimits_of_shape J }
  exact ⟨fun J _ _ ↦ Adjunction.hasColimitsOfShape_of_equivalence pointedEquivUnder.functor⟩

/-- The forgetful functor from pointed sets to types preserves filtered colimits. -/
instance : PreservesFilteredColimits (forget Pointed) where
  preserves_filtered_colimits J _ _ := by
    change PreservesColimitsOfShape J (pointedEquivUnder.functor ⋙ Under.forget pointedBase)
    letI : PreservesColimitsOfShape J pointedEquivUnder.functor := inferInstance
    letI : PreservesColimitsOfShape J (Under.forget pointedBase) := inferInstance
    infer_instance

private theorem pointed_isIso_of_bijective {X Y : Pointed} (f : X ⟶ Y)
    (hf : Function.Bijective f) : IsIso f := by
  simpa using
    (Pointed.Iso.mk (Equiv.ofBijective f hf) (by simpa using f.map_point)).isIso_hom

/-- The forgetful functor from pointed sets to types reflects isomorphisms. -/
instance : (forget Pointed).ReflectsIsomorphisms where
  reflects f :=
    pointed_isIso_of_bijective f <|
      (CategoryTheory.isIso_iff_bijective ((forget Pointed).map f)).mp inferInstance

/-- The category of groups has filtered colimits. -/
instance : HasFilteredColimits GrpCat where
  HasColimitsOfShape _ _ _ :=
    ⟨fun F ↦ ⟨GrpCat.FilteredColimits.colimitCocone F,
      GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩

-- Proof sketch: limits of Lie algebras are constructed on the corresponding limits of the
-- underlying vector spaces, with bracket defined pointwise.

/-- Lemma 6.15.2 (1): the category of pointed sets, with its forgetful functor to sets, defines a
type of algebraic structures. -/
instance pointed_sets_algebraic_structure_type :
    IsAlgebraicStructure Pointed (forget Pointed) :=
  inferInstance

/-- Lemma 6.15.2 (2): the category of abelian groups, with its forgetful functor to sets, defines
a type of algebraic structures. -/
instance abelian_groups_algebraic_structure_type :
    IsAlgebraicStructure AddCommGrpCat (forget AddCommGrpCat) :=
  inferInstance

/-- Lemma 6.15.2 (3): the category of groups, with its forgetful functor to sets, defines a type
of algebraic structures. -/
instance groups_algebraic_structure_type :
    IsAlgebraicStructure GrpCat (forget GrpCat) :=
  inferInstance

/-- Lemma 6.15.2 (4): the category of monoids, with its forgetful functor to sets, defines a type
of algebraic structures. -/
instance monoids_algebraic_structure_type :
    IsAlgebraicStructure MonCat (forget MonCat) := by
  letI : HasLimits MonCat := inferInstance
  letI : PreservesLimits (forget MonCat) := inferInstance
  let h : HasColimits MonCat := inferInstance
  letI : HasFilteredColimits MonCat :=
    { HasColimitsOfShape := fun I _ _ ↦ h.has_colimits_of_shape I }
  letI : PreservesFilteredColimits (forget MonCat) :=
    { preserves_filtered_colimits := fun I _ _ ↦ by infer_instance }
  letI : (forget MonCat).ReflectsIsomorphisms := inferInstance
  infer_instance

/-- Lemma 6.15.2 (5): the category of rings, with its forgetful functor to sets, defines a type
of algebraic structures. -/
instance rings_algebraic_structure_type :
    IsAlgebraicStructure RingCat (forget RingCat) := by
  letI : HasLimits RingCat := inferInstance
  letI : PreservesLimits (forget RingCat) := inferInstance
  let h : HasColimits RingCat := inferInstance
  letI : HasFilteredColimits RingCat :=
    { HasColimitsOfShape := fun I _ _ ↦ h.has_colimits_of_shape I }
  letI : PreservesFilteredColimits (forget RingCat) :=
    { preserves_filtered_colimits := fun I _ _ ↦ by infer_instance }
  letI : (forget RingCat).ReflectsIsomorphisms := inferInstance
  infer_instance

/-- Lemma 6.15.2 (6): for a fixed ring `R`, the category of `R`-modules with its forgetful functor
to sets defines a type of algebraic structures. -/
instance modules_algebraic_structure_type (R : Type u) [Ring R] :
    IsAlgebraicStructure (ModuleCat.{u} R) (forget (ModuleCat.{u} R)) := by
  letI : HasLimits (ModuleCat.{u} R) := inferInstance
  letI : PreservesLimits (forget (ModuleCat.{u} R)) := inferInstance
  let h : HasColimitsOfSize.{u, u} (ModuleCat.{u} R) := inferInstance
  letI : HasFilteredColimits (ModuleCat.{u} R) :=
    { HasColimitsOfShape := fun I _ _ ↦ h.has_colimits_of_shape I }
  letI : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
    { preserves_filtered_colimits := fun I _ _ ↦ by infer_instance }
  letI : (forget (ModuleCat.{u} R)).ReflectsIsomorphisms := inferInstance
  infer_instance

namespace LieAlgebraCat

section Limits

variable {R : Type u} [CommRing R]

namespace Shrink

variable {L : Type v} [LieRing L] [LieAlgebra R L] [Small.{u} L]

/-- Helper for Lemma 6.15.2: the bracket on a shrunk Lie algebra is transported along
`equivShrink`. -/
instance instBracket : Bracket (Shrink.{u} L) (Shrink.{u} L) where
  bracket x y := equivShrink L ⁅(equivShrink L).symm x, (equivShrink L).symm y⁆

/-- Helper for Lemma 6.15.2: unshrinking a transported bracket recovers the original bracket. -/
@[simp] theorem equivShrink_symm_lie (x y : Shrink.{u} L) :
    (equivShrink L).symm ⁅x, y⁆ = ⁅(equivShrink L).symm x, (equivShrink L).symm y⁆ :=
  by
    change
      (equivShrink L).symm ((equivShrink L) ⁅(equivShrink L).symm x, (equivShrink L).symm y⁆) =
        ⁅(equivShrink L).symm x, (equivShrink L).symm y⁆
    simp

/-- Helper for Lemma 6.15.2: shrinking preserves the Lie bracket. -/
@[simp] theorem equivShrink_lie (x y : L) :
    equivShrink L ⁅x, y⁆ = ⁅equivShrink L x, equivShrink L y⁆ := by
  change equivShrink L ⁅x, y⁆ =
    equivShrink L ⁅(equivShrink L).symm (equivShrink L x), (equivShrink L).symm (equivShrink L y)⁆
  simp

/-- Helper for Lemma 6.15.2: shrinking a small Lie algebra preserves its Lie ring structure. -/
instance instLieRing : LieRing (Shrink.{u} L) := by
  -- Transport each Lie-ring axiom along `equivShrink.symm`.
  refine
    { add_lie := ?_
      lie_add := ?_
      lie_self := ?_
      leibniz_lie := ?_ }
  · intro x y z
    exact (equivShrink L).symm.injective <| by
      simpa [equivShrink_symm_lie, equivShrink_symm_add] using
        (add_lie ((equivShrink L).symm x) ((equivShrink L).symm y) ((equivShrink L).symm z))
  · intro x y z
    exact (equivShrink L).symm.injective <| by
      simpa [equivShrink_symm_lie, equivShrink_symm_add] using
        (lie_add ((equivShrink L).symm x) ((equivShrink L).symm y) ((equivShrink L).symm z))
  · intro x
    exact (equivShrink L).symm.injective <| by
      simpa [equivShrink_symm_lie] using lie_self ((equivShrink L).symm x)
  · intro x y z
    exact (equivShrink L).symm.injective <| by
      simpa [equivShrink_symm_lie, equivShrink_symm_add] using
        (leibniz_lie ((equivShrink L).symm x) ((equivShrink L).symm y) ((equivShrink L).symm z))

/-- Helper for Lemma 6.15.2: shrinking a small Lie algebra preserves its scalar-compatible
Lie bracket. -/
instance instLieAlgebra : LieAlgebra R (Shrink.{u} L) := by
  -- Transport scalar compatibility of the bracket through `equivShrink.symm`.
  refine
    { lie_smul := ?_ }
  intro t x y
  exact (equivShrink L).symm.injective <| by
    simpa [equivShrink_symm_lie, equivShrink_symm_smul] using
      (LieAlgebra.lie_smul t ((equivShrink L).symm x) ((equivShrink L).symm y))

/-- Helper for Lemma 6.15.2: the shrink equivalence upgrades to a Lie algebra equivalence. -/
def lieEquiv : Shrink.{u} L ≃ₗ⁅R⁆ L := by
  -- Package the transported linear equivalence together with bracket preservation.
  exact
    { Shrink.linearEquiv R L with
      map_lie' := fun {x y} ↦ equivShrink_symm_lie x y }

end Shrink

namespace HasLimits

variable {J : Type u} [Category J] (F : J ⥤ LieAlgebraCat.{u} R)

/-- Helper for Lemma 6.15.2: the pointwise product of the diagram carries the induced Lie ring
structure. -/
instance piLieRing : LieRing (∀ j, F.obj j) where
  bracket x y j := ⁅x j, y j⁆
  add_lie x y z := by
    funext j
    exact add_lie (x j) (y j) (z j)
  lie_add x y z := by
    funext j
    exact lie_add (x j) (y j) (z j)
  lie_self x := by
    funext j
    exact lie_self (x j)
  leibniz_lie x y z := by
    funext j
    exact leibniz_lie (x j) (y j) (z j)

/-- Helper for Lemma 6.15.2: the pointwise product of the diagram carries the induced Lie algebra
structure. -/
instance piLieAlgebra : LieAlgebra R (∀ j, F.obj j) where
  lie_smul t x y := by
    funext j
    exact lie_smul t (x j) (y j)

/-- Helper for Lemma 6.15.2: the compatible families in a Lie algebra diagram should form the
source-faithful limit Lie subalgebra of the pointwise product. -/
def sectionsLieSubalgebra : LieSubalgebra R (∀ j, F.obj j) :=
  { ModuleCat.sectionsSubmodule (R := R)
      (F := F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) with
    lie_mem' := by
      intro x y hx hy
      intro j j' f
      -- Compatible sections remain compatible after taking the pointwise bracket.
      change F.map f ⁅x j, y j⁆ = ⁅x j', y j'⁆
      rw [← hx f, ← hy f]
      exact (F.map f).map_lie (x j) (y j) }

/-- Helper for Lemma 6.15.2: smallness of compatible families can be read from the type-theoretic
limit sections. -/
instance sectionsLieSubalgebra_small [Small.{u} (sectionsLieSubalgebra F)] :
    Small.{u} ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| Small.{u} (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: the raw compatible sections inherit the additive structure carried by
the Lie-subalgebra of compatible families. -/
instance sectionsAddCommMonoid : AddCommMonoid ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| AddCommMonoid (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: the raw compatible sections inherit the module structure carried by
the Lie-subalgebra of compatible families. -/
instance sectionsModule : Module R ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| Module R (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: the raw compatible sections inherit the Lie-ring structure carried by
the Lie-subalgebra of compatible families. -/
instance sectionsLieRing : LieRing ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| LieRing (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: the raw compatible sections inherit the Lie-algebra structure carried
by the Lie-subalgebra of compatible families. -/
instance sectionsLieAlgebra : LieAlgebra R ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| LieAlgebra R (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: shrinking the compatible-sections Lie subalgebra should induce the
Lie ring structure on the underlying type-theoretic limit. -/
instance limitLieRing [Small.{u} (sectionsLieSubalgebra F)] :
    LieRing (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt :=
  inferInstanceAs <| LieRing (Shrink.{u} (sectionsLieSubalgebra F))

/-- Helper for Lemma 6.15.2: shrinking the compatible-sections Lie subalgebra should induce the
Lie algebra structure on the underlying type-theoretic limit. -/
instance limitLieAlgebra [Small.{u} (sectionsLieSubalgebra F)] :
    LieAlgebra R (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt :=
  inferInstanceAs <| LieAlgebra R (Shrink.{u} (sectionsLieSubalgebra F))

/-- Helper for Lemma 6.15.2: the underlying module projection from the explicit Lie limit. -/
def limitπLinearMap [Small.{u} (sectionsLieSubalgebra F)] (j : J) :
    (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt →ₗ[R]
      ((F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).obj j) := by
  -- Route correction: define the projection directly on the type-valued limit carrier, rather
  -- than first comparing carriers with the module limit.
  refine
    { toFun := (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).π.app j
      map_smul' := ?_
      map_add' := ?_ }
  · intro x y
    -- Addition is handled by the same pointwise evaluation argument.
    simpa [Shrink.linearEquiv_apply, Types.Small.limitCone_π_app] using
      congrArg (fun s : (F ⋙ forget (LieAlgebraCat.{u} R)).sections => s.1 j)
        ((Shrink.linearEquiv R ((F ⋙ forget (LieAlgebraCat.{u} R)).sections)).map_add x y)
  · intro m x
    -- The projection is linear because evaluation of a compatible family commutes with scalars.
    simpa [Shrink.linearEquiv_apply, Types.Small.limitCone_π_app] using
      congrArg (fun s : (F ⋙ forget (LieAlgebraCat.{u} R)).sections => s.1 j)
        ((Shrink.linearEquiv R ((F ⋙ forget (LieAlgebraCat.{u} R)).sections)).map_smul m x)

/-- Helper for Lemma 6.15.2: the projections from the compatible-sections limit should be Lie
algebra morphisms. -/
def limitπLieHom [Small.{u} (sectionsLieSubalgebra F)] (j : J) :
    (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt →ₗ⁅R⁆ F.obj j := by
  -- Once the projection is explicit, bracket preservation is pointwise.
  exact
    { limitπLinearMap F j with
      map_lie' := by
        intro x y
        simpa [limitπLinearMap, Types.Small.limitCone_π_app, LieHom.coe_mk, LinearMap.coe_mk,
          LieAlgebraCat.Shrink.lieEquiv] using
          congrArg (fun s : (F ⋙ forget (LieAlgebraCat.{u} R)).sections => s.1 j)
            ((LieAlgebraCat.Shrink.lieEquiv
              (R := R) (L := (F ⋙ forget (LieAlgebraCat.{u} R)).sections)).map_lie x y) }

/-- Helper for Lemma 6.15.2: the explicit cone of compatible families in `LieAlgebraCat`. -/
def limitCone [Small.{u} (sectionsLieSubalgebra F)] : Cone F := by
  -- Package the pointwise projections into the candidate Lie-algebra limit cone.
  refine
    { pt := LieAlgebraCat.of R ((Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt)
      π :=
        { app := fun j ↦ limitπLieHom F j
          naturality := ?_ } }
  intro j j' f
  apply LieAlgebraCat.hom_ext
  intro x
  exact congr_fun ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) x

/-- Helper for Lemma 6.15.2: the compatible-sections cone should satisfy the universal property of
the limit in `LieAlgebraCat`. -/
def limitConeIsLimit [Small.{u} (sectionsLieSubalgebra F)] :
    IsLimit (limitCone F) := by
  -- Route correction: inherit the linear universal property from the module-valued limit cone,
  -- and only prove bracket preservation pointwise on the compatible-family projections.
  let hModule :
      IsLimit ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCone (limitCone F)) := by
    simpa [limitCone, limitπLieHom, limitπLinearMap] using
      (ModuleCat.HasLimits.limitConeIsLimit
        (F := F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)))
  refine IsLimit.ofFaithful (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) hModule
    (fun s ↦
      show s.pt →ₗ⁅R⁆ LieAlgebraCat.of R ((Types.Small.limitCone (F ⋙ forget _)).pt) from
        { toLinearMap := (hModule.lift ((forget₂ _ _).mapCone s)).hom
          map_lie' := ?_ })
    (fun _ ↦ rfl)
  intro x y
  let liftLinear : s.pt →ₗ[R] (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt :=
    (hModule.lift ((forget₂ _ _).mapCone s)).hom
  let xy : s.pt := ⁅x, y⁆
  let liftxy : (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt :=
    ⁅liftLinear x, liftLinear y⁆
  -- Compare the two candidate brackets after projecting to every component of the section.
  apply Types.Small.limitCone_pt_ext
  ext j
  change
    (limitπLieHom F j) (liftLinear xy) =
      (limitπLieHom F j) liftxy
  have hfac_lie :
      (limitπLieHom F j) (liftLinear xy) = (s.π.app j) xy := by
    simpa [limitπLieHom, limitπLinearMap] using
      (ConcreteCategory.congr_hom (hModule.fac ((forget₂ _ _).mapCone s) j)) xy
  have hfac_x : (limitπLieHom F j) (liftLinear x) = (s.π.app j) x := by
    simpa [limitπLieHom, limitπLinearMap] using
      (ConcreteCategory.congr_hom (hModule.fac ((forget₂ _ _).mapCone s) j)) x
  have hfac_y : (limitπLieHom F j) (liftLinear y) = (s.π.app j) y := by
    simpa [limitπLieHom, limitπLinearMap] using
      (ConcreteCategory.congr_hom (hModule.fac ((forget₂ _ _).mapCone s) j)) y
  calc
    (limitπLieHom F j) (liftLinear xy) = (s.π.app j) xy := hfac_lie
    _ = ⁅(s.π.app j) x, (s.π.app j) y⁆ := by
      simpa [xy] using LieHom.map_lie (s.π.app j) x y
    _ = ⁅(limitπLieHom F j) (liftLinear x), (limitπLieHom F j) (liftLinear y)⁆ := by
      rw [hfac_x, hfac_y]
    _ = (limitπLieHom F j) liftxy := by
      symm
      simpa [liftxy] using LieHom.map_lie (limitπLieHom F j) (liftLinear x) (liftLinear y)

/-- Helper for Lemma 6.15.2: a small compatible-sections Lie algebra diagram has a limit. -/
instance hasLimit [Small.{u} (sectionsLieSubalgebra F)] : HasLimit F :=
  HasLimit.mk
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

/-- Helper for Lemma 6.15.2: small indexing categories admit explicit limits in
`LieAlgebraCat`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J (LieAlgebraCat.{u} R) where
  has_limit _ := inferInstance

/-- Helper for Lemma 6.15.2: forgetting `LieAlgebraCat` to `ModuleCat` preserves the explicit
compatible-sections limit cone. -/
noncomputable instance forget₂Module_preservesLimit [Small.{u} (sectionsLieSubalgebra F)] :
    PreservesLimit F (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) :=
  preservesLimit_of_preserves_limit_cone (limitConeIsLimit F) <| by
    -- The mapped Lie limit cone is definitionally the module limit cone on the underlying
    -- module-valued diagram.
    simpa [limitCone, limitπLieHom, limitπLinearMap] using
      (ModuleCat.HasLimits.limitConeIsLimit
        (F := F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)))

/-- Helper for Lemma 6.15.2: forgetting to types preserves the explicit compatible-sections
limits. -/
noncomputable instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget (LieAlgebraCat.{u} R)) where
  preservesLimit := fun {K} ↦
    preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
      (Types.Small.limitConeIsLimit (K ⋙ forget (LieAlgebraCat.{u} R)))

end HasLimits

/-- Helper for Lemma 6.15.2: forgetting `LieAlgebraCat` to `ModuleCat` preserves the explicit
compatible-sections limits. -/
theorem forget₂Module_preservesLimits_aux (R : Type u) [CommRing R] :
    PreservesLimits (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) := by
  -- Assemble the shape-wise preservation result from the explicit cone comparison above.
  refine
    { preservesLimitsOfShape := fun {J} _ ↦
        { preservesLimit := fun {F} ↦ by infer_instance } }

/-- Helper for Lemma 6.15.2: the remaining limit-side step is to equip the compatible families in
the underlying module limit with the pointwise Lie bracket and prove the resulting cone is a limit.
-/
theorem hasLimits_aux (R : Type u) [CommRing R] : HasLimits (LieAlgebraCat.{u} R) := by
  -- The explicit compatible-sections limit exists for every small indexing category.
  refine
    { has_limits_of_shape := fun J _ ↦
        { has_limit := fun F ↦ by
            letI : Small.{u} J := by infer_instance
            infer_instance } }

/-- Helper for Lemma 6.15.2: once the compatible-sections limit cone is in place, forgetting to the
underlying module preserves limits by direct cone comparison. -/
theorem forget_preservesLimits_aux (R : Type u) [CommRing R] :
    PreservesLimits (forget (LieAlgebraCat.{u} R)) := by
  -- Each explicit Lie limit cone maps to the standard type-valued limit cone.
  refine
    { preservesLimitsOfShape := fun {J} _ ↦
        { preservesLimit := fun {F} ↦ by
            letI : Small.{u} J := by infer_instance
            infer_instance } }

instance hasLimits (R : Type u) [CommRing R] : HasLimits (LieAlgebraCat.{u} R) :=
  hasLimits_aux (R := R)

instance forget_preservesLimits (R : Type u) [CommRing R] :
    PreservesLimits (forget (LieAlgebraCat.{u} R)) :=
  forget_preservesLimits_aux (R := R)

end Limits

section ReflectsIso

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 6.15.2: a bijective Lie algebra morphism is an isomorphism, via the inverse
Lie equivalence on the underlying types. -/
theorem lie_isIso_of_bijective {L M : LieAlgebraCat.{u} R} (f : L ⟶ M)
    (hf : Function.Bijective f) : IsIso f := by
  -- A bijective Lie morphism upgrades to a Lie equivalence, and that equivalence supplies the
  -- inverse categorical morphism.
  let e : L ≃ₗ⁅R⁆ M := LieEquiv.ofBijective f hf
  let i : L ≅ M :=
    { hom := e.toLieHom
      inv := e.symm.toLieHom
      hom_inv_id := by
        ext x
        exact e.symm_apply_apply x
      inv_hom_id := by
        ext x
        exact e.apply_symm_apply x }
  have hhom : i.hom = f := by
    ext x
    rfl
  simpa [hhom] using i.isIso_hom

instance forget_reflectsIsomorphisms (R : Type u) [CommRing R] :
    (forget (LieAlgebraCat.{u} R)).ReflectsIsomorphisms where
  reflects f :=
    lie_isIso_of_bijective (R := R) f <|
      (CategoryTheory.isIso_iff_bijective ((forget (LieAlgebraCat.{u} R)).map f)).mp inferInstance

end ReflectsIso

section FilteredColimits

variable {R : Type u} [CommRing R]

namespace FilteredColimits

open CategoryTheory.IsFiltered renaming max → max'

variable {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ LieAlgebraCat.{u} R)

/-- Helper for Lemma 6.15.2: the filtered diagram of underlying modules attached to a Lie-algebra
diagram. -/
abbrev underlyingModuleDiagram : J ⥤ ModuleCat.{u} R :=
  F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)

/-- Helper for Lemma 6.15.2: the representative-level Lie bracket on the underlying module
filtered colimit. -/
noncomputable def colimitLieAux (x y : Σ j, F.obj j) :
    ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F) :=
  ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F)
    ⟨max' x.1 y.1, (⁅(F.map (IsFiltered.leftToMax x.1 y.1) x.2 : F.obj (max' x.1 y.1)),
      (F.map (IsFiltered.rightToMax x.1 y.1) y.2 : F.obj (max' x.1 y.1))⁆ :
        F.obj (max' x.1 y.1))⟩

/-- Helper for Lemma 6.15.2: the representative-level Lie bracket is compatible with changing the
left representative in the filtered-colimit relation. -/
theorem colimitLieAux_eq_of_rel_left {x x' y : Σ j, F.obj j}
    (hxx' : Types.FilteredColimit.Rel
      ((underlyingModuleDiagram (R := R) F) ⋙ forget (ModuleCat.{u} R)) x x') :
    colimitLieAux (R := R) F x y = colimitLieAux (R := R) F x' y := by
  -- Compare the two source representatives after moving every bracket term to one common object.
  obtain ⟨j₁, x⟩ := x
  obtain ⟨j₂, y⟩ := y
  obtain ⟨j₃, x'⟩ := x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  replace hfg : F.map f x = F.map g x' := by
    simpa using hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.leftToMax j₁ j₂) (IsFiltered.rightToMax j₁ j₂)
      (IsFiltered.rightToMax j₃ j₂) (IsFiltered.leftToMax j₃ j₂) f g
  apply ModuleCat.FilteredColimits.M.mk_eq
  use s, α, γ
  dsimp [colimitLieAux, underlyingModuleDiagram]
  change (F.map α) ⁅(F.map (IsFiltered.leftToMax j₁ j₂)) x, (F.map (IsFiltered.rightToMax j₁ j₂)) y⁆ =
    (F.map γ) ⁅(F.map (IsFiltered.leftToMax j₃ j₂)) x', (F.map (IsFiltered.rightToMax j₃ j₂)) y⁆
  rw [LieHom.map_lie, LieHom.map_lie]
  simp_rw [← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    ConcreteCategory.comp_apply, hfg]

/-- Helper for Lemma 6.15.2: the representative-level Lie bracket is compatible with changing the
right representative in the filtered-colimit relation. -/
theorem colimitLieAux_eq_of_rel_right {x y y' : Σ j, F.obj j}
    (hyy' : Types.FilteredColimit.Rel
      ((underlyingModuleDiagram (R := R) F) ⋙ forget (ModuleCat.{u} R)) y y') :
    colimitLieAux (R := R) F x y = colimitLieAux (R := R) F x y' := by
  -- The right-variable compatibility is the symmetric tulip comparison.
  obtain ⟨j₁, y⟩ := y
  obtain ⟨j₂, x⟩ := x
  obtain ⟨j₃, y'⟩ := y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  replace hfg : F.map f y = F.map g y' := by
    simpa using hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (IsFiltered.leftToMax j₂ j₁)
      (IsFiltered.leftToMax j₂ j₃) (IsFiltered.rightToMax j₂ j₃) f g
  apply ModuleCat.FilteredColimits.M.mk_eq
  use s, α, γ
  dsimp [colimitLieAux, underlyingModuleDiagram]
  change (F.map α) ⁅(F.map (IsFiltered.leftToMax j₂ j₁)) x, (F.map (IsFiltered.rightToMax j₂ j₁)) y⁆ =
    (F.map γ) ⁅(F.map (IsFiltered.leftToMax j₂ j₃)) x, (F.map (IsFiltered.rightToMax j₂ j₃)) y'⁆
  rw [LieHom.map_lie, LieHom.map_lie]
  simp_rw [← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    ConcreteCategory.comp_apply, hfg]

/-- Helper for Lemma 6.15.2: the filtered colimit of the underlying module diagram carries the
descended Lie bracket. -/
noncomputable instance colimitBracket :
    Bracket (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F))
      (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F)) := by
  -- Descend the representative-level bracket through the quotient presentation of the colimit.
  refine ⟨fun x y ↦ ?_⟩
  refine Quot.lift₂ (colimitLieAux (R := R) F) ?_ ?_ x y
  · intro x y y' h
    apply colimitLieAux_eq_of_rel_right
    exact Types.FilteredColimit.rel_of_colimitTypeRel _ _ _ h
  · intro x x' y h
    apply colimitLieAux_eq_of_rel_left
    exact Types.FilteredColimit.rel_of_colimitTypeRel _ _ _ h

/-- Helper for Lemma 6.15.2: the descended bracket on generators can be computed after moving to
any chosen common upper bound. -/
theorem colimit_lie_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    ⁅ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) x,
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) y⁆ =
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F)
        ⟨k, (⁅(F.map f x.2 : F.obj k), (F.map g y.2 : F.obj k)⁆ : F.obj k)⟩ := by
  -- Rewrite the default `max'`-based bracket through an arbitrary common upper bound.
  obtain ⟨j₁, x⟩ := x
  obtain ⟨j₂, y⟩ := y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  apply ModuleCat.FilteredColimits.M.mk_eq
  use s, α, β
  dsimp [colimitLieAux, underlyingModuleDiagram]
  change (F.map α) ⁅(F.map (IsFiltered.leftToMax j₁ j₂)) x, (F.map (IsFiltered.rightToMax j₁ j₂)) y⁆ =
    (F.map β) ⁅(F.map f) x, (F.map g) y⁆
  rw [LieHom.map_lie, LieHom.map_lie]
  simp_rw [← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂]

/-- Helper for Lemma 6.15.2: the descended bracket on two generators from the same object is the
expected image of the original bracket. -/
lemma colimit_lie_mk_eq' {j : J} (x y : F.obj j) :
    ⁅ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, x⟩,
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, y⟩⁆ =
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, (⁅x, y⁆ : F.obj j)⟩ := by
  -- Specialize the common-upper-bound formula to the identity maps.
  simpa using colimit_lie_mk_eq (R := R) (F := F) ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)

/-- Helper for Lemma 6.15.2: the filtered colimit of the underlying module diagram inherits the
Lie-ring structure of the source diagram. -/
noncomputable instance colimitLieRing :
    LieRing (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F)) := by
  refine
    { add_lie := ?_
      lie_add := ?_
      lie_self := ?_
      leibniz_lie := ?_ }
  · intro x y z
    -- Reduce to generators and move the three representatives to one common upper bound.
    obtain ⟨i, x, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
    obtain ⟨j, y, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
    obtain ⟨k, z, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) z
    let m : J := IsFiltered.max₃ i j k
    let fi : i ⟶ m := IsFiltered.firstToMax₃ i j k
    let fj : j ⟶ m := IsFiltered.secondToMax₃ i j k
    let fk : k ⟶ m := IsFiltered.thirdToMax₃ i j k
    rw [← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fi x,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fj y,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fk z,
      ModuleCat.FilteredColimits.colimit_add_mk_eq', colimit_lie_mk_eq', colimit_lie_mk_eq',
      colimit_lie_mk_eq', ModuleCat.FilteredColimits.colimit_add_mk_eq']
    exact congrArg
      (fun w : F.obj m ↦
        ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨m, w⟩)
      (add_lie ((F.map fi x : F.obj m)) ((F.map fj y : F.obj m)) ((F.map fk z : F.obj m)))
  · intro x y z
    -- The right-additivity proof uses the same common-upper-bound normalization.
    obtain ⟨i, x, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
    obtain ⟨j, y, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
    obtain ⟨k, z, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) z
    let m : J := IsFiltered.max₃ i j k
    let fi : i ⟶ m := IsFiltered.firstToMax₃ i j k
    let fj : j ⟶ m := IsFiltered.secondToMax₃ i j k
    let fk : k ⟶ m := IsFiltered.thirdToMax₃ i j k
    rw [← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fi x,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fj y,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fk z,
      ModuleCat.FilteredColimits.colimit_add_mk_eq', colimit_lie_mk_eq', colimit_lie_mk_eq',
      colimit_lie_mk_eq', ModuleCat.FilteredColimits.colimit_add_mk_eq']
    exact congrArg
      (fun w : F.obj m ↦
        ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨m, w⟩)
      (lie_add ((F.map fi x : F.obj m)) ((F.map fj y : F.obj m)) ((F.map fk z : F.obj m)))
  · intro x
    -- On a single generator, alternation reduces directly to the source Lie algebra.
    obtain ⟨j, x, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
    rw [colimit_lie_mk_eq', lie_self]
    simpa using
      (ModuleCat.FilteredColimits.colimit_zero_eq (underlyingModuleDiagram (R := R) F) j).symm
  · intro x y z
    -- After moving to one object, the Leibniz identity is the source identity.
    obtain ⟨i, x, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
    obtain ⟨j, y, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
    obtain ⟨k, z, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) z
    let m : J := IsFiltered.max₃ i j k
    let fi : i ⟶ m := IsFiltered.firstToMax₃ i j k
    let fj : j ⟶ m := IsFiltered.secondToMax₃ i j k
    let fk : k ⟶ m := IsFiltered.thirdToMax₃ i j k
    rw [← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fi x,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fj y,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fk z,
      colimit_lie_mk_eq', colimit_lie_mk_eq', colimit_lie_mk_eq', colimit_lie_mk_eq',
      colimit_lie_mk_eq', colimit_lie_mk_eq', ModuleCat.FilteredColimits.colimit_add_mk_eq']
    exact congrArg
      (fun w : F.obj m ↦
        ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨m, w⟩)
      (leibniz_lie ((F.map fi x : F.obj m)) ((F.map fj y : F.obj m)) ((F.map fk z : F.obj m)))

/-- Helper for Lemma 6.15.2: the descended bracket is compatible with the scalar action on the
filtered colimit module. -/
noncomputable instance colimitLieAlgebra :
    LieAlgebra R (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F)) := by
  refine
    { lie_smul := ?_ }
  intro r x y
  -- Move the two representatives to one object, then rewrite the scalar action and the bracket.
  obtain ⟨i, x, rfl⟩ :=
    ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
  obtain ⟨j, y, rfl⟩ :=
    ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
  let k : J := max' i j
  let f : i ⟶ k := IsFiltered.leftToMax i j
  let g : j ⟶ k := IsFiltered.rightToMax i j
  rw [← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) f x,
    ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) g y,
    ModuleCat.FilteredColimits.colimit_smul_mk_eq, colimit_lie_mk_eq', colimit_lie_mk_eq',
    ModuleCat.FilteredColimits.colimit_smul_mk_eq]
  exact congrArg
    (fun w : F.obj k ↦
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨k, w⟩)
    (LieAlgebra.lie_smul r ((F.map f x : F.obj k)) ((F.map g y : F.obj k)))

/-- Helper for Lemma 6.15.2: the bundled Lie algebra realizing the filtered colimit of the
diagram. -/
noncomputable def colimit : LieAlgebraCat.{u} R :=
  LieAlgebraCat.of R (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F))

/-- Helper for Lemma 6.15.2: each object of the diagram maps into the explicit filtered colimit by
the canonical generator map. -/
noncomputable def coconeMorphism (j : J) : F.obj j ⟶ colimit (R := R) F := by
  -- Reuse the module-level generator map and prove bracket preservation on same-object generators.
  exact
    { toLinearMap :=
        (ModuleCat.FilteredColimits.coconeMorphism (underlyingModuleDiagram (R := R) F) j).hom
      map_lie' := by
        intro x y
        symm
        simpa using colimit_lie_mk_eq' (R := R) (F := F) x y
    }

/-- Helper for Lemma 6.15.2: the underlying linear map of the Lie cocone morphism is exactly the
module filtered-colimit cocone map. -/
theorem coconeMorphism_underlying_eq (j : J) :
    (coconeMorphism (R := R) F j).toLinearMap =
      (ModuleCat.FilteredColimits.coconeMorphism (underlyingModuleDiagram (R := R) F) j).hom :=
  rfl

/-- Helper for Lemma 6.15.2: the explicit cocone over the filtered diagram of Lie algebras. -/
noncomputable def colimitCocone : Cocone F where
  pt := colimit (R := R) F
  ι :=
    { app := coconeMorphism (R := R) F
      naturality := by
        intro j j' f
        -- Naturality is inherited from the module cocone after forgetting the Lie bracket.
        apply LieAlgebraCat.hom_ext
        intro x
        simpa [coconeMorphism, colimit] using
          ConcreteCategory.congr_hom
            ((ModuleCat.FilteredColimits.colimitCocone
              (underlyingModuleDiagram (R := R) F)).ι.naturality f) x }

/-- Helper for Lemma 6.15.2: the universal Lie morphism from the explicit filtered colimit to any
other cocone point. -/
noncomputable def colimitDesc (t : Cocone F) : colimit (R := R) F ⟶ t.pt := by
  -- Reuse the module universal morphism and verify Lie compatibility on generators.
  let f :
      ModuleCat.FilteredColimits.colimit (underlyingModuleDiagram (R := R) F) ⟶
        ModuleCat.of R t.pt :=
    ModuleCat.FilteredColimits.colimitDesc (underlyingModuleDiagram (R := R) F)
      ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCocone t)
  have hf {j : J} (x : F.obj j) :
      f (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, x⟩) = t.ι.app j x :=
    ConcreteCategory.congr_hom
      (ModuleCat.FilteredColimits.ι_colimitDesc (underlyingModuleDiagram (R := R) F)
        ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCocone t) j) x
  exact
    { toLinearMap := f.hom
      map_lie' := by
        intro x y
        obtain ⟨i, x, rfl⟩ :=
          ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
        obtain ⟨j, y, rfl⟩ :=
          ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
        let xi : t.pt := t.ι.app i x
        let yj : t.pt := t.ι.app j y
        let xik : t.pt := t.ι.app (max' i j) (F.map (IsFiltered.leftToMax i j) x)
        let yjk : t.pt := t.ι.app (max' i j) (F.map (IsFiltered.rightToMax i j) y)
        -- Compute the bracket at the canonical common upper bound and then use the cocone laws.
        have hcolimit :
            f.hom
                ((⁅ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨i, x⟩,
                    ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, y⟩⁆) :
                  ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F))
              =
              f.hom
                (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F)
                  ⟨max' i j,
                    (⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
                      (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆ :
                        F.obj (max' i j))⟩) := by
          exact congrArg f.hom
            (colimit_lie_mk_eq (R := R) (F := F) ⟨i, x⟩ ⟨j, y⟩ (max' i j)
              (IsFiltered.leftToMax i j) (IsFiltered.rightToMax i j))
        have hdesc :
            f.hom
                (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F)
                  ⟨max' i j,
                    (⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
                      (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆ :
                        F.obj (max' i j))⟩)
              =
              ((t.ι.app (max' i j)
                (⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
                  (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆ :
                    F.obj (max' i j))) : t.pt) := by
          simpa using hf (j := max' i j)
            ((⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
              (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆ :
                F.obj (max' i j)))
        have hmap :
            ((t.ι.app (max' i j))
              (⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
                (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆) : t.pt) =
              (⁅xik, yjk⁆ : t.pt) := by
          simpa using LieHom.map_lie (t.ι.app (max' i j))
            (F.map (IsFiltered.leftToMax i j) x)
            (F.map (IsFiltered.rightToMax i j) y)
        have hleft : xik = xi := by
          change t.ι.app (max' i j) (F.map (IsFiltered.leftToMax i j) x) = t.ι.app i x
          exact ConcreteCategory.congr_hom (t.w (IsFiltered.leftToMax i j)) x
        have hright : yjk = yj := by
          change t.ι.app (max' i j) (F.map (IsFiltered.rightToMax i j) y) = t.ι.app j y
          exact ConcreteCategory.congr_hom (t.w (IsFiltered.rightToMax i j)) y
        have hfx : (f.hom) (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨i, x⟩) = xi := by
          simpa [xi] using hf (j := i) x
        have hfy : (f.hom) (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, y⟩) = yj := by
          simpa [yj] using hf (j := j) y
        exact hcolimit.trans <| hdesc.trans <| by
          rw [hmap, hleft, hright, ← hfx, ← hfy]
          rfl
    }

/-- Helper for Lemma 6.15.2: the underlying linear map of the universal Lie morphism is exactly
the module filtered-colimit desc map. -/
theorem colimitDesc_underlying_eq (t : Cocone F) :
    (colimitDesc (R := R) F t).toLinearMap =
      (ModuleCat.FilteredColimits.colimitDesc (underlyingModuleDiagram (R := R) F)
        ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCocone t)).hom :=
  rfl

/-- Helper for Lemma 6.15.2: the universal Lie morphism restricts to the given cocone map on each
diagram object. -/
@[reassoc (attr := simp)] theorem ι_colimitDesc (t : Cocone F) (j : J) :
    (colimitCocone (R := R) F).ι.app j ≫ colimitDesc (R := R) F t = t.ι.app j := by
  -- Forget to modules, where this is the standard filtered-colimit computation.
  apply LieAlgebraCat.hom_ext
  intro x
  simpa [colimitCocone, coconeMorphism, colimitDesc, colimit] using
    ConcreteCategory.congr_hom
      (ModuleCat.FilteredColimits.ι_colimitDesc (underlyingModuleDiagram (R := R) F)
        ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCocone t) j) x

/-- Helper for Lemma 6.15.2: the explicit Lie-algebra filtered-colimit cocone satisfies the
universal property. -/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone (R := R) F) where
  desc := colimitDesc (R := R) F
  fac t j := by
    simpa using ι_colimitDesc (R := R) (F := F) t j
  uniq t m h := by
    -- Extensionality reduces uniqueness to generator classes of the module colimit.
    apply LieAlgebraCat.hom_ext
    intro y
    obtain ⟨j, y, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
    simpa [colimitCocone, coconeMorphism, colimitDesc, colimit] using
      (ConcreteCategory.congr_hom (h j) y).trans
        (ConcreteCategory.congr_hom (ι_colimitDesc (R := R) (F := F) t j) y).symm

end FilteredColimits

/-- Helper for Lemma 6.15.2: the remaining source-faithful step is to put the Lie bracket on the
filtered colimit of the underlying module diagram and prove its universal property. -/
theorem hasFilteredColimits_aux (R : Type u) [CommRing R] :
    HasFilteredColimits (LieAlgebraCat.{u} R) := by
  -- Every filtered diagram gets the explicit cocone constructed above.
  refine
    { HasColimitsOfShape := fun J _ _ ↦
        ⟨fun F ↦ ⟨FilteredColimits.colimitCocone (R := R) F,
          FilteredColimits.colimitCoconeIsColimit (R := R) F⟩⟩ }

/-- Helper for Lemma 6.15.2: once the Lie bracket on filtered colimits is in place, forgetting to
modules preserves those filtered colimits by comparison with the underlying module cocone. -/
theorem forget₂Module_preservesFilteredColimits_aux (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) := by
  -- The explicit Lie filtered-colimit cocone forgets to the standard module filtered-colimit
  -- cocone.
  refine
    { preserves_filtered_colimits := fun J _ _ ↦
        ⟨fun {F} ↦
          preservesColimit_of_preserves_colimit_cocone
            (FilteredColimits.colimitCoconeIsColimit (R := R) F) <| by
              simpa [FilteredColimits.colimitCocone, FilteredColimits.coconeMorphism,
                FilteredColimits.colimit, FilteredColimits.colimitDesc] using
                (ModuleCat.FilteredColimits.colimitCoconeIsColimit
                  (FilteredColimits.underlyingModuleDiagram (R := R) F))⟩ }

instance hasFilteredColimits (R : Type u) [CommRing R] :
    HasFilteredColimits (LieAlgebraCat.{u} R) :=
  hasFilteredColimits_aux (R := R)

instance forget₂Module_preservesFilteredColimits (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) :=
  forget₂Module_preservesFilteredColimits_aux (R := R)

instance forget_preservesFilteredColimits (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget (LieAlgebraCat.{u} R)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (LieAlgebraCat R) (ModuleCat R))
    (forget (ModuleCat.{u} R))

end FilteredColimits

end LieAlgebraCat

/-- Lemma 6.15.2 (7): for a fixed commutative ring `R`, the category of Lie algebras over `R`, with its
forgetful functor to sets, defines a type of algebraic structures. -/
instance lie_algebras_algebraic_structure_type (R : Type u) [CommRing R] :
    IsAlgebraicStructure (LieAlgebraCat.{u} R) (forget (LieAlgebraCat.{u} R)) := by
  -- Route correction: the Lie-algebra limit and filtered-colimit constructions are already proved.
  -- The remaining work is only to supply those instances at the exact inherited parent types.
  letI : HasLimitsOfSize.{u, u} (LieAlgebraCat.{u} R) :=
    show HasLimitsOfSize.{u, u} (LieAlgebraCat.{u} R) from LieAlgebraCat.hasLimits (R := R)
  letI : PreservesLimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} R)) :=
    show PreservesLimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} R)) from
      LieAlgebraCat.forget_preservesLimits (R := R)
  letI : HasFilteredColimitsOfSize.{u, u} (LieAlgebraCat.{u} R) :=
    show HasFilteredColimitsOfSize.{u, u} (LieAlgebraCat.{u} R) from
      LieAlgebraCat.hasFilteredColimits (R := R)
  letI : PreservesFilteredColimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} R)) :=
    show PreservesFilteredColimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} R)) from
      LieAlgebraCat.forget_preservesFilteredColimits (R := R)
  letI : (forget (LieAlgebraCat.{u} R)).ReflectsIsomorphisms :=
    LieAlgebraCat.forget_reflectsIsomorphisms (R := R)
  -- With the exact parent classes in scope, the bundled algebraic-structure predicate follows.
  exact
    IsAlgebraicStructure.mk (C := LieAlgebraCat.{u} R) (F := forget (LieAlgebraCat.{u} R))

/-! ### Lemma_6_15_3 (from Chap06) -/
open CategoryTheory
open CategoryTheory.Limits

universe w v u

/- Domain-style sampling for algebraic-structure forgetful functors:
- primary domain: forgetful functors `F : C ⥤ Type w` satisfying the chapter owner predicate
  `IsAlgebraicStructure C F`, together with the canonical comparison isomorphisms expressing the
  source-level identifications of underlying sets for limits and filtered colimits;
- inspected owner declarations:
  `PreservesTerminal.iso`,
  `PreservesProduct.iso`,
  `PreservesPullback.iso`,
  `preservesColimitIso`;
- best owner abstraction:
  the chapter-level owner is `IsAlgebraicStructure C F`, while the main public surface here should
  directly reuse the corresponding comparison isomorphisms rather than restating only their
  projection formulas;
- primitive-vs-derived split:
  primitive data are exactly the fields of `IsAlgebraicStructure C F`;
  terminal/product/pullback/equalizer/filtered-colimit identifications and mono/epi detection are
  derived API, while the induced `ConcreteCategory` structure is only a local bridge for (5) and
  (6).

Source/core/bridge triage:
- `source-facing`: the six clauses of Lemma 6.15.3 about underlying sets and underlying maps for a
  type of algebraic structure;
- `core/canonical`: the preservation comparison isomorphisms and the concrete-category mono/epi
  theorems from mathlib;
- `bridge/view`: the concrete-category structure induced by `F`, used only to access the mono/epi
  owner theorems.
-/

section Terminal

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

/- Lemma 6.15.3 (1): the underlying type of the terminal algebraic structure is canonically
identified with the singleton type. The owner comparison is `PreservesTerminal.iso`, specialized
through `Types.terminalIso`. -/
recall PreservesTerminal.iso

/- Source-facing specialization of the terminal comparison to `PUnit`. -/
#check ((((PreservesTerminal.iso F) ≪≫ Types.terminalIso).toEquiv) :
  F.obj (⊤_ C) ≃ PUnit)

/-- Companion formula: under the canonical terminal identification, every element maps to the
unique point. -/
theorem terminalUnderlyingEquiv_apply (x : F.obj (⊤_ C)) :
    ((PreservesTerminal.iso F ≪≫ Types.terminalIso).hom) x = PUnit.unit := by
  simp

end Terminal

section Products

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
variable {ι : Type w} (A : ι → C) [HasProduct A] [PreservesLimit (Discrete.functor A) F]

/- Lemma 6.15.3 (2): the underlying type of a product is identified with the product of the
underlying types by the canonical owner comparison `PreservesProduct.iso`. -/
recall PreservesProduct.iso

/- Source-facing specialization of the product comparison isomorphism. -/
#check (PreservesProduct.iso F A : F.obj (∏ᶜ A) ≅ ∏ᶜ fun i ↦ F.obj (A i))

/-- Companion formula: the canonical product comparison recovers each underlying projection. -/
theorem productUnderlying_apply (x : F.obj (∏ᶜ A)) (i : ι) :
    Pi.π (fun j ↦ F.obj (A j)) i ((PreservesProduct.iso F A).hom x) =
      F.map (Pi.π A i) x := by
  letI : HasProduct (fun j ↦ F.obj (A j)) := inferInstance
  simpa [PreservesProduct.iso_hom] using congr_fun (piComparison_comp_π F A i) x

end Products

section PullbacksAndEqualizers

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

variable {A B C' : C} (f : A ⟶ B) (g : C' ⟶ B) [HasPullback f g]

/- Lemma 6.15.3 (3): the underlying type of a fibre product is identified with the pullback of the
underlying maps by the canonical owner comparison `PreservesPullback.iso`. -/
recall PreservesPullback.iso

/- Source-facing specialization of the pullback comparison isomorphism. -/
#check (PreservesPullback.iso F f g : F.obj (pullback f g) ≅ pullback (F.map f) (F.map g))

/-- Companion formula: the canonical pullback comparison is compatible with the left projection. -/
theorem pullbackUnderlying_fst_apply (x : F.obj (pullback f g)) :
    pullback.fst (F.map f) (F.map g) ((PreservesPullback.iso F f g).hom x) =
      F.map (pullback.fst f g) x := by
  simpa using congr_fun (PreservesPullback.iso_hom_fst F f g) x

variable {A' B' : C} (f' g' : A' ⟶ B') [HasEqualizer f' g']

/- Lemma 6.15.3 (4): the underlying type of an equalizer is identified with the equalizer of the
underlying maps by the canonical owner comparison `PreservesEqualizer.iso`. -/
recall PreservesEqualizer.iso

/- Source-facing specialization of the equalizer comparison isomorphism. -/
#check (PreservesEqualizer.iso F f' g' :
  F.obj (equalizer f' g') ≅ equalizer (F.map f') (F.map g'))

/-- Companion formula: the canonical equalizer comparison is compatible with the equalizer
inclusion. -/
theorem equalizerUnderlying_apply (x : F.obj (equalizer f' g')) :
    equalizer.ι (F.map f') (F.map g') ((PreservesEqualizer.iso F f' g').hom x) =
      F.map (equalizer.ι f' g') x := by
  simpa [PreservesEqualizer.iso_hom] using congr_fun (equalizerComparison_comp_π f' g' F) x

end PullbacksAndEqualizers

section MonoEpi

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

/-- Helper for Lemma 6.15.3: a mono becomes an injective underlying map after applying the
forgetful functor to types. -/
lemma underlying_injective_of_mono
    {A B : C} (f : A ⟶ B) [Mono f] :
    Function.Injective (F.map f) := by
  -- Map the mono into `Type` and read the result with the standard concrete criterion there.
  letI : Mono (F.map f) := F.map_mono f
  exact (CategoryTheory.mono_iff_injective (F.map f)).1 inferInstance

/-- Helper for Lemma 6.15.3: injectivity of the underlying map makes the mapped kernel-pair
projection an isomorphism. -/
lemma mapped_pullback_fst_isIso_of_underlying_injective
    {A B : C} (f : A ⟶ B) [HasPullback f f] [PreservesLimit (cospan f f) F]
    (hf : Function.Injective (F.map f)) :
    IsIso (F.map (pullback.fst f f)) := by
  -- The kernel pair of an injective map in `Type` has first projection an isomorphism.
  letI : Mono (F.map f) := (CategoryTheory.mono_iff_injective (F.map f)).2 hf
  -- Transport the `Type`-level kernel-pair isomorphism across the pullback comparison of `F`.
  have hcomparison_iso :
      IsIso ((PreservesPullback.iso F f f).hom ≫ pullback.fst (F.map f) (F.map f)) := by
    infer_instance
  simpa [PreservesPullback.iso_hom_fst] using hcomparison_iso

/-- Helper for Lemma 6.15.3: if the underlying map is injective, then the original morphism is
mono. -/
lemma mono_of_underlying_injective
    {A B : C} (f : A ⟶ B) (hf : Function.Injective (F.map f)) :
    Mono f := by
  -- Route correction: rather than using the general concrete-category criterion directly, we
  -- follow the source proof through the kernel pair of `f`.
  let hshape : HasLimitsOfShape WalkingCospan C := inferInstance
  let hpres : PreservesLimitsOfShape WalkingCospan F := inferInstance
  letI : HasPullback f f := hshape.has_limit (cospan f f)
  letI : PreservesLimit (cospan f f) F := hpres.preservesLimit
  letI : IsIso (F.map (pullback.fst f f)) :=
    mapped_pullback_fst_isIso_of_underlying_injective F f hf
  -- Since `F` reflects isomorphisms, the kernel-pair projection is already an isomorphism in `C`.
  letI : IsIso (pullback.fst f f) := isIso_of_reflects_iso (pullback.fst f f) F
  -- An isomorphism on the first kernel-pair projection forces `f` to be mono.
  exact (pullback.diagonal_isKernelPair f).mono_of_isIso_fst

/-- Lemma 6.15.3 (5): a morphism is a monomorphism exactly when its underlying map of types is
injective. -/
theorem mono_iff_underlying_injective
    {A B : C} (f : A ⟶ B) :
    Mono f ↔ Function.Injective (F.map f) := by
  constructor
  · intro hf
    -- The forward direction is the direct image of a mono under `F`.
    letI : Mono f := hf
    exact underlying_injective_of_mono F f
  · intro hf
    -- The converse is the source-faithful kernel-pair argument.
    exact mono_of_underlying_injective F f hf

/-- Lemma 6.15.3 (6): if the underlying map of a morphism under a faithful functor to types is
surjective, then the morphism is an epimorphism. -/
theorem epi_of_underlying_surjective
    {A B : C} (f : A ⟶ B) (hf : Function.Surjective (F.map f)) :
    Epi f := by
  -- Surjectivity makes the mapped morphism epi in `Type`.
  letI : Epi (F.map f) := (CategoryTheory.epi_iff_surjective (F.map f)).2 hf
  -- Because `F` is faithful, it reflects epimorphisms back to `C`.
  exact F.epi_of_epi_map (f := f) inferInstance

end MonoEpi

section FilteredColimit

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
variable {I : Type v} [Category.{v} I] [IsFiltered I] (D : I ⥤ C)
variable [HasColimit D] [PreservesColimit D F]

/- The filtered-colimit clause of Lemma 6.15.3 is the canonical comparison isomorphism
`preservesColimitIso F D`; the cocone-leg formula is the companion theorem
`ι_preservesColimitIso_inv`. -/
recall preservesColimitIso

/- Source-facing specialization of the filtered-colimit comparison isomorphism. -/
#check (preservesColimitIso F D : F.obj (colimit D) ≅ colimit (D ⋙ F))

recall ι_preservesColimitIso_inv

end FilteredColimit

/-! ### Lemma_6_15_4 (from Chap06) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.Types

universe w v u

/-
Domain-style sampling for Lemma 6.15.4:
- primary domain: factorization of morphisms in a type of algebraic structure through a mono,
  detected on underlying sets via pullbacks;
- inspected owner declarations:
  `Subobject.Factors`,
  `Subobject.factorThru`,
  `CategoryTheory.mono_iff_injective`,
  `PreservesPullback.iso_hom_fst`;
- best owner abstraction:
  the canonical factorization owner is `Subobject.Factors`, while the textbook existential
  factorization through `g` is the source-facing statement obtained from that owner by passing to
  the underlying object of `Subobject.mk g`;
- primitive data:
  the morphisms `f`, `g`, the mono structure on `g` or equivalently the injectivity of `F.map g`,
  the range inclusion `Set.range (F.map f) ⊆ Set.range (F.map g)`, and the ambient functor
  hypotheses actually used by the proof: `F.Faithful`, pullbacks in `𝒞`, preservation of
  pullbacks by `F`, and `F.ReflectsIsomorphisms`;
- derived API:
  the witness morphism from `Subobject.factorThru` and the comparison isomorphism
  `Subobject.underlyingIso g`.

Source/core/bridge triage:
- `source-facing`: `morphism_factors_through_of_range_subset_of_injective`;
- `core/canonical`: `Subobject.Factors`;
- `bridge/view`: `subobject_factors_of_range_subset`, which packages the source factorization in the
  canonical subobject owner.
-/

section

variable {𝒞 : Type u} [Category.{v} 𝒞] (F : 𝒞 ⥤ Type w)
  [HasLimitsOfShape WalkingCospan 𝒞] [PreservesLimitsOfShape WalkingCospan F]
  [F.ReflectsIsomorphisms]

-- Proof sketch: form the pullback `A ×_B C` of `f` and `g`. The injectivity of `F.map g` and the
-- range inclusion `range (F.map f) ⊆ range (F.map g)` make the set-theoretic pullback projection
-- to `F.obj A` bijective. Via the pullback comparison isomorphism for `F`, this shows that
-- `pullback.fst f g` becomes an isomorphism under `F`; since `F` reflects isomorphisms, it is
-- already an isomorphism in `𝒞`. The desired factorization is then the canonical morphism through
-- the subobject `Subobject.mk g`.
theorem subobject_factors_of_range_subset
    {A B C : 𝒞} (f : A ⟶ B) (g : C ⟶ B) [Mono g]
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    (Subobject.mk g).Factors f := by
  have hg_injective : Function.Injective (F.map g) :=
    (mono_iff_injective _).1 inferInstance
  have hfst_bijective : Function.Bijective (pullback.fst (F.map f) (F.map g)) := by
    have hcond :
        pullback.fst (F.map f) (F.map g) ≫ F.map f =
          pullback.snd (F.map f) (F.map g) ≫ F.map g :=
      pullback.condition
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply ext_of_isPullback (IsPullback.of_hasPullback (F.map f) (F.map g)) hxy
      apply hg_injective
      calc
        F.map g (pullback.snd (F.map f) (F.map g) x)
            = F.map f (pullback.fst (F.map f) (F.map g) x) := by
                simpa using congr_fun hcond.symm x
        _ = F.map f (pullback.fst (F.map f) (F.map g) y) := by simp [hxy]
        _ = F.map g (pullback.snd (F.map f) (F.map g) y) := by
              simpa using congr_fun hcond y
    · intro a
      rcases hfg ⟨a, rfl⟩ with ⟨c, hc⟩
      rcases exists_of_isPullback (IsPullback.of_hasPullback (F.map f) (F.map g)) a c hc.symm with
        ⟨x, rfl, _⟩
      exact ⟨x, rfl⟩
  let hshape : HasLimitsOfShape WalkingCospan 𝒞 := inferInstance
  let hpres : PreservesLimitsOfShape WalkingCospan F := inferInstance
  letI : HasLimit (cospan f g) := hshape.has_limit (cospan f g)
  letI : PreservesLimit (cospan f g) F := hpres.preservesLimit
  have hcomparison_bijective :
      Function.Bijective ((PreservesPullback.iso F f g).hom ≫ pullback.fst (F.map f) (F.map g)) :=
    hfst_bijective.comp <| (isIso_iff_bijective _).1 inferInstance
  have hmap_fst_bijective : Function.Bijective (F.map (pullback.fst f g)) := by
    simpa [PreservesPullback.iso_hom_fst] using hcomparison_bijective
  haveI : IsIso (F.map (pullback.fst f g)) := (isIso_iff_bijective _).2 hmap_fst_bijective
  haveI : IsIso (pullback.fst f g) := by
    exact isIso_of_reflects_iso (pullback.fst f g) F
  refine (Subobject.mk_factors_iff g f).2 ?_
  refine ⟨inv (pullback.fst f g) ≫ pullback.snd f g, ?_⟩
  calc
    (inv (pullback.fst f g) ≫ pullback.snd f g) ≫ g
        = inv (pullback.fst f g) ≫ (pullback.snd f g ≫ g) := by simp [Category.assoc]
    _ = inv (pullback.fst f g) ≫ (pullback.fst f g ≫ f) := by rw [← pullback.condition]
    _ = f := by simp

/-- Lemma 6.15.4: under the faithful, pullback-preserving, and isomorphism-reflecting hypotheses
satisfied by a type of algebraic structure, if the underlying function of `g` is injective and the
image of the underlying function of `f` is contained in the image of the underlying function of
`g`, then `f` factors through `g`. -/
theorem morphism_factors_through_of_range_subset_of_injective
    {A B C : 𝒞} (f : A ⟶ B) (g : C ⟶ B)
    [F.Faithful]
    (hg_injective : Function.Injective (F.map g))
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    ∃ t : A ⟶ C, f = t ≫ g := by
  have hmap_mono : Mono (F.map g) := (mono_iff_injective _).2 hg_injective
  letI : F.ReflectsMonomorphisms := Functor.reflectsMonomorphisms_of_faithful F
  letI : Mono g := F.mono_of_mono_map hmap_mono
  have hfactor : (Subobject.mk g).Factors f := subobject_factors_of_range_subset F f g hfg
  refine ⟨(Subobject.mk g).factorThru f hfactor ≫ (Subobject.underlyingIso g).hom, ?_⟩
  rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  exact (Subobject.factorThru_arrow (Subobject.mk g) f hfactor).symm

end

/-! ### Example_6_15_5 (from Chap06) -/
open CategoryTheory

universe w v u

/- Domain-style sampling for algebraic-structure factorization and commutative squares:
- primary domain: factorization of morphisms in a type of algebraic structure from injectivity of
  the underlying map and containment of underlying ranges, with the result presented as a
  commutative square;
- sampled owner API:
  `morphism_factors_through_of_range_subset_of_injective`,
  `subobject_factors_of_range_subset`,
  `CategoryTheory.CommSq`,
  `CommSq.mk`;
- best owner abstraction:
  `morphism_factors_through_of_range_subset_of_injective` for the factorization itself, with
  `CommSq` as the canonical square-shaped surface;
- primitive data:
  the composite `ab ≫ bd`, the morphism `cd`, injectivity of `F.map cd`, and the range inclusion
  for `F.map (ab ≫ bd)`;
- derived API:
  the existential square witness below is only the specialization `f := ab ≫ bd`, `g := cd` of
  that owner theorem;
- layer:
  `bridge/view`, not a second owner theorem.

The target declaration should therefore reuse the owner theorem directly and only restate its
conclusion in the canonical `CommSq` form.
-/

section

variable {𝒞 : Type u} [Category.{v} 𝒞] (F : 𝒞 ⥤ Type w) [IsAlgebraicStructure 𝒞 F]
variable {A B C D : 𝒞} (ab : A ⟶ B) (bd : B ⟶ D) (cd : C ⟶ D)

-- Proof sketch: apply
-- `morphism_factors_through_of_range_subset_of_injective` to the composite `ab ≫ bd` and the map
-- `cd`; the resulting factorization `ab ≫ bd = t ≫ cd` is exactly the commutativity condition for
-- the square with top edge `ab`, left edge `t`, right edge `bd`, and bottom edge `cd`.
/-- Example 6.15.5: if `C ⟶ D` is injective on underlying sets and the image of the composite
`A ⟶ B ⟶ D` is contained in the image of `C ⟶ D`, then there exists a morphism `A ⟶ C` making
the resulting square commute. -/
theorem exists_commSq_of_composite_range_subset_of_injective
    (hg_injective : Function.Injective (F.map cd))
    (hfg : Set.range (F.map (ab ≫ bd)) ⊆ Set.range (F.map cd)) :
    ∃ t : A ⟶ C, CommSq ab t bd cd := by
  -- First factor the composite `A ⟶ B ⟶ D` through `cd` using the range criterion.
  rcases morphism_factors_through_of_range_subset_of_injective
      F (ab ≫ bd) cd hg_injective hfg with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  -- The factorization equality is exactly the commutativity condition for the square.
  exact CommSq.mk ht

end
