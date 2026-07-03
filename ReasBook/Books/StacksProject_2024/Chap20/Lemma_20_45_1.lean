import Mathlib
import StacksProject_2024.Chap06.Lemma_6_33_3
import StacksProject_2024.Chap20.Lemma_20_32_2
import StacksProject_2024.Chap20.Lemma_20_33_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- Restriction of `\mathcal O_U`-modules along an inclusion `W \subset U` is additive. -/
instance moduleSheafRestriction_additive
    {X : RingedSpace.{u}} {W U : Opens X.carrier} (h : W ≤ U) :
    (moduleSheafRestriction (RingedSpace.ringCatSheaf X) h).Additive := sorry

/-- Restriction of `\mathcal O_U`-modules along an inclusion `W \subset U` preserves finite
limits. -/
instance moduleSheafRestriction_preservesFiniteLimits
    {X : RingedSpace.{u}} {W U : Opens X.carrier} (h : W ≤ U) :
    PreservesFiniteLimits (moduleSheafRestriction (RingedSpace.ringCatSheaf X) h) := sorry

/-- Restriction of `\mathcal O_U`-modules along an inclusion `W \subset U` preserves finite
colimits. -/
instance moduleSheafRestriction_preservesFiniteColimits
    {X : RingedSpace.{u}} {W U : Opens X.carrier} (h : W ≤ U) :
    PreservesFiniteColimits (moduleSheafRestriction (RingedSpace.ringCatSheaf X) h) := sorry

/-- The derived category `D(\mathcal O_U)` attached to an open subset `U \subset X`, viewed via
the ambient structure sheaf restricted to `U`. -/
abbrev localModuleDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  DerivedCategory (SheafOfModules (ringSheafRestriction (RingedSpace.ringCatSheaf X) U))

/-- The ambient derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ambientModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- Restriction from `D(\mathcal O_U)` to `D(\mathcal O_{U \cap V})` along the left inclusion
`U \cap V \subset U`. -/
abbrev leftDerivedRestrictionToOverlap
    (X : RingedSpace.{u}) (U V : Opens X.carrier) :
    localModuleDerived X U ⥤ localModuleDerived X (U ⊓ V) :=
  (moduleSheafRestriction (RingedSpace.ringCatSheaf X) inf_le_left).mapDerivedCategory

/-- Restriction from `D(\mathcal O_V)` to `D(\mathcal O_{U \cap V})` along the right inclusion
`U \cap V \subset V`. -/
abbrev rightDerivedRestrictionToOverlap
    (X : RingedSpace.{u}) (U V : Opens X.carrier) :
    localModuleDerived X V ⥤ localModuleDerived X (U ⊓ V) :=
  (moduleSheafRestriction (RingedSpace.ringCatSheaf X) inf_le_right).mapDerivedCategory

/-- A glued ambient derived object for two opens `U` and `V`, together with chosen
identifications of its restrictions with the local objects and of its two overlap restrictions. -/
structure TwoOpenDerivedGluing
    (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (A : localModuleDerived X U) (B : localModuleDerived X V)
    (c : (leftDerivedRestrictionToOverlap X U V).obj A ≅
      (rightDerivedRestrictionToOverlap X U V).obj B) where
  /-- The ambient object of `D(\mathcal O_X)`. -/
  obj : ambientModuleDerived X
  /-- The identification of the restriction to `U` with the prescribed object `A`. -/
  leftIso : (moduleRestrictionToOpenDerived X U).obj obj ≅ A
  /-- The identification of the restriction to `V` with the prescribed object `B`. -/
  rightIso : (moduleRestrictionToOpenDerived X V).obj obj ≅ B
  /-- A chosen comparison between the two ways of restricting the ambient object to
  `U \cap V`. -/
  overlapIso :
    (leftDerivedRestrictionToOverlap X U V).obj ((moduleRestrictionToOpenDerived X U).obj obj) ≅
      (rightDerivedRestrictionToOverlap X U V).obj
        ((moduleRestrictionToOpenDerived X V).obj obj)
  /-- The chosen overlap comparison reproduces the prescribed overlap isomorphism `c`. -/
  compatibility :
    c = ((leftDerivedRestrictionToOverlap X U V).mapIso leftIso).symm ≪≫
      overlapIso ≪≫
      (rightDerivedRestrictionToOverlap X U V).mapIso rightIso

variable {X : RingedSpace.{u}} {U V : Opens X.carrier}
variable {A : localModuleDerived X U} {B : localModuleDerived X V}
variable {c : (leftDerivedRestrictionToOverlap X U V).obj A ≅
  (rightDerivedRestrictionToOverlap X U V).obj B}

-- Proof sketch: take the canonical morphism
-- `Rj_{U, *}A ⊞ Rj_{V, *}B ⟶ Rj_{U \cap V, *}(B|_{U \cap V})` built from the two restriction maps
-- and the overlap isomorphism `c`, then choose an object completing it to a distinguished
-- triangle. Restriction to `U` and `V` splits the displayed triangle, giving the two required
-- isomorphisms.
/-- Lemma 20.45.1: for a ringed space covered by two opens `U` and `V`, objects
`A ∈ D(\mathcal O_U)` and `B ∈ D(\mathcal O_V)`, and an isomorphism
`c : A|_{U \cap V} \xrightarrow{\sim} B|_{U \cap V}`, there exists an ambient object
`F ∈ D(\mathcal O_X)` whose restrictions to `U` and `V` are identified with `A` and `B`,
and whose chosen overlap comparison induces `c`. -/
theorem exists_two_open_derived_gluing
    (X : RingedSpace.{u}) (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (A : localModuleDerived X U) (B : localModuleDerived X V)
    (c : (leftDerivedRestrictionToOverlap X U V).obj A ≅
      (rightDerivedRestrictionToOverlap X U V).obj B) :
    Nonempty (TwoOpenDerivedGluing X U V A B c) := sorry

-- Proof sketch: apply Lemma `20.33.3` to the ambient glued object `glue.obj` and the target
-- object `E`. This yields the Mayer-Vietoris exact segment on morphisms from `glue.obj` to `E`,
-- which is the exact sequence used in the textbook proof of the lifting statement.
/-- A chosen gluing object satisfies the Mayer-Vietoris exact segment of morphisms into any
ambient derived object. -/
theorem TwoOpenDerivedGluing.mayer_vietoris_hom_exact_segment
    (glue : TwoOpenDerivedGluing X U V A B c) (hUV : U ⊔ V = ⊤)
    (E : ambientModuleDerived X) :
    ∃ δ :
        derived_open_ext_neg_one_group X (U ⊓ V) glue.obj E ⟶
          derived_hom_group X glue.obj E,
      ∃ α :
          derived_hom_group X glue.obj E ⟶
            derived_open_pair_hom_group X U V glue.obj E,
        ∃ β :
            derived_open_pair_hom_group X U V glue.obj E ⟶
              derived_open_hom_group X (U ⊓ V) glue.obj E,
          (mk₃ δ α β).Exact := sorry

-- Proof sketch: exactness at the middle term says that any element of the pairwise-restriction
-- group annihilated by the overlap-difference map `β` comes from a global morphism. This is the
-- Mayer-Vietoris lifting criterion underlying the textbook's “moreover” clause.
/-- A kernel element in the Mayer-Vietoris pairwise-restriction group lifts to a global morphism
out of a chosen gluing object. -/
theorem TwoOpenDerivedGluing.exists_hom_to_of_kernel
    (glue : TwoOpenDerivedGluing X U V A B c) (E : ambientModuleDerived X)
    (δ : derived_open_ext_neg_one_group X (U ⊓ V) glue.obj E ⟶
      derived_hom_group X glue.obj E)
    (α : derived_hom_group X glue.obj E ⟶
      derived_open_pair_hom_group X U V glue.obj E)
    (β : derived_open_pair_hom_group X U V glue.obj E ⟶
      derived_open_hom_group X (U ⊓ V) glue.obj E)
    (hexact : (mk₃ δ α β).Exact)
    (m : derived_open_pair_hom_group X U V glue.obj E)
    (hm : β.hom m = 0) :
    ∃ φ : glue.obj ⟶ E, α.hom φ = m := sorry

end AlgebraicGeometry.RingedSpace
