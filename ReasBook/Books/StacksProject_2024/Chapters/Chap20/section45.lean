import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_45_1 (from Chap20) -/
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

/-! ### Lemma_20_45_2 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section CohomologyPart

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/-- Basiswise vanishing of negative hypercohomology on the preimages `f^{-1}(V)` of basis opens
`V ⊆ Y`. -/
abbrev basiswiseNegativePreimageHypercohomologyVanishing
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (K : DModX) : Prop :=
  ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 →
    ∀ i : ℤ, i < 0 →
      IsZero (moduleOpenHypercohomology X (preimageOpen f V) K i)

-- Proof sketch: apply Lemma `20.32.6` with `i < 0`. The basiswise vanishing hypothesis says that
-- the presheaf whose sheafification is `H^i(Rf_* K)` is zero on a topological basis, so its
-- sheafification, hence the cohomology sheaf itself, is zero.
/-- Lemma 20.45.2 (1): if `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)` is a morphism of ringed
spaces, `𝓑` is a basis for the topology on `Y`, and `K ∈ D(\mathcal O_X)` has
`H^i(f^{-1}(V), K) = 0` for every `V ∈ 𝓑` and every `i < 0`, then the negative cohomology
sheaves of `Rf_* K` vanish. -/
theorem pushforward_negative_cohomologySheaf_isZero_of_basiswise_negative_preimage_hypercohomology
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K : DModX)
    (hK : basiswiseNegativePreimageHypercohomologyVanishing f 𝓑 K) :
    ∀ i : ℤ, i < 0 →
      IsZero (ringedSpaceCohomologySheaf Y ((moduleDerivedPushforward f).obj K) i) := sorry

-- Proof sketch: first use the previous clause to show `H^i(Rf_* K) = 0` for `i < 0`. Then apply
-- Lemma `20.32.6` again to identify `H^i(f^{-1}(V), K)` with sections of the zero sheaf
-- `H^i(Rf_* K)` on an arbitrary open `V ⊆ Y`.
/-- Lemma 20.45.2 (2): under the same basiswise negative-vanishing hypothesis on `K`, one has
`H^i(f^{-1}(V), K) = 0` for every open subset `V ⊆ Y` and every `i < 0`. -/
theorem preimage_negative_hypercohomology_isZero_on_all_opens
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K : DModX)
    (hK : basiswiseNegativePreimageHypercohomologyVanishing f 𝓑 K) :
    ∀ V : Opens Y.carrier, ∀ i : ℤ, i < 0 →
      IsZero (moduleOpenHypercohomology X (preimageOpen f V) K i) := sorry

section ZeroPresheaf

variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat Y)]

/-- The presheaf on `Y` given by `V ↦ H^0(f^{-1}(V), K)`, realized as the degree-zero objectwise
cohomology presheaf of `Rf_* K`. -/
abbrev preimageZeroHypercohomologyPresheaf
    (f : X ⟶ Y) (K : DModX) : (Opens Y.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ringedSpaceObjectwiseCohomologyPresheaf Y ((moduleDerivedPushforward f).obj K) 0

-- Proof sketch: the previous clause kills the negative cohomology sheaves of `Rf_* K`. Hence
-- `Rf_* K` is concentrated in degrees `≥ 0`, so Lemma `20.32.6` identifies `H^0(Rf_* K)` with the
-- sheafification of the presheaf `V ↦ H^0(f^{-1}(V), K)`, while concentration in nonnegative
-- degrees implies this presheaf already satisfies the sheaf condition.
/-- Lemma 20.45.2 (3): under the same hypotheses, the rule
`V ↦ H^0(f^{-1}(V), K)` is a sheaf on `Y`. In Lean this is the degree-zero objectwise cohomology
presheaf of `Rf_* K`. -/
theorem preimage_zero_hypercohomology_presheaf_isSheaf
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K : DModX)
    (hK : basiswiseNegativePreimageHypercohomologyVanishing f 𝓑 K) :
    TopCat.Presheaf.IsSheaf (preimageZeroHypercohomologyPresheaf f K) := sorry

end ZeroPresheaf

end CohomologyPart

section ExtPart

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

/-- Basiswise vanishing of negative local Ext groups on the preimages `f^{-1}(V)` of basis opens
`V ⊆ Y`, formalized via the negative hypercohomology of the derived internal-Hom object. -/
abbrev basiswiseNegativePreimageExtVanishing
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (K L : DModX) : Prop :=
  ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 →
    ∀ i : ℤ, i < 0 →
      IsZero (moduleOpenHypercohomology X (preimageOpen f V) ((ihom K).obj L) i)

-- Proof sketch: apply the cohomology part of the lemma to the derived internal-Hom object
-- `R\mathcal H\!\mathit{om}(K, L)`. This is exactly the translation described in
-- Lemma `20.42.1`.
/-- Lemma 20.45.2 (4): if `K, L ∈ D(\mathcal O_X)` satisfy
`\operatorname{Ext}^i(K|_{f^{-1}(V)}, L|_{f^{-1}(V)}) = 0` for every `V ∈ 𝓑` and every `i < 0`,
then the same vanishing holds for every open subset `V ⊆ Y`. In Lean this is stated using the
negative hypercohomology of `R\mathcal H\!\mathit{om}(K, L)` on `f^{-1}(V)`. -/
theorem preimage_negative_ext_isZero_on_all_opens
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K L : DModX)
    (hKL : basiswiseNegativePreimageExtVanishing f 𝓑 K L) :
    ∀ V : Opens Y.carrier, ∀ i : ℤ, i < 0 →
      IsZero (moduleOpenHypercohomology X (preimageOpen f V) ((ihom K).obj L) i) := sorry

section ZeroDerivedHomPresheaf

variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat Y)]

/-- The presheaf on `Y` given by the degree-zero local Ext groups
`V ↦ H^0(f^{-1}(V), R\mathcal H\!\mathit{om}(K, L))`; by Lemma `20.42.1` its sections are
canonically identified pointwise with `Hom_{D(\mathcal O_{f^{-1}(V)})}(K|_{f^{-1}(V)},
L|_{f^{-1}(V)})`. -/
abbrev preimageZeroDerivedHomPresheaf
    (f : X ⟶ Y) (K L : DModX) : (Opens Y.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ringedSpaceObjectwiseCohomologyPresheaf Y
    ((moduleDerivedPushforward f).obj ((ihom K).obj L)) 0

-- Proof sketch: apply the zero-degree sheaf statement from the cohomology part to the object
-- `R\mathcal H\!\mathit{om}(K, L)`. Lemma `20.42.1` then identifies this zero-degree Ext presheaf
-- with the presheaf of local derived-Hom groups.
/-- Lemma 20.45.2 (5): under the same basiswise negative Ext-vanishing hypothesis, the rule
`V ↦ \operatorname{Hom}(K|_{f^{-1}(V)}, L|_{f^{-1}(V)})` is a sheaf on `Y`; in Lean this is
formalized via the canonically identified degree-zero internal-Hom presheaf. -/
theorem preimage_zero_derivedHom_presheaf_isSheaf
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (h𝓑 : Opens.IsBasis 𝓑)
    (K L : DModX)
    (hKL : basiswiseNegativePreimageExtVanishing f 𝓑 K L) :
    TopCat.Presheaf.IsSheaf (preimageZeroDerivedHomPresheaf f K L) := sorry

end ZeroDerivedHomPresheaf

end ExtPart

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_45_4 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

-- Proof sketch: apply Lemma `20.45.2` to the degree-zero derived-Hom presheaf of two global
-- solutions. The basiswise negative Ext vanishing forces that presheaf to be a sheaf, so the
-- local comparison isomorphisms glue to a unique global isomorphism.
/-- Lemma 20.45.4 (1): if the basis opens in `𝓑` cover `X`, pairwise intersections are unions of
basis opens contained in the intersection, and the local objects of the gluing problem have
vanishing negative self-Ext groups, then any two global solutions are uniquely isomorphic in a way
compatible with the gluing data. -/
theorem openFamilyDerivedGluing_solution_uniqueIso
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue) :
    ∀ S T : OpenFamilyDerivedGluing.GlobalSolution glue, ∃! e : S.obj ≅ T.obj,
      ∀ ⦃U : Opens X.carrier⦄ (hU : U ∈ 𝓑),
        (moduleRestrictionToOpenDerived X U).mapIso e ≪≫ T.iso hU =
          S.iso hU := sorry

-- Proof sketch: apply the same derived-Hom sheaf argument as in part `(1)` to one global
-- solution against itself. The local negative self-Ext vanishing hypothesis implies that the
-- negative derived endomorphism groups vanish on every basis open, hence globally as well.
/-- Lemma 20.45.4 (2): under the same hypotheses, every global solution has vanishing negative
self-Ext groups. -/
theorem openFamilyDerivedGluing_negative_selfExt_isZero
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue) :
    ∀ S : OpenFamilyDerivedGluing.GlobalSolution glue, ∀ i : ℤ, i < 0 →
      Subsingleton (S.obj ⟶ (shiftFunctor (DerivedCategory (RingedSpace.Modules X)) i).obj S.obj) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_45_5 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

namespace OpenFamilyDerivedGluing

/-- Restrict an isomorphism over `U ⊓ V` to a smaller open `W ≤ U ⊓ V`, identifying the two-step
restrictions with the direct restrictions from `U` and `V` to `W`. -/
noncomputable def overlapIsoRestrictFrom
    {U V W : Opens X.carrier}
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    (e : (derivedRestrictionBetweenOpens X inf_le_left).obj A ≅
      (derivedRestrictionBetweenOpens X inf_le_right).obj B)
    (hW : W ≤ U ⊓ V) :
    (derivedRestrictionBetweenOpens X (hW.trans inf_le_left)).obj A ≅
      (derivedRestrictionBetweenOpens X (hW.trans inf_le_right)).obj B :=
  ((derivedRestrictionBetweenOpensCompIso (X := X) hW inf_le_left).app A).symm ≪≫
    (Functor.mapIso (derivedRestrictionBetweenOpens X hW) e) ≪≫
      (derivedRestrictionBetweenOpensCompIso (X := X) hW inf_le_right).app B

-- Proof sketch: apply Lemma `20.45.4` to the restricted system on `U ⊓ V`, whose basis consists
-- of those `U' ∈ 𝓑` contained in `U ⊓ V`. The two restricted objects `K_U|_{U ⊓ V}` and
-- `K_V|_{U ⊓ V}` are both solutions, so the lemma gives a unique compatible isomorphism.
/-- The overlap restrictions of two basis members are uniquely isomorphic once the hypotheses of
Lemma `20.45.4` are imposed on the gluing system. -/
theorem overlapIso_existsUnique
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue)
    {U V : Opens X.carrier} (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) :
    ∃! e :
        (derivedRestrictionBetweenOpens X inf_le_left).obj (glue.obj hU) ≅
          (derivedRestrictionBetweenOpens X inf_le_right).obj (glue.obj hV),
      ∀ ⦃U' : Opens X.carrier⦄ (hU' : U' ∈ 𝓑) (hU'UV : U' ≤ U ⊓ V),
        overlapIsoRestrictFrom e hU'UV ≪≫
            glue.ρ hV hU' (hU'UV.trans inf_le_right) =
          glue.ρ hU hU' (hU'UV.trans inf_le_left) := sorry

/-- The canonical comparison isomorphism between the restrictions of `K_U` and `K_V` to
`U ⊓ V`, characterized by compatibility with the maps to every basis open inside `U ⊓ V`. -/
noncomputable def overlapIso
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue)
    {U V : Opens X.carrier} (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) :
    (derivedRestrictionBetweenOpens X inf_le_left).obj (glue.obj hU) ≅
      (derivedRestrictionBetweenOpens X inf_le_right).obj (glue.obj hV) :=
  Classical.choose (overlapIso_existsUnique glue hcover hinter hneg hU hV)

-- Proof sketch: unpack the unique-existence statement defining `overlapIso`; the chosen witness
-- inherits exactly the compatibility condition recorded there.
/-- The canonical overlap isomorphism restricts to the prescribed maps `ρ^U_{U'}` and
`ρ^V_{U'}` on every basis open `U' ⊆ U ⊓ V`. -/
theorem overlapIso_spec
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue)
    {U V : Opens X.carrier} (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) :
    ∀ ⦃U' : Opens X.carrier⦄ (hU' : U' ∈ 𝓑) (hU'UV : U' ≤ U ⊓ V),
      overlapIsoRestrictFrom (glue.overlapIso hcover hinter hneg hU hV) hU'UV ≪≫
          glue.ρ hV hU' (hU'UV.trans inf_le_right) =
        glue.ρ hU hU' (hU'UV.trans inf_le_left) := sorry

-- Proof sketch: restrict the three canonical overlap isomorphisms to `U ⊓ V ⊓ W`. Both the direct
-- map `ρ_{U,W}` and the composite `ρ_{U,V}` followed by `ρ_{V,W}` satisfy the same compatibility
-- with all basis opens contained in the triple intersection, so uniqueness from
-- `overlapIso_existsUnique` identifies them.
/-- Remark 20.45.5: the canonical overlap isomorphisms for a basis gluing datum satisfy the usual
cocycle condition on triple intersections, so the family `(K_U, ρ_{U,V})` behaves as a descent
datum for the open covering `X = ⋃_{U ∈ 𝓑} U`. -/
theorem overlapIso_cocycle
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue)
    {U V W : Opens X.carrier}
    (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hW : W ∈ 𝓑) :
    overlapIsoRestrictFrom (glue.overlapIso hcover hinter hneg hU hW)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) =
      overlapIsoRestrictFrom (glue.overlapIso hcover hinter hneg hU hV) inf_le_left ≪≫
        overlapIsoRestrictFrom (glue.overlapIso hcover hinter hneg hV hW)
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right) := sorry

end OpenFamilyDerivedGluing

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_45_6 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

namespace OpenFamilyDerivedGluing

-- Proof sketch: perform induction on the size of a finite basis cover of `X`. The two-open case
-- is handled by the preceding gluing lemma, while the induction step glues over the union of the
-- first `n` opens and then applies the two-open case once more. Uniqueness follows from the same
-- negative-Ext vanishing argument used in the earlier uniqueness lemma for global solutions.
/-- Lemma 20.45.6: assume `𝓑` is a basis covering `X`, pairwise intersections of basis opens are
generated by basis members contained in the intersection, and the prescribed local objects have
vanishing negative self-Ext groups on basis opens. Then the gluing datum admits a global
solution, and that solution is unique up to a unique isomorphism compatible with the basis
identifications. -/
theorem exists_globalSolution_uniqueUpToUniqueIso_of_finite_cover
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue) :
    ∃ S : OpenFamilyDerivedGluing.GlobalSolution glue,
      ∀ T : OpenFamilyDerivedGluing.GlobalSolution glue,
        ∃! e : S.obj ≅ T.obj,
          ∀ ⦃U : Opens X.carrier⦄ (hU : U ∈ 𝓑),
            (moduleRestrictionToOpenDerived X U).mapIso e ≪≫ T.iso hU =
              S.iso hU := sorry

end OpenFamilyDerivedGluing

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_45_7 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- Restriction of `\mathcal O_X`-modules to the open subspace `U`. -/
abbrev moduleSheafRestrictionToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Modules X ⥤ Modules (X.restrict U.isOpenEmbedding) :=
  SheafOfModules.pullback
    (⟨Functor.whiskerRight (X.ofRestrict U.isOpenEmbedding).hom.c
        (forget₂ CommRingCat RingCat.{u})⟩ :
      ringCatSheaf X ⟶
        (TopCat.Sheaf.pushforward RingCat.{u} (X.ofRestrict U.isOpenEmbedding).hom.base).obj
          (ringCatSheaf (X.restrict U.isOpenEmbedding)))

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

/-- Restriction to an open subspace is additive on sheaves of modules. -/
private instance moduleSheafRestrictionToOpen_additive :
    (moduleSheafRestrictionToOpen X U).Additive := sorry

/-- Restriction to an open subspace preserves finite limits on sheaves of modules. -/
private instance moduleSheafRestrictionToOpen_preservesFiniteLimits :
    PreservesFiniteLimits (moduleSheafRestrictionToOpen X U) := sorry

/-- Restriction to an open subspace preserves finite colimits on sheaves of modules. -/
private instance moduleSheafRestrictionToOpen_preservesFiniteColimits :
    PreservesFiniteColimits (moduleSheafRestrictionToOpen X U) := sorry

/-- The derived category `D(\mathcal O_U)` attached to the open subspace `U \subset X`. -/
abbrev moduleDerivedOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  DerivedCategory (Modules (X.restrict U.isOpenEmbedding))

/-- Restriction of a derived `\mathcal O_X`-module to the open subspace `U`. -/
abbrev moduleRestrictionToOpenDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (Modules X) ⥤ moduleDerivedOnOpen X U :=
  Functor.mapDerivedCategory (moduleSheafRestrictionToOpen X U)

/-- The open subset of the restricted ringed space `X|_V` cut out by an inclusion `U \subseteq V`.
-/
abbrev openSubsetOfLE {X : RingedSpace.{u}} {U V : Opens X.carrier} (_h : U ≤ V) :
    Opens ((X.restrict V.isOpenEmbedding : RingedSpace).carrier) :=
  (Opens.map V.inclusion').obj U

-- Restriction along `U ⊆ V` is implemented by first restricting to `V` and then transporting the
-- codomain back to the direct open subspace `U`.
-- Proof sketch: both sides are the derived categories of the same restricted ringed space; the
-- two presentations differ only by whether one first restricts to `V` and then to the open cut
-- out by `U ⊆ V`, or restricts directly to `U`.
/-- Identifies the derived category of `U` inside `X|_V` with the derived category of `U` inside
`X`. -/
theorem nested_moduleDerivedOnOpen_eq (X : RingedSpace.{u}) {U V : Opens X.carrier} (h : U ≤ V) :
    moduleDerivedOnOpen (X.restrict V.isOpenEmbedding) (openSubsetOfLE h) =
      moduleDerivedOnOpen X U := sorry

-- Proof sketch: apply `nested_moduleDerivedOnOpen_eq` to the codomain of the restriction functor
-- from `X|_V` to `U`, leaving the domain unchanged.
/-- The functor type of restriction from `V` to `U` matches the direct `D(\mathcal O_V) ⥤
D(\mathcal O_U)` interface. -/
theorem derivedRestrictionBetweenOpens_type_eq
    (X : RingedSpace.{u}) {U V : Opens X.carrier} (h : U ≤ V) :
    (moduleDerivedOnOpen X V ⥤
      moduleDerivedOnOpen (X.restrict V.isOpenEmbedding) (openSubsetOfLE h)) =
        (moduleDerivedOnOpen X V ⥤ moduleDerivedOnOpen X U) := sorry

/-- Restriction on derived categories along an inclusion `U \subseteq V` of open subsets of a
ringed space. -/
abbrev derivedRestrictionBetweenOpens
    (X : RingedSpace.{u}) {U V : Opens X.carrier} (h : U ≤ V) :
    moduleDerivedOnOpen X V ⥤ moduleDerivedOnOpen X U :=
  cast (derivedRestrictionBetweenOpens_type_eq X h)
    (moduleRestrictionToOpenDerived (X.restrict V.isOpenEmbedding) (openSubsetOfLE h))

/-- The derived Ext group `\operatorname{Ext}^i(A, B)` on an open subspace, written as morphisms
`A \to B[i]` in the derived category. -/
abbrev derivedExtGroupOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier)
    (A B : moduleDerivedOnOpen X U) (i : ℤ) : AddCommGrpCat :=
  AddCommGrpCat.of (A ⟶ B⟦i⟧)

-- Proof sketch: restricting from `W` to `V` and then from `V` to `U` yields the same restricted
-- ringed space as restricting directly from `W` to `U`, so the two derived restriction objects
-- coincide after transport across the identification of codomains.
/-- Iterated restriction along `U \subseteq V \subseteq W` gives the same restricted object as
direct restriction from `W` to `U`. -/
theorem nestedRestriction_obj_eq
    (X : RingedSpace.{u}) {U V W : Opens X.carrier} (hUV : U ≤ V) (hVW : V ≤ W)
    (K : moduleDerivedOnOpen X W) :
    (derivedRestrictionBetweenOpens X hUV).obj ((derivedRestrictionBetweenOpens X hVW).obj K) =
      ((derivedRestrictionBetweenOpens X (hUV.trans hVW)).obj K) := sorry

-- Proof sketch: this is the special case of `nestedRestriction_obj_eq` where the first step comes
-- from restricting a global derived object to `V`; the resulting object on `U` agrees with direct
-- restriction from `X` to `U`.
/-- Restricting a global derived object first to `V` and then to `U` agrees with direct
restriction to `U`. -/
theorem globalRestriction_obj_eq
    (X : RingedSpace.{u}) {U V : Opens X.carrier} (h : U ≤ V)
    (K : DerivedCategory (Modules X)) :
    (derivedRestrictionBetweenOpens X h).obj ((moduleRestrictionToOpenDerived X V).obj K) =
      ((moduleRestrictionToOpenDerived X U).obj K) := sorry

-- Proof sketch: choose K-injective representatives of the local objects and construct compatible
-- extension-by-zero transition morphisms by transfinite recursion. At successor stages, extend
-- across the new open using the given restriction isomorphism. At successor limits, take the
-- filtered colimit of the previously glued complexes and use vanishing of negative self-Ext to
-- identify this colimit with the prescribed local object. A final filtered colimit over the whole
-- well-ordered cover produces the global derived object.
/-- Lemma 20.45.7: for a ringed space `X`, a well-ordered increasing open cover `(W_\alpha)` that
is continuous at successor limits, and a compatible family of objects
`K_\alpha \in D(\mathcal O_{W_\alpha})` with `\operatorname{Ext}^i(K_\alpha, K_\alpha) = 0` for
`i < 0`, there exists an object `K \in D(\mathcal O_X)` whose restriction to each `W_\alpha` is
identified with `K_\alpha` and is compatible with the given restriction isomorphisms. -/
theorem exists_glued_derived_object_of_wellOrdered_open_cover
    {X : RingedSpace.{u}} {E : Type v} [LinearOrder E] [SuccOrder E] [WellFoundedLT E]
    (W : E → Opens X.carrier) (hcover : iSup W = ⊤) (hmono : Monotone W)
    (hlimit : ∀ ⦃α : E⦄, Order.IsSuccLimit α → W α = ⨆ β : Set.Iio α, W β.1)
    (Kα : ∀ α : E, moduleDerivedOnOpen X (W α))
    (hExt : ∀ α : E, ∀ i : ℤ, i < 0 → IsZero (derivedExtGroupOnOpen X (W α) (Kα α) (Kα α) i))
    (rho : ∀ {β α : E} (hβα : β < α),
      ((derivedRestrictionBetweenOpens X (hmono hβα.le)).obj (Kα α)) ≅ Kα β)
    (hrho : ∀ {γ β α : E} (hγβ : γ < β) (hβα : β < α),
      Eq.mp
        (congrArg (fun T ↦ T ⟶ Kα γ)
          (nestedRestriction_obj_eq X (hmono hγβ.le) (hmono hβα.le) (Kα α)))
        ((derivedRestrictionBetweenOpens X (hmono hγβ.le)).map (rho hβα).hom ≫
          (rho hγβ).hom) =
            (rho (lt_trans hγβ hβα)).hom) :
    ∃ (K : DerivedCategory (Modules X))
      (iso : ∀ α : E,
        ((moduleRestrictionToOpenDerived X (W α)).obj K) ≅ Kα α),
      ∀ {β α : E} (hβα : β < α),
        Eq.mp
          (congrArg (fun T ↦ T ⟶ Kα β)
            (globalRestriction_obj_eq X (hmono hβα.le) K))
          ((derivedRestrictionBetweenOpens X (hmono hβα.le)).map (iso α).hom ≫
            (rho hβα).hom) =
              (iso β).hom := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Theorem_20_45_8_BBD_gluing_lemma (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

namespace OpenFamilyDerivedGluing

-- Proof sketch: well-order a chain of unions of basis opens whose union is `X`. Use the finite
-- gluing step on successor stages and the transfinite gluing construction on limit stages, while
-- the negative-Ext uniqueness lemma identifies the stagewise solutions uniquely and makes the
-- transition isomorphisms compose correctly.
/-- Theorem 20.45.8 (BBD gluing lemma): if the basis opens in `𝓑` cover `X`, pairwise
intersections are unions of basis opens contained in the intersection, and the prescribed local
derived objects have vanishing negative self-Ext groups, then the gluing datum admits a global
solution. This global realization is unique up to a unique isomorphism compatible with the basis
identifications. -/
theorem exists_globalSolution_uniqueUpToUniqueIso
    (glue : OpenFamilyDerivedGluing X 𝓑)
    (hcover : BasisCoversSpace X 𝓑)
    (hinter : BasisIntersectionsGenerated X 𝓑)
    (hneg : OpenFamilyDerivedGluing.NegativeSelfExtVanishing glue) :
    ∃ S : OpenFamilyDerivedGluing.GlobalSolution glue,
      ∀ T : OpenFamilyDerivedGluing.GlobalSolution glue,
        ∃! e : S.obj ≅ T.obj,
          ∀ ⦃U : Opens X.carrier⦄ (hU : U ∈ 𝓑),
            (moduleRestrictionToOpenDerived X U).mapIso e ≪≫ T.iso hU =
              S.iso hU := sorry

end OpenFamilyDerivedGluing

end

end AlgebraicGeometry.RingedSpace
