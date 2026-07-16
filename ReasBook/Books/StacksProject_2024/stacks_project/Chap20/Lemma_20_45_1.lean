import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.45.1:
- primary domain: derived restriction of `𝒪_X`-modules to open subspaces and two-open
  gluing data in `D(𝒪_X)`;
- sampled owner declarations:
  `ModuleDerived`,
  `moduleDerivedOnOpen`,
  `moduleRestrictionToOpenDerived`,
  `derivedRestrictionBetweenOpens`,
  `moduleRestrictionToOpenDerivedCompIso`,
  `module_derived_mayer_vietoris_hom_exact_segment`;
- best owner abstraction: the ambient derived owner is `ModuleDerived X`, and the ambient
  restriction owner is `moduleRestrictionToOpenDerived X U`,
  and restriction between nested open subspaces is already available upstream through the
  Chapter 20 owner `derivedRestrictionBetweenOpens`;
- primitive data: the ringed space `X`, the opens `U, V`, the local derived objects on `U` and
  `V`, their overlap isomorphism, and the compatible local morphisms into a global target;
- derived API: the canonical comparison between the two restrictions of a global object to
  `U ⊓ V`, built from the Chapter 20 owner comparison isomorphisms, together with the
  Mayer-Vietoris extension of compatible local morphisms.

Source/core/bridge triage:
 - `source-facing`: the existence theorem `exists_two_open_derived_gluing` and its “moreover”
   companion `exists_two_open_derived_gluing_morphism`;
 - `core/canonical`: `ModuleDerived`, `moduleDerivedOnOpen`,
  `moduleRestrictionToOpenDerived`, `derivedRestrictionBetweenOpens`, and
  `module_derived_mayer_vietoris_hom_exact_segment`;
 - `bridge/view`: `moduleRestrictionToOpenDerivedCompIso`, used to compare direct and iterated
  restriction on the overlap.
-/

variable {X : RingedSpace.{u}}

section

variable {U V : Opens X.carrier}

local notation "DModX" => ModuleDerived X
local notation "DMod[" U "]" => moduleDerivedOnOpen X U
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U
local notation "DRes≤[" h "]" => derivedRestrictionBetweenOpens X h
local notation "DResFromXComp[" h "]" => moduleRestrictionToOpenDerivedCompIso X h

/-- The canonical comparison between the two iterated restrictions of a global derived object to
`U ⊓ V`, obtained by identifying both with the direct restriction from `X`. -/
abbrev twoOpenDerivedOverlapIso
    (U V : Opens X.carrier) (F : DModX) :
    (DRes≤[inf_le_left]).obj ((DRes[U]).obj F) ≅
      (DRes≤[inf_le_right]).obj ((DRes[V]).obj F) :=
  (DResFromXComp[inf_le_left]).app F ≪≫ ((DResFromXComp[inf_le_right]).app F).symm

/-- The restriction isomorphisms `leftIso` and `rightIso` realize `F` as a gluing of `A` and `B`
across the prescribed overlap isomorphism `c`. -/
abbrev IsTwoOpenDerivedGluing
    (U V : Opens X.carrier)
    {A : DMod[U]} {B : DMod[V]}
    (c : (DRes≤[inf_le_left]).obj A ≅ (DRes≤[inf_le_right]).obj B)
    {F : DModX} (leftIso : (DRes[U]).obj F ≅ A) (rightIso : (DRes[V]).obj F ≅ B) : Prop :=
  CommSq
    (twoOpenDerivedOverlapIso U V F).hom
    ((DRes≤[inf_le_left]).map leftIso.hom)
    ((DRes≤[inf_le_right]).map rightIso.hom)
    c.hom

/-- Unpack the overlap compatibility square from a two-open derived gluing witness. -/
theorem IsTwoOpenDerivedGluing.commSq
    {U V : Opens X.carrier}
    {A : DMod[U]} {B : DMod[V]}
    {c : (DRes≤[inf_le_left]).obj A ≅ (DRes≤[inf_le_right]).obj B}
    {F : DModX} {leftIso : (DRes[U]).obj F ≅ A} {rightIso : (DRes[V]).obj F ≅ B}
    (hglue : IsTwoOpenDerivedGluing U V c leftIso rightIso) :
    CommSq
      (twoOpenDerivedOverlapIso U V F).hom
      ((DRes≤[inf_le_left]).map leftIso.hom)
      ((DRes≤[inf_le_right]).map rightIso.hom)
      c.hom :=
  hglue

/-- Equational form of the overlap compatibility square of a two-open derived gluing witness. -/
theorem IsTwoOpenDerivedGluing.w
    {U V : Opens X.carrier}
    {A : DMod[U]} {B : DMod[V]}
    {c : (DRes≤[inf_le_left]).obj A ≅ (DRes≤[inf_le_right]).obj B}
    {F : DModX} {leftIso : (DRes[U]).obj F ≅ A} {rightIso : (DRes[V]).obj F ≅ B}
    (hglue : IsTwoOpenDerivedGluing U V c leftIso rightIso) :
    (twoOpenDerivedOverlapIso U V F).hom ≫ ((DRes≤[inf_le_right]).map rightIso.hom) =
      ((DRes≤[inf_le_left]).map leftIso.hom) ≫ c.hom :=
  (hglue.commSq).w

/-- The local morphisms `a` and `b` into a global target `E` agree on the overlap after
transporting across the comparison isomorphism `c`. -/
abbrev IsTwoOpenDerivedMorphismCompatible
    (U V : Opens X.carrier)
    {A : DMod[U]} {B : DMod[V]}
    (c : (DRes≤[inf_le_left]).obj A ≅ (DRes≤[inf_le_right]).obj B)
    (E : DModX) (a : A ⟶ (DRes[U]).obj E) (b : B ⟶ (DRes[V]).obj E) : Prop :=
  CommSq c.hom
    ((DRes≤[inf_le_left]).map a)
    ((DRes≤[inf_le_right]).map b)
    (twoOpenDerivedOverlapIso U V E).hom

/-- Unpack the compatibility square for local morphisms into a global target. -/
theorem IsTwoOpenDerivedMorphismCompatible.commSq
    {U V : Opens X.carrier}
    {A : DMod[U]} {B : DMod[V]}
    {c : (DRes≤[inf_le_left]).obj A ≅ (DRes≤[inf_le_right]).obj B}
    {E : DModX} {a : A ⟶ (DRes[U]).obj E} {b : B ⟶ (DRes[V]).obj E}
    (hcompat : IsTwoOpenDerivedMorphismCompatible U V c E a b) :
    CommSq c.hom
      ((DRes≤[inf_le_left]).map a)
      ((DRes≤[inf_le_right]).map b)
      (twoOpenDerivedOverlapIso U V E).hom :=
  hcompat

/-- Equational form of compatibility of local morphisms with the overlap isomorphism `c`. -/
theorem IsTwoOpenDerivedMorphismCompatible.w
    {U V : Opens X.carrier}
    {A : DMod[U]} {B : DMod[V]}
    {c : (DRes≤[inf_le_left]).obj A ≅ (DRes≤[inf_le_right]).obj B}
    {E : DModX} {a : A ⟶ (DRes[U]).obj E} {b : B ⟶ (DRes[V]).obj E}
    (hcompat : IsTwoOpenDerivedMorphismCompatible U V c E a b) :
    c.hom ≫ ((DRes≤[inf_le_right]).map b) =
      ((DRes≤[inf_le_left]).map a) ≫ (twoOpenDerivedOverlapIso U V E).hom :=
  (hcompat.commSq).w

-- Proof sketch: take the canonical morphism
-- `Rj_{U, *}A ⊞ Rj_{V, *}B ⟶ Rj_{U ∩ V, *}(B|_{U ∩ V})` built from the two restriction maps
-- and the overlap isomorphism `c`, then choose an object completing it to a distinguished
-- triangle. Restriction to `U` and `V` splits the displayed triangle, giving the two required
-- isomorphisms, and the resulting overlap comparison is the displayed commutative square.
/-- Lemma 20.45.1: for a ringed space covered by two opens `U` and `V`, objects
`A ∈ D(𝒪_U)` and `B ∈ D(𝒪_V)`, and an isomorphism
`c : A|_{U ∩ V} ≅ B|_{U ∩ V}`, there exists an ambient object
`F ∈ D(𝒪_X)` whose restrictions to `U` and `V` are identified with `A` and `B`,
and whose canonical overlap comparison induces `c`. -/
@[stacks 08DG]
theorem exists_two_open_derived_gluing
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (A : DMod[U]) (B : DMod[V])
    (c : (DRes≤[inf_le_left]).obj A ≅ (DRes≤[inf_le_right]).obj B) :
    ∃ (F : DModX) (leftIso : (DRes[U]).obj F ≅ A) (rightIso : (DRes[V]).obj F ≅ B),
      IsTwoOpenDerivedGluing U V c leftIso rightIso := sorry

-- Proof sketch: choose `F`, `leftIso`, and `rightIso` from `exists_two_open_derived_gluing`.
-- The compatibility hypothesis on `a` and `b` identifies the pair
-- `(leftIso.hom ≫ a, rightIso.hom ≫ b)` as an element in the kernel of the canonical
-- Mayer-Vietoris overlap-difference map from Lemma `20.33.3`, hence exactness produces a global
-- morphism `F ⟶ E` restricting to the prescribed local maps.
/-- Lemma 20.45.1, moreover clause: for a glued object `F` with restriction isomorphisms `leftIso`
and `rightIso`, any local morphisms into a global target `E` that are compatible on `U ⊓ V`
extend to a global morphism `F ⟶ E`. -/
@[stacks 08DG]
theorem exists_two_open_derived_gluing_morphism
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (A : DMod[U]) (B : DMod[V])
    (c : (DRes≤[inf_le_left]).obj A ≅ (DRes≤[inf_le_right]).obj B)
    {F : DModX} (leftIso : (DRes[U]).obj F ≅ A) (rightIso : (DRes[V]).obj F ≅ B)
    (hglue : IsTwoOpenDerivedGluing U V c leftIso rightIso)
    (E : DModX)
    (a : A ⟶ (DRes[U]).obj E) (b : B ⟶ (DRes[V]).obj E)
    (hcompat : IsTwoOpenDerivedMorphismCompatible U V c E a b) :
    ∃ α : F ⟶ E,
      (DRes[U]).map α = leftIso.hom ≫ a ∧
        (DRes[V]).map α = rightIso.hom ≫ b := sorry

end

end AlgebraicGeometry.RingedSpace
