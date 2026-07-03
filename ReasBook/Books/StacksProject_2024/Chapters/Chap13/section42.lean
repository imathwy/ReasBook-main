import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_42_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits

universe uI vD uD

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.42.1:
- primary domain: essentially constant cofiltered diagrams in pretriangulated categories, expressed by
  an eventual tailwise biproduct decomposition.
- sampled owner-level declarations:
  * `IsEssentiallyConstantCofilteredDiagram` in `Chap04/Definition_4_22_2`
  * `IsEssentiallyConstantCofilteredCone` in `Chap04/Definition_4_22_1`
  * `Functor.tail` and `Functor.mapLE` below for the canonical tail restriction and cofiltered
    transition-map surface on preorder-indexed inverse systems
  * `Pretriangulated.binaryBiproductData` in mathlib's pretriangulated API
  * `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang` in mathlib
- best owner abstraction:
  * `core/canonical`: `IsEssentiallyConstantCofilteredDiagram F`
  * `source-facing`: `HasTailDirectSumDecomposition F`, the explicit tailwise biproduct
    decomposition criterion
  * `bridge/view`: the equivalence theorem below, specialized to the pretriangulated setting

Primitive-vs-derived split:
- primitive source-facing data: a tail index, a fixed summand `A`, a complementary tail diagram
  `Z : OrderDual (Set.Ici i) ⥤ D`, a functor-level biproduct decomposition
  `F.tail i ≅ (Functor.const _).obj A ⊞ Z`, and eventual vanishing of the complementary transition
  maps along the cofiltered tail.
- derived API: the stagewise isomorphisms and their compatibility with the transition maps, both
  obtained by evaluating that natural isomorphism, together with the equivalence with the chapter
  owner `IsEssentiallyConstantCofilteredDiagram`. -/

namespace Functor

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D]

/-- The restriction of a cofiltered preorder-indexed diagram to the tail `Set.Ici i`. -/
abbrev tail (F : OrderDual I ⥤ D) (i : I) : OrderDual (Set.Ici i) ⥤ D :=
  (OrderHom.Subtype.val (Set.Ici i)).dual.toFunctor ⋙ F

/-- The transition map in a cofiltered preorder-indexed diagram attached to an inequality
`j ≤ j'`. -/
abbrev mapLE {J : Type*} [Preorder J] (F : OrderDual J ⥤ D) {j j' : J} (h : j ≤ j') :
    F.obj j' ⟶ F.obj j :=
  F.map (homOfLE h)

end

end Functor

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [HasBinaryBiproducts D]

/-- Evaluating a tailwise biproduct decomposition at a transition map recovers the expected
stagewise compatibility equation. -/
@[reassoc]
theorem tailDirectSumIso_hom_naturality {F : OrderDual I ⥤ D} {i : I} {A : D}
    {Z : OrderDual (Set.Ici i) ⥤ D}
    (e : F.tail i ≅ (Functor.const (OrderDual (Set.Ici i))).obj A ⊞ Z)
    {j j' : Set.Ici i} (hjj' : j ≤ j') :
    (F.tail i).mapLE hjj' ≫ (e.app j).hom =
      (e.app j').hom ≫ (((Functor.const (OrderDual (Set.Ici i))).obj A ⊞ Z).mapLE hjj') := by
  simpa [Functor.mapLE] using e.hom.naturality (homOfLE hjj')

/-- Lemma 13.42.1 source-facing criterion: after some stage, the inverse system `F` splits as a
fixed summand `A` together with a complementary tail diagram whose transition maps are eventually
zero, and the transition maps of `F` act as the identity on `A`. -/
def HasTailDirectSumDecomposition (F : OrderDual I ⥤ D) : Prop :=
  ∃ i : I,
    ∃ A : D,
      ∃ Z : OrderDual (Set.Ici i) ⥤ D,
        ∃ _e : F.tail i ≅ (Functor.const (OrderDual (Set.Ici i))).obj A ⊞ Z,
          ∀ j : Set.Ici i, ∃ j' : Set.Ici i, ∃ hjj' : j ≤ j', Z.mapLE hjj' = 0

end

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

-- Proof sketch: starting from an essentially constant cone, choose the eventual retraction from
-- Definition 4.22.1 and transport it to the whole tail. The pretriangulated splitting lemmas then
-- identify the whole tail functor with a biproduct `(Functor.const _).obj A ⊞ Z`, whose evaluated
-- components recover the stagewise isomorphisms `Fⱼ ≅ A ⊞ Zⱼ`; the factorization data assembles
-- the complementary summands into a tail inverse system whose transition maps become zero far
-- enough out.
-- Conversely, such a tailwise split decomposition directly reconstructs the retraction and
-- eventual factorization criterion in Definition 4.22.1.
/-- Lemma 13.42.1: a directed inverse system in a pretriangulated category is essentially constant
if and only if, after some index, every stage is isomorphic to a fixed summand `A` plus a
complementary inverse system `Z`, the transition maps `Fⱼ' ⟶ Fⱼ` act as the identity on `A`, and
the complementary transition maps are eventually zero. -/
theorem isEssentiallyConstantCofilteredDiagram_iff_hasEventuallyConstantDirectSumDecomposition
    [IsDirectedOrder I] (F : OrderDual I ⥤ D) :
    IsEssentiallyConstantCofilteredDiagram F ↔ HasTailDirectSumDecomposition F := sorry

end

end CategoryTheory

/-! ### Lemma_13_42_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CostructuredArrow
open CategoryTheory.Pretriangulated
open Opposite

universe uI vI uC vC uD vD

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.42.2:
- primary domain: essentially constant cofiltered diagrams and fixed pro-object values in a
  pretriangulated/triangulated setting.
- inspected owner-level declarations:
  `SequentialInverseSystem` in `Chap12/Definition_12_31_2`,
  `IsEssentiallyConstantCofilteredDiagram` in `Chap04/Definition_4_22_2`,
  `HasProObjectValue` in `Chap04/Remark_4_22_7`,
  `hasProObjectValue_iff_exists_stageMap_homColimitComparison` in
    `Chap04/Lemma_4_22_10`,
  `Triangle.π₁`, `Triangle.π₂`, `Triangle.π₃` in mathlib.
- best owner abstraction: the sequential diagram owner `SequentialInverseSystem`, the
  essential-constancy owner `IsEssentiallyConstantCofilteredDiagram`, the fixed pro-object-value
  owner `HasProObjectValue M X`, and the stage-map comparison owner `HasHomColimitComparison`.
- primitive-vs-derived split: the primitive data are the inverse system `T`, the positive stage
  `n + 1`, the fixed distinguished triangle `T'`, and the morphism from that stage to `T'`;
  the owner-level conclusions `HasProObjectValue` and
  `IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₂)` are derived from the corresponding
  Hom-colimit comparison data via Lemma `4.22.10`.

Source/core/bridge triage:
- `source-facing`: after some positive stage, the system admits a fixed distinguished triangle
  together with a morphism of distinguished triangles from that stage whose three components
  satisfy the Hom-colimit comparison criterion.
- `core/canonical`: `HasProObjectValue`, `IsEssentiallyConstantCofilteredDiagram`, `Triangle D`,
  and `HasHomColimitComparison`.
- `bridge/view`: the companion owner-level consequences below, obtained from the source-facing
  stage-map theorem via
  `hasProObjectValue_iff_exists_stageMap_homColimitComparison`. -/

section

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

-- Proof sketch: first rewrite the outer systems using Lemma 13.42.1 so that, on a tail, their
-- terms split as fixed summands plus essentially zero complements. The connecting morphisms on the
-- fixed summands define a single map `C ⟶ A⟦1⟧`; choose a distinguished triangle on that map, then
-- use `TR3` to compare one stage with it. Applying the homological functors `Hom(-, D)` shows that
-- the three components of that stage map corepresent the original inverse systems, so in
-- particular the three projected systems have fixed pro-object values given by the components of
-- `T'`, so the middle term system is essentially constant as well.
/-- Lemma 13.42.2, source-facing form: for a sequential inverse system of distinguished triangles
in a triangulated category, and in fact already in a pretriangulated category, if the first and
third term systems are essentially constant, then after some positive stage the system admits a
fixed distinguished triangle together with a morphism of distinguished triangles from that stage,
whose three components satisfy the stage-map comparison criterion of Lemma `4.22.10`.

The owner-level pro-object-value and essential-constancy consequences are recorded below as thin
companions. -/
theorem essentiallyConstant_middle_and_tail_value_triangle_of_essentiallyConstant_outer_terms
    {T : SequentialInverseSystem (Triangle D)} (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₁))
    (h₃ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₃)) :
    ∃ (T' : Triangle D) (n : ℕ),
      T' ∈ distTriang D ∧
        ∃ φ : T.obj (op (n + 1)) ⟶ T',
          HasHomColimitComparison
            (T ⋙ Triangle.π₁)
            (CostructuredArrow.mk φ.hom₁) ∧
          HasHomColimitComparison
            (T ⋙ Triangle.π₂)
            (CostructuredArrow.mk φ.hom₂) ∧
          HasHomColimitComparison
            (T ⋙ Triangle.π₃)
            (CostructuredArrow.mk φ.hom₃) := sorry

/-- Owner-level companion to Lemma 13.42.2: the fixed distinguished triangle produced there has
vertices corepresenting the three projected inverse systems. -/
theorem exists_proObjectValue_triangle_of_essentiallyConstant_outer_terms
    {T : SequentialInverseSystem (Triangle D)} (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₁))
    (h₃ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₃)) :
    ∃ T' : Triangle D,
      T' ∈ distTriang D ∧
        HasProObjectValue (T ⋙ Triangle.π₁) T'.obj₁ ∧
        HasProObjectValue (T ⋙ Triangle.π₂) T'.obj₂ ∧
        HasProObjectValue (T ⋙ Triangle.π₃) T'.obj₃ := sorry

/-- Owner-level consequence of Lemma 13.42.2: if the outer terms of a sequential inverse system
of distinguished triangles are essentially constant, then so is the middle term system. -/
theorem essentiallyConstant_middle_of_essentiallyConstant_outer_terms
    {T : SequentialInverseSystem (Triangle D)} (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₁))
    (h₃ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₃)) :
    IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₂) := sorry

end

end CategoryTheory

/-! ### Lemma_13_42_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite
open scoped CategoryTheory

universe w v u uI vI uC vC

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 13.42.3:
- primary domain: sequential inverse systems in `D(𝒜)`, boundedness via the canonical
  `t`-structure owners, and fixed pro-object values detected on the cohomology towers.
- sampled owner-level declarations:
  `SequentialInverseSystem` in `Chap12/Definition_12_31_2`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.isZero_of_isGE`,
  `DerivedCategory.isZero_of_isLE`,
  the chapter cohomology notation owner `H^i` in `Chap13/Definition_13_11_3`,
  `IsEssentiallyConstantCofilteredDiagram` in `Chap04/Definition_4_22_2`,
  `HasProObjectValue` in `Chap04/Remark_4_22_7`,
  `essentiallyConstant_proObject_characterizations` in `Chap04/Lemma_4_22_10`,
  `essentiallyConstant_middle_and_tail_value_triangle_of_essentiallyConstant_outer_terms` in
    `Chap13/Lemma_13_42_2`.
- best owner abstraction: the source-facing content is the bounded-cohomology induction theorem
  for a sequential inverse system in `D(𝒜)`; the canonical owners underneath it are
  `SequentialInverseSystem`, `DerivedCategory.IsGE`, `DerivedCategory.IsLE`,
  `IsEssentiallyConstantCofilteredDiagram`, and `HasProObjectValue`.
- primitive-vs-derived split: the primitive data are the inverse system `F` and the uniform
  cohomological bounds recorded canonically by `IsGE a` and `IsLE b` on every stage. The
  cohomology towers `F ⋙ H^i` for `i ∈ Set.Icc a b`, their essential constancy, and the resulting
  pro-object values are derived API around those owners; outside `Set.Icc a b`, the towers are
  canonically zero by `DerivedCategory.isZero_of_isGE` and `DerivedCategory.isZero_of_isLE`.

Source/core/bridge triage:
- `source-facing`: `essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology`,
  which records the textbook essential-constancy conclusion.
- `core/canonical`: `exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology`,
  together with the owner predicates `DerivedCategory.IsGE`, `DerivedCategory.IsLE`,
  `HasProObjectValue`, and `H^i`.
- `bridge/view`: the textbook formulation "cohomology vanishes outside `[a, b]`", which is
  equivalent to the pair of owner assumptions `(F.obj (op n)).IsGE a` and
  `(F.obj (op n)).IsLE b`. -/

-- Proof sketch: induct on the width `b - a` of the cohomological amplitude. The truncation
-- triangle at the bottom degree identifies `τ_{\le a} (A_n)` with `H^a(A_n)[-a]`, so the left
-- term system is essentially constant by the hypothesis on degree-`a` cohomology. The remaining
-- tail `τ_{\ge a + 1} (A_n)` has smaller amplitude and degreewise essentially constant
-- cohomology, hence is essentially constant by induction. Apply Lemma `13.42.2` to the resulting
-- inverse system of truncation triangles, then read off the cohomology values from the outer-term
-- identifications and the final clause of Lemma `13.42.2`. The source-facing essential-constancy
-- conclusion is then recovered from the Chapter 4 owner theorem
-- `essentiallyConstant_proObject_characterizations`.
/-- Core/canonical owner form of Lemma 13.42.3: under the same boundedness and degreewise
essential-constancy hypotheses, the sequential inverse system has a fixed pro-object value `A`,
and every cohomology tower `H^i(A_n)` is corepresented by `H^i(A)`. The textbook conclusion that
`F` is essentially constant is derived from this by the Chapter 4 owner criterion
`essentiallyConstant_proObject_characterizations`. -/
theorem exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (a b : ℤ)
    (hGE : ∀ n : ℕ, (F.obj (op n)).IsGE a)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b, IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    ∃ A : DerivedCategory 𝒜,
      HasProObjectValue F A ∧
        ∀ i : ℤ,
          HasProObjectValue (F ⋙ H^i) ((H^i).obj A) := sorry

/-- Lemma 13.42.3: if a sequential inverse system in `D(\mathcal A)` has uniformly bounded
cohomology, say in degrees `[a, b]`, and each cohomology inverse system `H^i(A_n)` is
essentially constant for `i ∈ [a, b]`, then the inverse system itself is essentially constant. -/
theorem essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (a b : ℤ)
    (hGE : ∀ n : ℕ, (F.obj (op n)).IsGE a)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b, IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    IsEssentiallyConstantCofilteredDiagram F := by
  rcases exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology
      F a b hGE hLE hH with ⟨_, hA, _⟩
  rcases hA with ⟨e⟩
  exact (essentiallyConstant_proObject_characterizations F).mp e.isCorepresentable

end CategoryTheory

/-! ### Lemma_13_42_4 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open SequentialProObjectMorphismRep
open scoped CategoryTheory ZeroObject

universe uC vC uD vD

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.42.4:
- primary domain: sequential inverse systems in a pretriangulated category, viewed through the
  Chapter 4 owner for sequential pro-object morphisms and the Hom-colimit functor
  `X ↦ colimₙ Hom(-, X)`.
- inspected owner-level declarations:
  `HasProObjectValue`,
  `SequentialProObjectMorphismRep`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `SequentialProObjectMorphismRep.ofOrderDualNatTrans`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective`,
  `Functor.whiskerLeft`,
  `Triangle.π₁Toπ₂`.
- best owner abstraction: the sequential pro-object morphism represented by the first maps in the
  triangle system, obtained from `Functor.whiskerLeft T Triangle.π₁Toπ₂` via
  `SequentialProObjectMorphismRep.ofOrderDualNatTrans`; the source-facing owner statement is that
  this representative is a pro-isomorphism, and its evaluation on a test object is the canonical
  Hom-colimit map after passing to the standard `ℕᵒᵖ` presentation of the sequential system.
- primitive data: the triangle system `T`, the first-to-second natural transformation
  `Functor.whiskerLeft T Triangle.π₁Toπ₂`.
- derived API: the pro-isomorphism owner
  `(SequentialProObjectMorphismRep.ofOrderDualNatTrans ...).IsProIsomorphism`, its evaluated
  morphism `(SequentialProObjectMorphismRep.ofOrderDualNatTrans ...).toProObjectHom.app X`, and
  the source-facing pro-zero condition `HasProObjectValue (T ⋙ Triangle.π₃) (0 : D)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, asserting that a pro-zero third term system forces the maps
  `Aₙ ⟶ Bₙ` to define a pro-isomorphism.
- `core/canonical`: `HasProObjectValue` and `SequentialProObjectMorphismRep`.
- `bridge/view`: `SequentialProObjectMorphismRep.ofOrderDualNatTrans` and
  `SequentialProObjectMorphismRep.toProObjectHom`. -/

section

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {T : OrderDual ℕ ⥤ Triangle D}

-- Proof sketch: for each test object `X`, apply the homological functor `Hom(-, X)` to every
-- distinguished triangle in the system to obtain an exact sequence of filtered colimits. Lemma
-- 10.8.8 gives exactness after passing to colimits, and the pro-zero hypothesis on `(Cₙ)` forces
-- the first and last colimit terms to vanish. Hence the middle map
-- `colimₙ Hom(Bₙ, X) → colimₙ Hom(Aₙ, X)` is bijective for every `X`, which is the Hom-colimit
-- form of the claimed pro-isomorphism by Remark 4.22.7.
/-- Lemma 13.42.4: for a sequential inverse system of distinguished triangles
`Aₙ ⟶ Bₙ ⟶ Cₙ ⟶ Aₙ⟦1⟧`, if the system `(Cₙ)` is essentially constant as a pro-object with value
`0`, then the maps `Aₙ ⟶ Bₙ` determine a pro-isomorphism between the pro-objects `(Aₙ)` and
`(Bₙ)`. -/
theorem triangleFirstToSecond_isProIsomorphism_of_proZero_third
    (hT : ∀ n : ℕ, T.obj n ∈ distTriang D)
    (h₃ : HasProObjectValue (T ⋙ Triangle.π₃) (0 : D))
    :
    (ofOrderDualNatTrans (Functor.whiskerLeft T Triangle.π₁Toπ₂)).IsProIsomorphism := sorry

/-- Bridge/view companion to Lemma 13.42.4: under the same pro-zero hypothesis on `(Cₙ)`, the
induced map `colimₙ Hom(Bₙ, X) → colimₙ Hom(Aₙ, X)` is bijective for every test object `X`. -/
theorem triangleFirstToSecond_toProObjectHom_app_bijective_of_proZero_third
    (hT : ∀ n : ℕ, T.obj n ∈ distTriang D)
    (h₃ : HasProObjectValue (T ⋙ Triangle.π₃) (0 : D))
    (X : D) :
    Function.Bijective
      ((ofOrderDualNatTrans (Functor.whiskerLeft T Triangle.π₁Toπ₂)).toProObjectHom.app X) := by
  simpa using
    isProIsomorphism_toProObjectHom_app_bijective
      (triangleFirstToSecond_isProIsomorphism_of_proZero_third hT h₃) X

end

end CategoryTheory

/-! ### Lemma_13_42_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite
open SequentialProObjectMorphismRep
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 13.42.5:
- primary domain: morphisms of sequential inverse systems in `D(𝒜)`, controlled through the
  Chapter 4 owner `SequentialProObjectMorphismRep` and detected on cohomology towers.
- inspected owner-level declarations:
  `SequentialInverseSystem`,
  `SequentialProObjectMorphismRep.ofNatTrans`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology`,
  `triangleFirstToSecond_isProIsomorphism_of_proZero_third`.
- best owner abstraction: the source-facing result is that the sequential representative attached
  to `α` is a pro-isomorphism; the owner-level bridge to Hom-colimit bijectivity is already
  upstream, so it should not be recopied locally.
- primitive data: the sequential inverse systems `A` and `B`, the natural transformation `α`, the
  uniform cohomological bounds on both systems expressed by the canonical owners `IsGE` / `IsLE`,
  and the degreewise owner-level pro-isomorphism hypotheses on the cohomology towers `A ⋙ H^i`
  and `B ⋙ H^i` in the
  bounded window `Set.Icc a b`.
- derived API: `(ofNatTrans α).IsProIsomorphism`; Hom-colimit bijectivity is derived from the
  upstream owner theorem `isProIsomorphism_toProObjectHom_app_bijective`.

Source/core/bridge triage:
- `source-facing`: the main theorem below, asserting that `α` induces a pro-isomorphism in
  `D(𝒜)`.
- `core/canonical`: `SequentialInverseSystem`, `SequentialProObjectMorphismRep`, and
  `.IsProIsomorphism`.
- `bridge/view`: the Hom-colimit evaluation map `.toProObjectHom.app X`, supplied upstream rather
  than by a second local wrapper theorem. -/

-- Proof sketch: choose a compatible inverse system of distinguished triangles extending the maps
-- `α.app (op n) : A.obj (op n) ⟶ B.obj (op n)`. The boundedness assumptions and the degreewise
-- pro-isomorphism
-- hypothesis imply, by Lemma `13.42.3`, that the cone system has pro-zero cohomology and hence is
-- pro-zero in `D(𝒜)`; outside `[a, b]` the cone cohomology towers are already zero by the uniform
-- bounds. Then Lemma `13.42.4` gives a pro-isomorphism for those triangles, and the owner-level
-- bridge `SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective` turns
-- that into bijectivity of the induced Hom-colimit map for every test object.
/-- Lemma 13.42.5: if `α : A ⟶ B` is a morphism of sequential inverse systems in `D(\mathcal A)`
and there exist integers `a` and `b` such that both systems have cohomology supported in
`[a, b]`, while for every degree `i ∈ [a, b]` the induced morphism of inverse systems on `H^i` is a
pro-isomorphism in `\mathcal A`, then `α` is a pro-isomorphism of inverse systems in
`D(\mathcal A)`. -/
theorem ofNatTrans_isProIsomorphism_of_uniformlyBounded_homologywise_proIso
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (a b : ℤ)
    (hAGE : ∀ n : ℕ, (A.obj (op n)).IsGE a)
    (hALE : ∀ n : ℕ, (A.obj (op n)).IsLE b)
    (hBGE : ∀ n : ℕ, (B.obj (op n)).IsGE a)
    (hBLE : ∀ n : ℕ, (B.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b,
      (ofNatTrans (Functor.whiskerRight α (H^i))).IsProIsomorphism) :
    (ofNatTrans α).IsProIsomorphism :=
  sorry

end CategoryTheory
