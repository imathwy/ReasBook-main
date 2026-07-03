import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_10_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜]
  [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]

/- Domain-style sampling:
- primary domain: distinguished triangles in homotopy categories of cochain complexes;
- sampled owner declarations in this domain:
  `Pretriangulated.distinguishedTriangles`,
  `distTriang (K(𝒜))`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `distTriang (K⁺(𝒜))`,
  the bounded homotopy-category owners from `Definition_13_8_1`;
- source/core/bridge triage:
  `source-facing`: the Stacks definition of distinguished triangles on `K(\mathcal A)` and on the
    bounded homotopy categories `K^+(\mathcal A)`, `K^-(\mathcal A)`, `K^b(\mathcal A)`;
  `core/canonical`: the owner `Pretriangulated.distinguishedTriangles`, surfaced as `distTriang`
    on each pretriangulated homotopy category;
  `bridge/view`: the degreewise-split characterization theorem on `K(\mathcal A)` and the
    bounded full-subcategory views from `Definition_13_8_1`; once the triangulated full-subcategory
    instances from Lemma 13.10.5 are in scope, their inclusions use the canonical reflection
    theorem `Functor.map_distinguished_iff`.

Primitive data is only the ambient homotopy category together with its canonical pretriangulated
structure. The degreewise-split description and the bounded full-subcategory descriptions are
derived API around that owner, so this file should recall the existing owner directly rather than
introduce any parallel local predicate or wrapper.
-/

/- Definition 13.10.1: on the homotopy category `K(\mathcal A) = HomotopyCategory 𝒜
(ComplexShape.up ℤ)`, distinguished triangles are given by the canonical owner
`distTriang (K(𝒜))`, i.e. the specialization of `Pretriangulated.distinguishedTriangles` to the
pretriangulated homotopy category. Equivalently, by
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`, a triangle is distinguished
exactly when it is isomorphic to the triangle attached to a termwise split exact sequence of
cochain complexes as in Definition 13.9.9. The same canonical owner is used for
`K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)`. -/
#check (distTriang (K(𝒜)))

/- Companion recall: the characterization of distinguished triangles in the homotopy category by
termwise split exact sequences of cochain complexes is exactly the canonical mathlib theorem
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`. -/
recall HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit

/- Definition 13.10.1 on the bounded homotopy categories uses the same canonical owner
`distTriang` on `K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)`. -/
#check (distTriang (K⁺(𝒜)))
#check (distTriang (K⁻(𝒜)))
#check (distTriang (Kᵇ(𝒜)))

/- Companion recall: the source-facing description of distinguished triangles in these bounded
homotopy categories is that the inclusion into `K(\mathcal A)` reflects distinguished triangles;
this is exactly the canonical theorem `Functor.map_distinguished_iff` applied to the full
faithful exact inclusions `ObjectProperty.ι (HomotopyCategory.plus 𝒜)`,
`ObjectProperty.ι (HomotopyCategory.minus 𝒜)`, and
`ObjectProperty.ι (HomotopyCategory.bounded 𝒜)`. -/
recall Functor.map_distinguished_iff

end

/-! ### Lemma_13_10_2 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open ComplexShape
open HomologicalComplex
open CochainComplex

universe v u

/- Source/core/bridge triage for Lemma 13.10.2:
- primary domain: termwise split short exact sequences of cochain complexes, their associated
  triangles in the homotopy category, and the octahedron axiom;
- inspected owner declarations:
  `ShortComplex`,
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `CategoryTheory.Triangulated.Octahedron`,
  `CategoryTheory.IsTriangulated.mk'`;
  from Definition 13.9.9, and the canonical homotopy-category triangles attached to them are the
  owner triangles `CochainComplex.trianglehOfDegreewiseSplit`; the octahedron datum should
  therefore be stated directly for the rows `ShortComplex.mk α p₁ hαp₁`,
  `ShortComplex.mk (α ≫ β) p₂ hαβp₂`, and `ShortComplex.mk β p₃ hβp₃`, not via extra
  existential short complexes that are immediately reidentified by equality proofs;
- layer:
  `source-facing`: the three short complexes attached to `α`, `β`, and `α ≫ β`, together with
    degreewise splitness;
  `core/canonical`: `ShortComplex`, `CochainComplex.trianglehOfDegreewiseSplit`, and
    `CategoryTheory.Triangulated.Octahedron`;
  `bridge/view`: the passage from the degreewise split rows to their owner triangles in the
    homotopy category;
- primitive data: the three third terms `Q₁`, `Q₂`, `Q₃`, the quotient maps
  `p₁ : B ⟶ Q₁`, `p₂ : C ⟶ Q₂`, `p₃ : C ⟶ Q₃`, their zero-composite relations with
  `α`, `α ≫ β`, and `β`, and the degreewise splitness existence conditions from
  Definition 13.9.9 for the associated rows `ShortComplex.mk α p₁ hαp₁`,
  `ShortComplex.mk (α ≫ β) p₂ hαβp₂`, and `ShortComplex.mk β p₃ hβp₃`;
- derived API: internal choices of splitting families, the connecting morphisms in the homotopy
  category, distinguishedness of the owner triangles, and the resulting octahedron datum.
-/

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V] [HasBinaryBiproducts V]

local notation "Q" => HomotopyCategory.quotient V (up ℤ)
local notation "K" => HomotopyCategory V (up ℤ)
section

variable {A B C X Y Z : CochainComplex V ℤ}

/- The only routine degreewise input needed later is that split monomorphisms compose
componentwise. We isolate that closure fact so the eventual octahedron proof can reuse it
without reopening the instance search argument in the main theorem. -/
/-- Helper for Lemma 13.10.2: termwise split monomorphisms of cochain complexes are closed under
composition. -/
lemma termwise_split_mono_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ n : ℤ, IsSplitMono (f.f n))
    (hg : ∀ n : ℤ, IsSplitMono (g.f n)) :
    ∀ n : ℤ, IsSplitMono ((f ≫ g).f n) := by
  intro n
  -- Each component map is a composition of split monomorphisms, hence split monic again.
  letI : IsSplitMono (f.f n) := hf n
  letI : IsSplitMono (g.f n) := hg n
  simpa using (show IsSplitMono (f.f n ≫ g.f n) from inferInstance)

/- Once a source-facing short complex is known to split after evaluation in every degree, its
owner triangle in the homotopy category is distinguished by the standard degreewise-split
characterization. This packages that bridge into a single reusable lemma. -/
/-- Helper for Lemma 13.10.2: the canonical triangle attached to a degreewise split short complex
of cochain complexes is distinguished in the homotopy category. -/
lemma triangle_mk_mem_distTriang_of_degreewise_split_short_complex
    (S : ShortComplex (CochainComplex V ℤ))
    (σ : ∀ n : ℤ, (S.map (eval V (up ℤ) n)).Splitting) :
    let T := trianglehOfDegreewiseSplit S σ
    Triangle.mk ((Q).map S.f) T.mor₂ T.mor₃ ∈ distTriang K := by
  let T := trianglehOfDegreewiseSplit S σ
  -- The bridge/view theorem identifies `T` with the standard owner triangle of `S`.
  simpa [T] using
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).2
      ⟨S, σ, ⟨Iso.refl _⟩⟩

-- Proof sketch: produce the three source-facing rows from Definition 13.9.9 attached to `α`,
-- `β`, and `α ≫ β`, together with chosen splitting families. These choices determine the
-- canonical owner triangles `CochainComplex.trianglehOfDegreewiseSplit` for the three rows.
-- Publicly, keep those owner triangles visible and state the octahedron datum directly for them,
-- rather than existentially repackaging their second and third morphisms.
/-- Lemma 13.10.2: if `α : A^• ⟶ B^•` and `β : B^• ⟶ C^•` are termwise split injections of
cochain complexes in an additive category, then there exist three source-facing short complexes
realizing the rows `0 ⟶ A^• ⟶ B^• ⟶ Q₁^• ⟶ 0`, `0 ⟶ A^• ⟶ C^• ⟶ Q₂^• ⟶ 0`, and
`0 ⟶ B^• ⟶ C^• ⟶ Q₃^• ⟶ 0`. Choosing splittings for these rows yields their canonical owner
triangles `trianglehOfDegreewiseSplit`, and these three owner triangles fit into an octahedron in
the homotopy category, expressing `TR4`. -/
theorem split_injections_of_cochain_complexes_have_octahedron
    {A B C : CochainComplex V ℤ} (α : A ⟶ B) (β : B ⟶ C)
    (hα : ∀ n : ℤ, IsSplitMono (α.f n)) (hβ : ∀ n : ℤ, IsSplitMono (β.f n)) :
    ∃ (Q₁ Q₂ Q₃ : CochainComplex V ℤ)
      (p₁ : B ⟶ Q₁) (hαp₁ : α ≫ p₁ = 0)
      (p₂ : C ⟶ Q₂) (hαβp₂ : (α ≫ β) ≫ p₂ = 0)
      (p₃ : C ⟶ Q₃) (hβp₃ : β ≫ p₃ = 0),
      (let S₁₂ := ShortComplex.mk α p₁ hαp₁
       let S₁₃ := ShortComplex.mk (α ≫ β) p₂ hαβp₂
       let S₂₃ := ShortComplex.mk β p₃ hβp₃
       ∃ (σ₁₂ : ∀ n : ℤ, (S₁₂.map (eval V (up ℤ) n)).Splitting)
         (σ₁₃ : ∀ n : ℤ, (S₁₃.map (eval V (up ℤ) n)).Splitting)
         (σ₂₃ : ∀ n : ℤ, (S₂₃.map (eval V (up ℤ) n)).Splitting),
         let T₁₂ := trianglehOfDegreewiseSplit S₁₂ σ₁₂
         let T₁₃ := trianglehOfDegreewiseSplit S₁₃ σ₁₃
         let T₂₃ := trianglehOfDegreewiseSplit S₂₃ σ₂₃
         ∃ (h₁₂ : Triangle.mk ((Q).map α) T₁₂.mor₂ T₁₂.mor₃ ∈ distTriang K)
           (h₂₃ : Triangle.mk ((Q).map β) T₂₃.mor₂ T₂₃.mor₃ ∈ distTriang K)
           (h₁₃ : Triangle.mk ((Q).map (α ≫ β)) T₁₃.mor₂ T₁₃.mor₃ ∈ distTriang K),
           Nonempty (Octahedron (Functor.map_comp Q α β).symm h₁₂ h₂₃ h₁₃)) := by
  -- Route correction: the ambient octahedron axiom already supplies the final `TR4` datum once
  -- the three source-facing rows `A ⟶ B ⟶ Q₁`, `A ⟶ C ⟶ Q₂`, and `B ⟶ C ⟶ Q₃` are available.
  -- The unresolved point is earlier: under the present assumptions we only know that each
  -- component `α.f n`, `β.f n`, and `(α ≫ β).f n` is split mono.
  -- TODO: a complete proof needs a source-level construction turning those componentwise split
  -- monomorphisms into actual cochain-level rows with maps `p₁`, `p₂`, and `p₃` whose evaluated
  -- short complexes admit splittings. Mathlib exposes complement decompositions for a split mono
  -- only after a cokernel is given, and the current hypotheses do not provide those cokernels.
  sorry

end

/-! ### Proposition_13_10_3 (from Chap13) -/
open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

/- Domain-style sampling:
- primary domain: triangulated structures on homotopy categories of cochain complexes;
- sampled owner declarations:
  `K(𝒜)`;
  `Pretriangulated (K(𝒜))`;
  `IsTriangulated (K(𝒜))`;
- best owner abstraction: the canonical owner `IsTriangulated (K(𝒜))`;
- primitive data: an additive category with zero object and binary biproducts;
- derived API: the triangulated structure on the homotopy category of cochain complexes.

Source/core/bridge triage:
- `source-facing`: Proposition 13.10.3, asserting that the homotopy category `K(\mathcal A)` is
  triangulated;
- `core/canonical`: the existing triangulated owner instance on `K(𝒜)`;
- `bridge/view`: the textbook notation `K(\mathcal A)` from `Definition_13_8_1` for
  `HomotopyCategory 𝒜 (up ℤ)`.

This proposition is therefore a pure canonical recall item. The file should use the existing owner
instance directly, with no local wrapper or duplicate declaration.
-/

/- Proposition 13.10.3: for an additive category `\mathcal A`, the homotopy category
`K(\mathcal A)` of cochain complexes, equipped with its standard translation functors and
distinguished triangles, carries the canonical triangulated structure. This is exactly the
existing owner instance `IsTriangulated (K(𝒜))`. -/
#check (inferInstance : IsTriangulated (K(𝒜)))

end CategoryTheory

/-! ### Remark_13_10_4 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

variable (𝒜) [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜]

/- Domain-style sampling:
- primary domain: triangulated structures on bounded homotopy categories;
- relevant owner declarations in this domain:
  `HomotopyCategory.plus`,
  `HomotopyCategory.minus`,
  `HomotopyCategory.bounded`,
  `CategoryTheory.ObjectProperty.IsTriangulated`;
- source/core/bridge triage:
  `source-facing`: the direct triangulated structures on the bounded homotopy categories
    `K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)`;
  `core/canonical`: the triangulated object-property instances on
    `HomotopyCategory.plus 𝒜`, `HomotopyCategory.minus 𝒜`, and `HomotopyCategory.bounded 𝒜`;
  `bridge/view`: the full-subcategory realizations `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)` inside `K(𝒜)`.

Primitive data for the boundedness notions lives in `Definition_13_8_1`, while the triangulated
owner instances are established in `Lemma_13_10_5`. This remark is therefore a direct recall of
those source-facing full-subcategory consequences, not a second owner file and not a new bridge.
-/

/- Remark 13.10.4: for an additive category `\mathcal A`, the same cone argument as in
Proposition 13.10.3 shows that the bounded-below, bounded-above, and bounded homotopy categories
`K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)` are triangulated; below this is
reproved by identifying them as triangulated subcategories of `K(\mathcal A)`. Here we record the
direct triangulated structures on the corresponding homotopy categories of bounded complexes. -/
#check (inferInstance :
  IsTriangulated (K⁺(𝒜)))

/- Companion recall: the bounded-above homotopy category `K^{-}(\mathcal A)` is triangulated. -/
#check (inferInstance :
  IsTriangulated (K⁻(𝒜)))

/- Companion recall: the bounded homotopy category `K^{b}(\mathcal A)` is triangulated. -/
#check (inferInstance :
  IsTriangulated (Kᵇ(𝒜)))

/-! ### Lemma_13_10_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
  [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜]

/- Domain-style sampling:
- primary domain: triangulated bounded homotopy categories of cochain complexes;
- sampled owner declarations:
  `HomotopyCategory.plus`,
  `HomotopyCategory.minus`,
  `HomotopyCategory.bounded`,
  `CategoryTheory.ObjectProperty.IsTriangulated`,
  `ObjectProperty.FullSubcategory`,
  `CategoryTheory.IsTriangulated`;
- best owner abstraction: the bounded homotopy categories `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)` from
  `Definition_13_8_1`, viewed as the full subcategories cut out by the canonical boundedness
  object properties on `K(𝒜)`;
- primitive data: the object properties `HomotopyCategory.plus 𝒜`,
  `HomotopyCategory.minus 𝒜`, and `HomotopyCategory.bounded 𝒜`;
- derived API: the triangulated full-subcategory instances on `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)`.
- source/core/bridge triage:
  `source-facing`: the bounded homotopy categories `K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`,
    and `K^{b}(\mathcal A)`;
  `core/canonical`: the triangulated object-property API on `K(\mathcal A)`;
  `bridge/view`: the realization of those object properties as full subcategories.

This file is therefore the owner for the triangulated boundedness properties on `K(\mathcal A)`,
while the source-facing full-subcategory statements remain direct instance recalls.
-/

/-- The bounded-below objects in the homotopy category form a triangulated object property. -/
instance :
    (HomotopyCategory.plus 𝒜).IsTriangulated := sorry

/-- The bounded-above objects in the homotopy category form a triangulated object property. -/
instance :
    (HomotopyCategory.minus 𝒜).IsTriangulated := sorry

/-- The bounded objects in the homotopy category form a triangulated object property. -/
instance :
    (HomotopyCategory.bounded 𝒜).IsTriangulated := sorry

/- Lemma 13.10.5: the bounded-below, bounded-above, and bounded full subcategories
`K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)` of `K(\mathcal A)` are
triangulated. In the chapter API these are the source-facing full-subcategory views of the three
owner instances above, so the textbook statement is recovered below by direct instance recall. -/
#check (inferInstance :
  IsTriangulated (K⁺(𝒜)))
#check (inferInstance :
  IsTriangulated (K⁻(𝒜)))
#check (inferInstance :
  IsTriangulated (Kᵇ(𝒜)))

end

end CategoryTheory

/-! ### Lemma_13_10_6 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Preadditive 𝒜] [Preadditive ℬ]
  [HasZeroObject 𝒜] [HasZeroObject ℬ]
  [HasBinaryBiproducts 𝒜] [HasBinaryBiproducts ℬ]

/- Domain-style sampling for Lemma 13.10.6:
- primary domain: triangulated full subcategories of homotopy categories and exact functors
  between them;
- sampled owner declarations:
  `boundedBelowHomotopyProperty`,
  `boundedAboveHomotopyProperty`,
  `ObjectProperty.lift`,
  `CategoryTheory.ObjectProperty.IsTriangulated`;
- best owner abstraction: the bounded homotopy categories `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)` are the
  source-facing full-subcategory views inside `K(𝒜)`, while the canonical core is the
  triangulated object-property API together with `ObjectProperty.lift` for restricted functors;
- primitive data: the boundedness object properties from `Definition_13_8_1` and the ambient
  additive functor `F.mapHomotopyCategory (up ℤ)`;
- derived API: the triangulated instances for those object properties, the landing lemmas for the
  restricted functors, and the induced functors on bounded homotopy categories;
- source/core/bridge triage:
  `source-facing`: the exact functors on `K(𝒜)`, `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)`;
  `core/canonical`: `ObjectProperty.IsTriangulated` and `ObjectProperty.lift`;
  `bridge/view`: the bounded full-subcategory realizations inside the ambient homotopy category.

The boundedness owners already live upstream in `Definition_13_8_1`, so this file keeps only the
bridge/view declarations needed to transport triangulated and functorial structure to those full
subcategories. -/

/-- The bounded-below objects in the homotopy category form a triangulated object property. -/
instance boundedBelowHomotopyProperty_isTriangulated :
    (boundedBelowHomotopyProperty 𝒜).IsTriangulated := sorry

/-- The bounded-above objects in the homotopy category form a triangulated object property. -/
instance boundedAboveHomotopyProperty_isTriangulated :
    (boundedAboveHomotopyProperty 𝒜).IsTriangulated := sorry

/-- The bounded objects in the homotopy category form a triangulated object property. -/
instance boundedHomotopyProperty_isTriangulated :
    (boundedHomotopyProperty 𝒜).IsTriangulated := sorry

variable (F : 𝒜 ⥤ ℬ) [F.Additive]

-- Proof sketch: represent `X` by a bounded-below cochain complex and apply `F` termwise; an
-- additive functor preserves zero objects, so the same lower bound still works after applying `F`.
/-- The functor on homotopy categories induced by an additive functor preserves bounded-below
objects. -/
theorem mapHomotopyCategory_obj_mem_boundedBelowHomotopyProperty
    (X : K⁺(𝒜)) :
    boundedBelowHomotopyProperty ℬ ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := sorry

-- Proof sketch: represent `X` by a bounded-above cochain complex and apply `F` termwise; an
-- additive functor preserves zero objects, so the same upper bound still works after applying `F`.
/-- The functor on homotopy categories induced by an additive functor preserves bounded-above
objects. -/
theorem mapHomotopyCategory_obj_mem_boundedAboveHomotopyProperty
    (X : K⁻(𝒜)) :
    boundedAboveHomotopyProperty ℬ ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := sorry

-- Proof sketch: combine the bounded-below and bounded-above preservation statements for the same
-- object of the bounded homotopy category.
/-- The functor on homotopy categories induced by an additive functor preserves bounded objects. -/
theorem mapHomotopyCategory_obj_mem_boundedHomotopyProperty
    (X : Kᵇ(𝒜)) :
    boundedHomotopyProperty ℬ ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := sorry

/-- The restriction of `F.mapHomotopyCategory (up ℤ)` to bounded-below homotopy categories. -/
abbrev mapBoundedBelowHomotopyCategory :
    K⁺(𝒜) ⥤ K⁺(ℬ) :=
  ObjectProperty.lift (boundedBelowHomotopyProperty ℬ)
    (ObjectProperty.ι (boundedBelowHomotopyProperty 𝒜) ⋙ F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategory_obj_mem_boundedBelowHomotopyProperty F)

/-- The restriction of `F.mapHomotopyCategory (up ℤ)` to bounded-above homotopy categories. -/
abbrev mapBoundedAboveHomotopyCategory :
    K⁻(𝒜) ⥤ K⁻(ℬ) :=
  ObjectProperty.lift (boundedAboveHomotopyProperty ℬ)
    (ObjectProperty.ι (boundedAboveHomotopyProperty 𝒜) ⋙ F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategory_obj_mem_boundedAboveHomotopyProperty F)

/-- The restriction of `F.mapHomotopyCategory (up ℤ)` to bounded homotopy categories. -/
abbrev mapBoundedHomotopyCategory :
    Kᵇ(𝒜) ⥤ Kᵇ(ℬ) :=
  ObjectProperty.lift (boundedHomotopyProperty ℬ)
    (ObjectProperty.ι (boundedHomotopyProperty 𝒜) ⋙ F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategory_obj_mem_boundedHomotopyProperty F)

/- Lemma 13.10.6 (1): the additive functor `F : \mathcal A \to \mathcal B` induces an exact
functor `K(\mathcal A) \to K(\mathcal B)` on homotopy categories; in the canonical API, exactness
is the triangulated-functor instance below, together with the canonical shift-commuting structure
on `F.mapHomotopyCategory (up ℤ)`. -/
#check (inferInstance : (F.mapHomotopyCategory (up ℤ)).IsTriangulated)

/- Lemma 13.10.6 (2): the induced functor on bounded-below homotopy categories
`K^{+}(\mathcal A) \to K^{+}(\mathcal B)` is exact; it is the restriction of
`F.mapHomotopyCategory (up ℤ)` to the full subcategories of bounded-below objects. -/
#check (inferInstance : (mapBoundedBelowHomotopyCategory F).IsTriangulated)

/- Lemma 13.10.6 (3): the induced functor on bounded-above homotopy categories
`K^{-}(\mathcal A) \to K^{-}(\mathcal B)` is exact; it is the restriction of
`F.mapHomotopyCategory (up ℤ)` to the full subcategories of bounded-above objects. -/
#check (inferInstance : (mapBoundedAboveHomotopyCategory F).IsTriangulated)

/- Lemma 13.10.6 (4): the induced functor on bounded homotopy categories
`K^{b}(\mathcal A) \to K^{b}(\mathcal B)` is exact; it is the restriction of
`F.mapHomotopyCategory (up ℤ)` to the full subcategories of bounded objects. -/
#check (inferInstance : (mapBoundedHomotopyCategory F).IsTriangulated)

end

end CategoryTheory

/-! ### Lemma_13_10_7 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex

universe v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

local notation "K" => HomotopyCategory 𝒜 (up ℤ)
local notation "Q" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling for Lemma 13.10.7:
- primary domain: distinguished triangles in the homotopy category of cochain complexes and their
  realization by degreewise split short exact sequences;
- inspected owner declarations:
  `distTriang (K)`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `Triangle.isoMk`;
- best owner abstraction: the canonical owner is the distinguished-triangle class `distTriang K`,
  while the degreewise split model is the bridge/view
  `CochainComplex.trianglehOfDegreewiseSplit`; comparison data should therefore be an ordinary
  triangle isomorphism, not a second local wrapper predicate;
- primitive data: a degreewise split short complex `0 ⟶ A ⟶ B' ⟶ C ⟶ 0` together with a triangle
  isomorphism whose first and third components are identities;
- derived API: distinguishedness of the target triangle and the equality of third morphisms follow
  from `hT` and the triangle-isomorphism commutativity, so they should not be stored as primitive
  public data.
- source/core/bridge triage:
  `source-facing`: the comparison theorem promised by Lemma 13.10.7;
  `core/canonical`: `distTriang K`;
  `bridge/view`: `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` together with
    `CochainComplex.trianglehOfDegreewiseSplit`.
-/

-- Proof sketch: use the characterization of distinguished triangles in `K(\mathcal A)` by
-- degreewise split triangles together with the explicit inverse-rotation of a cone triangle. The
-- proof in the text constructs a triangle `(A^•, W^•[-1], C^•, a', b', c)` from the cone of `c`,
-- then applies TR3 and the two-out-of-three lemma for morphisms of triangles to obtain an
-- isomorphism whose first and third components are identities.
/-- Lemma 13.10.7: if `(A^•, B^•, C^•, a, b, c)` is a distinguished triangle in
`K(\mathcal A)`, then it is isomorphic, through the identity on `A^•` and `C^•`, to a
distinguished triangle `(A^•, (B')^•, C^•, a', b', c)` coming from a degreewise split short exact
sequence `0 ⟶ A^n ⟶ (B')^n ⟶ C^n ⟶ 0` in every degree. -/
theorem distinguished_triangle_iso_to_degreewiseSplit
    {A B C : CochainComplex 𝒜 ℤ}
    {a : (Q).obj A ⟶ (Q).obj B}
    {b : (Q).obj B ⟶ (Q).obj C}
    {c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b c ∈ distTriang K) :
    ∃ (B' : CochainComplex 𝒜 ℤ) (f : A ⟶ B') (g : B' ⟶ C) (hfg : f ≫ g = 0)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk f g hfg).map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting),
      ∃ e : Triangle.mk a b c ≅
          CochainComplex.trianglehOfDegreewiseSplit (ShortComplex.mk f g hfg) σ,
        e.hom.hom₁ = 𝟙 ((Q).obj A) ∧
          e.hom.hom₃ = 𝟙 ((Q).obj C) := sorry

end

end CategoryTheory

/-! ### Remark_13_10_8 (from Chap13) -/
open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂ HomotopyCategory

noncomputable section

universe v u

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]
  [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] [HasCountableCoproducts 𝒜]

/- Domain-style sampling:
- primary domain: totalization of cohomological double complexes and the induced exact functors on
  homotopy categories;
- sampled owner declarations:
  `CategoryTheory.Functor.mapHomotopyCategory`,
  `HomologicalComplex₂.flipFunctor`,
  `HomologicalComplex₂.totalFunctor`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the two source-facing totalization functors on homotopy categories are
  the canonical owner `F.mapHomotopyCategory (up ℤ)` applied to the additive complex-level
  functors `totalFunctor` and `flipFunctor ⋙ totalFunctor`; this remark should record only the
  inherited `Functor.CommShift` and `Functor.IsTriangulated` structures on those owners, not
  rebuild the quotient lifts by hand;
- primitive data: the complex-level functors `totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)` and
  `flipFunctor 𝒜 (up ℤ) (up ℤ) ⋙ totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)`, together with their
  additive structures;
- derived API: the canonical homotopy-category functors obtained via `Functor.mapHomotopyCategory`
  and their inherited `CommShift` and `IsTriangulated` instances.
- source/core/bridge triage:
  `source-facing`: the two totalization functors on the homotopy category of double complexes;
  `core/canonical`: `Functor.mapHomotopyCategory`, `Functor.CommShift`, and
    `Functor.IsTriangulated`;
  `bridge/view`: the two source-facing functors are the instances of
    `Functor.mapHomotopyCategory (up ℤ)` attached to `totalFunctor` and
    `flipFunctor ⋙ totalFunctor`.

This file therefore records Remark 13.10.8 by direct owner recall on
`mapHomotopyCategory`, without a parallel public totalization-functor API. -/

local instance : HasBinaryBiproducts (HomologicalComplex 𝒜 (up ℤ)) where
  has_binary_biproduct K L := by
    let _ : ∀ i : ℤ, HasBinaryBiproduct (K.X i) (L.X i) := fun _ ↦ inferInstance
    infer_instance

local instance : HasBinaryBiproducts (HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) where
  has_binary_biproduct K L := by
    delta HomologicalComplex₂
    infer_instance

local instance : (flipFunctor 𝒜 (up ℤ) (up ℤ)).Additive where
  map_add := by
    intro K L f g
    ext i j
    rfl

local instance : (totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).Additive where
  map_add := by
    intro K L f g
    ext i
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ h
    change K.ιTotal (up ℤ) i₁ i₂ i h ≫ (total.map (f + g) (up ℤ)).f i =
      K.ιTotal (up ℤ) i₁ i₂ i h ≫ ((total.map f (up ℤ)).f i + (total.map g (up ℤ)).f i)
    rw [Preadditive.comp_add]
    simp [Preadditive.add_comp]

/- Remark 13.10.8: viewing a double complex as
`\cdots \to A^{\bullet,-1} \to A^{\bullet,0} \to A^{\bullet,1} \to \cdots`, the induced
totalization functor on homotopy categories is the canonical owner
`(flipFunctor ⋙ totalFunctor).mapHomotopyCategory (up ℤ)`, and its exactness API is the inherited
`CommShift`/`IsTriangulated` structure on that owner. -/
#check
  (inferInstance :
    (((flipFunctor 𝒜 (up ℤ) (up ℤ)) ⋙ totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory
      (up ℤ)).CommShift ℤ)

#check
  (inferInstance :
    (((flipFunctor 𝒜 (up ℤ) (up ℤ)) ⋙ totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory
      (up ℤ)).IsTriangulated)

/- Viewing a double complex instead as
`\cdots \to A^{-1,\bullet} \to A^{0,\bullet} \to A^{1,\bullet} \to \cdots`, the induced
totalization functor on homotopy categories is the canonical owner
`(totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory (up ℤ)`, again with the inherited
`CommShift`/`IsTriangulated` structure. -/
#check
  (inferInstance :
    ((totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory (up ℤ)).CommShift ℤ)

#check
  (inferInstance :
    ((totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory (up ℤ)).IsTriangulated)

/-! ### Remark_13_10_9 (from Chap13) -/
open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory

noncomputable section

universe v₁ u₁ v₂ u₂ v₃ u₃

set_option checkBinderAnnotations false

section

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
  [Preadditive 𝒜] [Preadditive ℬ] [Preadditive 𝒞]
  [HasZeroObject 𝒜] [HasZeroObject ℬ] [HasZeroObject 𝒞]
  [HasBinaryBiproducts 𝒜] [HasBinaryBiproducts ℬ] [HasBinaryBiproducts 𝒞]
  [HasCountableCoproducts 𝒞]

variable (tensor : 𝒜 ⥤ ℬ ⥤ 𝒞)
variable [tensor.Additive] [∀ X : 𝒜, (tensor.obj X).Additive]
variable [∀ (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ),
  CochainComplex.HasMapBifunctor X Y tensor]

/-- A bilinear bifunctor preserves zero morphisms in the first variable. -/
noncomputable instance tensor_preservesZeroMorphisms : tensor.PreservesZeroMorphisms := sorry

/-- For a fixed left tensor factor, the induced functor preserves zero morphisms. -/
noncomputable instance tensor_obj_preservesZeroMorphisms (X : 𝒜) :
    (tensor.obj X).PreservesZeroMorphisms := sorry

-- Proof sketch: this is the identity case of `HomologicalComplex.mapBifunctorMap` with the left
-- factor fixed; the resulting morphism on total complexes is the identity.
/-- The complex-level tensor-totalization functor with fixed left factor preserves identities. -/
theorem tensor_right_complex_functor_map_id
    (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 X) (𝟙 Y) tensor (ComplexShape.up ℤ) =
      𝟙 (CochainComplex.mapBifunctor X Y tensor) := sorry

-- Proof sketch: functoriality of `HomologicalComplex.mapBifunctorMap` in the varying right factor
-- gives the composition law after totalization.
/-- The complex-level tensor-totalization functor with fixed left factor preserves composition. -/
theorem tensor_right_complex_functor_map_comp
    (X : CochainComplex 𝒜 ℤ) {Y₁ Y₂ Y₃ : CochainComplex ℬ ℤ}
    (φ : Y₁ ⟶ Y₂) (ψ : Y₂ ⟶ Y₃) :
    HomologicalComplex.mapBifunctorMap (𝟙 X) (φ ≫ ψ) tensor (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap (𝟙 X) φ tensor (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 X) ψ tensor (ComplexShape.up ℤ) := sorry

/-- The complex-level functor `Y^\bullet ↦ \mathrm{Tot}(X^\bullet \otimes Y^\bullet)` for a fixed
left tensor factor `X^\bullet`. -/
abbrev tensor_right_complex_functor (X : CochainComplex 𝒜 ℤ) :
    CochainComplex ℬ ℤ ⥤ CochainComplex 𝒞 ℤ where
  obj Y := CochainComplex.mapBifunctor X Y tensor
  map φ := HomologicalComplex.mapBifunctorMap (𝟙 X) φ tensor (ComplexShape.up ℤ)
  map_id Y := tensor_right_complex_functor_map_id tensor X Y
  map_comp φ ψ := tensor_right_complex_functor_map_comp tensor X φ ψ

-- Proof sketch: this is the identity case of `HomologicalComplex.mapBifunctorMap` with the right
-- factor fixed; the resulting total-complex morphism is the identity.
/-- The complex-level tensor-totalization functor with fixed right factor preserves identities. -/
theorem tensor_left_complex_functor_map_id
    (Y : CochainComplex ℬ ℤ) (X : CochainComplex 𝒜 ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 X) (𝟙 Y) tensor (ComplexShape.up ℤ) =
      𝟙 (CochainComplex.mapBifunctor X Y tensor) := sorry

-- Proof sketch: functoriality of `HomologicalComplex.mapBifunctorMap` in the varying left factor
-- gives the composition law after totalization.
/-- The complex-level tensor-totalization functor with fixed right factor preserves composition. -/
theorem tensor_left_complex_functor_map_comp
    (Y : CochainComplex ℬ ℤ) {X₁ X₂ X₃ : CochainComplex 𝒜 ℤ}
    (φ : X₁ ⟶ X₂) (ψ : X₂ ⟶ X₃) :
    HomologicalComplex.mapBifunctorMap (φ ≫ ψ) (𝟙 Y) tensor (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap φ (𝟙 Y) tensor (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap ψ (𝟙 Y) tensor (ComplexShape.up ℤ) := sorry

/-- The complex-level functor `X^\bullet ↦ \mathrm{Tot}(X^\bullet \otimes Y^\bullet)` for a fixed
right tensor factor `Y^\bullet`. -/
abbrev tensor_left_complex_functor (Y : CochainComplex ℬ ℤ) :
    CochainComplex 𝒜 ℤ ⥤ CochainComplex 𝒞 ℤ where
  obj X := CochainComplex.mapBifunctor X Y tensor
  map φ := HomologicalComplex.mapBifunctorMap φ (𝟙 Y) tensor (ComplexShape.up ℤ)
  map_id X := tensor_left_complex_functor_map_id tensor Y X
  map_comp φ ψ := tensor_left_complex_functor_map_comp tensor Y φ ψ

/-- A homotopy in the varying right complex induces a homotopy after tensor-totalization with a
fixed left factor. -/
  noncomputable def tensor_right_homotopy_of_homotopy
    (X : CochainComplex 𝒜 ℤ) {L M : CochainComplex ℬ ℤ} {α β : L ⟶ M} (h : Homotopy α β) :
    Homotopy
      (HomologicalComplex.mapBifunctorMap (𝟙 X) α tensor (ComplexShape.up ℤ))
      (HomologicalComplex.mapBifunctorMap (𝟙 X) β tensor (ComplexShape.up ℤ)) :=
  HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 X) h tensor (ComplexShape.up ℤ)

/-- A homotopy in the varying left complex induces a homotopy after tensor-totalization with a
fixed right factor. -/
noncomputable def tensor_left_homotopy_of_homotopy
    (Y : CochainComplex ℬ ℤ) {L M : CochainComplex 𝒜 ℤ} {α β : L ⟶ M} (h : Homotopy α β) :
    Homotopy
      (HomologicalComplex.mapBifunctorMap α (𝟙 Y) tensor (ComplexShape.up ℤ))
      (HomologicalComplex.mapBifunctorMap β (𝟙 Y) tensor (ComplexShape.up ℤ)) :=
  HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 Y) tensor (ComplexShape.up ℤ)

/-- The functor on `K(\mathcal B)` induced by tensor-totalization with a fixed left factor
`X^\bullet`. -/
abbrev tensor_right_homotopy_functor (X : CochainComplex 𝒜 ℤ) :
    HomotopyCategory ℬ (up ℤ) ⥤ HomotopyCategory 𝒞 (up ℤ) :=
  CategoryTheory.Quotient.lift _
    (tensor_right_complex_functor tensor X ⋙ HomotopyCategory.quotient 𝒞 (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _ (tensor_right_homotopy_of_homotopy tensor X h))

/-- The functor on `K(\mathcal A)` induced by tensor-totalization with a fixed right factor
`Y^\bullet`. -/
abbrev tensor_left_homotopy_functor (Y : CochainComplex ℬ ℤ) :
    HomotopyCategory 𝒜 (up ℤ) ⥤ HomotopyCategory 𝒞 (up ℤ) :=
  CategoryTheory.Quotient.lift _
    (tensor_left_complex_functor tensor Y ⋙ HomotopyCategory.quotient 𝒞 (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _ (tensor_left_homotopy_of_homotopy tensor Y h))

/-- The homotopy-category functor induced by a fixed left tensor factor commutes with shifts. -/
noncomputable instance tensor_right_homotopy_functor_commShift (X : CochainComplex 𝒜 ℤ) :
    (tensor_right_homotopy_functor tensor X).CommShift ℤ := sorry

/-- The homotopy-category functor induced by a fixed right tensor factor commutes with shifts. -/
noncomputable instance tensor_left_homotopy_functor_commShift (Y : CochainComplex ℬ ℤ) :
    (tensor_left_homotopy_functor tensor Y).CommShift ℤ := sorry

-- Proof sketch: apply Remark 13.10.8 to the double complexes obtained from the bifunctor `tensor`.
-- The induced functors on complexes respect homotopies by
-- `HomologicalComplex.mapBifunctorMapHomotopy₂` and
-- `HomologicalComplex.mapBifunctorMapHomotopy₁`, so they descend to `K(\mathcal B)` and
-- `K(\mathcal A)`. Exactness is encoded by `Functor.IsTriangulated`. For the right-variable shift,
-- the canonical isomorphism is the signed `CochainComplex.mapBifunctorShift₂Iso`.
/-- Remark 13.10.9: fixing either factor of a bilinear functor
`\otimes : \mathcal A ⥤ \mathcal B ⥤ \mathcal C` yields an exact functor on homotopy categories,
namely `Y^\bullet ↦ \mathrm{Tot}(X^\bullet \otimes Y^\bullet)` on `K(\mathcal B)` and
`X^\bullet ↦ \mathrm{Tot}(X^\bullet \otimes Y^\bullet)` on `K(\mathcal A)`. -/
theorem tensor_left_right_homotopy_functor_isTriangulated
    (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ) :
    (tensor_right_homotopy_functor tensor X).IsTriangulated ∧
      (tensor_left_homotopy_functor tensor Y).IsTriangulated := sorry

end
