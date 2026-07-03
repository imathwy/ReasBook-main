import Mathlib
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_33_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Preadditive D]

/- Domain-style sampling for Definition 13.33.1:
- primary domain: telescope triangles for sequential diagrams in a preadditive / triangulated
  category;
- sampled owner declarations:
  `CategoryTheory.Functor.ofSequence`,
  `CategoryTheory.Functor.ofSequence_map_homOfLE_succ`,
  `CategoryTheory.Limits.Sigma.map'`,
  `CategoryTheory.Limits.Sigma.ι_comp_map'`;
- best owner abstraction: the canonical sequential diagram `K : ℕ ⥤ D`;
- primitive-vs-derived split:
  the primitive data are the diagram `K`;
  the telescope endomorphism and the homotopy-colimit predicate are derived API built from `K`.

Source/core/bridge triage:
- `source-facing`: the telescope morphism `1 - f` and the distinguished-triangle predicate
  defining a homotopy colimit of a sequential diagram;
- `core/canonical`: the owner `K : ℕ ⥤ D`;
- `bridge/view`: `Functor.ofSequence`, used downstream to pass from a textbook family
  `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` to the canonical owner. -/

/-- The telescope endomorphism `1 - f` of the coproduct of a sequential diagram. -/
def sequentialTelescopeMap (K : ℕ ⥤ D) [HasCoproduct K.obj] :
    ∐ K.obj ⟶ ∐ K.obj :=
  𝟙 _ - Sigma.map' Nat.succ (fun n ↦ K.map (homOfLE (Nat.le_succ n)))

/-- On the `n`th coproduct summand, the telescope map is `1 - f_n`. -/
@[reassoc]
theorem Sigma.ι_comp_sequentialTelescopeMap (K : ℕ ⥤ D) [HasCoproduct K.obj] (n : ℕ) :
    Sigma.ι K.obj n ≫ sequentialTelescopeMap K =
      Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
  simp [sequentialTelescopeMap, Preadditive.comp_sub]

attribute [simp] Sigma.ι_comp_sequentialTelescopeMap_assoc

/-- The telescope map is natural with respect to morphisms of sequential diagrams. -/
@[reassoc]
theorem sequentialTelescopeMap_naturality {K L : ℕ ⥤ D}
    [HasCoproduct K.obj] [HasCoproduct L.obj] (φ : K ⟶ L) :
    sequentialTelescopeMap K ≫ Limits.Sigma.map φ.app =
      Limits.Sigma.map φ.app ≫ sequentialTelescopeMap L := by
  apply Sigma.hom_ext
  intro n
  simp [sequentialTelescopeMap, Preadditive.comp_sub, Preadditive.sub_comp,
    φ.naturality_assoc]

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Definition 13.33.1: assuming the direct sum `∐ n, K n` exists, an object `K∞` is a derived
colimit, or homotopy colimit, of a sequential system `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` if it occurs as the
third object of a distinguished triangle whose first morphism is the telescope map `1 - f`. -/
def IsHomotopyColimitOf (K : ℕ ⥤ D) [HasCoproduct K.obj] (Khocolim : D) :
    Prop :=
  ∃ (g : ∐ K.obj ⟶ Khocolim) (h : Khocolim ⟶ (∐ K.obj)⟦(1 : ℤ)⟧),
    Triangle.mk (sequentialTelescopeMap K) g h ∈ distTriang D

end

end CategoryTheory

/-! ### Remark_13_33_2 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling for Remark 13.33.2:
- primary domain: sequential homotopy colimits in a pretriangulated category;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.sequentialTelescopeMap`,
  `CategoryTheory.Limits.Sigma.desc`,
  `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`,
  `CategoryTheory.exists_distinguished_triangle_unique_up_to_iso`;
- best owner abstraction: the chapter owner predicate `IsHomotopyColimitOf S Khocolim`;
- primitive-vs-derived split:
  the primitive source-facing presentation data are the maps `ι : ∀ n, S.obj n ⟶ K`, the
  connecting morphism `c : K ⟶ ∐ n, S.obj n⟦1⟧`, and the distinguished telescope triangle;
  the compatibility relation `S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n` is derived from
  that triangle and should not be stored as primitive public data.

Source/core/bridge triage:
- `source-facing`: an explicit telescope presentation by structure maps and a distinguished
  triangle;
- `core/canonical`: `IsHomotopyColimitOf S Khocolim`;
- `bridge/view`: the theorems below converting between the canonical owner and explicit
  source-style presentation data. -/

variable {S : ℕ ⥤ D} [HasCoproduct S.obj]
  [HasCoproduct (fun n ↦ S.obj n⟦(1 : ℤ)⟧)]

/-- In a distinguished telescope triangle, the induced structure maps from the coproduct summands
are automatically compatible with the sequential transition maps. -/
theorem telescopePresentation_compat {Khocolim : D} (ι : ∀ n, S.obj n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D) (n : ℕ) :
    S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n := by
  have hzero :
      sequentialTelescopeMap S ≫ Limits.Sigma.desc ι = 0 := by
    simpa [Triangle.mk] using comp_distTriang_mor_zero₁₂ _ hK
  have hcompat :
      ι n - S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = 0 := by
    have hzero' := congrArg (fun f ↦ Sigma.ι S.obj n ≫ f) hzero
    simpa [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp, Limits.Sigma.ι_desc,
      Category.assoc, comp_zero] using hzero'
  have hcompat' : ι n = S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) := by
    simpa [sub_eq_zero] using hcompat
  simpa using hcompat'.symm

namespace IsHomotopyColimitOf

/-- A homotopy-colimit object admits source-style structure maps from each term and a connecting
morphism whose telescope triangle is distinguished; the compatibility of the structure maps is
derived, not additional primitive data. -/
theorem exists_presentation {Khocolim : D} (hK : IsHomotopyColimitOf S Khocolim) :
    ∃ (ι : ∀ n, S.obj n ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧),
      (∀ n, S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n) ∧
        Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
          (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
            distTriang D := by
  rcases hK with ⟨g, h, htriangle⟩
  let ι : ∀ n, S.obj n ⟶ Khocolim := fun n ↦ Sigma.ι S.obj n ≫ g
  let c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧ :=
    h ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).hom
  have hdesc : Limits.Sigma.desc ι = g := by
    apply Limits.Sigma.hom_ext
    intro n
    simpa [ι] using Limits.Sigma.ι_desc ι n
  have hc :
      c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv = h := by
    dsimp [c]
    have hc' :
        h ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).hom ≫
            (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv =
          h ≫ 𝟙 _ := by
      exact congrArg (fun f ↦ h ≫ f)
        (Iso.hom_inv_id (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj))
    simpa [Category.assoc] using hc'
  have hpresentation :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D := by
    rw [hdesc, hc]
    exact htriangle
  refine ⟨ι, c, ?_, hpresentation⟩
  intro n
  exact telescopePresentation_compat ι c hpresentation n

end IsHomotopyColimitOf

-- Proof sketch: both source-style presentations define distinguished telescope triangles with the
-- same first morphism. Apply the upstream comparison theorem
-- `exists_distinguished_triangle_unique_up_to_iso` from Lemma `13.4.7` to those two triangles and
-- extract the third component of the resulting triangle isomorphism.
/-- Any two source-style telescope presentations of a sequential homotopy colimit are isomorphic
through a map compatible with the structure maps and with the connecting morphisms. -/
theorem exists_iso_between_derived_colimit_presentations {Khocolim Khocolim' : D}
    (ι : ∀ n, S.obj n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D)
    (ι' : ∀ n, S.obj n ⟶ Khocolim') (c' : Khocolim' ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK' :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι')
        (c' ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D) :
    ∃ e : Khocolim ≅ Khocolim',
      (∀ n, ι n ≫ e.hom = ι' n) ∧
        e.hom ≫ c' = c := by
  obtain ⟨eT, he₁, he₂⟩ := exists_distinguished_triangle_unique_up_to_iso hK hK'
  refine ⟨Triangle.π₃.mapIso eT, ?_, ?_⟩
  · intro n
    have comm₂ := eT.hom.comm₂
    simpa [Limits.Sigma.ι_desc, Limits.Sigma.ι_desc_assoc, he₂] using
      congrArg (fun f ↦ Sigma.ι S.obj n ≫ f) comm₂
  · apply (cancel_mono (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv).1
    have comm₃ := eT.hom.comm₃
    simpa [he₁, Category.assoc] using comm₃.symm

-- Proof sketch: this is exactly the comparison theorem for two telescope presentations proved
-- above, restated as the label-associated entry for the Stacks remark.
/-- Remark 13.33.2: any two source-style telescope presentations of a sequential derived colimit
are canonically isomorphic through a map compatible with the structure maps and the connecting
morphisms of the distinguished triangles. -/
theorem exists_iso_between_derivedColimit_presentations {Khocolim Khocolim' : D}
    (ι : ∀ n, S.obj n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D)
    (ι' : ∀ n, S.obj n ⟶ Khocolim')
    (c' : Khocolim' ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK' :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι')
        (c' ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D) :
    ∃ e : Khocolim ≅ Khocolim',
      (∀ n, ι n ≫ e.hom = ι' n) ∧
        e.hom ≫ c' = c := by
  exact exists_iso_between_derived_colimit_presentations ι c hK ι' c' hK'

end

end CategoryTheory

/-! ### Remark_13_33_3 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-
Domain-style sampling for Remark 13.33.3:
- primary domain: morphisms between telescope triangles in a pretriangulated category;
- sampled owner declarations:
  `CategoryTheory.NatTrans.ofSequence`,
  `CategoryTheory.sequentialTelescopeMap_naturality`,
  `CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism`,
  `CategoryTheory.Pretriangulated.completeDistinguishedTriangleMorphism`,
  `CategoryTheory.TriangleMorphism`;
- best owner abstraction: the TR3 existence theorem
  `Pretriangulated.complete_distinguished_triangle_morphism`, with `TriangleMorphism` as the
  canonical bridge/view packaging;
- primitive-vs-derived split:
  the primitive data are the sequential diagrams `S`, `T`, a natural transformation `α : S ⟶ T`,
  and the two distinguished telescope presentations;
  the map between the two derived-colimit objects is derived API, namely the third component of a
  triangle morphism completing the telescope-map square.

Source/core/bridge triage:
- `source-facing`: a morphism of sequential systems together with two chosen telescope
  presentations;
- `core/canonical`: `Pretriangulated.complete_distinguished_triangle_morphism`;
- `bridge/view`: `TriangleMorphism`, `NatTrans.ofSequence`, and
  `sequentialTelescopeMap_naturality`. -/

variable {S T : ℕ ⥤ D} [HasCoproduct S.obj] [HasCoproduct T.obj]
  [HasCoproduct (fun n ↦ S.obj n⟦(1 : ℤ)⟧)] [HasCoproduct (fun n ↦ T.obj n⟦(1 : ℤ)⟧)]

-- Proof sketch: apply the TR3 owner `complete_distinguished_triangle_morphism` to the two chosen
-- telescope triangles and to the commuting square
-- `sequentialTelescopeMap_naturality α`. The resulting third component is the required map
-- between the two chosen derived-colimit objects. For source-style component maps `aₙ`, first
-- package them as `NatTrans.ofSequence aₙ ...`.
/-- Remark 13.33.3: a morphism of sequential systems induces at least one morphism between any two
chosen derived-colimit presentations, compatible with the structure maps and the connecting maps of
the two telescope triangles. No uniqueness is asserted. -/
theorem exists_morphism_between_derivedColimit_presentations (α : S ⟶ T)
    {Kcolim Lcolim : D} (i : ∀ n : ℕ, S.obj n ⟶ Kcolim) (j : ∀ n : ℕ, T.obj n ⟶ Lcolim)
    (c : Kcolim ⟶ ∐ fun n : ℕ ↦ S.obj n⟦(1 : ℤ)⟧)
    (d : Lcolim ⟶ ∐ fun n : ℕ ↦ T.obj n⟦(1 : ℤ)⟧)
    (hS : Triangle.mk (sequentialTelescopeMap S)
      (Limits.Sigma.desc i)
      (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈ distTriang D)
    (hT : Triangle.mk (sequentialTelescopeMap T)
      (Limits.Sigma.desc j)
      (d ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) T.obj).inv) ∈ distTriang D) :
    ∃ a : Kcolim ⟶ Lcolim,
      CommSq (Limits.Sigma.desc i) (Limits.Sigma.map α.app) a (Limits.Sigma.desc j) ∧
        CommSq
          (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv)
          a
          ((Limits.Sigma.map α.app)⟦(1 : ℤ)⟧')
          (d ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) T.obj).inv) := by
  obtain ⟨a, ha₂, ha₃⟩ :=
    complete_distinguished_triangle_morphism _ _ hS hT (Limits.Sigma.map α.app)
      (Limits.Sigma.map α.app) (by simpa using sequentialTelescopeMap_naturality α)
  exact ⟨a, ⟨ha₂⟩, ⟨ha₃⟩⟩

end

end CategoryTheory

/-! ### Lemma_13_33_4 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D]

/- Domain-style sampling for Lemma 13.33.4:
- primary domain: sequential diagrams in a triangulated category, together with homotopy colimits
  and the source-facing structure maps from Remark 13.33.2;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.IsHomotopyColimitOf.exists_presentation`,
  `CategoryTheory.exists_iso_between_derived_colimit_presentations`,
  `CategoryTheory.sequentialTelescopeMap`,
  `Preorder.Monotone.functor`;
- best owner abstraction: the original sequential system is the canonical diagram `K : ℕ ⥤ D`;
  `IsHomotopyColimitOf K X` is the core owner, and a subsequence should be only a thin
  reindexing view of `K`, not a new ambient system owner;
- primitive-vs-derived split:
  the primitive data are the sequential diagram `K` and the strictly increasing index function
  `s : ℕ → ℕ`;
  the reindexed subsystem is derived API obtained by precomposing `K` with the monotone functor
  induced by `s`, while the explicit telescope-presentation maps and distinguished-triangle
  witnesses remain bridge-level source-facing data.

Source/core/bridge triage:
- `source-facing`: the sequential system `(K_n, f_n)` and the chosen subsequence of indices;
- `core/canonical`: the predicate `IsHomotopyColimitOf K X`;
- `bridge/view`: the reindexed diagram `hs.monotone.functor ⋙ K`, obtained by precomposing `K`
  along the monotone functor attached to the strictly increasing map `s`, together with the
  explicit telescope-presentation data used to compare chosen structure maps. -/

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

-- Proof sketch: use Remark 13.33.2 to choose source-style telescope presentations from each
-- `IsHomotopyColimitOf` hypothesis, compare them using the subsequence reindexing bridge from
-- Remarks 13.33.2 and 13.33.3, and transport the resulting isomorphism back to the canonical
-- owner predicate. The converse direction is symmetric.
/-- Lemma 13.33.4: an object is a homotopy colimit of a strictly increasing
subsequence if and only if it is a homotopy colimit of the original sequential system. -/
theorem isHomotopyColimitOf_subsequence_iff
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Khocolim : D} :
    IsHomotopyColimitOf (hs.monotone.functor ⋙ K) Khocolim ↔ IsHomotopyColimitOf K Khocolim :=
  sorry

end

end CategoryTheory

/-! ### Lemma_13_33_5 (from Chap13) -/
open CategoryTheory Limits
open DerivedCategory

universe w v u uI

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.33.5:
- primary domain: coproducts in derived categories, with the colimit structure owned by
  `IsColimit` and transported along a functor through preservation of the corresponding discrete
  colimit;
- inspected owner declarations:
  `CategoryTheory.Limits.coproductIsCoproduct`,
  `CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit`,
  `CategoryTheory.Limits.isColimitOfHasCoproductOfPreservesColimit`,
  `CategoryTheory.Limits.hasCoproducts_of_colimit_cofans`,
  `CategoryTheory.CountableAB4`;
- best owner abstraction: `PreservesColimit (Discrete.functor K) DerivedCategory.Q`, together with
  the induced canonical `IsColimit` witness on `DerivedCategory.Q.obj (∐ K)` and the resulting
  countable-coproduct owner on `DerivedCategory 𝒜`;
- primitive-vs-derived split:
  the primitive data in this item are the countable family `K` and the exactness hypothesis
  encoded by `CountableAB4 𝒜`, which already carries countable coproducts; the explicit
  `IsColimit` witness for the canonical cofan and the ambient countable-coproduct structure on
  `DerivedCategory 𝒜` are derived API and should be obtained from the owner preservation
  predicate rather than stored primitively.
-/

/-
Source/core/bridge triage for Lemma 13.33.5:
- source-facing: the Stacks lemma says that `DerivedCategory.Q.obj (∐ K)` with the canonical maps
  from the summands is a coproduct of the images of `K`, so the file should expose the resulting
  canonical `IsColimit` witness directly and package it into the ambient countable-coproduct owner
  for `DerivedCategory 𝒜`;
- core/canonical: coproduct preservation for `DerivedCategory.Q`, expressed as
  `PreservesColimit (Discrete.functor K) DerivedCategory.Q`;
- bridge/view: the source-facing coproduct witness is obtained by applying
  `Limits.isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q K` after establishing the
  owner instance below, and arbitrary countable derived families are then handled by choosing
  representatives with `DerivedCategory.Q.objPreimage`; downstream files should reuse these
  bridges instead of rebuilding bespoke `HasCoproduct` witnesses.
-/

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable {α : Type uI}

section

variable [HasCoproductsOfShape α 𝒜] [HasExactColimitsOfShape (Discrete α) 𝒜]

-- Proof sketch: exact countable coproducts imply that the localization functor to the derived
-- category preserves the coproduct of any countable family of cochain complexes.
private theorem derivedCategory_Q_preserves_coproduct_of_exact
    (K : α → CochainComplex 𝒜 ℤ) :
    PreservesColimit (Discrete.functor K) Q := by
  sorry

end

-- `CountableAB4.ofShape` is small-universe, so transport it across `Shrink` for arbitrary
-- countable index types.
private theorem hasExactColimitsOfShape_of_countable
    {C : Type u} [Category.{v} C] [HasCountableCoproducts C] [CountableAB4 C]
    (α : Type uI) [Countable α] :
    HasExactColimitsOfShape (Discrete α) C := by
  letI : Countable (Shrink.{0} α) := Countable.of_equiv α (equivShrink.{0} α)
  letI : HasExactColimitsOfShape (Discrete (Shrink.{0} α)) C :=
    CountableAB4.ofShape (Shrink.{0} α)
  exact HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence (equivShrink.{0} α)).symm

section

variable [HasCountableCoproducts 𝒜] [CountableAB4 𝒜] [Countable α]

-- Proof sketch: recover exactness of `α`-indexed coproducts from the countable `AB4` owner on
-- `𝒜`, then apply the exact-coproduct preservation lemma above.
/-- Exact countable direct sums make the localization functor `DerivedCategory.Q` preserve the
coproduct of any countable family of cochain complexes. -/
theorem derivedCategory_Q_preserves_countableCoproduct
    (K : α → CochainComplex 𝒜 ℤ) :
    PreservesColimit (Discrete.functor K) Q := by
  letI : HasExactColimitsOfShape (Discrete α) 𝒜 := hasExactColimitsOfShape_of_countable α
  exact derivedCategory_Q_preserves_coproduct_of_exact K

/-- The image in the derived category of the termwise direct sum of a countable family of
cochain complexes is a coproduct of the corresponding family of derived-category objects. -/
noncomputable def derivedCategory_coproduct_isColimit_of_termwise_countableDirectSums
    (K : α → CochainComplex 𝒜 ℤ) :
    IsColimit (Cofan.mk (Q.obj (∐ K)) fun i ↦ Q.map (Sigma.ι K i)) :=
  letI := derivedCategory_Q_preserves_countableCoproduct K
  isColimitOfHasCoproductOfPreservesColimit Q K

attribute [instance] derivedCategory_Q_preserves_countableCoproduct

end

section

variable [HasCountableCoproducts 𝒜] [CountableAB4 𝒜]

-- Proof sketch: for each countable index type `α`, transport the small-universe owner
-- `CountableAB4.ofShape` across `Shrink` to recover exactness of `α`-indexed coproducts in `𝒜`,
-- then apply the canonical cofan theorem above to each family of complexes.
/-- Exact countable coproducts in `𝒜` induce `α`-indexed coproducts in `D(\mathcal A)`. -/
noncomputable instance derivedCategory_hasCoproductsOfShape_of_exactCountableCoproducts
    (α : Type uI) [Countable α] :
    HasCoproductsOfShape α (DerivedCategory 𝒜) where
  has_colimit F := by
    letI : HasExactColimitsOfShape (Discrete α) 𝒜 := hasExactColimitsOfShape_of_countable α
    let X : α → DerivedCategory 𝒜 := fun i ↦ F.obj ⟨i⟩
    let K : α → CochainComplex 𝒜 ℤ := fun i ↦ Q.objPreimage (X i)
    let eK : ∀ i, Q.obj (K i) ≅ X i := fun i ↦ Q.objObjPreimageIso (X i)
    let e : Discrete.functor (fun i ↦ Q.obj (K i)) ≅ Discrete.functor X :=
      Discrete.natIso fun i : Discrete α ↦ eK i.as
    have hX :
        IsColimit (Cofan.mk (Q.obj (∐ K)) fun i ↦ (eK i).inv ≫ Q.map (Sigma.ι K i)) := by
      exact (IsColimit.precomposeInvEquiv e
        (Cofan.mk (Q.obj (∐ K)) fun i ↦ Q.map (Sigma.ι K i))).symm
        (derivedCategory_coproduct_isColimit_of_termwise_countableDirectSums K)
    refine HasColimit.mk
      ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj
          (Cofan.mk (Q.obj (∐ K)) fun i ↦ (eK i).inv ≫ Q.map (Sigma.ι K i)),
        ?_⟩
    exact (IsColimit.precomposeHomEquiv _ _).symm hX

/-- Exact countable coproducts in `𝒜` induce countable coproducts in `D(\mathcal A)`. -/
noncomputable instance derivedCategory_hasCountableCoproducts_of_exactCountableCoproducts :
    HasCountableCoproducts (DerivedCategory 𝒜) where
  out _ := inferInstance

end

end

end CategoryTheory

/-! ### Lemma_13_33_6 (from Chap13) -/
open CategoryTheory.Limits
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasColimitsOfShape ℕ C]

/- Domain-style sampling for Lemma 13.33.6:
- primary domain: exactness of countable coproducts in abelian categories obtained from exact
  sequential colimits, together with the canonical telescope map for a sequential diagram;
- inspected owner declarations:
  `CategoryTheory.CountableAB4.of_countableAB5`,
  `CategoryTheory.Limits.liftToFinsetColimitCocone`,
  `CategoryTheory.sequentialTelescopeMap`,
  `CategoryTheory.Functor.ofSequence`;
- best owner abstraction: the Grothendieck-axiom owner `CountableAB4.of_countableAB5`, with the
  internal countable-coproduct bridge below supplying the remaining owner hypothesis from
  sequential colimits;
- primitive-vs-derived split:
  the primitive data here are finite coproducts, sequential colimits, and the diagram `K : ℕ ⥤ C`;
  the countable-coproduct structure and the `CountableAB4` consequence are derived API, while the
  telescope comparison map to the sequential colimit is the source-facing morphism needed
  downstream.

Source/core/bridge triage:
- `source-facing`: the telescope map to the sequential colimit and the resulting short exact
  sequence;
- `core/canonical`: `CountableAB4.of_countableAB5`;
- `bridge/view`: the local instance below, which supplies the owner theorem with its remaining
  hypothesis at exactly the assumption level used in this file family. -/

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

-- Proof sketch: compute on each coproduct summand. The identity part of
-- `sequentialTelescopeMap K = 𝟙 - Sigma.map' Nat.succ _` contributes the
-- colimit cocone leg
-- `colimit.ι _ n`, and the shifted part contributes
-- `K.map (homOfLE (Nat.le_add_right n 1)) ≫ colimit.ι _ (n + 1) = colimit.ι _ n` by cocone
-- naturality, so the difference is zero.
/-- The telescope map of a sequential diagram becomes zero after postcomposition with any
compatible cocone map. -/
theorem sequentialTelescopeMap_comp_sigmaDesc
    (K : ℕ ⥤ C) [HasCoproduct K.obj] {X : C} (ι : ∀ n, K.obj n ⟶ X)
    (hι : ∀ n, K.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n) :
    sequentialTelescopeMap K ≫ Limits.Sigma.desc ι = 0 := by
  apply Limits.Sigma.hom_ext
  intro n
  rw [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp, comp_zero, sub_eq_zero,
    Sigma.ι_desc]
  rw [Category.assoc, Sigma.ι_desc]
  exact (hι n).symm

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasColimitsOfShape ℕ 𝒜]

/-- Sequential colimits in an abelian category induce countable coproducts by expressing a
countable family as the filtered colimit of its finite partial sums. -/
theorem hasCountableCoproducts_of_sequentialColimits : HasCountableCoproducts 𝒜 where
  out J := by
    intro _
    classical
    let _ : HasColimitsOfShape (Finset (Discrete J)) 𝒜 :=
      Functor.Final.hasColimitsOfShape_of_final
        (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    exact ⟨fun F ↦ HasColimit.mk (liftToFinsetColimitCocone F)⟩

local instance : HasCountableCoproducts 𝒜 := hasCountableCoproducts_of_sequentialColimits

/- Exactness of countable direct sums from exact sequential colimits is provided by the canonical
Grothendieck-axiom owner `CategoryTheory.CountableAB4.of_countableAB5`, applied with the bridge
above supplying countable coproducts from sequential colimits internally. -/
recall CountableAB4.of_countableAB5

/-- Helper for Lemma 13.33.6: the canonical map from the countable coproduct to the sequential
colimit presents a cokernel of the telescope map. -/
theorem sigma_desc_cokernelCofork_nonempty_of_sequentialTelescope
    [HasExactColimitsOfShape ℕ 𝒜] (K : ℕ ⥤ 𝒜) :
    Nonempty
      (IsColimit
      (CokernelCofork.ofπ (Limits.Sigma.desc (colimit.ι K))
        (sequentialTelescopeMap_comp_sigmaDesc K (colimit.ι K)
          (fun n ↦ colimit.w K (homOfLE (Nat.le_succ n)))))) := by
  -- The universal property of the sequential colimit turns any cocone-killing map on the
  -- coproduct into the unique factor through `Sigma.desc (colimit.ι K)`.
  refine ⟨CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk ↦ ?_⟩
  -- Each coproduct summand provides a cocone leg once the telescope relation is read off from
  -- the vanishing of `sequentialTelescopeMap K ≫ k`.
  have hkCompat :
      ∀ n,
        K.map (homOfLE (Nat.le_succ n)) ≫ (Sigma.ι K.obj (n + 1) ≫ k) =
          Sigma.ι K.obj n ≫ k := by
    intro n
    have hzero : Sigma.ι K.obj n ≫ sequentialTelescopeMap K ≫ k = 0 := by
      simpa using congrArg (fun t ↦ Sigma.ι K.obj n ≫ t) hk
    have hdiff :
        Sigma.ι K.obj n ≫ k - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) ≫ k = 0 := by
      simpa [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp, Category.assoc] using
        hzero
    have hEq :
        Sigma.ι K.obj n ≫ k = K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) ≫ k := by
      simpa [sub_eq_zero] using hdiff
    exact hEq.symm
  have hkNat :
      ∀ n,
        K.map (homOfLE (Nat.le_succ n)) ≫ (Sigma.ι K.obj (n + 1) ≫ k) =
          (Sigma.ι K.obj n ≫ k) ≫ ((Functor.const ℕ).obj A).map (homOfLE (Nat.le_succ n)) := by
    intro n
    simpa using hkCompat n
  let c : Cocone K :=
    Cocone.mk A <|
      NatTrans.ofSequence
        (fun n ↦ Sigma.ι K.obj n ≫ k)
        hkNat
  refine ⟨colimit.desc K c, ?_⟩
  -- The factorization is checked on each coproduct summand.
  apply Limits.Sigma.hom_ext
  intro n
  have hι :
      Sigma.ι K.obj n ≫ Limits.Sigma.desc (colimit.ι K) ≫ colimit.desc K c =
        colimit.ι K n ≫ colimit.desc K c := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ t ≫ colimit.desc K c) (Limits.Sigma.ι_desc (colimit.ι K) n)
  rw [hι, colimit.ι_desc]
  simp [c]

/-- Helper for Lemma 13.33.6: the `n`th finite partial sum of a sequential diagram, built
recursively by adjoining one more summand. -/
def finite_prefix_obj [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) : ℕ → 𝒜
  | 0 => (0 : 𝒜)
  | n + 1 => finite_prefix_obj K n ⊞ K.obj n

/-- Helper for Lemma 13.33.6: the canonical inclusion of one finite prefix into the next. -/
def finite_prefix_inclusion [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) (n : ℕ) :
    finite_prefix_obj K n ⟶ finite_prefix_obj K (n + 1) :=
  biprod.inl

/-- Helper for Lemma 13.33.6: the inclusion of the new last summand into the next finite prefix. -/
def finite_prefix_lastι [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) (n : ℕ) :
    K.obj n ⟶ finite_prefix_obj K (n + 1) :=
  biprod.inr

/-- Helper for Lemma 13.33.6: the recursively corrected projection from a finite prefix to its
last quotient summand. -/
def finite_prefix_stage_projection [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    (n : ℕ) → finite_prefix_obj K (n + 1) ⟶ K.obj n
  | 0 => biprod.snd
  | n + 1 =>
      biprod.desc
        (finite_prefix_stage_projection K n ≫ K.map (homOfLE (Nat.le_succ n)))
        (𝟙 _)

/-- Helper for Lemma 13.33.6: the finite-stage telescope map
`A₀ ⊞ ⋯ ⊞ Aₙ₋₁ ⟶ A₀ ⊞ ⋯ ⊞ Aₙ`. -/
def finite_prefix_stage_map [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    (n : ℕ) → finite_prefix_obj K n ⟶ finite_prefix_obj K (n + 1)
  | 0 => finite_prefix_inclusion K 0
  | n + 1 =>
      biprod.desc
        (finite_prefix_stage_map K n ≫ finite_prefix_inclusion K (n + 1))
        (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1) -
          K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1))

/-- Helper for Lemma 13.33.6: the recursive retraction showing that each finite-stage telescope
map is split mono. -/
def finite_prefix_stage_retraction [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    (n : ℕ) → finite_prefix_obj K (n + 1) ⟶ finite_prefix_obj K n
  | 0 => biprod.fst
  | n + 1 =>
      biprod.desc
        (biprod.lift (finite_prefix_stage_retraction K n)
          (finite_prefix_stage_projection K n))
        0

/-- Helper for Lemma 13.33.6: the last summand of a finite prefix is sent isomorphically to the
stage quotient. -/
theorem finite_prefix_lastι_comp_projection [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_lastι K n ≫ finite_prefix_stage_projection K n = 𝟙 _ :=
  by
    intro n
    -- The quotient map reads off the newest biproduct summand directly.
    cases n with
    | zero =>
        rw [finite_prefix_lastι, finite_prefix_stage_projection]
        exact biprod.inr_snd
    | succ n =>
        rw [finite_prefix_lastι, finite_prefix_stage_projection]
        exact biprod.inr_desc _ _

/-- Helper for Lemma 13.33.6: the newest last summand is annihilated by the recursive retraction. -/
theorem finite_prefix_lastι_comp_retraction [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_lastι K n ≫ finite_prefix_stage_retraction K n = 0 :=
  by
    intro n
    -- The retraction discards the newest outer summand by construction.
    cases n with
    | zero =>
        rw [finite_prefix_lastι, finite_prefix_stage_retraction]
        exact biprod.inr_fst
    | succ n =>
        rw [finite_prefix_lastι, finite_prefix_stage_retraction]
        exact biprod.inr_desc _ _

/-- Helper for Lemma 13.33.6: the old finite-prefix inclusion becomes the previous stage
projection followed by the next transition map after postcomposition with the successor-stage
projection. -/
theorem finite_prefix_inclusion_comp_stage_projection [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ) :
    finite_prefix_inclusion K (n + 1) ≫ finite_prefix_stage_projection K (n + 1) =
      finite_prefix_stage_projection K n ≫ K.map (homOfLE (Nat.le_succ n)) := by
  -- The successor-stage projection is defined by descending from the old prefix and the new
  -- summand, so the old inclusion picks out the transported previous projection.
  rw [finite_prefix_inclusion, finite_prefix_stage_projection]
  exact biprod.inl_desc _ _

/-- Helper for Lemma 13.33.6: the correction term in the successor-stage telescope map is killed
by the successor-stage projection. -/
theorem finite_prefix_correction_comp_stage_projection [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ) :
    ((finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) -
        (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1))) ≫
      finite_prefix_stage_projection K (n + 1) = 0 := by
  -- Route correction: normalize the raw correction term after postcomposition first, so both
  -- summands become the same transition map and cancel before re-entering the wrapped branch proof.
  rw [Preadditive.sub_comp]
  have hold :
      (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
          finite_prefix_stage_projection K (n + 1) =
        K.map (homOfLE (Nat.le_succ n)) := by
    calc
      (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
          finite_prefix_stage_projection K (n + 1) =
        finite_prefix_lastι K n ≫
          (finite_prefix_inclusion K (n + 1) ≫ finite_prefix_stage_projection K (n + 1)) := by
            simp [Category.assoc]
      _ = finite_prefix_lastι K n ≫
          (finite_prefix_stage_projection K n ≫ K.map (homOfLE (Nat.le_succ n))) := by
            rw [finite_prefix_inclusion_comp_stage_projection]
      _ = (finite_prefix_lastι K n ≫ finite_prefix_stage_projection K n) ≫
          K.map (homOfLE (Nat.le_succ n)) := by
            simp [Category.assoc]
      _ = K.map (homOfLE (Nat.le_succ n)) := by
            rw [finite_prefix_lastι_comp_projection, Category.id_comp]
  have hnew :
      (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
          finite_prefix_stage_projection K (n + 1) =
        K.map (homOfLE (Nat.le_succ n)) := by
    calc
      (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
          finite_prefix_stage_projection K (n + 1) =
        K.map (homOfLE (Nat.le_succ n)) ≫
          (finite_prefix_lastι K (n + 1) ≫ finite_prefix_stage_projection K (n + 1)) := by
            simp [Category.assoc]
      _ = K.map (homOfLE (Nat.le_succ n)) := by
            rw [finite_prefix_lastι_comp_projection, Category.comp_id]
  rw [hold, hnew]
  exact sub_self _

/-- Helper for Lemma 13.33.6: on the old summands, the successor-stage telescope map followed by
the stage projection is the previous stage projection transported by the next transition map. -/
theorem finite_prefix_stage_projection_successor_old_branch [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ) :
    biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_projection K (n + 1) =
      finite_prefix_stage_map K n ≫ finite_prefix_stage_projection K n ≫
        K.map (homOfLE (Nat.le_succ n)) := by
  -- The old branch of the successor-stage map is the previous stage map followed by the old
  -- inclusion, so the raw inclusion/projection formula finishes the transport.
  rw [finite_prefix_stage_map, biprod.inl_desc_assoc, Category.assoc,
    finite_prefix_inclusion_comp_stage_projection]

/-- Helper for Lemma 13.33.6: on the newest summand, the successor-stage projection cancels the
correction term in the telescope map. -/
theorem finite_prefix_stage_projection_successor_new_branch [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ) :
    biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_projection K (n + 1) = 0 := by
  -- The wrapped new branch is exactly the raw correction term after precomposing with
  -- `biprod.inr`.
  rw [finite_prefix_stage_map, biprod.inr_desc_assoc]
  exact finite_prefix_correction_comp_stage_projection K n

/-- Helper for Lemma 13.33.6: the finite-stage telescope map kills the corrected projection to the
new quotient summand. -/
theorem finite_prefix_stage_map_comp_projection [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_stage_map K n ≫ finite_prefix_stage_projection K n = 0 :=
  by
    intro n
    induction n with
    | zero =>
        -- At the initial stage the telescope map is the old inclusion into the first biproduct.
        rw [finite_prefix_stage_map, finite_prefix_stage_projection]
        exact biprod.inl_snd
    | succ n ih =>
        -- Compare the successor-stage composite on the old and new summands separately.
        apply biprod.hom_ext'
        · calc
            biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫
                finite_prefix_stage_projection K (n + 1) =
              finite_prefix_stage_map K n ≫ finite_prefix_stage_projection K n ≫
                K.map (homOfLE (Nat.le_succ n)) := by
                  exact finite_prefix_stage_projection_successor_old_branch K n
            _ = 0 := by
                  simpa [Category.assoc] using
                    congrArg (fun f ↦ f ≫ K.map (homOfLE (Nat.le_succ n))) ih
            _ = biprod.inl ≫
                (0 : finite_prefix_obj K (n + 1) ⟶ K.obj (n + 1)) := by
                  symm
                  change biprod.inl ≫
                      (0 : finite_prefix_obj K (n + 1) ⟶ K.obj (n + 1)) =
                    (0 : finite_prefix_obj K n ⟶ K.obj (n + 1))
                  exact comp_zero
        · calc
            biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫
                finite_prefix_stage_projection K (n + 1) = 0 := by
                  exact finite_prefix_stage_projection_successor_new_branch K n
            _ = biprod.inr ≫
                (0 : finite_prefix_obj K (n + 1) ⟶ K.obj (n + 1)) := by
                  symm
                  change biprod.inr ≫
                      (0 : finite_prefix_obj K (n + 1) ⟶ K.obj (n + 1)) =
                    (0 : K.obj n ⟶ K.obj (n + 1))
                  exact comp_zero

/-- Helper for Lemma 13.33.6: the successor-stage telescope composite with the recursive
retraction restricts to the two biproduct inclusions on the old and new branches. -/
theorem finite_prefix_stage_retraction_successor_branches [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ)
    (hret : finite_prefix_stage_map K n ≫ finite_prefix_stage_retraction K n = 𝟙 _)
    (hproj : finite_prefix_stage_map K n ≫ finite_prefix_stage_projection K n = 0) :
    biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
        biprod.inl ∧
      biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
        biprod.inr := by
  constructor
  · -- The old branch lands in the old prefix via the retraction and has zero new component.
    have hold :
        biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
          finite_prefix_stage_map K n ≫
            biprod.lift (finite_prefix_stage_retraction K n)
              (finite_prefix_stage_projection K n) := by
      calc
        biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
            finite_prefix_stage_map K n ≫ finite_prefix_inclusion K (n + 1) ≫
              finite_prefix_stage_retraction K (n + 1) := by
              rw [finite_prefix_stage_map, biprod.inl_desc_assoc, Category.assoc]
        _ = finite_prefix_stage_map K n ≫
            biprod.lift (finite_prefix_stage_retraction K n)
              (finite_prefix_stage_projection K n) := by
              rw [finite_prefix_inclusion, finite_prefix_stage_retraction]
              exact congrArg (fun t ↦ finite_prefix_stage_map K n ≫ t)
                (biprod.inl_desc
                  (biprod.lift (finite_prefix_stage_retraction K n)
                    (finite_prefix_stage_projection K n))
                  0)
    rw [hold]
    apply biprod.hom_ext
    · -- Postcomposing with `biprod.fst` recovers the induction hypothesis `hret`.
      simpa [Category.assoc, hret] using hret
    · -- Postcomposing with `biprod.snd` recovers the vanishing hypothesis `hproj`.
      simpa [Category.assoc, hproj] using hproj
  · -- The new branch is the last summand together with the correction term, whose retraction part
    -- vanishes while the projection part is the identity.
    have hnew :
        biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
          finite_prefix_lastι K n ≫
            biprod.lift (finite_prefix_stage_retraction K n)
              (finite_prefix_stage_projection K n) := by
      calc
        biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
            (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1) -
                K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
              finite_prefix_stage_retraction K (n + 1) := by
              rw [finite_prefix_stage_map, biprod.inr_desc_assoc]
        _ =
            (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
                finite_prefix_stage_retraction K (n + 1) -
              (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
                finite_prefix_stage_retraction K (n + 1) := by
              rw [Preadditive.sub_comp]
        _ = finite_prefix_lastι K n ≫
            biprod.lift (finite_prefix_stage_retraction K n)
              (finite_prefix_stage_projection K n) := by
              have hleft :
                  (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
                      finite_prefix_stage_retraction K (n + 1) =
                    finite_prefix_lastι K n ≫
                      biprod.lift (finite_prefix_stage_retraction K n)
                        (finite_prefix_stage_projection K n) := by
                rw [finite_prefix_inclusion, finite_prefix_stage_retraction, Category.assoc]
                exact congrArg (fun t ↦ finite_prefix_lastι K n ≫ t)
                  (biprod.inl_desc
                    (biprod.lift (finite_prefix_stage_retraction K n)
                      (finite_prefix_stage_projection K n))
                    0)
              have hright :
                  (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
                      finite_prefix_stage_retraction K (n + 1) = 0 := by
                rw [Category.assoc, finite_prefix_lastι_comp_retraction]
                rw [Limits.comp_zero]
              rw [hleft, hright]
              simp
    rw [hnew]
    apply biprod.hom_ext
    · -- The old component vanishes because the newest summand is killed by the retraction.
      simpa [Category.assoc] using finite_prefix_lastι_comp_retraction (K := K) n
    · -- The new component is read off by the stage projection.
      simpa [Category.assoc] using finite_prefix_lastι_comp_projection (K := K) n

/-- Helper for Lemma 13.33.6: the finite-stage telescope map admits the recursive retraction above,
so it is split mono. -/
theorem finite_prefix_stage_map_comp_retraction [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_stage_map K n ≫ finite_prefix_stage_retraction K n = 𝟙 _ :=
  by
    intro n
    induction n with
    | zero =>
        -- The initial-stage retraction is the left projection from the first biproduct.
        rw [finite_prefix_stage_map, finite_prefix_stage_retraction]
        exact biprod.inl_fst
    | succ n ih =>
        -- The successor-stage identity is determined by its restrictions to the two biproduct
        -- summands, which are exactly the branch equalities proved above.
        apply biprod.hom_ext'
        · exact
            (finite_prefix_stage_retraction_successor_branches K n ih
              (finite_prefix_stage_map_comp_projection K n)).1.trans <|
              (Category.comp_id biprod.inl).symm
        · exact
            (finite_prefix_stage_retraction_successor_branches K n ih
              (finite_prefix_stage_map_comp_projection K n)).2.trans <|
              (Category.comp_id biprod.inr).symm

/-- Helper for Lemma 13.33.6: each finite-stage telescope map is a split monomorphism. -/
theorem finite_prefix_stage_splitMono [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) (n : ℕ) :
    IsSplitMono (finite_prefix_stage_map K n) :=
  IsSplitMono.mk' ⟨finite_prefix_stage_retraction K n,
    finite_prefix_stage_map_comp_retraction K n⟩

/-- Helper for Lemma 13.33.6: each finite-stage telescope map is a monomorphism. -/
theorem finite_prefix_stage_mono [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) (n : ℕ) :
    Mono (finite_prefix_stage_map K n) := by
  let _ : IsSplitMono (finite_prefix_stage_map K n) := finite_prefix_stage_splitMono K n
  infer_instance

/-- Helper for Lemma 13.33.6: the finite prefixes form the left sequential diagram. -/
def finite_prefix_left_functor [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) : ℕ ⥤ 𝒜 :=
  Functor.ofSequence (fun n ↦ finite_prefix_inclusion K n)

/-- Helper for Lemma 13.33.6: the shifted finite prefixes form the middle sequential diagram. -/
def finite_prefix_middle_functor [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) : ℕ ⥤ 𝒜 :=
  Functor.ofSequence (X := fun n ↦ finite_prefix_obj K (n + 1))
    (fun n ↦ finite_prefix_inclusion K (n + 1))

/-- Helper for Lemma 13.33.6: the recursive finite-stage telescope maps satisfy the successor
naturality equation required by `NatTrans.ofSequence`. -/
theorem finite_prefix_stage_naturality_succ [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_inclusion K n ≫ finite_prefix_stage_map K (n + 1) =
        finite_prefix_stage_map K n ≫ finite_prefix_inclusion K (n + 1) := by
  intro n
  -- The successor-stage map restricts to the previous stage map on the older summands.
  rw [finite_prefix_inclusion, finite_prefix_stage_map]
  exact biprod.inl_desc _ _

/-- Helper for Lemma 13.33.6: the finite-stage telescope maps assemble into a natural
transformation from the left prefix system to the shifted one. -/
def finite_prefix_stage_natTrans [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    finite_prefix_left_functor K ⟶ finite_prefix_middle_functor K :=
  NatTrans.ofSequence
    (fun n ↦ finite_prefix_stage_map K n)
    (fun n ↦ by
      -- The sequence constructor only needs the successor-step naturality.
      simpa [finite_prefix_left_functor, finite_prefix_middle_functor,
        Functor.ofSequence_map_homOfLE_succ] using finite_prefix_stage_naturality_succ K n)

/-- Helper for Lemma 13.33.6: the canonical map from a finite prefix to the countable coproduct. -/
def finite_prefix_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) [HasCoproduct K.obj] :
    (n : ℕ) → finite_prefix_obj K n ⟶ ∐ K.obj
  | 0 => 0
  | n + 1 => biprod.desc (finite_prefix_to_sigma K n) (Sigma.ι K.obj n)

/-- Helper for Lemma 13.33.6: finite-prefix inclusions are compatible with the canonical maps into
the countable coproduct. -/
theorem finite_prefix_inclusion_comp_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
      finite_prefix_inclusion K n ≫ finite_prefix_to_sigma K (n + 1) =
        finite_prefix_to_sigma K n := by
  intro n
  -- This is the defining property of the left summand inclusion of a biproduct.
  exact biprod.inl_desc _ _

/-- Helper for Lemma 13.33.6: the new last summand of a finite prefix maps to the corresponding
summand of the countable coproduct. -/
theorem finite_prefix_lastι_comp_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
      finite_prefix_lastι K n ≫ finite_prefix_to_sigma K (n + 1) = Sigma.ι K.obj n := by
  intro n
  -- The recursive coproduct map adjoins the new summand by `Sigma.ι`.
  rw [finite_prefix_lastι, finite_prefix_to_sigma]
  exact biprod.inr_desc _ _

/-- Helper for Lemma 13.33.6: the correction term in the successor-stage telescope map becomes the
expected `1 - f_n` branch after postcomposition with the canonical map to the countable coproduct. -/
theorem finite_prefix_correction_comp_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (n : ℕ) :
    ((finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) -
        (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1))) ≫
      finite_prefix_to_sigma K (n + 2) =
        Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
  -- The old part becomes the `n`th coproduct summand, and the new corrected part becomes the
  -- shifted summand after transport by the transition morphism.
  rw [Preadditive.sub_comp]
  have hold :
      (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
          finite_prefix_to_sigma K (n + 2) =
        Sigma.ι K.obj n := by
    calc
      (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
          finite_prefix_to_sigma K (n + 2) =
        finite_prefix_lastι K n ≫
          (finite_prefix_inclusion K (n + 1) ≫ finite_prefix_to_sigma K (n + 2)) := by
            simp [Category.assoc]
      _ = finite_prefix_lastι K n ≫ finite_prefix_to_sigma K (n + 1) := by
            rw [finite_prefix_inclusion_comp_to_sigma]
      _ = Sigma.ι K.obj n := finite_prefix_lastι_comp_to_sigma K n
  have hnew :
      (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
          finite_prefix_to_sigma K (n + 2) =
        K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
    calc
      (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
          finite_prefix_to_sigma K (n + 2) =
        K.map (homOfLE (Nat.le_succ n)) ≫
          (finite_prefix_lastι K (n + 1) ≫ finite_prefix_to_sigma K (n + 2)) := by
            simp [Category.assoc]
      _ = K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
            rw [finite_prefix_lastι_comp_to_sigma]
  rw [hold, hnew]

/-- Helper for Lemma 13.33.6: the finite-stage telescope maps are compatible with the global
telescope endomorphism of the countable coproduct. -/
theorem finite_prefix_stage_map_comp_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
        finite_prefix_to_sigma K n ≫ sequentialTelescopeMap K =
        finite_prefix_stage_map K n ≫ finite_prefix_to_sigma K (n + 1) :=
  by
    intro n
    induction n with
    | zero =>
        -- The zero-stage map is initial, and the first finite-stage telescope map is the
        -- inclusion into the first biproduct.
        simpa [finite_prefix_stage_map, finite_prefix_to_sigma] using
          (finite_prefix_inclusion_comp_to_sigma (K := K) 0).symm
    | succ n ih =>
        -- Route correction: compare the old and new branches after postcomposition with
        -- `finite_prefix_to_sigma` using the raw successor formulas, rather than asking Lean to
        -- normalize the wrapped branches directly.
        apply biprod.hom_ext'
        · calc
            biprod.inl ≫ finite_prefix_to_sigma K (n + 1) ≫ sequentialTelescopeMap K =
                finite_prefix_to_sigma K n ≫ sequentialTelescopeMap K := by
                  rw [finite_prefix_to_sigma, biprod.inl_desc_assoc]
            _ = finite_prefix_stage_map K n ≫ finite_prefix_to_sigma K (n + 1) := ih
            _ = biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫
                finite_prefix_to_sigma K (n + 2) := by
                  rw [finite_prefix_stage_map, biprod.inl_desc_assoc, Category.assoc,
                    finite_prefix_inclusion_comp_to_sigma]
        · calc
            biprod.inr ≫ finite_prefix_to_sigma K (n + 1) ≫ sequentialTelescopeMap K =
                Sigma.ι K.obj n ≫ sequentialTelescopeMap K := by
                  rw [finite_prefix_to_sigma, biprod.inr_desc_assoc]
            _ = Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
                  simpa using
                    (Sigma.ι_comp_sequentialTelescopeMap_assoc (K := K) n
                      (h := 𝟙 (∐ K.obj)))
            _ = biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫
                finite_prefix_to_sigma K (n + 2) := by
                  rw [finite_prefix_stage_map, biprod.inr_desc_assoc,
                    finite_prefix_correction_comp_to_sigma]

/-- Helper for Lemma 13.33.6: the left cocone legs satisfy the `NatTrans.ofSequence` successor
compatibility. -/
theorem finite_prefix_left_cocone_naturality [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
      (finite_prefix_left_functor K).map (homOfLE (Nat.le_succ n)) ≫
          finite_prefix_to_sigma K (n + 1) =
        finite_prefix_to_sigma K n ≫ ((Functor.const ℕ).obj (∐ K.obj)).map
          (homOfLE (Nat.le_succ n)) :=
  by
    intro n
    -- Unfold the successor map of the sequence functor and use the left-summand formula.
    simpa [finite_prefix_left_functor, Functor.ofSequence_map_homOfLE_succ] using
      finite_prefix_inclusion_comp_to_sigma K n

/-- Helper for Lemma 13.33.6: the middle cocone legs satisfy the `NatTrans.ofSequence` successor
compatibility. -/
theorem finite_prefix_middle_cocone_naturality [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
      (finite_prefix_middle_functor K).map (homOfLE (Nat.le_succ n)) ≫
          finite_prefix_to_sigma K (n + 2) =
        finite_prefix_to_sigma K (n + 1) ≫ ((Functor.const ℕ).obj (∐ K.obj)).map
          (homOfLE (Nat.le_succ n)) :=
  by
    intro n
    -- The shifted finite-prefix system has the same successor map one stage later.
    simpa [finite_prefix_middle_functor, Functor.ofSequence_map_homOfLE_succ] using
      finite_prefix_inclusion_comp_to_sigma K (n + 1)

/-- Helper for Lemma 13.33.6: the left finite-prefix cocone lands in the countable coproduct. -/
def finite_prefix_left_cocone [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) [HasCoproduct K.obj] :
    Cocone (finite_prefix_left_functor K) :=
  Cocone.mk (∐ K.obj) <|
    NatTrans.ofSequence
      (fun n ↦ finite_prefix_to_sigma K n)
      (finite_prefix_left_cocone_naturality K)

/-- Helper for Lemma 13.33.6: the shifted finite-prefix cocone lands in the countable coproduct. -/
def finite_prefix_middle_cocone [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) [HasCoproduct K.obj] :
    Cocone (finite_prefix_middle_functor K) :=
  Cocone.mk (∐ K.obj) <|
    NatTrans.ofSequence
      (fun n ↦ finite_prefix_to_sigma K (n + 1))
      (finite_prefix_middle_cocone_naturality K)

/-- Helper for Lemma 13.33.6: a morphism out of each finite prefix is determined by its
restriction to the previous prefix and by its value on the newest summand. -/
theorem finite_prefix_desc_eq_sigma_desc_of_branches [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] {X : 𝒜} (g : ∀ n, finite_prefix_obj K n ⟶ X)
    (a : ∀ n, K.obj n ⟶ X)
    (hg : ∀ n, finite_prefix_inclusion K n ≫ g (n + 1) = g n)
    (ha : ∀ n, finite_prefix_lastι K n ≫ g (n + 1) = a n) :
    ∀ n, finite_prefix_to_sigma K n ≫ Limits.Sigma.desc a = g n := by
  intro n
  induction n with
  | zero =>
      -- The zero-stage map is unique because the initial prefix object is zero.
      have h0 : IsZero (finite_prefix_obj K 0) := by
        simpa [finite_prefix_obj] using (isZero_zero 𝒜)
      exact h0.eq_of_src _ _
  | succ n ih =>
      -- The successor-stage map is determined by the previous prefix and the newest summand.
      apply biprod.hom_ext'
      · calc
          biprod.inl ≫ finite_prefix_to_sigma K (n + 1) ≫ Limits.Sigma.desc a =
            finite_prefix_to_sigma K n ≫ Limits.Sigma.desc a := by
              simp [finite_prefix_to_sigma, finite_prefix_inclusion, Category.assoc]
          _ = g n := ih
          _ = biprod.inl ≫ g (n + 1) := (hg n).symm
      · calc
          biprod.inr ≫ finite_prefix_to_sigma K (n + 1) ≫ Limits.Sigma.desc a =
            a n := by
              rw [finite_prefix_to_sigma, biprod.inr_desc_assoc, Limits.Sigma.ι_desc]
          _ = biprod.inr ≫ g (n + 1) := (ha n).symm

/-- Helper for Lemma 13.33.6: the coproduct map built from the newest summands recovers any cocone
on the left finite-prefix system. -/
theorem finite_prefix_left_desc_fac [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_left_functor K)) :
    ∀ n,
      finite_prefix_to_sigma K n ≫
          Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1)) =
        s.ι.app n := by
  intro n
  -- Route correction: instead of a second ad hoc induction, reconstruct the cocone from the
  -- old branch and newest summand through the generic finite-prefix descent lemma.
  simpa using finite_prefix_desc_eq_sigma_desc_of_branches (K := K)
    (g := fun i ↦ s.ι.app i)
    (a := fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1))
    (hg := fun i ↦ by
      -- Cocone naturality identifies the old branch with the previous cocone leg.
      simpa [finite_prefix_left_functor, Functor.ofSequence_map_homOfLE_succ] using
        s.w (homOfLE (Nat.le_succ i)))
    (ha := fun i ↦ rfl) n

/-- Helper for Lemma 13.33.6: the explicit descendant from the countable coproduct satisfies the
left finite-prefix cocone equations. -/
theorem finite_prefix_left_cocone_fac [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_left_functor K)) :
    ∀ n,
      (finite_prefix_left_cocone K).ι.app n ≫
          Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1)) =
        s.ι.app n := by
  intro n
  -- The explicit cocone is defined from the same finite-prefix maps.
  simpa [finite_prefix_left_cocone] using finite_prefix_left_desc_fac K s n

/-- Helper for Lemma 13.33.6: the descendant from the countable coproduct is unique for cocones on
the left finite-prefix system. -/
theorem finite_prefix_left_cocone_uniq [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_left_functor K))
    (m : (finite_prefix_left_cocone K).pt ⟶ s.pt)
    (hm : ∀ n, (finite_prefix_left_cocone K).ι.app n ≫ m = s.ι.app n) :
    m = Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1)) := by
  -- Compare both maps on each coproduct summand using the cocone equation at stage `i + 1`.
  apply Limits.Sigma.hom_ext
  intro i
  have hi := congrArg (fun t ↦ finite_prefix_lastι K i ≫ t) (hm (i + 1))
  have hleft' :
      finite_prefix_lastι K i ≫ finite_prefix_to_sigma K (i + 1) ≫ m =
        finite_prefix_lastι K i ≫ s.ι.app (i + 1) := by
    simpa [finite_prefix_left_cocone, Category.assoc] using hi
  have hsigma := congrArg (fun t ↦ t ≫ m) (finite_prefix_lastι_comp_to_sigma (K := K) i).symm
  have hleft'' :
      (finite_prefix_lastι K i ≫ finite_prefix_to_sigma K (i + 1)) ≫ m =
        finite_prefix_lastι K i ≫ s.ι.app (i + 1) := by
    simpa [Category.assoc] using hleft'
  have hleft : Sigma.ι K.obj i ≫ m = finite_prefix_lastι K i ≫ s.ι.app (i + 1) := by
    exact hsigma.trans hleft''
  have hright :
      finite_prefix_lastι K i ≫ s.ι.app (i + 1) =
        Sigma.ι K.obj i ≫
          Limits.Sigma.desc (fun j ↦ finite_prefix_lastι K j ≫ s.ι.app (j + 1)) := by
    simpa using
      (CategoryTheory.Limits.Sigma.ι_desc (fun j ↦ finite_prefix_lastι K j ≫ s.ι.app (j + 1)) i).symm
  exact hleft.trans hright

/-- Helper for Lemma 13.33.6: the left finite-prefix cocone is colimit, because any cocone is
determined by its values on the newly added summands. -/
noncomputable def finite_prefix_left_isColimit [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    IsColimit (finite_prefix_left_cocone K) :=
  IsColimit.mk
    (fun s ↦ Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1)))
    (fun s n ↦ finite_prefix_left_cocone_fac K s n)
    (fun s m hm ↦ finite_prefix_left_cocone_uniq K s m hm)

/-- Helper for Lemma 13.33.6: the coproduct map built from the newest summands also recovers any
cocone on the shifted finite-prefix system. -/
theorem finite_prefix_middle_desc_fac [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_middle_functor K)) :
    ∀ n,
      finite_prefix_to_sigma K (n + 1) ≫
          Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i) =
        s.ι.app n := by
  intro n
  -- The shifted cocone uses the same reconstruction lemma after padding the zero stage.
  simpa using finite_prefix_desc_eq_sigma_desc_of_branches (K := K)
    (g := fun
      | 0 => 0
      | i + 1 => s.ι.app i)
    (a := fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i)
    (hg := fun
      | 0 => by
          -- The padded zero stage is forced by the zero object.
          have h0 : IsZero (finite_prefix_obj K 0) := by
            simpa [finite_prefix_obj] using (isZero_zero 𝒜)
          exact h0.eq_of_src _ _
      | i + 1 => by
          -- Cocone naturality handles each genuine successor stage.
          simpa [finite_prefix_middle_functor, Functor.ofSequence_map_homOfLE_succ] using
            s.w (homOfLE (Nat.le_succ i)))
    (ha := fun i ↦ rfl) (n + 1)

/-- Helper for Lemma 13.33.6: the explicit descendant from the countable coproduct satisfies the
shifted finite-prefix cocone equations. -/
theorem finite_prefix_middle_cocone_fac [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_middle_functor K)) :
    ∀ n,
      (finite_prefix_middle_cocone K).ι.app n ≫
          Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i) =
        s.ι.app n := by
  intro n
  -- The shifted explicit cocone uses the same finite-prefix maps with one index shift.
  simpa [finite_prefix_middle_cocone] using finite_prefix_middle_desc_fac K s n

/-- Helper for Lemma 13.33.6: the descendant from the countable coproduct is unique for cocones on
the shifted finite-prefix system. -/
theorem finite_prefix_middle_cocone_uniq [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_middle_functor K))
    (m : (finite_prefix_middle_cocone K).pt ⟶ s.pt)
    (hm : ∀ n, (finite_prefix_middle_cocone K).ι.app n ≫ m = s.ι.app n) :
    m = Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i) := by
  -- The shifted cocone has the same summandwise uniqueness after precomposing with `lastι`.
  apply Limits.Sigma.hom_ext
  intro i
  have hi := congrArg (fun t ↦ finite_prefix_lastι K i ≫ t) (hm i)
  have hleft' :
      finite_prefix_lastι K i ≫ finite_prefix_to_sigma K (i + 1) ≫ m =
        finite_prefix_lastι K i ≫ s.ι.app i := by
    simpa [finite_prefix_middle_cocone, Category.assoc] using hi
  have hsigma := congrArg (fun t ↦ t ≫ m) (finite_prefix_lastι_comp_to_sigma (K := K) i).symm
  have hleft'' :
      (finite_prefix_lastι K i ≫ finite_prefix_to_sigma K (i + 1)) ≫ m =
        finite_prefix_lastι K i ≫ s.ι.app i := by
    simpa [Category.assoc] using hleft'
  have hleft : Sigma.ι K.obj i ≫ m = finite_prefix_lastι K i ≫ s.ι.app i := by
    exact hsigma.trans hleft''
  have hright :
      finite_prefix_lastι K i ≫ s.ι.app i =
        Sigma.ι K.obj i ≫ Limits.Sigma.desc (fun j ↦ finite_prefix_lastι K j ≫ s.ι.app j) := by
    simpa using
      (CategoryTheory.Limits.Sigma.ι_desc (fun j ↦ finite_prefix_lastι K j ≫ s.ι.app j) i).symm
  exact hleft.trans hright

/-- Helper for Lemma 13.33.6: the shifted finite-prefix cocone is also colimit, using the same
summandwise reconstruction one stage earlier. -/
noncomputable def finite_prefix_middle_isColimit [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    IsColimit (finite_prefix_middle_cocone K) :=
  IsColimit.mk
    (fun s ↦ Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i))
    (fun s n ↦ finite_prefix_middle_cocone_fac K s n)
    (fun s m hm ↦ finite_prefix_middle_cocone_uniq K s m hm)

/-- Helper for Lemma 13.33.6: the explicit finite-prefix cocones are compatible with the global
telescope map. -/
theorem finite_prefix_cocone_compat [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) [HasCoproduct K.obj] :
    ∀ n,
      (finite_prefix_left_cocone K).ι.app n ≫ sequentialTelescopeMap K =
        (finite_prefix_stage_natTrans K).app n ≫ (finite_prefix_middle_cocone K).ι.app n :=
  by
    intro n
    -- This is exactly the finite-stage compatibility, rewritten through the explicit cocone data.
    simpa [finite_prefix_left_cocone, finite_prefix_middle_cocone, finite_prefix_stage_natTrans] using
      finite_prefix_stage_map_comp_to_sigma K n

-- Proof sketch: apply part (1) to obtain exact countable coproducts. Then express the direct sum
-- as the sequential colimit of the finite partial sums and apply exactness of sequential colimits
-- to the standard short exact sequences
-- `0 ⟶ A₀ ⨿ ⋯ ⨿ Aₙ₋₁ ⟶ A₀ ⨿ ⋯ ⨿ Aₙ ⟶ Aₙ ⟶ 0`, whose colimit identifies with the telescope
-- short complex.
/-- Lemma 13.33.6: for a sequential diagram in an abelian category with exact colimits over `ℕ`,
the telescope map on the countable direct sum fits into a short exact sequence
`0 ⟶ ⨿ Kₙ ⟶ ⨿ Kₙ ⟶ colim K ⟶ 0`. -/
theorem sequentialTelescope_shortExact [HasExactColimitsOfShape ℕ 𝒜] (K : ℕ ⥤ 𝒜) :
    (ShortComplex.mk (sequentialTelescopeMap K)
      (Limits.Sigma.desc (colimit.ι K))
      (sequentialTelescopeMap_comp_sigmaDesc K (colimit.ι K)
        fun n ↦ colimit.w K (homOfLE (Nat.le_succ n)))).ShortExact :=
  by
    -- Exactness follows once the canonical map to the sequential colimit is identified as the
    -- cokernel of the telescope map.
    have hExact :
        (ShortComplex.mk (sequentialTelescopeMap K)
          (Limits.Sigma.desc (colimit.ι K))
          (sequentialTelescopeMap_comp_sigmaDesc K (colimit.ι K)
            fun n ↦ colimit.w K (homOfLE (Nat.le_succ n)))).Exact := by
      exact ShortComplex.exact_of_g_is_cokernel _
        (Classical.choice <|
          sigma_desc_cokernelCofork_nonempty_of_sequentialTelescope K)
    let _ : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts
    let _ : CountableAB4 𝒜 := CountableAB4.of_countableAB5 𝒜
    -- The mono statement comes from the source-faithful finite-prefix telescope systems: each
    -- finite-stage map is split mono, and the global telescope map is their colimit.
    have hMonoNat : Mono (finite_prefix_stage_natTrans K) := by
      -- Each component is mono by the finite split-mono calculation above.
      have : ∀ n, Mono ((finite_prefix_stage_natTrans K).app n) := by
        intro n
        change Mono (finite_prefix_stage_map K n)
        exact finite_prefix_stage_mono K n
      exact NatTrans.mono_of_mono_app (finite_prefix_stage_natTrans K)
    have hMono : Mono (sequentialTelescopeMap K) := by
      let _ : Mono (finite_prefix_stage_natTrans K) := hMonoNat
      exact Limits.colim.map_mono' (finite_prefix_stage_natTrans K)
        (finite_prefix_left_isColimit K) (finite_prefix_middle_isColimit K)
        (sequentialTelescopeMap K) (finite_prefix_cocone_compat K)
    exact ShortComplex.ShortExact.mk' hExact hMono inferInstance

end

end CategoryTheory

/-! ### Lemma_13_33_7 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open CategoryTheory.Pretriangulated
open DerivedCategory

universe w v u

noncomputable section

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable [HasColimitsOfShape ℕ 𝒜] [HasExactColimitsOfShape ℕ 𝒜]

/- Domain-style sampling for Lemma 13.33.7:
- primary domain: homotopy colimits in derived categories, obtained from the telescope triangle of
  a sequential diagram of cochain complexes;
- inspected owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.derivedCategory_Q_preserves_countableCoproduct`,
  `CategoryTheory.sequentialTelescope_shortExact`;
- best owner abstraction:
  the source-facing datum is the sequential diagram `S : ℕ ⥤ CochainComplex 𝒜 ℤ`, and the
  canonical owner for the conclusion is `IsHomotopyColimitOf (S ⋙ DerivedCategory.Q)`;
- primitive-vs-derived split:
  the primitive data are only the diagram `S`;
  the countable coproduct in `DerivedCategory 𝒜` and the distinguished telescope triangle are
  derived API coming from the Chapter 13 coproduct-preservation bridge and the exact telescope
  short exact sequence.

Source/core/bridge triage:
- `source-facing`: the termwise colimit complex represents a homotopy colimit of the image
  sequence in the derived category;
- `core/canonical`: `IsHomotopyColimitOf (S ⋙ DerivedCategory.Q)`;
- `bridge/view`: the local countable-coproduct bridge on `𝒜`, together with
  `derivedCategory_hasCountableCoproducts_of_exactCountableCoproducts`, supplies the owner
  predicate with the needed coproduct of `Q.obj (S.obj n)`. -/

local instance : HasCountableCoproducts 𝒜 := hasCountableCoproducts_of_sequentialColimits

local instance : CountableAB4 𝒜 := by
  let _ : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts
  exact CountableAB4.of_countableAB5 𝒜

-- Proof sketch: exact sequential colimits give the short exact telescope sequence
-- `0 ⟶ ⨿ L_n^• ⟶ ⨿ L_n^• ⟶ colim L_n^• ⟶ 0`. Applying the localization functor
-- `CochainComplex 𝒜 ℤ ⥤ DerivedCategory 𝒜` and the canonical distinguished-triangle construction
-- for short exact sequences yields the standard telescope triangle, so the termwise colimit is
-- best recorded via the canonical owner `IsHomotopyColimitOf`.
/-- Lemma 13.33.7: if an abelian category admits exact sequential colimits, then the termwise
colimit of a sequential system of cochain complexes is a homotopy colimit of the induced
sequential diagram in the derived category. -/
theorem termwise_colimit_is_homotopy_colimit (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    IsHomotopyColimitOf (S ⋙ Q) (Q.obj (colimit S)) := by
  sorry

/-- The canonical map from the telescope coproduct `∐ Q(Sₙ)` to the derived image of the termwise
colimit complex. This is the source-facing map used when the homotopy-colimit presentation from
`termwise_colimit_is_homotopy_colimit` is expressed by the actual short exact telescope sequence of
`S`. -/
def termwise_colimit_presentation_map (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    ∐ (fun n ↦ Q.obj (S.obj n)) ⟶ Q.obj (colimit S) :=
  (PreservesCoproduct.iso Q S.obj).inv ≫ Q.map (Limits.Sigma.desc (colimit.ι S))

/-- The connecting morphism in the canonical telescope triangle presenting `Q.obj (colimit S)` as
a homotopy colimit of `S ⋙ Q`. -/
def termwise_colimit_presentation_connecting (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    Q.obj (colimit S) ⟶ (∐ fun n ↦ Q.obj (S.obj n))⟦(1 : ℤ)⟧ :=
  triangleOfSESδ (sequentialTelescope_shortExact S) ≫
    ((PreservesCoproduct.iso Q S.obj).hom⟦(1 : ℤ)⟧')

-- Proof sketch: start from the distinguished triangle `triangleOfSES` attached to the canonical
-- telescope short exact sequence of `S`, then transport its first two objects from
-- `Q.obj (∐ Sₙ)` to the actual coproduct `∐ Q(Sₙ)` using `PreservesCoproduct.iso Q S.obj`.
/-- The canonical telescope triangle for the termwise colimit complex is distinguished. This is
the explicit source-facing presentation underlying `termwise_colimit_is_homotopy_colimit`. -/
theorem termwise_colimit_presentation_distinguished (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    Triangle.mk
        (sequentialTelescopeMap (S ⋙ Q))
        (termwise_colimit_presentation_map S)
        (termwise_colimit_presentation_connecting S) ∈
      distTriang (DerivedCategory 𝒜) := by
  sorry

end

end CategoryTheory
