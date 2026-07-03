import Mathlib
import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_30_1 (from Chap06) -/
open CategoryTheory TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The full subcategory of `Opens X` spanned by the basis members `B`. -/
abbrev BasisOpen (B : Set (Opens X)) :=
  ObjectProperty.FullSubcategory fun U : Opens X ↦ U ∈ B

variable {B : Set (Opens X)}

/- Definition 6.30.1:
- primary domain: set-valued presheaves on the basis-open category of a topological space
- sampled owner abstractions:
  `ObjectProperty.FullSubcategory`,
  `Presheaf`,
  `((BasisOpen B)ᵒᵖ ⥤ Type _)`,
  `TopCat.Presheaf`
- source-facing layer: the basis-open category `BasisOpen B`
- core/canonical owner: `Presheaf`, specialized to `BasisOpen B`
- primitive data: only the underlying contravariant functor on basis opens
- derived API: morphisms are natural transformations in this functor category
-/
/-
Definition 6.30.1 lives at the source/core boundary: once the source-facing owner
`BasisOpen B` is fixed, a presheaf of sets on the basis `B` is exactly the canonical project owner
`Presheaf (BasisOpen B)`.
-/
recall Presheaf

#check (Presheaf (BasisOpen B))

variable (ℱ 𝒢 : Presheaf (BasisOpen B))

/- Companion recall: morphisms of presheaves on the basis `B` are the natural transformations in
this functor category. -/
#check (ℱ ⟶ 𝒢)

/-! ### Definition_6_30_2 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Presheaf

universe u v w

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Definition 6.30.2:
- primary domain: sheaves of sets on a topological basis, stated by the Stacks Project gluing
  condition `(**)` on basis covers and chosen basis covers of pairwise intersections;
- sampled owner abstractions:
  `BasisOpen`,
  `SemiRepresentableFamily.Over`,
  `Presheaf`,
  `Functor.inducedTopology`,
  `Sheaf`;
- source-facing layer: basis covers, chosen covers of pairwise intersections, and the resulting
  gluing condition `(**)` for a basis presheaf;
- core/canonical owner: `Functor.inducedTopology` and `Sheaf` on the basis-open category, but only
  as a bridge once `hB : Opens.IsBasis B` is fixed;
- bridge/view layer: `BasisSiteSheaf`, the canonical sheaf category on the induced site.

Primitive data are the basis-open category together with basis covers and chosen overlap covers.
The source-facing owner is the gluing predicate on presheaves; the induced-topology sheaf category
is a derived bridge, not the main public definition. -/

/-- The inclusion of the basis-open category into the category of open subsets of `X`. -/
abbrev basisOpenInclusion (B : Set (Opens X)) : BasisOpen B ⥤ Opens X :=
  ObjectProperty.ι (fun U : Opens X ↦ U ∈ B)

private theorem range_basisOpenInclusion_obj (B : Set (Opens X)) :
    Set.range (basisOpenInclusion B).obj = B := by
  ext U
  constructor
  · rintro ⟨V, rfl⟩
    exact V.2
  · intro hU
    exact ⟨⟨U, hU⟩, rfl⟩

/-- The inclusion of basis opens into all opens is cover dense when `B` is a topological basis. -/
theorem basisOpenInclusion_isCoverDense {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) := by
  let G : BasisOpen B ⥤ Opens (TopCat.of X) := basisOpenInclusion B
  refine (TopCat.Opens.coverDense_iff_isBasis G).2 ?_
  simpa [G, range_basisOpenInclusion_obj B] using hB

/-- A covering of a basis open `U` by basis opens. -/
structure BasisCover (B : Set (Opens X)) (U : BasisOpen B) where
  /-- The index type of the covering family. -/
  ι : Type u
  /-- The basis open indexed by `i`. -/
  obj : ι → BasisOpen B
  /-- The inclusion of the `i`-th basis open into `U`. -/
  hom : ∀ i : ι, obj i ⟶ U
  /-- The union of the members of the family is `U`. -/
  iUnion_eq : (U.obj : Set X) = ⋃ i : ι, ((obj i).obj : Set X)

/-- Chosen coverings of the pairwise intersections in a basis cover. -/
structure BasisIntersectionCover (B : Set (Opens X)) {U : BasisOpen B}
    (𝒰 : BasisCover B U) where
  /-- The index type for the chosen cover of `Uᵢ ∩ Uⱼ`. -/
  κ : 𝒰.ι → 𝒰.ι → Type u
  /-- The basis opens covering each pairwise intersection. -/
  obj (i j : 𝒰.ι) (k : κ i j) : BasisOpen B
  /-- The inclusion of a chosen overlap open into the left member of the pair. -/
  left (i j : 𝒰.ι) (k : κ i j) : obj i j k ⟶ 𝒰.obj i
  /-- The inclusion of a chosen overlap open into the right member of the pair. -/
  right (i j : 𝒰.ι) (k : κ i j) : obj i j k ⟶ 𝒰.obj j
  /-- The chosen overlap family covers `Uᵢ ∩ Uⱼ`. -/
  iUnion_eq (i j : 𝒰.ι) :
    (((𝒰.obj i).obj ⊓ (𝒰.obj j).obj : Opens X) : Set X) =
      ⋃ k, ((obj i j k).obj : Set X)

namespace BasisCover

variable {B : Set (Opens X)} {U : BasisOpen B}

/-- The sheaf condition `(**)` for a basis cover together with chosen coverings of pairwise
intersections. -/
def HasSheafCondition (F : Presheaf (BasisOpen B)) (𝒰 : BasisCover B U)
    (𝒱 : BasisIntersectionCover B 𝒰) : Prop :=
  ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
    (∀ i j k, F.map ((𝒱.left i j k).op) (s i) = F.map ((𝒱.right i j k).op) (s j)) →
      ∃! t : F.obj (op U), ∀ i, F.map ((𝒰.hom i).op) t = s i

/-- Helper for Definition 6.30.2: a basis cover `𝒱` refines `𝒰` if each member of `𝒱` factors
through some member of `𝒰`. -/
def Refines (𝒱 𝒰 : BasisCover B U) : Prop :=
  ∃ α : 𝒱.ι → 𝒰.ι, ∀ i : 𝒱.ι, ∃ f : 𝒱.obj i ⟶ 𝒰.obj (α i), 𝒱.hom i = f ≫ 𝒰.hom (α i)

/-- A family `C(U)` of basis covers is cofinal if every basis cover of `U` is refined by a member
of `C(U)`. -/
def IsCofinalSystem (C : ∀ U : BasisOpen B, Set (BasisCover B U)) : Prop :=
  ∀ U : BasisOpen B, ∀ 𝒰 : BasisCover B U, ∃ 𝒱 : BasisCover B U, 𝒱 ∈ C U ∧
    Refines 𝒱 𝒰

end BasisCover

namespace CategoryTheory.Presheaf

variable {B : Set (Opens X)}

/-- Definition 6.30.2: a presheaf of sets on the basis `B` is a sheaf on that basis if it
satisfies the Stacks gluing condition `(**)` for every basis cover and every chosen basis cover of
its pairwise intersections. -/
def IsBasisSheaf (F : Presheaf (BasisOpen B)) : Prop :=
  ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U) (𝒱 : BasisIntersectionCover B 𝒰),
    BasisCover.HasSheafCondition F 𝒰 𝒱

/-- A basis sheaf satisfies the gluing condition `(**)` for every basis cover and every chosen
cover of the pairwise intersections. -/
-- Proof sketch: unfold `IsBasisSheaf`.
theorem isBasisSheaf_iff (F : Presheaf (BasisOpen B)) :
    F.IsBasisSheaf ↔
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U) (𝒱 : BasisIntersectionCover B 𝒰),
        BasisCover.HasSheafCondition F 𝒰 𝒱 := by
  -- The theorem is exactly the definitional expansion of `IsBasisSheaf`.
  rfl

end CategoryTheory.Presheaf

/-- The source-facing category of sheaves of sets on the basis `B`, defined by the gluing
condition `(**)` from Definition 6.30.2. -/
abbrev BasisSheaf (B : Set (Opens X)) :=
  ObjectProperty.FullSubcategory fun F : Presheaf (BasisOpen B) ↦ Presheaf.IsBasisSheaf F

/-- The Grothendieck topology on basis opens induced from the topology on all opens of `X`,
available once `B` is known to be a topological basis. -/
noncomputable abbrev basisGrothendieckTopology (B : Set (Opens X)) (hB : Opens.IsBasis B) :
    GrothendieckTopology (BasisOpen B) := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  exact (basisOpenInclusion B).inducedTopology (Opens.grothendieckTopology X)

/-- The canonical bridge/view category of `C`-valued sheaves on the induced basis site. -/
abbrev BasisSiteSheaf (C : Type v) [Category.{w} C] (B : Set (Opens X)) (hB : Opens.IsBasis B) :=
  Sheaf (basisGrothendieckTopology B hB) C

/-! ### Lemma_6_30_3 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.Presheaf
open TopCat.Presheaf

universe u v

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 6.30.3:
- primary domain: the basis-site sheaf condition on chosen covers and chosen overlap covers;
- sampled owner declarations:
  `GrothendieckTopology.OneHypercover`,
  `GrothendieckTopology.OneHypercoverFamily.IsGenerating`,
  `PreOneHypercover.multifork`,
  `Limits.Multifork.isLimit_types_iff`;
- source-facing layer: a basis cover of `U` and a chosen basis cover of each pairwise overlap;
- core/canonical owner: the resulting `1`-hypercover on the basis site
  `basisGrothendieckTopology B`;
- bridge/view layer: `BasisCover.toOneHypercover` and
  `BasisCover.hasSheafCondition_iff_isLimitMultifork`, which identify the Stacks-style condition
  `(**)` with the canonical multifork limit condition for that owner.

Primitive data here are only the cover by basis opens and the chosen overlap covers, now owned by
`Definition_6_30_2`. The fixed target family, refinement relation, generated sieve, and the
generic sheaf criterion on a family of `1`-hypercovers are already owned upstream by
`SemiRepresentableFamily.Over` and `GrothendieckTopology.OneHypercoverFamily`. -/

namespace BasisCover

variable {B : Set (Opens X)} {U : BasisOpen B}

/-- Helper for Lemma 6.30.3: the sieve generated by the arrows of a basis cover. -/
abbrev toSieve (𝒰 : BasisCover B U) : Sieve U :=
  Sieve.ofArrows 𝒰.obj 𝒰.hom

/-- The pre-`1`-hypercover on `U` attached to a basis cover together with chosen overlap covers. -/
def toPreOneHypercover (𝒰 : BasisCover B U) (𝒱 : BasisIntersectionCover B 𝒰) :
    PreOneHypercover U where
  I₀ := 𝒰.ι
  X i := 𝒰.obj i
  f i := 𝒰.hom i
  I₁ i j := 𝒱.κ i j
  Y _ _ k := 𝒱.obj _ _ k
  p₁ _ _ k := 𝒱.left _ _ k
  p₂ _ _ k := 𝒱.right _ _ k
  w _ _ k := by
    apply ObjectProperty.hom_ext
    exact Subsingleton.elim _ _

/-- Helper for Lemma 6.30.3: a refinement of basis covers induces inclusion of the generated
sieves. -/
private theorem toSieve_le_of_refines {𝒰 𝒱 : BasisCover B U}
    (h : Refines 𝒰 𝒱) :
    𝒰.toSieve ≤ 𝒱.toSieve := by
  rcases h with ⟨α, hα⟩
  -- Each member of the refining cover factors through a member of the target cover.
  rw [BasisCover.toSieve, BasisCover.toSieve, Sieve.ofArrows, Sieve.generate_le_iff,
    Presieve.ofArrows_le_iff]
  intro i
  rcases hα i with ⟨f, hf⟩
  exact (Sieve.mem_ofArrows_iff (Y := 𝒱.obj) (f := 𝒱.hom) (g := 𝒰.hom i)).2 ⟨α i, f, hf⟩

private theorem mem_toSieve_basisGrothendieckTopology
    (hB : Opens.IsBasis B) (𝒰 : BasisCover B U) :
    𝒰.toSieve ∈ basisGrothendieckTopology B hB U := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  have hmem :
      𝒰.toSieve ∈ (basisOpenInclusion B).inducedTopology (Opens.grothendieckTopology X) U := by
    rw [Functor.mem_inducedTopology_sieves_iff]
    intro x hx
    change x ∈ (U.obj : Set X) at hx
    rw [𝒰.iUnion_eq] at hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
    refine ⟨(𝒰.obj i).obj, (𝒰.hom i).hom, ?_, hx⟩
    exact ⟨𝒰.obj i, 𝒰.hom i, 𝟙 _, Sieve.ofArrows_mk _ _ i, by simp⟩
  simpa [basisGrothendieckTopology] using hmem

private theorem mem_sieve₁_basisGrothendieckTopology
    (hB : Opens.IsBasis B) (𝒰 : BasisCover B U) (𝒱 : BasisIntersectionCover B 𝒰)
    {i j : 𝒰.ι} {W : BasisOpen B}
    (p₁ : W ⟶ 𝒰.obj i) (p₂ : W ⟶ 𝒰.obj j) (_w : p₁ ≫ 𝒰.hom i = p₂ ≫ 𝒰.hom j) :
    (𝒰.toPreOneHypercover 𝒱).sieve₁ p₁ p₂ ∈ basisGrothendieckTopology B hB W := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  have hmem :
      (𝒰.toPreOneHypercover 𝒱).sieve₁ p₁ p₂ ∈
        (basisOpenInclusion B).inducedTopology (Opens.grothendieckTopology X) W := by
    rw [Functor.mem_inducedTopology_sieves_iff]
    intro x hx
    have hxij :
        x ∈ (((𝒰.obj i).obj ⊓ (𝒰.obj j).obj : Opens X) : Set X) := by
      exact ⟨(leOfHom p₁.hom) hx, (leOfHom p₂.hom) hx⟩
    rw [𝒱.iUnion_eq i j] at hxij
    rcases Set.mem_iUnion.mp hxij with ⟨k, hxk⟩
    have hxWk : x ∈ ((W.obj ⊓ (𝒱.obj i j k).obj : Opens X) : Set X) := by
      exact ⟨hx, hxk⟩
    obtain ⟨_, ⟨Z, hZB, rfl⟩, hxZ, hZle⟩ :=
      hB.exists_subset_of_mem_open hxWk ((W.obj ⊓ (𝒱.obj i j k).obj).2)
    let ZB : BasisOpen B := ⟨Z, hZB⟩
    have hZW : Z ≤ W.obj := le_trans hZle inf_le_left
    have hZY : Z ≤ (𝒱.obj i j k).obj := le_trans hZle inf_le_right
    let g : ZB ⟶ W := ⟨homOfLE hZW⟩
    let h : ZB ⟶ 𝒱.obj i j k := ⟨homOfLE hZY⟩
    have hg : (𝒰.toPreOneHypercover 𝒱).sieve₁ p₁ p₂ g := by
      refine ⟨k, h, ?_, ?_⟩
      all_goals
        apply ObjectProperty.hom_ext
        exact Subsingleton.elim _ _
    refine ⟨Z, g.hom, ?_, hxZ⟩
    exact ⟨ZB, g, 𝟙 _, hg, by simp⟩
  simpa [basisGrothendieckTopology] using hmem

/-- The `1`-hypercover on the basis site attached to a basis cover together with chosen overlap
covers. -/
def toOneHypercover (hB : Opens.IsBasis B) (𝒰 : BasisCover B U) (𝒱 : BasisIntersectionCover B 𝒰) :
    GrothendieckTopology.OneHypercover.{u} (basisGrothendieckTopology B hB) U where
  toPreOneHypercover := 𝒰.toPreOneHypercover 𝒱
  mem₀ := by
    -- The `0`-covering sieve of the hypercover is exactly the sieve generated by `𝒰`.
    simpa [BasisCover.toSieve, BasisCover.toPreOneHypercover]
      using mem_toSieve_basisGrothendieckTopology hB 𝒰
  mem₁ _ _ _ p₁ p₂ w := mem_sieve₁_basisGrothendieckTopology hB 𝒰 𝒱 p₁ p₂ w

/-- The canonical overlap-cover attached to a basis cover, obtained by taking all basis opens
contained in each actual pairwise intersection. -/
def intersectionBasisCover (hB : Opens.IsBasis B) (𝒰 : BasisCover B U) :
    BasisIntersectionCover B 𝒰 where
  κ i j := { V : BasisOpen B // V.obj ≤ (𝒰.obj i).obj ⊓ (𝒰.obj j).obj }
  obj _ _ k := k.1
  left _ _ k := ⟨homOfLE (le_trans k.2 inf_le_left)⟩
  right _ _ k := ⟨homOfLE (le_trans k.2 inf_le_right)⟩
  iUnion_eq i j := by
    ext x
    constructor
    · intro hx
      obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVle⟩ :=
        hB.exists_subset_of_mem_open hx (((𝒰.obj i).obj ⊓ (𝒰.obj j).obj).2)
      exact Set.mem_iUnion.mpr ⟨⟨⟨V, hVB⟩, hVle⟩, hxV⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hxk⟩
      exact k.2 hxk

private abbrev CompatibleSections
    (F : Presheaf.{max u v} (BasisOpen B)) (𝒰 : BasisCover B U)
    (𝒱 : BasisIntersectionCover B 𝒰) :=
  { s : FamilyOfElementsOnObjects F 𝒰.obj //
      ∀ i j k, F.map ((𝒱.left i j k).op) (s i) = F.map ((𝒱.right i j k).op) (s j) }

private def sectionsEquiv
    (F : Presheaf.{max u v} (BasisOpen B)) (𝒰 : BasisCover B U)
    (𝒱 : BasisIntersectionCover B 𝒰) :
    ((𝒰.toPreOneHypercover 𝒱).multicospanIndex F).sections ≃ CompatibleSections F 𝒰 𝒱 where
  toFun s := ⟨s.val, fun i j k ↦ s.property ⟨(i, j), k⟩⟩
  invFun s := ⟨s.1, fun ⟨(i, j), k⟩ ↦ s.2 i j k⟩
  left_inv s := by
    cases s
    rfl
  right_inv s := by
    cases s
    rfl

/-- The Stacks-style condition `(**)` for a basis cover is exactly the multiequalizer condition for
the corresponding basis-site `1`-hypercover. -/
theorem hasSheafCondition_iff_isLimitMultifork
    (F : Presheaf.{max u v} (BasisOpen B)) (𝒰 : BasisCover B U)
    (𝒱 : BasisIntersectionCover B 𝒰) :
    HasSheafCondition F 𝒰 𝒱 ↔
      Nonempty (IsLimit ((𝒰.toPreOneHypercover 𝒱).multifork F)) := by
  rw [Limits.Multifork.isLimit_types_iff,
    ← Function.Bijective.of_comp_iff' (sectionsEquiv F 𝒰 𝒱).bijective,
    Function.bijective_iff_existsUnique]
  unfold HasSheafCondition
  constructor
  · intro h y
    rcases y with ⟨s, hs⟩
    rcases h s hs with ⟨t, ht, huniq⟩
    refine ⟨t, ?_, ?_⟩
    · apply Subtype.ext
      apply funext
      intro i
      exact ht i
    · intro t' ht'
      apply huniq
      intro i
      exact congrArg (fun z ↦ z.1 i) ht'
  · intro h s hs
    rcases h ⟨s, hs⟩ with ⟨t, ht, huniq⟩
    refine ⟨t, ?_, ?_⟩
    · intro i
      exact congrArg (fun z ↦ z.1 i) ht
    · intro t' ht'
      apply huniq
      apply Subtype.ext
      apply funext
      intro i
      exact ht' i

/-- The basis cover attached to a covering sieve on the basis site, obtained by taking as members
the basis opens which already occur as domains of arrows in the sieve. -/
def ofCoveringSieve (hB : Opens.IsBasis B) (S : Sieve U)
    (hS : S ∈ basisGrothendieckTopology B hB U) :
    BasisCover B U where
  ι := Σ V : BasisOpen B, { f : V ⟶ U // S f }
  obj a := a.1
  hom a := a.2.1
  iUnion_eq := by
    ext x
    constructor
    · intro hx
      -- Use induced-topology membership to move the covering sieve back to an actual open cover.
      letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
        basisOpenInclusion_isCoverDense hB
      have hS' : S ∈ (basisOpenInclusion B).inducedTopology (Opens.grothendieckTopology X) U := by
        simpa [basisGrothendieckTopology] using hS
      have hPush :
          S.functorPushforward (basisOpenInclusion B) ∈ Opens.grothendieckTopology X U.obj := by
        rwa [Functor.mem_inducedTopology_sieves_iff] at hS'
      obtain ⟨W, g, hg, hxW⟩ := hPush x hx
      obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVW⟩ := hB.exists_subset_of_mem_open hxW W.2
      let VB : BasisOpen B := ⟨V, hVB⟩
      let f : VB ⟶ U := ⟨homOfLE (le_trans hVW (leOfHom g))⟩
      have hVPush :
          (S.functorPushforward (basisOpenInclusion B)) ((basisOpenInclusion B).map f) := by
        simpa [f] using
          (S.functorPushforward (basisOpenInclusion B)).downward_closed hg (homOfLE hVW)
      have hf : S f := by
        change (S.arrows.functorPushforward (basisOpenInclusion B)) ((basisOpenInclusion B).map f)
          at hVPush
        rwa [Sieve.mem_functorPushforward_iff_of_full_of_faithful] at hVPush
      exact Set.mem_iUnion.mpr ⟨⟨VB, ⟨f, hf⟩⟩, hxV⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨a, hx⟩
      exact (leOfHom a.2.1.hom) hx

private theorem ofCoveringSieve_toSieve_le
    (hB : Opens.IsBasis B) (S : Sieve U) (hS : S ∈ basisGrothendieckTopology B hB U) :
    (ofCoveringSieve hB S hS).toSieve ≤ S := by
  -- Every generator of the reconstructed basis cover already belonged to the original sieve.
  rw [BasisCover.toSieve, Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro a
  exact a.2.2

end BasisCover

variable {B : Set (Opens X)}

variable (F : Presheaf.{max u v} (BasisOpen B))
variable (C : ∀ U : BasisOpen B, Set (BasisCover B U))
variable
  (hInter :
    ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U → BasisIntersectionCover B 𝒰)

private def basisOneHypercoverFamily (hB : Opens.IsBasis B) :
    GrothendieckTopology.OneHypercoverFamily.{u} (basisGrothendieckTopology B hB) :=
  fun ⦃U⦄ E ↦
    ∃ (𝒰 : BasisCover B U) (h𝒰 : 𝒰 ∈ C U),
      E = BasisCover.toOneHypercover hB 𝒰 (hInter 𝒰 h𝒰)

private instance basisOneHypercoverFamily_isGenerating
    (hB : Opens.IsBasis B) (hCofinal : BasisCover.IsCofinalSystem C) :
    (basisOneHypercoverFamily C hInter hB).IsGenerating := by
  constructor
  intro U S hS
  -- Route correction: the current `BasisCover` API uses explicit `Refines`, not family morphisms.
  let 𝒲 := BasisCover.ofCoveringSieve hB S hS
  obtain ⟨𝒰, h𝒰, hrefine⟩ := hCofinal U 𝒲
  refine ⟨BasisCover.toOneHypercover hB 𝒰 (hInter 𝒰 h𝒰), ⟨𝒰, h𝒰, rfl⟩, ?_⟩
  -- Cofinality gives a refinement into the basis cover coming from the ambient covering sieve.
  have hφ : 𝒰.toSieve ≤ 𝒲.toSieve :=
    BasisCover.toSieve_le_of_refines hrefine
  exact le_trans (by
      simpa [BasisCover.toSieve, BasisCover.toOneHypercover, BasisCover.toPreOneHypercover]
        using hφ) (by
    simpa [BasisCover.toSieve, 𝒲] using
      BasisCover.ofCoveringSieve_toSieve_le hB S hS)

-- Proof sketch: package each basis cover in the chosen cofinal system together with its chosen
-- overlap covers as a basis-site `1`-hypercover, apply the generic one-hypercover sheaf criterion,
-- and then translate the resulting multifork condition back to the Stacks-style basis sheaf
-- condition `(**)`.
/-- Lemma 6.30.3: a basis presheaf is a sheaf if and only if it satisfies the basis sheaf
condition `(**)` on a chosen cofinal system of basis coverings, using the given coverings of the
pairwise intersections of those chosen coverings. -/
theorem basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem
    (hB : Opens.IsBasis B) (hCofinal : BasisCover.IsCofinalSystem C) :
    Presheaf.IsSheaf (basisGrothendieckTopology B hB) F ↔
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), ∀ h𝒰 : 𝒰 ∈ C U,
        BasisCover.HasSheafCondition F 𝒰 (hInter 𝒰 h𝒰) := by
  have hSheafIff :
      Presheaf.IsSheaf (basisGrothendieckTopology B hB) F ↔
        ∀ ⦃U : BasisOpen B⦄
          (E : GrothendieckTopology.OneHypercover.{u} (basisGrothendieckTopology B hB) U),
            basisOneHypercoverFamily C hInter hB E →
              Nonempty (IsLimit (E.multifork F)) := by
    let H := basisOneHypercoverFamily C hInter hB
    letI : H.IsGenerating := basisOneHypercoverFamily_isGenerating C hInter hB hCofinal
    simpa [H] using H.isSheaf_iff F
  constructor
  · intro hSheaf U 𝒰 h𝒰
    have hLimit :=
      (hSheafIff.1 hSheaf) (BasisCover.toOneHypercover hB 𝒰 (hInter 𝒰 h𝒰)) ⟨𝒰, h𝒰, rfl⟩
    exact (𝒰.hasSheafCondition_iff_isLimitMultifork F (hInter 𝒰 h𝒰)).2 hLimit
  · intro hCondition
    refine (hSheafIff.2 ?_)
    intro U E hE
    rcases hE with ⟨𝒰, h𝒰, rfl⟩
    exact (𝒰.hasSheafCondition_iff_isLimitMultifork F (hInter 𝒰 h𝒰)).1
      (hCondition 𝒰 h𝒰)

/-- Under the basis hypothesis, the source-facing Stacks condition `(**)` is equivalent to the
canonical sheaf condition on the induced basis site. -/
theorem basisPresheaf_isBasisSheaf_iff_isSheaf
    (hB : Opens.IsBasis B) :
    F.IsBasisSheaf ↔
      Presheaf.IsSheaf (basisGrothendieckTopology B hB) F := by
  constructor
  · intro hCondition
    let C : ∀ U : BasisOpen B, Set (BasisCover B U) := fun _ ↦ Set.univ
    let hInter :
        ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U → BasisIntersectionCover B 𝒰 :=
      fun _ 𝒰 _ ↦ 𝒰.intersectionBasisCover hB
    have hCofinal : BasisCover.IsCofinalSystem C := by
      -- The maximal system is cofinal because every cover trivially refines itself.
      intro U 𝒰
      refine ⟨𝒰, Set.mem_univ _, ?_⟩
      refine ⟨fun i ↦ i, ?_⟩
      intro i
      exact ⟨𝟙 _, by simp⟩
    exact
      (basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem
        F C hInter hB hCofinal).2
        (by
          intro U 𝒰 h𝒰
          exact hCondition 𝒰 (𝒰.intersectionBasisCover hB))
  · intro hSheaf U 𝒰 𝒱
    exact
      (𝒰.hasSheafCondition_iff_isLimitMultifork F 𝒱).2
        ⟨(𝒰.toOneHypercover hB 𝒱).isLimitMultifork ⟨F, hSheaf⟩⟩

/-! ### Lemma_6_30_4 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Presheaf

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)}

/-
Domain-style sampling for Lemma 6.30.4:
- primary domain: the basis-site sheaf condition, expressed through explicit basis covers and their
  pairwise overlaps;
- sampled owner declarations:
  `BasisCover`,
  `BasisIntersectionCover`,
  `BasisCover.HasSheafCondition`,
  `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible`;
- source/core/bridge triage:
  `source-facing`: the Stacks-style pairwise-overlap compatibility and unique gluing statement for
    a basis cover whose overlaps already lie in the basis;
  `core/canonical`: the owner object `BasisCover` together with the generic site-theoretic
    compatibility predicate `FamilyOfElementsOnObjects.IsCompatible`;
  `bridge/view`: the singleton overlap cover `BasisCover.singletonIntersectionCover`, which turns
    the general basis sheaf condition `(**)` into the source-facing pairwise-overlap form.

Primitive data are only the basis cover `𝒰 : BasisCover B U` and the cover-specific witness
`hInter` asserting that each actual overlap `Uᵢ ∩ Uⱼ` of that chosen cover lies in `B`. The
pairwise-overlap equalities are derived API: they unpack
`BasisCover.HasSheafCondition` for this singleton overlap cover, and should remain only a companion
bridge to the generic owner `FamilyOfElementsOnObjects.IsCompatible`, not a second primitive
owner.
-/

namespace BasisCover

variable {U : BasisOpen B}
variable (𝒰 : BasisCover B U)
variable (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)

/-- The actual pairwise overlap `Uᵢ ∩ Uⱼ`, viewed as a basis open when intersections stay in
`B`. -/
def intersection
    (i j : 𝒰.ι) : BasisOpen B :=
  ⟨(𝒰.obj i).obj ⊓ (𝒰.obj j).obj,
    hInter i j⟩

/-- The canonical inclusion of the overlap `Uᵢ ∩ Uⱼ` into the left factor `Uᵢ`. -/
abbrev intersectionLeft
    (i j : 𝒰.ι) : 𝒰.intersection hInter i j ⟶ 𝒰.obj i :=
  ⟨homOfLE inf_le_left⟩

/-- The canonical inclusion of the overlap `Uᵢ ∩ Uⱼ` into the right factor `Uⱼ`. -/
abbrev intersectionRight
    (i j : 𝒰.ι) : 𝒰.intersection hInter i j ⟶ 𝒰.obj j :=
  ⟨homOfLE inf_le_right⟩

/-- The source-facing pairwise-overlap compatibility condition is equivalent to the generic
site-theoretic compatibility predicate on the family of basis opens underlying the cover. -/
theorem isCompatible_iff
    (F : Presheaf.{max u v} (BasisOpen B)) (s : FamilyOfElementsOnObjects F 𝒰.obj) :
    s.IsCompatible ↔
      ∀ i j,
        F.map ((𝒰.intersectionLeft hInter i j).op) (s i) =
          F.map ((𝒰.intersectionRight hInter i j).op) (s j) := by
  constructor
  · intro hs i j
    simpa using
      hs (𝒰.intersection hInter i j) i j
        (𝒰.intersectionLeft hInter i j) (𝒰.intersectionRight hInter i j)
  · intro hs Z i j f g
    let h : Z ⟶ 𝒰.intersection hInter i j :=
      ⟨homOfLE <| le_inf (leOfHom f.hom) (leOfHom g.hom)⟩
    have hf : f = h ≫ 𝒰.intersectionLeft hInter i j := by
      apply ObjectProperty.hom_ext
      exact Subsingleton.elim _ _
    have hg : g = h ≫ 𝒰.intersectionRight hInter i j := by
      apply ObjectProperty.hom_ext
      exact Subsingleton.elim _ _
    calc
      F.map f.op (s i)
          = F.map h.op (F.map ((𝒰.intersectionLeft hInter i j).op) (s i)) := by
              rw [hf, op_comp, FunctorToTypes.map_comp_apply]
      _ = F.map h.op (F.map ((𝒰.intersectionRight hInter i j).op) (s j)) := by
            rw [hs i j]
      _ = F.map g.op (s j) := by
            rw [hg, op_comp, FunctorToTypes.map_comp_apply]

/-- The canonical overlap-cover bridge for a basis cover `𝒰`, obtained by taking each
`Uᵢ ∩ Uⱼ` itself as a singleton basis cover when intersections remain in `B`. -/
def singletonIntersectionCover
    : BasisIntersectionCover B 𝒰 where
  κ _ _ := PUnit
  obj i j _ := 𝒰.intersection hInter i j
  left i j _ := 𝒰.intersectionLeft hInter i j
  right i j _ := 𝒰.intersectionRight hInter i j
  iUnion_eq i j := by
    ext x
    simp [intersection]

/-- Lemma 6.30.4 specializes the basis sheaf condition `(**)` of Lemma 6.30.3 to the case where
the pairwise overlaps are already members of the basis, so no auxiliary overlap cover needs to be
chosen. -/
theorem hasSheafCondition_iff_uniqueGluing
    (F : Presheaf.{max u v} (BasisOpen B)) :
    HasSheafCondition F 𝒰 (𝒰.singletonIntersectionCover hInter) ↔
      ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
        s.IsCompatible →
          ∃! t : F.obj (op U), ∀ i, F.map (𝒰.hom i).op t = s i := by
  constructor
  · intro h s hs
    exact h s (fun i j _ ↦ (𝒰.isCompatible_iff hInter F s).1 hs i j)
  · intro h s hs
    exact h s ((𝒰.isCompatible_iff hInter F s).2 (fun i j ↦ hs i j PUnit.unit))

end BasisCover

-- Proof sketch: use Lemma 6.30.3 with the canonical singleton overlap covers from
-- `BasisCover.singletonIntersectionCover`, and rewrite the resulting sheaf condition by
-- `BasisCover.hasSheafCondition_iff_uniqueGluing`.
/-- Lemma 6.30.4: a basis presheaf is a sheaf exactly when unique gluing holds on each cover in a
chosen cofinal system, provided pairwise intersections of members of those covers stay in the
basis. -/
theorem basisPresheaf_isSheaf_iff_uniqueGluing_on_cofinal_basis_covers
    (hB : Opens.IsBasis B)
    (C : ∀ U : BasisOpen B, Set (BasisCover B U)) (hC : BasisCover.IsCofinalSystem C)
    (hInter :
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U →
        ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (F : Presheaf.{max u v} (BasisOpen B)) :
    Presheaf.IsSheaf (basisGrothendieckTopology B hB) F ↔
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U →
        ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
          s.IsCompatible →
            ∃! t : F.obj (op U), ∀ i, F.map (𝒰.hom i).op t = s i := by
  let hInterC : ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U → BasisIntersectionCover B 𝒰 :=
    fun {U} 𝒰 h𝒰 ↦ 𝒰.singletonIntersectionCover (hInter 𝒰 h𝒰)
  constructor
  · intro hSheaf U 𝒰 h𝒰 s hs
    have hCondition :=
      (basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem F C hInterC hB hC).1 hSheaf
    exact (𝒰.hasSheafCondition_iff_uniqueGluing (hInter 𝒰 h𝒰) F).1 (hCondition 𝒰 h𝒰) s hs
  · intro hUnique
    refine (basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem F C hInterC hB hC).2 ?_
    intro U 𝒰 h𝒰
    exact (𝒰.hasSheafCondition_iff_uniqueGluing (hInter 𝒰 h𝒰) F).2 (hUnique 𝒰 h𝒰)

/-! ### Lemma_6_30_5 (from Chap06) -/
open CategoryTheory Limits Opposite TopologicalSpace TopCat TopCat.Presheaf
open TopCat.Presheaf.Sheafify

noncomputable section

universe u v

namespace BasisSheaf

variable {X : Type u} [TopologicalSpace X] {B : Set (Opens X)}

-- Route correction: this item now stops at the source-facing basis-stalk statement of
-- Lemma 6.30.5. The later ordinary-sheaf transport belongs to `Lemma_6_30_6`, not here.

/-- The stalk of a basis sheaf at `x`, computed directly as the filtered colimit over basis
neighborhoods of `x`. -/
abbrev stalk (F : BasisSheaf B) (hB : Opens.IsBasis B) (x : X) :=
  basisPresheafStalk F.obj x

/-- The family of basis-stalk germs associated to a section over a basis open `U`. -/
abbrev sectionToBasisStalkFamily (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B) :
    F.obj.obj (op U) → ∀ x : U.1, F.stalk hB x.1 :=
  fun s x ↦
    colimit.ι (basisPresheafStalkDiagram F.obj x.1) (op ⟨U, x.2⟩) s

/-- The source-facing local representability condition from Stacks Lemma 6.30.5: a family of basis
stalk elements on `U` is locally induced by sections on basis neighborhoods inside `U`. -/
def IsLocallyRepresentable (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B)
    (t : ∀ x : U.1, F.stalk hB x.1) : Prop :=
  ∀ x : U.1,
    ∃ (V : BasisOpen B) (i : V ⟶ U) (_ : x.1 ∈ V.1) (s : F.obj.obj (op V)),
      ∀ y : V.1, t ⟨y.1, i.hom.le y.2⟩ = sectionToBasisStalkFamily F hB V s y

/-- Helper for Lemma 6.30.5: basis neighborhoods of `x` form a filtered indexing category after
taking opposites, since the basis can be refined inside any pairwise intersection. -/
instance basisOpenNhds_isFiltered (hB : Opens.IsBasis B) (x : X) :
    IsFiltered (BasisOpenNhds B x)ᵒᵖ := by
  classical
  letI : Nonempty ((BasisOpenNhds B x)ᵒᵖ) := by
    obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, -⟩ :=
      hB.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨op ⟨⟨W, hWB⟩, hxW⟩⟩
  refine
    { nonempty := inferInstance
      toIsFilteredOrEmpty :=
        { cocone_objs := ?_
          cocone_maps := ?_ } }
  · intro U V
    -- Refine two basis neighborhoods by a smaller basis neighborhood inside their intersection.
    have hxUV :
        x ∈ (((unop U).1.1 ⊓ (unop V).1.1 : Opens X)) := ⟨(unop U).2, (unop V).2⟩
    obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, hWle⟩ :=
      hB.exists_subset_of_mem_open hxUV ((((unop U).1.1 ⊓ (unop V).1.1 : Opens X)).2)
    let T : BasisOpenNhds B x := ⟨⟨W, hWB⟩, hxW⟩
    have hTU : W ≤ (unop U).1.1 := le_trans hWle inf_le_left
    have hTV : W ≤ (unop V).1.1 := le_trans hWle inf_le_right
    let iTU : T ⟶ unop U :=
      ObjectProperty.homMk
        (ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hTU))
    let iTV : T ⟶ unop V :=
      ObjectProperty.homMk
        (ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hTV))
    refine ⟨op T, ?_, ?_, trivial⟩
    · exact iTU.op
    · exact iTV.op
  · intro U V f g
    -- The indexing category is a preorder, so parallel arrows are automatically equal.
    refine ⟨V, 𝟙 V, ?_⟩
    apply Opposite.unop_injective
    apply ObjectProperty.hom_ext _
    apply ObjectProperty.hom_ext _
    exact Subsingleton.elim _ _

/-- Helper for Lemma 6.30.5: equality of two basis-stalk germs at a point can be represented on a
smaller basis neighborhood by equal restricted sections. -/
lemma exists_restriction_eq_of_basis_stalk_eq
    (F : BasisSheaf B) (hB : Opens.IsBasis B)
    {V W : BasisOpen B}
    (sV : F.obj.obj (op V)) (sW : F.obj.obj (op W))
    {x : X} (hxV : x ∈ V.1) (hxW : x ∈ W.1)
    (hEq :
      sectionToBasisStalkFamily F hB V sV ⟨x, hxV⟩ =
        sectionToBasisStalkFamily F hB W sW ⟨x, hxW⟩) :
    ∃ (T : BasisOpen B) (iTV : T ⟶ V) (iTW : T ⟶ W), x ∈ T.1 ∧
      F.obj.map iTV.op sV = F.obj.map iTW.op sW := by
  -- Unpack equality in the filtered colimit into equality after restriction to a common
  -- basis neighborhood of `x`.
  letI : IsFiltered (BasisOpenNhds B x)ᵒᵖ := basisOpenNhds_isFiltered (B := B) hB x
  rw [sectionToBasisStalkFamily, sectionToBasisStalkFamily] at hEq
  rw [Types.FilteredColimit.colimit_eq_iff (F := basisPresheafStalkDiagram F.obj x)] at hEq
  rcases hEq with ⟨T, iTV, iTW, hEq⟩
  refine ⟨(unop T).1, (iTV.unop).hom, (iTW.unop).hom, (unop T).2, ?_⟩
  simpa [basisPresheafStalkDiagram] using hEq

/-- Helper for Lemma 6.30.5: taking the basis-stalk germ family commutes with restricting a
section to a smaller basis open. -/
lemma sectionToBasisStalkFamily_map
    (F : BasisSheaf B) (hB : Opens.IsBasis B)
    {V W : BasisOpen B} (i : V ⟶ W) (s : F.obj.obj (op W)) (x : V.1) :
    sectionToBasisStalkFamily F hB V (F.obj.map i.op s) x =
      sectionToBasisStalkFamily F hB W s ⟨x.1, i.hom.le x.2⟩ := by
  -- Both germs are represented by the same section, viewed along the colimit cocone naturality.
  let ix : (⟨V, x.2⟩ : BasisOpenNhds B x.1) ⟶ ⟨W, i.hom.le x.2⟩ := ObjectProperty.homMk i
  rw [sectionToBasisStalkFamily, sectionToBasisStalkFamily]
  change
    colimit.ι (basisPresheafStalkDiagram F.obj x.1) (op ⟨V, x.2⟩)
        (((basisPresheafStalkDiagram F.obj x.1).map ix.op) s) =
      colimit.ι (basisPresheafStalkDiagram F.obj x.1) (op ⟨W, i.hom.le x.2⟩) s
  exact congrFun (colimit.w (basisPresheafStalkDiagram F.obj x.1) ix.op) s

/-- Helper for Lemma 6.30.5: for any basis cover, take as overlap cover all basis opens contained
in the actual pairwise intersections. -/
def intersectionBasisCover (hB : Opens.IsBasis B) {U : BasisOpen B} (𝒰 : BasisCover B U) :
    BasisIntersectionCover B 𝒰 where
  κ i j := { V : BasisOpen B // V.1 ≤ (𝒰.obj i).1 ⊓ (𝒰.obj j).1 }
  obj _ _ k := k.1
  left _ _ k := ⟨homOfLE (le_trans k.2 inf_le_left)⟩
  right _ _ k := ⟨homOfLE (le_trans k.2 inf_le_right)⟩
  iUnion_eq i j := by
    ext x
    constructor
    · intro hx
      obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, hWle⟩ :=
        hB.exists_subset_of_mem_open hx (((𝒰.obj i).1 ⊓ (𝒰.obj j).1).2)
      exact Set.mem_iUnion.mpr ⟨⟨⟨W, hWB⟩, hWle⟩, hxW⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
      exact k.2 hk

variable (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B)

-- Proof sketch: this is the defining colimit-germ family, so for each `x : U` we may take the
-- neighborhood `V = U` and the original section `s`.
/-- Any section over `U` determines a basis-stalk family satisfying the source-facing local
representability condition. -/
theorem sectionToBasisStalkFamily_isLocallyRepresentable (s : F.obj.obj (op U)) :
    IsLocallyRepresentable F hB U (sectionToBasisStalkFamily F hB U s) := by
  intro x
  refine ⟨U, 𝟙 U, x.2, s, ?_⟩
  -- The chosen witness section is literally the original section on `U`.
  intro y
  simp [sectionToBasisStalkFamily]

/-- Helper for Lemma 6.30.5: the map from sections on a basis open to their basis-stalk families
is injective. -/
lemma sectionToBasisStalkFamily_injective :
    Function.Injective (sectionToBasisStalkFamily F hB U) := by
  intro s s' hss'
  classical
  have hlocal :
      ∀ x : U.1,
        ∃ (V : BasisOpen B) (i : V ⟶ U), x.1 ∈ V.1 ∧
          F.obj.map i.op s = F.obj.map i.op s' := by
    intro x
    -- Equality of germs at `x` becomes equality after restriction to a smaller basis open.
    obtain ⟨V, iVs, iVs', hxV, hEq⟩ :=
      exists_restriction_eq_of_basis_stalk_eq F hB s s' x.2 x.2 (congrFun hss' x)
    have hi_hom : iVs.hom = iVs'.hom := Subsingleton.elim _ _
    have hi' : iVs = iVs' := ObjectProperty.hom_ext _ hi_hom
    refine ⟨V, iVs, hxV, ?_⟩
    simpa [hi'] using hEq
  choose V i hi hs using hlocal
  let 𝒰 : BasisCover B U :=
    { ι := U.1
      obj := V
      hom := i
      iUnion_eq := by
        ext y
        constructor
        · intro hy
          exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hi ⟨y, hy⟩⟩
        · intro hy
          rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
          exact (i x).hom.le hx }
  let σ : ∀ x : 𝒰.ι, F.obj.obj (op (𝒰.obj x)) := fun x ↦ F.obj.map ((𝒰.hom x).op) s
  have hcompat :
      ∀ x y k,
        F.obj.map ((intersectionBasisCover hB 𝒰).left x y k).op (σ x) =
          F.obj.map ((intersectionBasisCover hB 𝒰).right x y k).op (σ y) := by
    intro x y k
    -- Both overlap restrictions are the restriction of the same global section `s`.
    have hcomp :
        (intersectionBasisCover hB 𝒰).left x y k ≫ 𝒰.hom x =
          (intersectionBasisCover hB 𝒰).right x y k ≫ 𝒰.hom y :=
      ObjectProperty.hom_ext _ (Subsingleton.elim _ _)
    dsimp [σ]
    calc
      F.obj.map ((intersectionBasisCover hB 𝒰).left x y k).op (F.obj.map (𝒰.hom x).op s) =
          F.obj.map (((intersectionBasisCover hB 𝒰).left x y k ≫ 𝒰.hom x).op) s := by
            simp [FunctorToTypes.map_comp_apply]
      _ = F.obj.map (((intersectionBasisCover hB 𝒰).right x y k ≫ 𝒰.hom y).op) s := by
            rw [hcomp]
      _ = F.obj.map ((intersectionBasisCover hB 𝒰).right x y k).op (F.obj.map (𝒰.hom y).op s) := by
            simp [FunctorToTypes.map_comp_apply]
  obtain ⟨t, ht, ht_unique⟩ := F.property 𝒰 (intersectionBasisCover hB 𝒰) σ hcompat
  have hs_glue : ∀ x, F.obj.map ((𝒰.hom x).op) s = σ x := by
    intro x
    rfl
  have hs'_glue : ∀ x, F.obj.map ((𝒰.hom x).op) s' = σ x := by
    intro x
    calc
      F.obj.map ((𝒰.hom x).op) s' = F.obj.map ((𝒰.hom x).op) s := by
        symm
        exact hs x
      _ = σ x := rfl
  -- Uniqueness for the basis sheaf condition identifies the two original sections.
  exact (ht_unique s hs_glue).trans (ht_unique s' hs'_glue).symm

-- Proof sketch: on each overlap basis open, the two local sections induce the same basis-stalk
-- family because both realize the original family `t`; injectivity on that overlap then gives the
-- required equality of restricted sections. The basis sheaf condition glues these local sections.
/-- Lemma 6.30.5: for a sheaf of sets `F` on a basis `B` and a basis open `U`, taking germs gives a
bijection from sections on `U` to families of basis-stalk elements on `U` that are locally induced
by sections on basis neighborhoods inside `U`. -/
theorem sections_bijective_toLocallyRepresentableFamilies :
    Function.Bijective
      (fun s : F.obj.obj (op U) ↦
        show { t : ∀ x : U.1, F.stalk hB x.1 | IsLocallyRepresentable F hB U t } from
          ⟨sectionToBasisStalkFamily F hB U s,
            sectionToBasisStalkFamily_isLocallyRepresentable F hB U s⟩) := by
  constructor
  · intro s s' h
    -- Injectivity is the uniqueness half of the source proof.
    apply sectionToBasisStalkFamily_injective F hB U
    exact congrArg Subtype.val h
  · intro t
    rcases t with ⟨t, ht⟩
    suffices ∃ s : F.obj.obj (op U), sectionToBasisStalkFamily F hB U s = t by
      rcases this with ⟨s, hs⟩
      exact ⟨s, Subtype.ext hs⟩
    classical
    choose V i hi σ hσ using ht
    let 𝒰 : BasisCover B U :=
      { ι := U.1
        obj := V
        hom := i
        iUnion_eq := by
          ext y
          constructor
          · intro hy
            exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hi ⟨y, hy⟩⟩
          · intro hy
            rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
            exact (i x).hom.le hx }
    have hcompat :
        ∀ x y k,
          F.obj.map ((intersectionBasisCover hB 𝒰).left x y k).op (σ x) =
            F.obj.map ((intersectionBasisCover hB 𝒰).right x y k).op (σ y) := by
      intro x y k
      -- On the overlap, both restricted local sections realize the same stalk family `t`.
      apply sectionToBasisStalkFamily_injective F hB ((intersectionBasisCover hB 𝒰).obj x y k)
      ext z
      calc
        sectionToBasisStalkFamily F hB ((intersectionBasisCover hB 𝒰).obj x y k)
            (F.obj.map ((intersectionBasisCover hB 𝒰).left x y k).op (σ x)) z =
          sectionToBasisStalkFamily F hB (V x) (σ x)
            ⟨z.1, ((intersectionBasisCover hB 𝒰).left x y k).hom.le z.2⟩ := by
              simpa using
                sectionToBasisStalkFamily_map F hB
                  ((intersectionBasisCover hB 𝒰).left x y k) (σ x) z
        _ = t ⟨z.1, (i x).hom.le (((intersectionBasisCover hB 𝒰).left x y k).hom.le z.2)⟩ := by
          symm
          exact hσ x ⟨z.1, ((intersectionBasisCover hB 𝒰).left x y k).hom.le z.2⟩
        _ = t ⟨z.1, (i y).hom.le (((intersectionBasisCover hB 𝒰).right x y k).hom.le z.2)⟩ := by
          have hz :
              (⟨z.1, (i x).hom.le (((intersectionBasisCover hB 𝒰).left x y k).hom.le z.2)⟩ : U.1) =
                ⟨z.1, (i y).hom.le (((intersectionBasisCover hB 𝒰).right x y k).hom.le z.2)⟩ :=
            Subtype.ext rfl
          cases hz
          rfl
        _ = sectionToBasisStalkFamily F hB (V y) (σ y)
            ⟨z.1, ((intersectionBasisCover hB 𝒰).right x y k).hom.le z.2⟩ := by
          exact hσ y ⟨z.1, ((intersectionBasisCover hB 𝒰).right x y k).hom.le z.2⟩
        _ =
          sectionToBasisStalkFamily F hB ((intersectionBasisCover hB 𝒰).obj x y k)
            (F.obj.map ((intersectionBasisCover hB 𝒰).right x y k).op (σ y)) z := by
              symm
              simpa using
                sectionToBasisStalkFamily_map F hB
                  ((intersectionBasisCover hB 𝒰).right x y k) (σ y) z
    obtain ⟨s, hs, -⟩ := F.property 𝒰 (intersectionBasisCover hB 𝒰) σ hcompat
    refine ⟨s, ?_⟩
    ext x
    have hxEq : (⟨x.1, (𝒰.hom x).hom.le (hi x)⟩ : U.1) = x := Subtype.ext rfl
    -- Evaluate the glued section on the chosen neighborhood witnessing local representability at
    -- `x`.
    calc
      sectionToBasisStalkFamily F hB U s x =
          sectionToBasisStalkFamily F hB U s ⟨x.1, (𝒰.hom x).hom.le (hi x)⟩ := by
            cases hxEq.symm
            rfl
      _ =
          sectionToBasisStalkFamily F hB (V x)
            (F.obj.map ((𝒰.hom x).op) s) ⟨x.1, hi x⟩ := by
              symm
              simpa using
                sectionToBasisStalkFamily_map F hB (𝒰.hom x) s ⟨x.1, hi x⟩
      _ = sectionToBasisStalkFamily F hB (V x) (σ x) ⟨x.1, hi x⟩ := by
        rw [hs x]
      _ = t ⟨x.1, (i x).hom.le (hi x)⟩ := by
        symm
        exact hσ x ⟨x.1, hi x⟩
      _ = t x := by
        cases hxEq
        rfl

/-- `Set.BijOn` restatement of Lemma 6.30.5. -/
theorem sections_bijOn_locallyRepresentableFamilies :
    Set.BijOn
      (sectionToBasisStalkFamily F hB U)
      (Set.univ : Set (F.obj.obj (op U)))
      { t : ∀ x : U.1, F.stalk hB x.1 | IsLocallyRepresentable F hB U t } := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact sectionToBasisStalkFamily_isLocallyRepresentable F hB U s
  · intro s _ s' _ h
    exact sectionToBasisStalkFamily_injective F hB U h
  · intro t ht
    obtain ⟨s, hs⟩ :=
      (sections_bijective_toLocallyRepresentableFamilies F hB U).2 ⟨t, ht⟩
    exact ⟨s, Set.mem_univ _, congrArg Subtype.val hs⟩

end BasisSheaf

/-! ### Lemma_6_30_6 (from Chap06) -/
open CategoryTheory TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)

/- Domain-style sampling for Lemma 6.30.6:
- primary domain: sheaves of sets on a topological basis and their canonical extension to sheaves
  on `X`;
- sampled owner declarations:
  `BasisSheaf`,
  `BasisSiteSheaf`,
  `basisPresheaf_isBasisSheaf_iff_isSheaf`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
- source/core/bridge triage:
  `source-facing`: `BasisSheaf B`, defined by the Stacks gluing condition on the basis;
  `core/canonical`: `(basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense`;
  `bridge/view`: the comparison from `BasisSheaf B` to `BasisSiteSheaf (Type (max u v)) B hB`.

Primitive data are only a basis presheaf together with the source-facing sheaf predicate. The
induced-topology sheaf structure and the extension to a sheaf on `X` are derived from the
canonical dense-subsite equivalence, so the public API here should expose that bridge and its
direct consequences rather than parallel compatibility aliases. -/

/-- The source-facing category of basis sheaves is equivalent to the canonical sheaf category on
the induced basis site. -/
noncomputable def basisSheafToBasisSiteSheafEquiv :
    BasisSheaf B ≌ BasisSiteSheaf (Type (max u v)) B hB where
  functor :=
    { obj := fun F ↦ ⟨F.obj,
        (basisPresheaf_isBasisSheaf_iff_isSheaf F.obj hB).1 F.property⟩
      map := fun f ↦ ObjectProperty.homMk f.hom }
  inverse :=
    { obj := fun F ↦ ⟨F.obj,
        (basisPresheaf_isBasisSheaf_iff_isSheaf F.obj hB).2 F.property⟩
      map := fun f ↦ ObjectProperty.homMk f.hom }
  unitIso :=
    NatIso.ofComponents (fun F ↦ Iso.refl F) fun {_ _} f ↦ by
      ext
      rfl
  counitIso :=
    NatIso.ofComponents (fun F ↦ Iso.refl F) fun {_ _} f ↦ by
      ext
      rfl

/-- The comparison equivalence between source-facing basis sheaves on `B` and sheaves on `X`. -/
noncomputable abbrev basisSheafComparisonEquiv :
    BasisSheaf B ≌ TopCat.Sheaf (Type (max u v)) X := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  exact (basisSheafToBasisSiteSheafEquiv hB).trans <|
    by
      simpa [BasisSiteSheaf, basisGrothendieckTopology] using
        ((basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
          (Opens.grothendieckTopology X) (Type (max u v)))

namespace BasisSheaf

variable {X : TopCat.{u}} {B : Set (Opens X)}

/-- The canonical basis-site sheaf attached to a source-facing basis sheaf. -/
noncomputable abbrev toBasisSiteSheaf (F : BasisSheaf B) (hB : Opens.IsBasis B) :
    BasisSiteSheaf (Type (max u v)) B hB :=
  (basisSheafToBasisSiteSheafEquiv hB).functor.obj F

/-- Lemma 6.30.6: the canonical extension of a basis sheaf to an ordinary sheaf on `X`. -/
noncomputable abbrev extend (F : BasisSheaf B) (hB : Opens.IsBasis B) :
    TopCat.Sheaf (Type (max u v)) X :=
  (basisSheafComparisonEquiv hB).functor.obj F

/-- Restrict a sheaf on `X` back to a source-facing basis sheaf on `B`. -/
noncomputable abbrev restrictFromSheaf (hB : Opens.IsBasis B)
    (Fext : TopCat.Sheaf (Type (max u v)) X) : BasisSheaf B :=
  (basisSheafComparisonEquiv hB).inverse.obj Fext

/-- The canonical extension restricts back to the original basis sheaf. -/
noncomputable abbrev extendRestrictionIso (F : BasisSheaf B) (hB : Opens.IsBasis B) :
    F ≅ restrictFromSheaf hB (extend F hB) :=
  (basisSheafComparisonEquiv hB).unitIso.app F

/-- The comparison morphism from `F` to the restriction of `F.extend hB` is an isomorphism. -/
-- Proof sketch: this morphism is the `hom` field of the canonical isomorphism
-- `extendRestrictionIso F hB`.
lemma extendRestrictionHom_isIso (F : BasisSheaf B) (hB : Opens.IsBasis B) :
    IsIso ((extendRestrictionIso F hB).hom) :=
  by
    -- The target morphism is already the `hom` of the canonical comparison isomorphism.
    infer_instance

/-- The component over a basis open of the restriction comparison from `F` to the restriction of
its extension. -/
noncomputable abbrev restrictExtendComponentHom
    (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : (BasisOpen B)ᵒᵖ) :
    F.obj.obj U ⟶ ((basisOpenInclusion B).op ⋙ (F.extend hB).presheaf).obj U := by
  simpa [extend, restrictFromSheaf] using
    (F.extendRestrictionIso hB).hom.hom.app U

/-- The uniqueness clause of Lemma 6.30.6: any sheaf on `X` whose restriction to the basis is
identified with `F` is canonically isomorphic to `F.extend hB`. -/
noncomputable abbrev iso_extend_of_restrictIso
    (F : BasisSheaf B) (hB : Opens.IsBasis B)
    (Fext : TopCat.Sheaf (Type (max u v)) X)
    (e : restrictFromSheaf hB Fext ≅ F) :
    Fext ≅ extend F hB :=
  ((basisSheafComparisonEquiv hB).counitIso.app Fext).symm ≪≫
    (basisSheafComparisonEquiv hB).functor.mapIso e

end BasisSheaf

/-! ### Lemma_6_30_7 (from Chap06) -/
open CategoryTheory TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)

/- Domain-style sampling for Lemma 6.30.7:
- primary domain: restriction of sheaves from a topological space to a chosen basis of opens;
- sampled owner declarations:
  `basisSheafComparisonEquiv`,
  `BasisSheaf.restrictFromSheaf`,
  `BasisSheaf.extend`,
  `basisOpenInclusion`;
- best owner abstraction: the source-facing inverse equivalence
  `(basisSheafComparisonEquiv hB).symm`, together with its canonical restriction object
  `BasisSheaf.restrictFromSheaf`;
- primitive data: only the basis witness `hB` and a sheaf on `X`;
- derived API: the restricted basis sheaf and its underlying presheaf description by
  precomposition with `(basisOpenInclusion B).op`;
- source/core/bridge triage:
  `source-facing`: restriction from sheaves on `X` to source-facing basis sheaves on `B`;
  `core/canonical`: `basisSheafComparisonEquiv hB`;
  `bridge/view`: the underlying presheaf formula for `BasisSheaf.restrictFromSheaf`.

This item adds no new owner beyond the inverse of `basisSheafComparisonEquiv hB`, so the refined
file should recall that canonical equivalence directly rather than keep a parallel local alias. -/

/- Lemma 6.30.7: for a topological space `X` and a basis `B` of open subsets, restriction to
the source-facing basis sheaf category is exactly the inverse equivalence to
`basisSheafComparisonEquiv hB`. -/
#check
  (show TopCat.Sheaf (Type (max u v)) X ≌ BasisSheaf B from
    (basisSheafComparisonEquiv hB).symm)

namespace BasisSheaf

variable {X : TopCat.{u}} {B : Set (Opens X)} {hB : Opens.IsBasis B}

/- Companion view: the restricted basis sheaf is obtained by precomposing the original sheaf with
the basis-open inclusion. -/
theorem restrictFromSheaf_obj
    (F : TopCat.Sheaf (Type (max u v)) X) :
    (restrictFromSheaf hB F).obj = (basisOpenInclusion B).op ⋙ F.presheaf :=
  rfl

end BasisSheaf

end

/-! ### Definition_6_30_8 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits

universe u v w u1

variable {X : Type u} [TopologicalSpace X]

variable {C : Type v} [Category.{w} C]
variable {B : Set (Opens X)}

/- Domain-style sampling for Definition 6.30.8:
- primary domain: `C`-valued presheaves and sheaves on the basis site attached to a topological
  basis of `X`;
- sampled owner abstractions:
  `Presheaf`,
  `basisGrothendieckTopology`,
  `BasisSiteSheaf`,
  `Presheaf.isSheaf_iff_isSheaf_comp`;
- source-facing layer: `C`-valued presheaves on the full subcategory of basis opens, their
  morphisms, and the source description of the sheaf condition via the underlying set-valued basis
  presheaf `ℱ ⋙ F`;
- core/canonical owner: for the sheaf notion this is the chapter owner `BasisSiteSheaf C B`;
  for raw `C`-valued presheaves there is no separate upstream generic owner beyond the functor
  category `((BasisOpen B)ᵒᵖ ⥤ C)`, so this file should not introduce a parallel local wrapper;
- bridge/view layer: the canonical comparison theorem
  `Presheaf.isSheaf_iff_isSheaf_comp (basisGrothendieckTopology B) ℱ F`, which identifies the
  basis-site sheaf condition on `ℱ` with the sheaf condition on the underlying set-valued basis
  presheaf `ℱ ⋙ F`;
- primitive data versus derived API: the primitive data are only the functor
  `((BasisOpen B)ᵒᵖ ⥤ C)` and its natural transformations. Once `hB` is fixed, the sheaf notion
  is already owned by `BasisSiteSheaf C B`; the underlying `Type`-valued basis presheaf and the
  comparison theorem are derived companion views rather than parallel owners.

Source/core/bridge triage:
- `source-facing`: a `C`-valued basis presheaf, its morphisms, and the source criterion using the
  underlying set-valued basis presheaf;
- `core/canonical`: the chapter owner `BasisSiteSheaf C B` for sheaves on the basis site;
- `bridge/view`: `Presheaf.isSheaf_iff_isSheaf_comp (basisGrothendieckTopology B) ℱ F`.
-/

/- Definition 6.30.8 (1): a presheaf with values in a category `C` on a basis `B` of `X` is a
`C`-valued contravariant functor on the full subcategory of basis opens. -/
#check ((BasisOpen B)ᵒᵖ ⥤ C)

variable (ℱ 𝒢 : (BasisOpen B)ᵒᵖ ⥤ C)

/- Definition 6.30.8 (2): a morphism of presheaves with values in `C` on `B` is a natural
transformation, i.e. a family of morphisms compatible with restriction. -/
#check (ℱ ⟶ 𝒢)

variable (hB : Opens.IsBasis B)
variable (F : C ⥤ Type u1)

/- Definition 6.30.8 (3): for a type of algebraic structure `(C, F)`, the source's underlying
presheaf of sets attached to a `C`-valued basis presheaf `ℱ` is the composite `ℱ ⋙ F`, i.e.
`U ↦ F.obj (ℱ.obj U)`. -/
#check (ℱ ⋙ F)

/- Definition 6.30.8 (4): the canonical owner for `C`-valued sheaves on the basis `B` is the
basis-site sheaf category `BasisSiteSheaf C B`. -/
#check (BasisSiteSheaf C B hB)

section

variable [HasLimitsOfSize.{u, u} C] [PreservesLimitsOfSize.{u, u} F] [F.ReflectsIsomorphisms]

/- Companion bridge: under the standard algebraic-category hypotheses on the underlying-set
functor `F`, the source sheaf condition on the underlying set-valued basis presheaf `ℱ ⋙ F`
is equivalent to the canonical basis-site sheaf condition on `ℱ`. -/
#check
  (Presheaf.isSheaf_iff_isSheaf_comp (basisGrothendieckTopology B hB) ℱ F :
    Presheaf.IsSheaf (basisGrothendieckTopology B hB) ℱ ↔
      Presheaf.IsSheaf (basisGrothendieckTopology B hB) (ℱ ⋙ F))

end

/-! ### Lemma_6_30_9 (from Chap06) -/
open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {C : Type u} [Category.{u} C]
variable {B : Set (Opens X)}
variable (hB : Opens.IsBasis B)
variable [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C]

/-
Domain-style sampling for Lemma 6.30.9:
- primary domain: dense-subsite comparison for sheaves on a topological basis;
- inspected owner declarations:
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`,
  `basisOpenInclusion_isCoverDense`,
  `basisGrothendieckTopology`,
  `BasisSiteSheaf`;
- source/core/bridge triage:
  `source-facing`: extension and uniqueness for a sheaf on the basis `B`;
  `core/canonical`: `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
  `bridge/view`: the identification of `BasisSiteSheaf C B` with sheaves on the induced topology
  from `basisOpenInclusion B`.

Primitive data is only the basis-site sheaf category `BasisSiteSheaf C B`. The extension object
and uniqueness statement are derived from the dense-subsite equivalence, so the public entry should
be that bridge rather than a parallel local existential or chosen-extension wrapper.
-/

/- Lemma 6.30.9: for a topological basis `B`, sheaves on the basis site and sheaves on `X` are
equivalent. This is the source-facing specialization of the canonical dense-subsite comparison
`(basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense`. -/
#check
  (show BasisSiteSheaf C B hB ≌ TopCat.Sheaf C X from by
    letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
      basisOpenInclusion_isCoverDense hB
    change Sheaf (basisGrothendieckTopology B hB) C ≌ TopCat.Sheaf C X
    exact
      (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
        (Opens.grothendieckTopology X) C)

end

/-! ### Lemma_6_30_10 (from Chap06) -/
open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe v u

section

variable {C : Type v} [Category.{u} C]
variable {X : TopCat.{u}}
variable {B : Set (Opens X)}
variable (hB : Opens.IsBasis B)
variable [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C]

/- Domain-style sampling for Lemma 6.30.10:
- primary domain: dense-subsite comparison for sheaves on a topological basis;
- sampled owner abstractions:
  `basisOpenInclusion_isCoverDense`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`,
  `BasisSiteSheaf`;
- best owner abstraction: the canonical dense-subsite comparison, whose inverse functor is the
  restriction functor on sheaves
  `(basisOpenInclusion B).sheafPushforwardContinuous C (basisGrothendieckTopology B hB)
    (Opens.grothendieckTopology X)`;
- primitive data: the basis-open inclusion `basisOpenInclusion B` and the induced topology
  `basisGrothendieckTopology B hB`;
- derived API: continuity of the inclusion, equivalence of the restriction functor, and its
  presheaf-level comparison isomorphism;
- source/core/bridge triage:
  `source-facing`: restriction from sheaves on `X` to sheaves on the basis `B`;
  `core/canonical`: `Functor.sheafPushforwardContinuous` together with
    `Functor.sheafPushforwardContinuousCompSheafToPresheafIso` and
    `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
  `bridge/view`: the equality `BasisSiteSheaf C B = Sheaf (basisGrothendieckTopology B) C`.
-/

/- Lemma 6.30.10: if `B` is a basis for the topology on `X`, then restriction to basis opens
induces an equivalence between `C`-valued sheaves on `X` and `C`-valued sheaves on the basis
site `B`. This is the source-facing specialization of the canonical dense-subsite comparison. -/
#check
  (by
    letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
      basisOpenInclusion_isCoverDense hB
    letI : Functor.IsContinuous (basisOpenInclusion B)
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) :=
      Functor.IsCoverDense.isContinuous
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) (basisOpenInclusion B)
        (Functor.inducedTopology_coverPreserving (basisOpenInclusion B)
          (Opens.grothendieckTopology X))
    exact
      (show Functor.IsEquivalence
          ((basisOpenInclusion B).sheafPushforwardContinuous C
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)) from by
        simpa using inferInstanceAs
          (((basisOpenInclusion B).sheafPushforwardContinuous C
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).IsEquivalence)))

variable (ℱ : TopCat.Sheaf C X)

/- Companion view: restricting a sheaf on `X` to the basis site `B` is given on underlying
presheaves by precomposition with `(basisOpenInclusion B).op`. This is exactly the canonical
comparison isomorphism `sheafPushforwardContinuousCompSheafToPresheafIso`. -/
#check
  (by
    letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
      basisOpenInclusion_isCoverDense hB
    letI : Functor.IsContinuous (basisOpenInclusion B)
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) :=
      Functor.IsCoverDense.isContinuous
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) (basisOpenInclusion B)
        (Functor.inducedTopology_coverPreserving (basisOpenInclusion B)
          (Opens.grothendieckTopology X))
    exact
      (show (((basisOpenInclusion B).sheafPushforwardContinuous C
          (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj ℱ).obj ≅
            (basisOpenInclusion B).op ⋙ ℱ.presheaf from by
        simpa using
          ((basisOpenInclusion B).sheafPushforwardContinuousCompSheafToPresheafIso C
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).app ℱ))

end

/-! ### Definition_6_30_11 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)}

/- Domain-style sampling for Definition 6.30.11:
- primary domain: presheaves and sheaves of modules over a ring-valued presheaf or sheaf on the
  basis site attached to a topological basis;
- sampled owner abstractions:
  `PMod(𝒪)`,
  `PresheafOfModules`,
  `PresheafOfModules.presheaf`,
  `SheafOfModules`,
  `SheafOfModules.forget`;
- source-facing layer: the Stacks categories of presheaves and sheaves of `𝒪`-modules on the
  basis `B`;
- core/canonical owner: `PresheafOfModules 𝒪` in the presheaf case and `SheafOfModules 𝒪` in the
  sheaf case;
- bridge/view layer: the notation `PMod(𝒪)` from Definition 6.6.1 in the presheaf case and
  `Mod(𝒪)` from Definition 6.10.1 in the sheaf case;
- primitive data versus derived API: `PresheafOfModules` already owns the module objects and
  semilinear restriction maps, while `SheafOfModules` adds only the sheaf condition on the
  underlying abelian presheaf. This file should therefore recall those owners directly, rather
  than introduce a basis-site-specific wrapper.
-/

section PresheafCase

variable (𝒪 : (BasisOpen B)ᵒᵖ ⥤ RingCat.{u})

/- Definition 6.30.11 (1): for a ring-valued presheaf `𝒪` on the basis site `B`, the canonical
owner for presheaves of `𝒪`-modules is `PresheafOfModules`. Specialized to the basis site, the
source-facing category is written `PMod(𝒪)` and has canonical owner `PresheafOfModules 𝒪`. -/
recall PresheafOfModules

/- Source-facing Stacks notation for the same owner on the basis site. -/
#check PMod(𝒪)

variable (ℱ 𝒢 : PMod(𝒪))

/- Definition 6.30.11 (2): a morphism of presheaves of `𝒪`-modules on `B` is a morphism in the
category `PMod(𝒪)`. -/
#check (ℱ ⟶ 𝒢)

/- Companion recall: restriction maps in a presheaf of `𝒪`-modules are semilinear, and the
underlying presheaf of abelian groups is the canonical `PresheafOfModules.presheaf`. -/
recall PresheafOfModules.map_smul
recall PresheafOfModules.presheaf

end PresheafCase

section SheafCase

variable {hB : Opens.IsBasis B}
variable (𝒪 : BasisSiteSheaf RingCat.{u} B hB)

/- Definition 6.30.11 (3): for a sheaf of rings `𝒪` on the basis site `B`, the canonical owner
for sheaves of `𝒪`-modules is `SheafOfModules`. On the source-facing surface from
Definition 6.10.1, the same category is written `Mod(𝒪)`. -/
recall SheafOfModules

/- Source-facing Stacks notation for the same owner. -/
#check Mod(𝒪)

variable (ℱ 𝒢 : Mod(𝒪))

/- A morphism of sheaves of `𝒪`-modules on the basis site is a morphism in `Mod(𝒪)`. -/
#check (ℱ ⟶ 𝒢)

/- Companion recalls: the underlying presheaf of modules and the underlying sheaf of abelian
groups of a sheaf of `𝒪`-modules are obtained by the canonical functors
`SheafOfModules.forget 𝒪` and `SheafOfModules.toSheaf 𝒪`. -/
#check (SheafOfModules.forget 𝒪)
#check (SheafOfModules.toSheaf 𝒪)

end SheafCase
