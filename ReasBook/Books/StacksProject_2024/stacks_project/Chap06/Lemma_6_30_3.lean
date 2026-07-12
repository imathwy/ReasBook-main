import StacksProject_2024.Chap06.Definition_6_30_2
import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.Presheaf
open CategoryTheory.SemiRepresentableFamily.Over
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

private theorem mem_toSieve_basisGrothendieckTopology
    (hB : Opens.IsBasis B) (𝒰 : BasisCover B U) :
    𝒰.family.toSieve ∈ basisGrothendieckTopology B hB U := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  have hmem :
      𝒰.family.toSieve ∈ (basisOpenInclusion B).inducedTopology (Opens.grothendieckTopology X) U := by
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
  mem₀ := mem_toSieve_basisGrothendieckTopology hB 𝒰
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
  family := {
    index := Σ V : BasisOpen B, { f : V ⟶ U // S f }
    obj := fun a ↦ Over.mk a.2.1 }
  iUnion_eq := by
    ext x
    constructor
    · intro hx
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
    (ofCoveringSieve hB S hS).family.toSieve ≤ S := by
  rw [SemiRepresentableFamily.Over.toSieve, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
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
  let 𝒲 := BasisCover.ofCoveringSieve hB S hS
  obtain ⟨𝒰, h𝒰, hrefine⟩ := hCofinal U 𝒲
  rcases hrefine with ⟨φ⟩
  refine ⟨BasisCover.toOneHypercover hB 𝒰 (hInter 𝒰 h𝒰), ⟨𝒰, h𝒰, rfl⟩, ?_⟩
  have hφ : 𝒰.family.toSieve ≤ 𝒲.family.toSieve :=
    toSieve_le_of_hom φ
  exact le_trans hφ (by
    simpa [𝒲] using
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
      intro U 𝒰
      exact ⟨𝒰, Set.mem_univ _, ⟨𝟙 _⟩⟩
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
