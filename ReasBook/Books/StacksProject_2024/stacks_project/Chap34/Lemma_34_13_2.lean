import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.Order.Directed
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

noncomputable section

/- Semantic recall: `lean_leansearch` recalled general scheme-cover and standard-smooth APIs, while
local Chapter 34 precedent represents finite affine standard covering families by
`AffineFamilyOver`. This item is therefore stated as the object, morphism, and equality comparison
for those finite affine families over a directed affine inverse limit. The source tag evidence is
consistent with Stacks tag `049N`. -/

/-- A finite family of affine schemes mapping to a fixed base scheme. -/
structure AffineFamilyOver (T : Scheme.{u}) where
  /-- The number of members in the family. -/
  n : ℕ
  /-- The source schemes in the family. -/
  U : Fin n → Scheme.{u}
  /-- The structure morphisms to the common base. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Every member of the family is affine. -/
  isAffine : ∀ j, IsAffine (U j)

/-- An affine family over `T` can be used as its underlying finite family of morphisms to `T`. -/
instance {T : Scheme.{u}} :
    CoeFun (AffineFamilyOver T) (fun 𝒰 ↦ (j : Fin 𝒰.n) → 𝒰.U j ⟶ T) where
  coe 𝒰 := 𝒰.map

namespace AffineFamilyOver

variable {T : Scheme.{u}}

/-- A refinement of finite affine families over the same base scheme. -/
structure Refinement (𝒱 𝒰 : AffineFamilyOver T) where
  /-- The target index in the coarser family for each member of the refining family. -/
  toIndex : Fin 𝒱.n → Fin 𝒰.n
  /-- The factorization morphisms exhibiting the refinement. -/
  lift : (k : Fin 𝒱.n) → 𝒱.U k ⟶ 𝒰.U (toIndex k)
  /-- Each refining morphism factors through the chosen member of the coarser family. -/
  fac : ∀ k, lift k ≫ 𝒰.map (toIndex k) = 𝒱.map k

/-- A refinement can be used as its underlying family of factorization morphisms. -/
instance {𝒱 𝒰 : AffineFamilyOver T} :
    CoeFun (Refinement 𝒱 𝒰) (fun r ↦ (k : Fin 𝒱.n) → 𝒱.U k ⟶ 𝒰.U (r.toIndex k)) where
  coe r := r.lift

/-- A witness that a finite affine family over `T` is isomorphic, as a family over `T`, to the
base change of a finite affine family over `S` along `p : T ⟶ S`. -/
structure IsBaseChangeOf {S T : Scheme.{u}} (p : T ⟶ S)
    (𝒰S : AffineFamilyOver S) (𝒰T : AffineFamilyOver T) where
  /-- The index bijection between the original family and the displayed base-changed family. -/
  indexEquiv : Fin 𝒰S.n ≃ Fin 𝒰T.n
  /-- The componentwise isomorphisms from the categorical pullbacks to the displayed members. -/
  componentIso : ∀ j : Fin 𝒰S.n, pullback p (𝒰S.map j) ≅ 𝒰T.U (indexEquiv j)
  /-- Each component isomorphism is compatible with the structure morphism to the new base. -/
  map_eq : ∀ j : Fin 𝒰S.n,
    (componentIso j).hom ≫ 𝒰T.map (indexEquiv j) = pullback.fst p (𝒰S.map j)

end AffineFamilyOver

/-- The five standard topologies appearing in Lemma 34.13.2. -/
inductive StandardTopology where
  /-- The Zariski topology. -/
  | zariski
  /-- The étale topology. -/
  | etale
  /-- The smooth topology. -/
  | smooth
  /-- The syntomic topology. -/
  | syntomic
  /-- The fppf topology. -/
  | fppf

namespace StandardTopology

/-- A finite affine family over a scheme is a standard covering for one of the five topologies
used in Lemma 34.13.2. The target affineness and the common finite family are explicit, while the
topology-specific member condition is selected by `τ`. -/
def IsStandardCover {T : Scheme.{u}} (τ : StandardTopology) (𝒰 : AffineFamilyOver T) : Prop :=
  IsAffine T ∧
    (∀ t : T, ∃ j : Fin 𝒰.n, t ∈ Set.range ⇑(ConcreteCategory.hom (𝒰.map j).base)) ∧
      match τ with
      | zariski =>
          ∀ j : Fin 𝒰.n,
            IsOpenImmersion (𝒰.map j) ∧
              ∃ s : Γ(T, ⊤),
                Set.range ⇑(ConcreteCategory.hom (𝒰.map j).base) = (T.basicOpen s : Set T)
      | etale => ∀ j : Fin 𝒰.n, Etale (𝒰.map j)
      | smooth =>
          ∀ j : Fin 𝒰.n,
            RingHom.IsStandardSmooth (CommRingCat.Hom.hom (Scheme.Hom.appTop (𝒰.map j)))
      | syntomic =>
          ∀ j : Fin 𝒰.n,
            let f := CommRingCat.Hom.hom (Scheme.Hom.appTop (𝒰.map j))
            @Algebra.IsRelativeGlobalCompleteIntersection _ _ _ _ f.toAlgebra
      | fppf =>
          ∀ j : Fin 𝒰.n, Flat (𝒰.map j) ∧ LocallyOfFinitePresentation (𝒰.map j)

end StandardTopology

namespace AffineFamilyOver

namespace Refinement

/-- A witness that a refinement of finite affine families over `T` is the base change of a
refinement over `S`, relative to chosen base-change identifications of the source and target
families. -/
structure IsBaseChangeOf {S T : Scheme.{u}} {p : T ⟶ S}
    {𝒰S 𝒱S : AffineFamilyOver S} {𝒰T 𝒱T : AffineFamilyOver T}
    (h𝒰 : AffineFamilyOver.IsBaseChangeOf p 𝒰S 𝒰T)
    (h𝒱 : AffineFamilyOver.IsBaseChangeOf p 𝒱S 𝒱T)
    (rS : Refinement 𝒰S 𝒱S) (rT : Refinement 𝒰T 𝒱T) where
  /-- The target-index map commutes with the two base-change index bijections. -/
  index_compatible : ∀ j : Fin 𝒰S.n,
    h𝒱.indexEquiv (rS.toIndex j) = rT.toIndex (h𝒰.indexEquiv j)
  /-- The componentwise morphism between categorical pullbacks induced by the original
  refinement. -/
  pullbackLift : ∀ j : Fin 𝒰S.n,
    pullback p (𝒰S.map j) ⟶ pullback p (𝒱S.map (rS.toIndex j))
  /-- The induced pullback lift is compatible with the projection to the new base. -/
  pullbackLift_fst : ∀ j : Fin 𝒰S.n,
    pullbackLift j ≫ pullback.fst p (𝒱S.map (rS.toIndex j)) =
      pullback.fst p (𝒰S.map j)
  /-- The induced pullback lift is compatible with the projection to the old source member. -/
  pullbackLift_snd : ∀ j : Fin 𝒰S.n,
    pullbackLift j ≫ pullback.snd p (𝒱S.map (rS.toIndex j)) =
      pullback.snd p (𝒰S.map j) ≫ rS.lift j
  /-- After transport along the chosen component isomorphisms, the displayed refinement over `T`
  agrees with the induced pullback refinement. -/
  lift_compatible : ∀ j : Fin 𝒰S.n,
    HEq ((h𝒰.componentIso j).hom ≫ rT.lift (h𝒰.indexEquiv j))
      (pullbackLift j ≫ (h𝒱.componentIso (rS.toIndex j)).hom)

/-- The compatibility conditions asserting that a refinement between two explicitly given
later-stage affine families descends a refinement already seen on the affine limit. -/
structure DescendedStageCompatibility {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (τ : StandardTopology) {i : I}
    (𝒱i 𝒱i' : AffineFamilyOver (D.obj i))
    (𝒱T 𝒱T' : AffineFamilyOver c.pt)
    (f : Refinement 𝒱T 𝒱T') {i' : I} (hi : i ≤ i')
    (source target : AffineFamilyOver (D.obj i'))
    (source_limitBaseChange : AffineFamilyOver.IsBaseChangeOf (c.π.app i') source 𝒱T)
    (target_limitBaseChange : AffineFamilyOver.IsBaseChangeOf (c.π.app i') target 𝒱T')
    (refinement : Refinement source target) : Prop where
  /-- The descended source family is a standard covering for the selected topology. -/
  source_standard : τ.IsStandardCover source
  /-- The descended target family is a standard covering for the selected topology. -/
  target_standard : τ.IsStandardCover target
  /-- The descended source family base-changes to the original source family at stage `i`. -/
  source_baseChange :
    Nonempty (AffineFamilyOver.IsBaseChangeOf (D.map (homOfLE hi)) 𝒱i source)
  /-- The descended target family base-changes to the original target family at stage `i`. -/
  target_baseChange :
    Nonempty (AffineFamilyOver.IsBaseChangeOf (D.map (homOfLE hi)) 𝒱i' target)
  /-- The original refinement on the limit is the base change of the descended refinement. -/
  refinement_baseChange :
    Nonempty (IsBaseChangeOf source_limitBaseChange target_limitBaseChange refinement f)

/-- The compatibility conditions asserting that two explicitly given later-stage refinements
become equal and still base-change to the original refinements. -/
structure EventualEqualityStageCompatibility {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (τ : StandardTopology) {i : I}
    (𝒱i 𝒱i' : AffineFamilyOver (D.obj i))
    (f g : Refinement 𝒱i 𝒱i') {i' : I} (hi : i ≤ i')
    (source target : AffineFamilyOver (D.obj i'))
    (source_baseChange : AffineFamilyOver.IsBaseChangeOf (D.map (homOfLE hi)) 𝒱i source)
    (target_baseChange : AffineFamilyOver.IsBaseChangeOf (D.map (homOfLE hi)) 𝒱i' target)
    (first second : Refinement source target) : Prop where
  /-- The later-stage source family is a standard covering for the selected topology. -/
  source_standard : τ.IsStandardCover source
  /-- The later-stage target family is a standard covering for the selected topology. -/
  target_standard : τ.IsStandardCover target
  /-- The first original refinement is the base change of the first descended refinement. -/
  first_baseChange : Nonempty (IsBaseChangeOf source_baseChange target_baseChange f first)
  /-- The second original refinement is the base change of the second descended refinement. -/
  second_baseChange : Nonempty (IsBaseChangeOf source_baseChange target_baseChange g second)
  /-- The two descended refinements agree at the later stage. -/
  equal : first = second

end Refinement

end AffineFamilyOver

open StandardTopology

/-- Lemma 34.13.2 (1): a standard `τ`-covering of the affine limit `T` descends to a standard
`τ`-covering at some stage, whose base change to `T` is isomorphic to the original covering. -/
@[stacks 049N]
theorem exists_standardCover_descends_along_directedAffineLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD_affine : ∀ i : I, IsAffine (D.obj i))
    (τ : StandardTopology) (𝒱 : AffineFamilyOver c.pt)
    (h𝒱 : τ.IsStandardCover 𝒱) :
    ∃ i : I, ∃ 𝒱i : AffineFamilyOver (D.obj i),
      τ.IsStandardCover 𝒱i ∧
        Nonempty (AffineFamilyOver.IsBaseChangeOf (c.π.app i) 𝒱i 𝒱) := sorry

/-- Lemma 34.13.2 (2): a morphism between the base changes to the affine limit of two standard
`τ`-coverings at a fixed stage descends, after passing to a later stage, to a morphism between the
corresponding base-changed standard coverings. -/
@[stacks 049N]
theorem standardCover_refinement_descends_along_directedAffineLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD_affine : ∀ k : I, IsAffine (D.obj k))
    (τ : StandardTopology) {i : I}
    (𝒱i 𝒱i' : AffineFamilyOver (D.obj i))
    (h𝒱i : τ.IsStandardCover 𝒱i) (h𝒱i' : τ.IsStandardCover 𝒱i')
    (𝒱T 𝒱T' : AffineFamilyOver c.pt)
    (h𝒱T : AffineFamilyOver.IsBaseChangeOf (c.π.app i) 𝒱i 𝒱T)
    (h𝒱T' : AffineFamilyOver.IsBaseChangeOf (c.π.app i) 𝒱i' 𝒱T')
    (f : AffineFamilyOver.Refinement 𝒱T 𝒱T') :
    ∃ i' : I, ∃ hi : i ≤ i',
      ∃ 𝒱iStage : AffineFamilyOver (D.obj i'),
      ∃ 𝒱iStage' : AffineFamilyOver (D.obj i'),
      ∃ hStageT : AffineFamilyOver.IsBaseChangeOf (c.π.app i') 𝒱iStage 𝒱T,
      ∃ hStageT' : AffineFamilyOver.IsBaseChangeOf (c.π.app i') 𝒱iStage' 𝒱T',
      ∃ fi' : AffineFamilyOver.Refinement 𝒱iStage 𝒱iStage',
        AffineFamilyOver.Refinement.DescendedStageCompatibility D c τ 𝒱i 𝒱i' 𝒱T 𝒱T' f hi
          𝒱iStage 𝒱iStage' hStageT hStageT' fi' := sorry

/-- Lemma 34.13.2 (3): if two morphisms of standard `τ`-coverings at a fixed stage become equal
after base change to the affine limit, then they become equal after base change to some later
stage. -/
@[stacks 049N]
theorem standardCover_refinement_eventually_equal_of_limit_baseChange_equal
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD_affine : ∀ k : I, IsAffine (D.obj k))
    (τ : StandardTopology) {i : I}
    (𝒱i 𝒱i' : AffineFamilyOver (D.obj i))
    (h𝒱i : τ.IsStandardCover 𝒱i) (h𝒱i' : τ.IsStandardCover 𝒱i')
    (f g : AffineFamilyOver.Refinement 𝒱i 𝒱i')
    (𝒱T 𝒱T' : AffineFamilyOver c.pt)
    (h𝒱T : AffineFamilyOver.IsBaseChangeOf (c.π.app i) 𝒱i 𝒱T)
    (h𝒱T' : AffineFamilyOver.IsBaseChangeOf (c.π.app i) 𝒱i' 𝒱T')
    (fT gT : AffineFamilyOver.Refinement 𝒱T 𝒱T')
    (hfT : AffineFamilyOver.Refinement.IsBaseChangeOf h𝒱T h𝒱T' f fT)
    (hgT : AffineFamilyOver.Refinement.IsBaseChangeOf h𝒱T h𝒱T' g gT)
    (hfgT : fT = gT) :
    ∃ i' : I, ∃ hi : i ≤ i',
      ∃ 𝒱iStage : AffineFamilyOver (D.obj i'),
      ∃ 𝒱iStage' : AffineFamilyOver (D.obj i'),
      ∃ hStage : AffineFamilyOver.IsBaseChangeOf (D.map (homOfLE hi)) 𝒱i 𝒱iStage,
      ∃ hStage' : AffineFamilyOver.IsBaseChangeOf (D.map (homOfLE hi)) 𝒱i' 𝒱iStage',
      ∃ fi' gi' : AffineFamilyOver.Refinement 𝒱iStage 𝒱iStage',
        AffineFamilyOver.Refinement.EventualEqualityStageCompatibility D τ 𝒱i 𝒱i' f g hi
          𝒱iStage 𝒱iStage' hStage hStage' fi' gi' := sorry

end

end AlgebraicGeometry
