import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_1_11_21 (from Items/Chap01) -/
universe u

open FreeGroup
open scoped Pointwise

-- Layer triage:
-- `source-facing`: the ambient group `F`, the subset `S`, the generation hypothesis
-- `Subgroup.closure S = ⊤`, the inverse-disjointness hypothesis `Disjoint S S⁻¹`, and the
-- Section `11` owner property on `S ∪ S⁻¹`.
-- `core/canonical`: `IsFreeGroupBasis S` from Definition `1-1-1`,
-- `closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word` from Proposition `1-1-12`,
-- `Set.HasNontrivialNoncancellingProducts (S ∪ S⁻¹)` from Proposition `1-11-20`, and
-- `Subgroup.closure`.
-- `bridge/view`: none. The long quantified word hypothesis is already owned by the Section `11`
-- subset property, and the inverse-disjointness hypothesis is the source-facing bridge from
-- Section `11` noncancelling words to the Chapter `1-1` reduced-word owner criterion.
--
-- Domain sampling:
-- 1. `IsFreeGroupBasis` is the chapter owner abstraction for the textbook claim that `S` is a
--    basis of the ambient free group.
-- 2. `Subgroup.closure S = ⊤` is the canonical way to state that `S` generates `F`.
-- 3. `closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word` is the chapter owner bridge
--    from reduced words in the letters of `S` to the basis conclusion.
-- 4. `Set.HasNontrivialNoncancellingProducts` from Proposition `1-11-20` is the owner
--    abstraction for the Section `11` nontrivial-word hypothesis.

section

variable {F : Type u} [Group F]

/-- Corollary 1-11-21: if `S` generates `F`, is disjoint from its inverse set, and every nonempty
noncancelling word in letters from `S ∪ S⁻¹` has nontrivial product, then `S` is a basis for the
free group `F`. -/
-- Proof sketch: use Proposition `1-1-12` to reduce the basis claim on the generated subgroup to
-- nontriviality of reduced words in the letters of `S`. The inverse-disjointness hypothesis turns
-- reduced signed words on `S` into Section `11` noncancelling products in `S ∪ S⁻¹`, so the owner
-- hypothesis `hprod` supplies the required nontriviality. Finally `hgen` identifies the generated
-- subgroup with the whole ambient group `F`.
theorem isFreeGroupBasis_of_closure_eq_top_of_nontrivial_noncancelling_products
    (S : Set F) (hgen : Subgroup.closure S = ⊤)
    (hdisj : Disjoint S S⁻¹)
    (hprod : Set.HasNontrivialNoncancellingProducts (S ∪ S⁻¹)) :
    IsFreeGroupBasis S := by
  let T : Set (Subgroup.closure S) := {x | (x : F) ∈ S}
  have hT : IsFreeGroupBasis T := by
    rw [closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word]
    intro w hw hred
    let eval : S × Bool → F := fun x ↦ cond x.2 x.1.1 x.1.1⁻¹
    have hmem : ∀ u ∈ w.map eval, u ∈ S ∪ S⁻¹ := by
      intro u hu
      rcases List.mem_map.mp hu with ⟨x, hx, rfl⟩
      dsimp [eval]
      by_cases hx2 : x.2
      · left
        show (bif x.2 then (x.1 : F) else (x.1 : F)⁻¹) ∈ S
        have hxmem : (x.1 : F) ∈ S := x.1.2
        simpa [hx2] using hxmem
      · right
        rw [Set.mem_inv]
        show (bif x.2 then (x.1 : F) else (x.1 : F)⁻¹)⁻¹ ∈ S
        have hxmem : (x.1 : F) ∈ S := x.1.2
        simpa [hx2] using hxmem
    have hchain : (w.map eval).IsChain (fun u v ↦ u * v ≠ 1) := by
      rw [FreeGroup.IsReduced] at hred
      exact List.isChain_map_of_isChain eval (fun a b hab hmul ↦ by
        rw [Set.disjoint_left] at hdisj
        cases ha : a.2 <;> cases hb : b.2
        · have hEq : (a.1 : F) = (b.1 : F)⁻¹ := by
            dsimp [eval] at hmul
            simp [ha, hb] at hmul
            exact inv_mul_eq_one.mp hmul
          exact hdisj b.1.2 <| by
            rw [Set.mem_inv]
            simpa [hEq] using a.1.2
        · have hEq : (a.1 : F) = b.1 := by
            dsimp [eval] at hmul
            simp [ha, hb] at hmul
            exact inv_mul_eq_one.mp hmul
          have hbool : false = true := by
            simpa [ha, hb] using hab (Subtype.ext hEq)
          cases hbool
        · have hEq : (a.1 : F) = b.1 := by
            dsimp [eval] at hmul
            simp [ha, hb] at hmul
            exact mul_inv_eq_one.mp hmul
          have hbool : true = false := by
            simpa [ha, hb] using hab (Subtype.ext hEq)
          cases hbool
        · have hEq : (b.1 : F) = (a.1 : F)⁻¹ := by
            dsimp [eval] at hmul
            simp [ha, hb] at hmul
            exact (mul_eq_one_iff_eq_inv').mp hmul
          exact hdisj a.1.2 <| by
            rw [Set.mem_inv]
            simpa [hEq] using b.1.2) hred
    have hne : (w.map eval).prod ≠ (1 : F) :=
      hprod.prod_ne_one (by simpa [eval] using hw) hmem hchain
    simpa [eval, lift_mk] using hne
  intro H _ φ
  let eS : T ≃ S :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun x ↦ ⟨⟨x.1, Subgroup.subset_closure x.2⟩, x.2⟩
      left_inv := fun x ↦ by
        cases x
        rfl
      right_inv := fun x ↦ rfl }
  let eF : Subgroup.closure S ≃* F := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  let ψ : T → H := fun x ↦ φ (eS x)
  rcases hT ψ with ⟨ψStar, hψStar, hψUnique⟩
  refine ⟨ψStar.comp eF.symm.toMonoidHom, ?_, ?_⟩
  · intro s
    have hs : (eF.symm s.1 : Subgroup.closure S) = ⟨s.1, Subgroup.subset_closure s.2⟩ := by
      ext
      simp [eF]
    simpa [ψ, eS, hs] using hψStar (eS.symm s)
  · intro γ hγ
    have hcomp : γ.comp eF.toMonoidHom = ψStar := by
      apply hψUnique
      intro x
      simpa [ψ, eS, eF] using hγ (eS x)
    ext g
    have := congrArg (fun f : Subgroup.closure S →* H ↦ f (eF.symm g)) hcomp
    simpa [eF] using this

end

/-! ### Proposition_1_11_22 (from Items/Chap01) -/
noncomputable section

universe u v w

open GroupExtension

/- Proposition 1-11-22 is the Section `11` conclusion that the ambient group `G*` splits over the
free quotient `F`, with kernel `N`, so `G*` is a semidirect product of `N` by `F`.

Layer triage:
- `source-facing`: the extension `1 → N → G* → F → 1` and the existence of a homomorphic section
  of the quotient map `G* → F`.
- `core/canonical`: `GroupExtension N GStar F`, `GroupExtension.Splitting`, and the canonical
  semidirect-product equivalence attached to a splitting.
- `bridge/view`: the source-facing right inverse to `rightHom` is packaged as a
  `GroupExtension.Splitting`, from which the canonical semidirect-product equivalence is derived.

Domain sampling:
1. `GroupExtension N GStar F` is mathlib's owner abstraction for the short exact sequence
   `1 → N → G* → F → 1`.
2. `GroupExtension.Splitting` is the canonical owner of a split extension.
3. `IsFreeGroup.of`, `IsFreeGroup.lift`, and `IsFreeGroup.ext_hom` are the owner API for building
   and characterizing homomorphisms out of the free quotient `F`.
4. `GroupExtension.Splitting.semidirectProductMulEquiv` is the canonical decomposition of a split
   extension as a semidirect product.

Primitive vs. derived:
the primitive data are the extension `S` and the freeness of the quotient `F`; the source-facing
conclusion is that the extension splits, whose canonical owner is `S.Splitting`. The raw
right-inverse equation for `rightHom` and the semidirect-product equivalence are derived API from
that owner. -/

section

variable {N : Type u} {GStar : Type v} {F : Type w} [Group N] [Group GStar] [Group F]

/-- Proposition 1-11-22: if `1 → N → G* → F → 1` is an extension and the quotient `F` is free,
then the extension splits. Equivalently, the quotient map `G* → F` admits a homomorphic section,
and hence `G*` is canonically identified with a semidirect product via
`s.semidirectProductMulEquiv`. -/
theorem GroupExtension.exists_splitting_of_free_quotient
    (S : GroupExtension N GStar F) [IsFreeGroup F] :
    Nonempty S.Splitting := by
  let s : F →* GStar :=
    IsFreeGroup.lift fun a ↦ Function.surjInv S.rightHom_surjective (IsFreeGroup.of a)
  have hs : S.rightHom.comp s = MonoidHom.id F := by
    apply IsFreeGroup.ext_hom
    intro a
    simp [s, Function.surjInv_eq]
  exact ⟨⟨s, fun g ↦ DFunLike.congr_fun hs g⟩⟩

/-- Bridge/view form of Proposition 1-11-22: the splitting produced by
`exists_splitting_of_free_quotient` yields a homomorphic right inverse to `rightHom`. -/
theorem GroupExtension.exists_rightInverse_rightHom_of_free_quotient
    (S : GroupExtension N GStar F) [IsFreeGroup F] :
    ∃ s : F →* GStar, S.rightHom.comp s = MonoidHom.id F := by
  obtain ⟨s⟩ := S.exists_splitting_of_free_quotient
  exact ⟨s, s.rightHom_comp_splitting⟩

namespace GroupExtension.Splitting

/-- The canonical semidirect-product equivalence sends the copy of `F` in `N ⋊[s.conjAct] F` to
the chosen splitting of the quotient map. -/
theorem semidirectProductMulEquiv_inr {S : GroupExtension N GStar F} (s : S.Splitting) (g : F) :
    s.semidirectProductMulEquiv (SemidirectProduct.inr g) = s g := by
  change S.inl 1 * s g = s g
  simp

end GroupExtension.Splitting

end

/-! ### Proposition_1_11_23 (from Items/Chap01) -/
universe u v w x

open Monoid
open scoped Pointwise

section

/- Proposition 1-11-23 lies in Section 11 on subgroups of an amalgamated free product.

Layer triage:
- `source-facing`: the amalgamated free product `PushoutI φ`, the subgroup `G*`, the conjugate
  intersection subgroups `p⁻¹ Hᵢ p ∩ G*`, and the normal subgroup `N` generated by all of them.
- `core/canonical`: `Monoid.PushoutI` for the ambient amalgamated product, `Subgroup.comap` and
  `Subgroup.map` for the conjugate intersections, `Subgroup.normalClosure` for the generated
  normal subgroup, the tree-product owner declarations from Proposition `1-11-11`, and
  `IsFreeGroup` for the quotient.
- `bridge/view`: the textbook family `C*` is recorded as the canonical subgroup
  `conjugateFactorIntersectionSubgroup`, while the normal subgroup `N` is the canonical normal
  closure of the union of their elements inside `G*`.

Domain sampling:
1. `Monoid.PushoutI φ` is mathlib's owner abstraction for a free product with a subgroup
   amalgamated.
2. `Monoid.PushoutI.of_injective` is the canonical bridge from injectivity of the amalgamating maps
   to honest embedded factor subgroups in the pushout.
3. `Subgroup.comap`, `Subgroup.map`, and `Subgroup.normalClosure` are the canonical owners for the
   subgroup constructions appearing in the proposition.
4. `SimpleGraph.IsTree` is mathlib's owner abstraction for the graph-theoretic tree appearing in
   the tree-product clause.
5. `IsFreeGroup` is mathlib's owner abstraction for the conclusion that the quotient is free.

Primitive vs. derived:
the primitive data are the amalgamated pushout diagram `φ` and the subgroup `G*`; the conjugate
intersection subgroups and their generated normal subgroup are canonical constructions from those
data, while the tree-product conclusion reuses the Chapter 1 source-facing owner
`TreeProductDiagram.IsTreeProductOf`, built from the core pair `TreeProductCocone` and
`IsTreeProduct`. -/

variable {ι : Type u} {A : Type v} {H : ι → Type w}
variable [Group A] [∀ i, Group (H i)]
variable (φ : ∀ i, A →* H i)

/-- The subgroup `p⁻¹ Hᵢ p ∩ G*`, viewed as a subgroup of `G*`, where `Hᵢ` is the image of the
`i`th factor in the amalgamated product `PushoutI φ`. -/
abbrev conjugateFactorIntersectionSubgroup
    (GStar : Subgroup (PushoutI φ)) (p : PushoutI φ) (i : ι) : Subgroup GStar :=
  Subgroup.comap GStar.subtype <| MulAut.conj p⁻¹ • (PushoutI.of i).range

/-- The normal subgroup of `G*` generated by all conjugate intersections `p⁻¹ Hᵢ p ∩ G*`. -/
abbrev generatedConjugateFactorNormalSubgroup
    (GStar : Subgroup (PushoutI φ)) : Subgroup GStar :=
  Subgroup.normalClosure
    {x : GStar | ∃ p : PushoutI φ, ∃ i : ι,
      x ∈ conjugateFactorIntersectionSubgroup φ GStar p i}

/-- Membership in `conjugateFactorIntersectionSubgroup` means that the ambient element of `G*`
lies in the conjugate of the `i`th factor subgroup by `p⁻¹`. -/
-- Proof sketch: unfold `conjugateFactorIntersectionSubgroup`; it is defined as the `comap` of the
-- conjugated factor subgroup along the inclusion `G* ↪ PushoutI φ`.
theorem mem_conjugateFactorIntersectionSubgroup_iff
    (GStar : Subgroup (PushoutI φ)) (p : PushoutI φ) (i : ι) (x : GStar) :
    x ∈ conjugateFactorIntersectionSubgroup φ GStar p i ↔
      ((x : GStar) : PushoutI φ) ∈ MulAut.conj p⁻¹ • (PushoutI.of i).range :=
  Iff.rfl

/-- The subgroup `generatedConjugateFactorNormalSubgroup GStar` is exactly the normal closure in
`G*` of the union of the conjugate intersections `p⁻¹ Hᵢ p ∩ G*`. -/
-- Proof sketch: unfold `generatedConjugateFactorNormalSubgroup`; by definition it is the normal
-- closure of the set of elements of `G*` lying in some
-- `conjugateFactorIntersectionSubgroup (φ := φ) GStar p i`.
theorem generatedConjugateFactorNormalSubgroup_eq_normalClosure
    (GStar : Subgroup (PushoutI φ)) :
    generatedConjugateFactorNormalSubgroup φ GStar =
      Subgroup.normalClosure
        {x : GStar | ∃ p : PushoutI φ, ∃ i : ι,
          x ∈ conjugateFactorIntersectionSubgroup φ GStar p i} :=
  rfl

/-- Proposition 1-11-23 (1): if `G = PushoutI φ` is the free product of the factors `Hᵢ` with the
subgroup `A` amalgamated and `G*` is a subgroup of `G`, then the normal subgroup `N` of `G*`
generated by all conjugate intersections `p⁻¹ Hᵢ p ∩ G*` is a tree product of a certain family of
these groups. -/
-- Proof sketch: use the Kurosh subgroup theorem for amalgamated products to construct a tree of
-- groups whose vertex groups are the conjugate intersections appearing in the statement. The
-- induced cocone exhibits `N` as a tree product in the sense of
-- `TreeProductDiagram.IsTreeProductOf`, and each vertex group is one of the conjugate
-- intersections appearing in the statement.
theorem exists_treeProduct_of_generatedConjugateFactorNormalSubgroup
    (hφ : ∀ i, Function.Injective (φ i)) (GStar : Subgroup (PushoutI φ)) :
    ∃ Δ : TreeProductDiagram,
      Δ.IsTreeProductOf (generatedConjugateFactorNormalSubgroup φ GStar) ∧
      (∀ a : Δ.Vertex,
        ∃ p : PushoutI φ, ∃ i : ι,
          Nonempty (Δ.vertexGroup a ≃* conjugateFactorIntersectionSubgroup φ GStar p i)) := sorry

/-- Proposition 1-11-23 (2): in the same amalgamated-product setup, the quotient `G* / N` by the
normal subgroup generated by the conjugate intersections `p⁻¹ Hᵢ p ∩ G*` is a free group. -/
-- Proof sketch: after constructing `N` as the tree product in clause `(1)`, apply the Section 11
-- splitting argument from Proposition `1-11-22` and the free-basis criterion from Corollary
-- `1-11-21` to identify the quotient with the free group carried by the reduced transversal
-- generators.
theorem isFreeGroup_quotient_generatedConjugateFactorNormalSubgroup
    (hφ : ∀ i, Function.Injective (φ i)) (GStar : Subgroup (PushoutI φ)) :
    IsFreeGroup (GStar ⧸ generatedConjugateFactorNormalSubgroup φ GStar) := sorry

end

/-! ### Proposition_1_11_24 (from Items/Chap01) -/
universe u v w x y

open Monoid
open scoped Pointwise

section

variable {G : Type y} [Group G]

/-- The `Option`-indexed family of subgroup factors obtained by adjoining one distinguished free
subgroup `F` to an indexed family `K`. -/
abbrev kuroshFactors {κ : Type x} (F : Subgroup G) (K : κ → Subgroup G) :
    Option κ → Subgroup G :=
  fun
    | none => F
    | some j => K j

/-- The carrier family underlying `kuroshFactors F K`, used as the summand family for the indexed
free product `CoprodI`. -/
abbrev kuroshFactorFamily {κ : Type x} (F : Subgroup G) (K : κ → Subgroup G) :
    Option κ → Type _ :=
  fun i ↦ (kuroshFactors F K i : Type _)

/-- Each summand in `kuroshFactorFamily F K` inherits its canonical group structure from the
corresponding subgroup. -/
instance instGroupKuroshFactorFamily {κ : Type x} (F : Subgroup G) (K : κ → Subgroup G)
    (i : Option κ) : Group (kuroshFactorFamily F K i) := by
  simpa [kuroshFactorFamily] using
    (inferInstance : Group ((kuroshFactors F K i : Subgroup G) : Type _))

end

section

variable {G : Type y} [Group G]

/-- A witness that `H` is the free product of the subgroup family `K` together with the free
factor `F`. -/
structure IsKuroshFactorDecomposition {κ : Type x}
    (H : Subgroup G) (K : κ → Subgroup H) (F : Subgroup H)
    (e : CoprodI (kuroshFactorFamily F K) ≃* H) : Prop where
  /-- The distinguished factor `F` is free. -/
  freeFactor_isFree : IsFreeGroup F
  /-- The free-product inclusion of each `Option`-indexed factor identifies with the corresponding
  subgroup inclusion into `H`. -/
  comp_of (i : Option κ) :
      e.toMonoidHom.comp
        (CoprodI.of : kuroshFactorFamily F K i →* CoprodI (kuroshFactorFamily F K)) =
      (kuroshFactors F K i).subtype

namespace IsKuroshFactorDecomposition

variable {κ : Type x} {H : Subgroup G} {K : κ → Subgroup H} {F : Subgroup H}
variable {e : CoprodI (kuroshFactorFamily F K) ≃* H}

/-- The distinguished factor inclusion in a Kurosh decomposition is the subgroup inclusion
`F ↪ H`. -/
theorem freeFactor_comp_of (h : IsKuroshFactorDecomposition H K F e) :
    e.toMonoidHom.comp
        (CoprodI.of : kuroshFactorFamily F K none →* CoprodI (kuroshFactorFamily F K)) =
      F.subtype :=
  by simpa [kuroshFactorFamily, kuroshFactors] using h.comp_of none

/-- Each indexed subgroup factor inclusion in a Kurosh decomposition is the subgroup inclusion
`K j ↪ H`. -/
theorem factor_comp_of (h : IsKuroshFactorDecomposition H K F e) (j : κ) :
    e.toMonoidHom.comp
        (CoprodI.of : kuroshFactorFamily F K (some j) →* CoprodI (kuroshFactorFamily F K)) =
      (K j).subtype :=
  by simpa [kuroshFactorFamily, kuroshFactors] using h.comp_of (some j)

end IsKuroshFactorDecomposition

end

section

variable {ι : Type u} {A : Type v} {H : ι → Type w}
variable [Group A] [∀ i, Group (H i)]
variable (φ : ∀ i, A →* H i)

/- Proposition 1-11-24 lies in Section 11 on subgroups of an amalgamated free product.

Layer triage:
- `source-facing`: the amalgamated product `PushoutI φ`, the subgroup `G*`, the conjugate
  intersections `Hᵢᵖ ∩ G*`, the conjugates of the amalgamated subgroup `A`, and the conclusion that
  `G*` is the free product of certain such intersections together with a free group.
- `core/canonical`: `Monoid.PushoutI` for the ambient amalgamated product,
  `conjugateFactorIntersectionSubgroup` from Proposition `1-11-23` for the subgroup factors,
  `Monoid.CoprodI` for the free product decomposition, and `IsFreeGroup` for the extra free factor.
- `bridge/view`: `kuroshFactorFamily` packages the family of conjugate-intersection factors together
  with one distinguished free subgroup, and `IsKuroshFactorDecomposition` is the resulting
  reusable owner for the free-product decomposition data.

Domain sampling:
1. `Monoid.PushoutI φ` is mathlib's owner abstraction for a free product with the subgroup `A`
   amalgamated across the factors.
2. `conjugateFactorIntersectionSubgroup φ GStar p i` is the canonical subgroup
   `p⁻¹ Hᵢ p ∩ G*` inside `G*`.
3. `Monoid.CoprodI` is mathlib's owner abstraction for free products of an indexed family of
   groups, with canonical inclusions `Monoid.CoprodI.of`.
4. `IsFreeGroup` is mathlib's owner abstraction for the statement that the residual factor is a
   free group.

Primitive vs. derived:
the primitive data are the amalgamating diagram `φ`, the subgroup `G*`, and the hypothesis that
`G*` meets every conjugate of the base subgroup trivially. The asserted Kurosh decomposition uses
the Chapter 1 owner `IsKuroshFactorDecomposition`; the additional source-facing content here is
that each factor `K j` is realized by a conjugate intersection `p⁻¹ Hᵢ p ∩ G*`. -/

/-- Proposition 1-11-24: if `G = PushoutI φ` is the free product of the factors `Hᵢ` with the
subgroup `A` amalgamated and `G*` intersects every conjugate of `A` trivially, then `G*` is the
free product of certain actual conjugate-intersection subgroups `p⁻¹ Hᵢ p ∩ G*` together with one
free subgroup factor. -/
-- Proof sketch: apply Proposition `1-11-23` to the normal subgroup generated by the conjugate
-- intersections. Under the extra hypothesis, the edge groups in the resulting tree-product
-- description are trivial because they lie in conjugates of the amalgamated subgroup. Hence that
-- normal subgroup is an honest free product of the conjugate-intersection factors. Proposition
-- `1-11-22` then splits `G*` over the free quotient, producing a free subgroup factor and the
-- required free-product decomposition of `G*`.
theorem exists_freeProduct_decomposition_of_disjoint_base_conjugates
    (hφ : ∀ i, Function.Injective (φ i))
    (GStar : Subgroup (PushoutI φ))
    (htriv :
      ∀ p : PushoutI φ, Disjoint GStar (MulAut.conj p⁻¹ • (PushoutI.base φ).range)) :
    ∃ (κ : Type x) (K : κ → Subgroup GStar) (F : Subgroup GStar)
      (e : CoprodI (kuroshFactorFamily F K) ≃* GStar),
      IsKuroshFactorDecomposition GStar K F e ∧
        ∀ j, ∃ p : PushoutI φ, ∃ i : ι,
          K j = conjugateFactorIntersectionSubgroup φ GStar p i := sorry

end

/-! ### Proposition_1_11_25 (from Items/Chap01) -/
universe u v

noncomputable section

open Monoid
open Monoid.CoprodI
open scoped Symmetrization

namespace Monoid.CoprodI

section

variable {ι : Type u} {factors : ι → Type v} [∀ i, Group (factors i)]

/-- An element of a free product is conjugate into a free factor if it is conjugate to some image
`of x` of one of the factors. -/
def IsConjugateIntoFactor (g : CoprodI factors) : Prop :=
  ∃ i, ∃ x : factors i, IsConj g (of x)

/-- Internal product of the contiguous block of entries of `w` from position `h` through position
`k`. The public API only uses it under the accompanying in-range hypotheses. -/
private def contiguousSubproduct {G : Type*} [Monoid G] (w : List G) (h k : ℕ) : G :=
  ((w.drop h).take (k + 1 - h)).prod

/-- Two finite subsets of a free product are related by a Nielsen transformation if some genuine
finite enumerations of them are related by the Chapter I owner relation `nielsen_transforms_to`.
The list/finite-set bridge is internal: the primitive public data are the finite subsets
themselves, not nodup witness lists. -/
def NielsenTransformsTo (X Y : Finset (CoprodI factors)) : Prop :=
  letI : DecidableEq (CoprodI factors) := Classical.decEq _
  ∃ U V : List (CoprodI factors),
    U.Nodup ∧
      V.Nodup ∧
      U.toFinset = X ∧
      V.toFinset = Y ∧
      nielsen_transforms_to U V

/-- A subset of a free product satisfies the length dichotomy of Proposition `1-11-25` if every
noncancelling product of letters from `Y^{±1}` either has total syllable length dominating each
factor, or contains a contiguous block of letters conjugate into the free factors whose product is
shorter than one of its letters. For `w = []`, the first alternative is vacuous. -/
class HasNielsenLengthDichotomy (Y : Set (CoprodI factors)) : Prop where
  dichotomy :
    ∀ (w : List (CoprodI factors)) (_ : ∀ g ∈ w, g ∈ Y^{±1})
      (_ : w.IsChain (fun a b ↦ a * b ≠ 1)),
      (∀ i : Fin w.length, syllableLength (w.get i) ≤ syllableLength w.prod) ∨
        ∃ h k : ℕ,
          h ≤ k ∧
            k < w.length ∧
            (∀ j : Fin w.length,
              h ≤ j.1 → j.1 ≤ k → IsConjugateIntoFactor (w.get j)) ∧
            ∃ i : Fin w.length,
              h ≤ i.1 ∧
                i.1 ≤ k ∧
                syllableLength (contiguousSubproduct w h k) < syllableLength (w.get i)

/-- Proposition 1-11-25: every finite subset of the indexed free product can be carried by a
Nielsen transformation to a finite subset satisfying the free-product length dichotomy from the
text. -/
-- Layer triage:
-- `source-facing`: a finite subset `X` of the free product and a Nielsen-equivalent finite subset
-- `Y` whose underlying subset satisfies the stated length alternative for noncancelling words in
-- `Y^{±1}`.
-- `core/canonical`: `Monoid.CoprodI` for the ambient free product, `Word.equiv`
-- for canonical reduced words, and `IsConj` for conjugacy.
-- `bridge/view`: `syllableLength`, `IsConjugateIntoFactor`, and the finite-set Nielsen relation
-- `NielsenTransformsTo`, which bridges the finite source data to the owner predicate
-- `HasNielsenLengthDichotomy` on subsets.
-- Domain sampling:
-- 1. `Monoid.CoprodI` is mathlib's owner abstraction for indexed free products.
-- 2. `Monoid.CoprodI.syllableLength` is the chapter owner for the canonical syllable length,
--    derived from the unique reduced-word normal form `Word.equiv`.
-- 3. `nielsen_transforms_to` from Definition `1-2-1` is the chapter owner abstraction for finite
--    Nielsen transformations on lists, while Proposition `1-2-23` and Definition `1-2-3` show
--    the chapter owner pattern: a reusable Nielsen property lives on `Set`, and finite lists or
--    finite sets only provide bridge data to that owner.
-- 4. `IsConj` is the canonical conjugacy relation, so conjugacy into a factor is stated directly
--    without adding a surrogate wrapper structure.
-- Primitive vs. derived:
-- the primitive owner data are only the subset `Y` and the dichotomy property on words in
-- `Y^{±1}`. The finite Nielsen relation on `X` and `Y` is the source-facing bridge witnessing
-- that the finite input can be carried to such a subset, and the contiguous-block product is only
-- a private implementation helper for the displayed in-range conclusion.
-- Proof sketch: choose a finite enumeration of `X`, run the Nielsen-reduction process for free
-- products from the textbook until all forbidden counterexamples to the displayed alternative have
-- been removed, and let `Y` be the resulting finite subset.
theorem exists_nielsen_image_with_length_dichotomy
    (X : Finset (CoprodI factors)) :
    ∃ Y : Finset (CoprodI factors),
      NielsenTransformsTo X Y ∧
        HasNielsenLengthDichotomy (Y : Set (CoprodI factors)) := sorry

end

end Monoid.CoprodI
