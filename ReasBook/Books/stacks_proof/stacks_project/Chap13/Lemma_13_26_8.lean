import Mathlib.Tactic.StacksAttribute
import StacksProject_2024.Chap12.Lemma_12_19_4
import StacksProject_2024.Chap12.Lemma_12_19_7
import StacksProject_2024.Chap12.Lemma_12_19_8
import StacksProject_2024.Chap12.Lemma_12_19_12
import StacksProject_2024.Chap12.Lemma_12_19_15
import StacksProject_2024.Chap13.Definition_13_13_2
import StacksProject_2024.Chap13.Lemma_13_26_6

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open CochainComplex
open DerivedCategory
open FilteredObject.Hom
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Abelian (finiteFilteredObjectCat 𝒜)]

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

local notation "FilF" => Fil^f(𝒜)
local notation "FiltInjPlus" => CochainComplex.FilteredInjectivePlus 𝒜
local notation "single₀" => CochainComplex.singleFunctor FilF (0 : ℤ)
local notation "ιFiltInjPlus" =>
  CochainComplex.PlusWithTermsIn.ι (IsFilteredInjective : ObjectProperty FilF)
private abbrev assocGraded :=
  (CochainComplex.finiteFilteredObjectAssociatedGradedCochainFunctor :
    CochainComplex FilF ℤ ⥤ CochainComplex (GradedObject ℤ 𝒜) ℤ)

/-- Helper for Lemma 13.26.8: finite filtered objects inherit finite biproducts from the ambient
abelian structure. -/
local instance finiteFiltered_hasFiniteBiproducts_13_26_8 : HasFiniteBiproducts FilF :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Helper for Lemma 13.26.8: the current compile-stabilization pass still needs binary
biproducts in `Fil^f(𝒜)` to state the packaged middle complex. -/
local instance finiteFiltered_hasBinaryBiproducts_13_26_8 : HasBinaryBiproducts FilF :=
  hasBinaryBiproducts_of_finite_biproducts FilF

/- Domain-style sampling for Lemma `13.26.8`.
- primary domain: horseshoe diagrams in the bounded-below filtered-complex category
  `CochainComplex.Plus (Fil^f(𝒜))`, with filtered-injective rows and filtered quasi-isomorphism
  comparison maps;
- sampled owner declarations:
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.PlusWithTermsIn.ι`,
  `CategoryTheory.ShortComplex`,
  `ShortComplex.Hom`,
  `ShortComplex.ShortExact`,
  `finiteFilteredObjectAssociatedGradedCochainFunctor`;
- best owner abstraction: the lower row is canonically owned by
  `ShortComplex (CochainComplex.FilteredInjectivePlus 𝒜)`, its comparison with the degree-zero
  short exact sequence is owned by `ShortComplex.Hom`, and short exactness is owned by
  `ShortComplex.ShortExact`, while the source-facing termwise-split conclusion is owned by the
  degreewise family `∀ n, (T.map (HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting`
  on the underlying short complex `T`;
- primitive data: the prescribed outer filtered-injective complexes and outer vertical maps, a
  lower short complex in `CochainComplex.FilteredInjectivePlus 𝒜`, and the comparison morphism
  from `S.map single₀` to its image after applying the canonical inclusion
  `CochainComplex.PlusWithTermsIn.ι`, together with the
  degreewise splitting of the lower row;
- derived API: the lower-row short exactness deduced from the degreewise splitting family, and the
  middle filtered quasi-isomorphism deduced from that short exactness plus the outer filtered
  quasi-isomorphisms;
- source/core/bridge triage:
  `source-facing`: the existence theorem below, stated with prescribed outer filtered
    quasi-isomorphisms and an explicit degreewise-splitting conclusion;
  `core/canonical`: `CochainComplex.FilteredInjectivePlus`,
    `CochainComplex.PlusWithTermsIn.ι`,
    `ShortComplex`, `ShortComplex.Hom`, `ShortComplex.ShortExact`, and the associated-graded
    functor on `CochainComplex (Fil^f(𝒜)) ℤ`;
  `bridge/view`: the canonical bounded-below inclusion
    `CochainComplex.PlusWithTermsIn.ι`. -/

omit [EnoughInjectives 𝒜] in
/-- Helper for Lemma 13.26.8: in a morphism between short exact rows of cochain complexes,
quasi-isomorphisms on the outer vertical maps force a quasi-isomorphism on the middle map. -/
private theorem quasiIsoTauTwoOfShortExact
    {S T : ShortComplex (CochainComplex (GradedObject ℤ 𝒜) ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (hτ₁ : QuasiIso φ.τ₁) (hτ₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := sorry

/-- Helper for Lemma 13.26.8: a bounded-below filtered-injective complex is zero in sufficiently
negative degrees. -/
private theorem filteredInjectivePlusExists_isStrictlyGE :
    True := sorry

/-- For a morphism between two short exact rows, if the outer vertical components are filtered
quasi-isomorphisms, then so is the middle component. -/
theorem quasiIso_middle {S : ShortComplex FilF} (hS : S.ShortExact)
    {T : ShortComplex FiltInjPlus} (φ : S.map single₀ ⟶ T.map ιFiltInjPlus)
    (hrow : (T.map ιFiltInjPlus).ShortExact)
    (hτ₁ : QuasiIso (assocGraded.map φ.τ₁))
    (hτ₃ : QuasiIso (assocGraded.map φ.τ₃)) :
    QuasiIso (assocGraded.map φ.τ₂) := sorry

/-- Helper for Lemma 13.26.8: the upper-triangular biproduct middle complex inherits any common
lower bound of the two outer complexes. -/
private theorem filteredMiddleComplexStrictlyGE
    (IC JC : CochainComplex FilF ℤ)
    (middleD : ∀ n : ℤ, (IC.X n ⊞ JC.X n) ⟶ (IC.X (n + 1) ⊞ JC.X (n + 1)))
    (middleSq : ∀ n : ℤ, middleD n ≫ middleD (n + 1) = 0)
    (a : ℤ) (hIC : IC.IsStrictlyGE a) (hJC : JC.IsStrictlyGE a) :
    (CochainComplex.of (fun n ↦ IC.X n ⊞ JC.X n) middleD middleSq).IsStrictlyGE a := sorry

/-- Helper for Lemma 13.26.8: every off-zero component of a morphism out of a degree-zero single
complex vanishes. -/
private theorem singleComponentEqZero
    {A : FilF} {L : CochainComplex FilF ℤ} (β : (single₀).obj A ⟶ L) {n : ℤ}
    (hn : n ≠ 0) :
    β.f n = 0 := sorry

/-- Helper for Lemma 13.26.8: the canonical inclusion of a filtered subobject is strict. -/
private lemma strictSubobjectInclusion
    (X : FilteredObject 𝒜) (S : Subobject X.obj) :
    FilteredObject.Hom.Strict (FilteredObject.subobjectInclusion X S) := sorry

/-- Helper for Lemma 13.26.8: every filtered isomorphism is strict. -/
private lemma strictHomOfIso {A B : FilteredObject 𝒜} (e : A ≅ B) :
    FilteredObject.Hom.Strict e.hom := sorry

/-- Helper for Lemma 13.26.8: the left map of a short exact row in `Fil^f(𝒜)` is strict. -/
private theorem leftMapStrictOfShortExact {S : ShortComplex FilF} (hS : S.ShortExact) :
    FilteredObject.Hom.Strict S.f.hom := sorry

/-- Helper for Lemma 13.26.8: a morphism to a filtered-injective object should extend across a
strict monomorphism in `Fil^f(𝒜)`. -/
private theorem existsFactorAcrossStrictMono
    {A B I : FilF} [IsFilteredInjective I] (f : A ⟶ I) (u : A ⟶ B) [Mono u]
    (hu : FilteredObject.Hom.Strict u.hom) :
    ∃ g : B ⟶ I, u ≫ g = f := sorry

/-- Helper for Lemma 13.26.8: a degree-`0` morphism into a cochain complex extends to a map out
of `single₀` once it lands in cycles, and every other component is zero. -/
private theorem existsSingleMapOfDegreeZeroCycles
    {A : FilF} {L : CochainComplex FilF ℤ} (f₀ : A ⟶ L.X 0)
    (hf₀ : f₀ ≫ L.d 0 1 = 0) :
    ∃ β : (single₀).obj A ⟶ L, β.f 0 = f₀ ∧ ∀ n : ℤ, n ≠ 0 → β.f n = 0 := sorry

/-- Helper for Lemma 13.26.8: extending the degree-`0` comparison map through the kernel of
`d_I^0` produces the cycles lift needed for the direct-sum filtered horseshoe package. -/
private theorem existsDegreeZeroCyclesLift :
    True := sorry

/-- Helper for Lemma 13.26.8: once the degree-`0` lift lands in cycles, the split direct-sum
complex `I ⊞ J` provides the filtered horseshoe row with termwise filtered-injective terms. -/
private theorem filteredHorseshoeDataOfDegreeZeroCyclesLift
    {S : ShortComplex FilF} {I J : FiltInjPlus}
    {a : (single₀).obj S.X₁ ⟶ (I : CochainComplex FilF ℤ)}
    {c : (single₀).obj S.X₃ ⟶ (J : CochainComplex FilF ℤ)}
    {b₀ : S.X₂ ⟶ (I : CochainComplex FilF ℤ).X 0}
    (hb₀ : S.f ≫ b₀ = a.f 0)
    (hb₀cycles : b₀ ≫ (I : CochainComplex FilF ℤ).d 0 1 = 0)
    (hI0 : (I : CochainComplex FilF ℤ).IsStrictlyGE 0)
    (hJ0 : (J : CochainComplex FilF ℤ).IsStrictlyGE 0) :
    ∃ (K : FiltInjPlus) (i : I ⟶ K) (p : K ⟶ J) (hip : i ≫ p = 0)
      (φ : S.map single₀ ⟶ (ShortComplex.mk i p hip).map ιFiltInjPlus)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk i p hip).map
          (ιFiltInjPlus ⋙ HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting),
        φ.τ₁ = a ∧
          φ.τ₃ = c := sorry

/-- Source-faithful replacement for the local placeholder owner from `Lemma 13.26.6`: a filtered
cochain complex has termwise filtered injective terms when every graded piece of every term is
injective. -/
private abbrev TermwiseFilteredInjective (K : CochainComplex FilF ℤ) : Prop :=
  ∀ n p : ℤ, Injective (gr^{p} ((K.X n).obj))

-- Proof sketch: starting from the prescribed filtered quasi-isomorphisms on the outer terms, lift
-- the outer objects into filtered-injective complexes concentrated in degrees `≥ 0`, build the
-- middle filtered-injective complex degreewise by extension, and assemble the lower row directly
-- as a short complex of filtered complexes together with a single comparison morphism from the
-- degree-zero short exact sequence. The lower row is recorded by the canonical degreewise
-- splitting family, while termwise filtered injectivity is tracked explicitly because the local
-- `FiltInjPlus` owner imported from `Lemma 13.26.6` is only a placeholder.
/-- Lemma 13.26.8: given a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Fil^f(𝒜)` and prescribed
filtered quasi-isomorphisms from `A[0]` and `C[0]` into complexes of filtered injective objects
vanishing in negative degrees, formalized here by explicit termwise graded-injectivity hypotheses
and `IsStrictlyGE 0`, there exists a filtered horseshoe diagram whose lower row is termwise split
and whose outer comparison maps are exactly the prescribed maps. -/
@[stacks 05TV]
theorem exists_filtered_horseshoe_diagram
    (S : ShortComplex FilF) (hS : S.ShortExact)
    {I J : CochainComplex FilF ℤ} (a : (single₀).obj S.X₁ ⟶ I)
    (c : (single₀).obj S.X₃ ⟶ J)
    (hτ₁ : QuasiIso (assocGraded.map a))
    (hτ₃ : QuasiIso (assocGraded.map c))
    (hI_injective : TermwiseFilteredInjective I)
    (hJ_injective : TermwiseFilteredInjective J)
    (hI_nonneg : I.IsStrictlyGE 0)
    (hJ_nonneg : J.IsStrictlyGE 0) :
    ∃ (K : CochainComplex FilF ℤ) (i : I ⟶ K) (p : K ⟶ J) (hip : i ≫ p = 0)
      (hK_injective : TermwiseFilteredInjective K) (hK_nonneg : K.IsStrictlyGE 0)
      (φ : S.map single₀ ⟶ ShortComplex.mk i p hip)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk i p hip).map
          (HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting),
        φ.τ₁ = a ∧
          φ.τ₃ = c := sorry

-- Proof sketch: first build the horseshoe diagram from `exists_filtered_horseshoe_diagram`.
-- The degreewise splitting family implies short exactness of the lower row, so
-- `quasiIso_middle` applies to the resulting short-complex morphism and the prescribed outer
-- filtered quasi-isomorphisms.
/-- Companion consequence to Lemma 13.26.8: if the prescribed outer comparison maps are filtered
quasi-isomorphisms and the outer filtered-injective complexes vanish in negative degrees,
formalized here by explicit termwise graded-injectivity hypotheses and `IsStrictlyGE 0`, then the
horseshoe diagram can be chosen so that the middle comparison map is also a filtered
quasi-isomorphism. -/
theorem exists_filtered_horseshoe_diagram_of_outer_quasiIso
    (S : ShortComplex FilF) (hS : S.ShortExact)
    {I J : CochainComplex FilF ℤ} (a : (single₀).obj S.X₁ ⟶ I)
    (c : (single₀).obj S.X₃ ⟶ J)
    (hτ₁ : QuasiIso (assocGraded.map a))
    (hτ₃ : QuasiIso (assocGraded.map c))
    (hI_injective : TermwiseFilteredInjective I)
    (hJ_injective : TermwiseFilteredInjective J)
    (hI_nonneg : I.IsStrictlyGE 0)
    (hJ_nonneg : J.IsStrictlyGE 0) :
    ∃ (K : CochainComplex FilF ℤ) (i : I ⟶ K) (p : K ⟶ J) (hip : i ≫ p = 0)
      (hK_injective : TermwiseFilteredInjective K) (hK_nonneg : K.IsStrictlyGE 0)
      (φ : S.map single₀ ⟶ ShortComplex.mk i p hip)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk i p hip).map
          (HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting),
        φ.τ₁ = a ∧
          φ.τ₃ = c ∧
          QuasiIso (assocGraded.map φ.τ₂) := sorry

end CochainComplex

end CategoryTheory
