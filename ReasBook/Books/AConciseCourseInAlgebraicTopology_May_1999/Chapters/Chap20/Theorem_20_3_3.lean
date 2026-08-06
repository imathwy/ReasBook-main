import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Theorem_20_3_2

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open scoped Manifold Topology

noncomputable section

universe u

-- Semantic recall: `Theorem_20_1_2` already provides the canonical absolute local-coefficient
-- owner `ChosenUniversalCoverChainModel`. For the pair `(M, M \ K)`, this file keeps the
-- source-facing relative notion by choosing a universal-cover model of `M`, a lifted chain model
-- of the complement preimage `coverMap ⁻¹'(M \ K)`, and a chain map whose underlying map agrees
-- with the actual complement inclusion on singular chains.

/-- The complement of `K` inside the chosen universal cover `C.cover`, viewed as the lifted
subspace lying over `M \ K`. -/
abbrev universalCoverComplement
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (K : Set M) :=
  { y : C.cover // C.coverMap y ∉ K }

/-- The inclusion of the lifted complement of `K` into the chosen universal cover `C.cover`. -/
abbrev universalCoverComplementInclusion
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (K : Set M) :
    TopCat.of (universalCoverComplement C K) ⟶ TopCat.of C.cover :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The singular chain complex of the lifted complement `coverMap ⁻¹'(M \ K)` in the chosen
universal cover `C.cover`. -/
abbrev universalCoverComplementSingularChains
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (K : Set M) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of (universalCoverComplement C K))

/-- The singular-chain map induced by the inclusion of the lifted complement into the chosen
universal cover. -/
abbrev universalCoverComplementInclusionChainMap
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (K : Set M) :
    universalCoverComplementSingularChains C K ⟶ universalCoverSingularChains ℤ C.cover :=
  ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
    (universalCoverComplementInclusion C K)

/-- Forgetting equivariance sends a morphism of `π₁(M, x)`-equivariant chain complexes to its
underlying chain map of `ℤ`-module-valued complexes. -/
def forgottenEquivariantChainMap
    {M : Type} [TopologicalSpace M] {x : M}
    {C D : ChainComplex (Rep ℤ (FundamentalGroup M x)) ℕ} (f : C ⟶ D) :
    forgottenEquivariantCoverChains x C ⟶ forgottenEquivariantCoverChains x D where
  f i := (f.f i).toModuleCatHom
  comm' i j _ := by
    change ((f.f i ≫ D.d i j).toModuleCatHom = (C.d i j ≫ f.f j).toModuleCatHom)
    exact congrArg (fun g ↦ g.toModuleCatHom) (f.comm i j)

/-- A chosen based `π₁(M, x)`-equivariant chain model of the pair `(M, M \ K)`. The complement
chain complex is tied to the actual lifted complement in the chosen universal cover of `M`, and
the recorded chain map models the complement inclusion after forgetting equivariance. -/
structure ChosenRelativeUniversalCoverPairChainModel
    {M : Type} [TopologicalSpace M] (π : FundamentalGroupoid M ⥤ ModuleCat ℤ)
    (x : M) (K : Set M) where
  ambientModel : ChosenUniversalCoverChainModel π x
  complementChains : ChainComplex (Rep ℤ (FundamentalGroup M x)) ℕ
  complementChainsIsoToSingularChains :
    forgottenEquivariantCoverChains x complementChains ≅
      universalCoverComplementSingularChains ambientModel K
  complementInclusionChainMap : complementChains ⟶ ambientModel.coverChains
  complementInclusionChainMap_comm :
    forgottenEquivariantChainMap complementInclusionChainMap ≫
        ambientModel.coverChainsIsoToSingularChains_spec.hom =
      complementChainsIsoToSingularChains.hom ≫
        universalCoverComplementInclusionChainMap ambientModel K

namespace ChosenRelativeUniversalCoverPairChainModel

/-- The chosen relative local-coefficient chain complex of `(M, M \ K)` attached to `C`. -/
abbrev chainComplex
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ}
    {x : M} {K : Set M} (C : ChosenRelativeUniversalCoverPairChainModel π x K) :
    ChainComplex (Rep ℤ (FundamentalGroup M x)) ℕ :=
  cokernel C.complementInclusionChainMap

/-- Unfolding `C.chainComplex` recovers the cokernel of the chosen complement-inclusion chain
map. -/
theorem chainComplex_def
    {M : Type} [TopologicalSpace M] (π : FundamentalGroupoid M ⥤ ModuleCat ℤ)
    (x : M) (K : Set M) (C : ChosenRelativeUniversalCoverPairChainModel π x K) :
    C.chainComplex = cokernel C.complementInclusionChainMap :=
  rfl

/-- The degree-`i` local-coefficient homology group of `(M, M \ K)` computed from the chosen
pair model `C`. -/
abbrev homology
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ}
    {x : M} {K : Set M} (C : ChosenRelativeUniversalCoverPairChainModel π x K) (i : ℕ) :
    ModuleCat ℤ :=
  (HomologicalComplex.coinvariantsTensorObj (localSystemFiberRep π x) C.chainComplex).homology i

/-- Unfolding `C.homology i` recovers the homology of the coinvariants complex built from the
chosen relative chain complex `C.chainComplex`. -/
theorem homology_def
    {M : Type} [TopologicalSpace M] (π : FundamentalGroupoid M ⥤ ModuleCat ℤ)
    (x : M) (K : Set M) (C : ChosenRelativeUniversalCoverPairChainModel π x K) (i : ℕ) :
    C.homology i =
      (HomologicalComplex.coinvariantsTensorObj (localSystemFiberRep π x) C.chainComplex).homology
        i :=
  rfl

/-- A chosen pair model `C` computes a degreewise relative local-coefficient homology owner `Hπ`
when each degree is identified by an explicit comparison isomorphism. -/
abbrev ComputesHomology
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ}
    {x : M} {K : Set M} (C : ChosenRelativeUniversalCoverPairChainModel π x K)
    (Hπ : ℕ → ModuleCat ℤ) : Type :=
  ∀ i : ℕ, C.homology i ≅ Hπ i

/-- Unfolding `C.ComputesHomology Hπ` gives the degreewise comparison isomorphisms from the
chosen pair-relative homology owner `C.homology i` to `Hπ i`. -/
theorem computesHomology_def
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ}
    {x : M} {K : Set M} (C : ChosenRelativeUniversalCoverPairChainModel π x K)
    (Hπ : ℕ → ModuleCat ℤ) :
    C.ComputesHomology Hπ = (∀ i : ℕ, C.homology i ≅ Hπ i) :=
  rfl

end ChosenRelativeUniversalCoverPairChainModel

/-- The degree-`i` relative local-coefficient homology group `H_i(M, M \ K; π)` attached to the
chosen pair model `C`. -/
abbrev relativeLocalCoefficientHomologyGroup
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ}
    {x : M} {K : Set M} (C : ChosenRelativeUniversalCoverPairChainModel π x K) (i : ℕ) :
    ModuleCat ℤ :=
  C.homology i

/-- Unfolding `relativeLocalCoefficientHomologyGroup C i` recovers the chosen pair-model homology
owner `C.homology i`. -/
theorem relativeLocalCoefficientHomologyGroup_def
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ}
    {x : M} {K : Set M} (C : ChosenRelativeUniversalCoverPairChainModel π x K) (i : ℕ) :
    relativeLocalCoefficientHomologyGroup C i = C.homology i :=
  rfl

/-- If `C` computes a degreewise owner `Hπ`, then `relativeLocalCoefficientHomologyGroup C i`
identifies with `Hπ i`. -/
abbrev relativeLocalCoefficientHomologyGroupIso
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ}
    {x : M} {K : Set M} (C : ChosenRelativeUniversalCoverPairChainModel π x K)
    (Hπ : ℕ → ModuleCat ℤ) (hHπ : C.ComputesHomology Hπ) (i : ℕ) :
    relativeLocalCoefficientHomologyGroup C i ≅ Hπ i :=
  hHπ i

section

variable {n : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
variable [Fact (Module.finrank ℝ E = n)]

/-- If `C` is a chosen based `π₁(M, x)`-equivariant chain model of the pair `(M, M \ K)`, then
its pair-relative local-coefficient homology owner `C.homology i` vanishes in every degree
`i > n` for compact `K`. -/
theorem isZero_chosenRelativeLocalCoefficientHomology_of_lt
    (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) (K : Set M) (hK : IsCompact K) {x : M}
    (C : ChosenRelativeUniversalCoverPairChainModel π x K)
    {i : ℕ} (hi : n < i) :
    IsZero (C.homology i) := sorry

/-- If the chosen pair model `C` of `(M, M \ K)` computes a degreewise owner `Hπ`, then `Hπ`
vanishes in every degree `i > n` for compact `K`. -/
theorem isZero_computedRelativeLocalCoefficientHomologyGroup_of_lt
    (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) (K : Set M) (hK : IsCompact K) {x : M}
    (C : ChosenRelativeUniversalCoverPairChainModel π x K) (Hπ : ℕ → ModuleCat ℤ)
    (hHπ : C.ComputesHomology Hπ)
    {i : ℕ} (hi : n < i) :
    IsZero (Hπ i) :=
  IsZero.of_iso
    (isZero_chosenRelativeLocalCoefficientHomology_of_lt π K hK C hi)
    (hHπ i).symm

/-- Theorem 20.3.3 (1): for a compact subset `K ⊂ M`, the relative local-coefficient homology
group `H_i(M, M \ K; π)`, represented in this file by
`relativeLocalCoefficientHomologyGroup C i`, vanishes in every degree `i > n`. -/
theorem isZero_relativeLocalCoefficientHomologyGroup_of_lt
    (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) (K : Set M) (hK : IsCompact K)
    {x : M} (C : ChosenRelativeUniversalCoverPairChainModel π x K) {i : ℕ} (hi : n < i) :
    IsZero (relativeLocalCoefficientHomologyGroup C i) :=
  isZero_chosenRelativeLocalCoefficientHomology_of_lt π K hK C hi

end

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [Fact (Module.finrank ℝ E = n)]

/-- An `R`-orientation on `M` yields an `R`-fundamental class at each compact subset `K`. -/
theorem exists_fundamentalClassAtSubspace_of_rOrientedManifold
    (o : ROrientedManifold R I n M) (K : Set M) (hK : IsCompact K) :
    ∃ η : relativeTopHomologyGroup R n M K, isFundamentalClassAtSubspace R n M K η := sorry

end
