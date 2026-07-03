import Mathlib
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_23_1 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open scoped Simplicial

universe v u

namespace AlgebraicTopology.DoldKan

@[inherit_doc]
scoped[DoldKan] notation "s[" X "]" => AlgebraicTopology.AlternatingFaceMapComplex.obj X

end AlgebraicTopology.DoldKan

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteLimits A] [HasFiniteColimits A]

/- Domain-style sampling for Lemma 14.23.1:
- primary domain: exact functors and the alternating face map complex on simplicial objects of a
  preadditive category with finite limits and finite colimits;
- sampled owner declarations:
  `exactFunctor`,
  `exactFunctor_iff`,
  `AlgebraicTopology.alternatingFaceMapComplex`,
  `AlgebraicTopology.map_alternatingFaceMapComplex`;
- best owner abstraction: the canonical exactness predicate
  `exactFunctor (SimplicialObject A) (ChainComplex A ℕ)` applied to the owner functor
  `alternatingFaceMapComplex A`;
- primitive data: the ambient category `A` together with its preadditive structure and finite
  limits and finite colimits;
- derived API: the source-facing exactness theorem used later to deduce exactness of the
  normalized Moore complex.

Source/core/bridge triage:
- `source-facing`: the exactness statement for the specific functor denoted `s` in the Stacks text;
- `core/canonical`: `exactFunctor`, together with the owner functor `alternatingFaceMapComplex A`;
- `bridge/view`: this theorem is the source-facing specialization of the canonical exact-functor
  owner predicate, with no extra wrapper structure. -/

private def alternatingFaceMapComplexCompEvalIso (n : ℕ) :
    alternatingFaceMapComplex A ⋙ HomologicalComplex.eval A (ComplexShape.down ℕ) n ≅
      (evaluation SimplexCategoryᵒᵖ A).obj (Opposite.op ⦋n⦌) :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)
    (fun {X Y} f ↦ by simp [alternatingFaceMapComplex_map_f])

omit [HasFiniteColimits A] in
private theorem alternatingFaceMapComplex_preservesFiniteLimits :
    PreservesFiniteLimits (alternatingFaceMapComplex A) :=
  ⟨fun _ _ _ ↦
    HomologicalComplex.preservesLimitsOfShape_of_eval (alternatingFaceMapComplex A)
      (fun n ↦
        preservesLimitsOfShape_of_natIso (alternatingFaceMapComplexCompEvalIso n).symm)⟩

omit [HasFiniteLimits A] in
private theorem alternatingFaceMapComplex_preservesFiniteColimits :
    PreservesFiniteColimits (alternatingFaceMapComplex A) :=
  ⟨fun _ _ _ ↦
    HomologicalComplex.preservesColimitsOfShape_of_eval (alternatingFaceMapComplex A)
      (fun n ↦
        preservesColimitsOfShape_of_natIso (alternatingFaceMapComplexCompEvalIso n).symm)⟩

-- Proof sketch: by Lemma 14.22.1, exactness in the simplicial-object and chain-complex
-- categories of a preadditive category with finite limits and finite colimits is detected
-- degreewise. The functor
-- `AlgebraicTopology.alternatingFaceMapComplex A` is defined degreewise from evaluation on the
-- simplicial object, so it preserves exact short complexes objectwise and hence is exact.
/-- Lemma 14.23.1: the functor `s`, i.e. the alternating face map complex functor
`AlgebraicTopology.alternatingFaceMapComplex A`, is exact. -/
theorem alternatingFaceMapComplex_exact :
    exactFunctor (SimplicialObject A) (ChainComplex A ℕ) (alternatingFaceMapComplex A) := by
  exact (exactFunctor_iff _).2
    ⟨alternatingFaceMapComplex_preservesFiniteLimits,
      alternatingFaceMapComplex_preservesFiniteColimits⟩

end

end CategoryTheory

/-! ### Lemma_14_23_2 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open ZeroObject
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open Abelian.DoldKan
open HomologicalComplex
open scoped Simplicial DoldKan

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 14.23.2:
- primary domain: chain-complex exactness and Dold-Kan comparison for simplicial objects in an
  abelian category;
- sampled owner declarations:
  `HomologicalComplex.Acyclic`,
  `eilenbergMacLaneExtensionComplex_acyclic`,
  `HomologicalComplex.ExactAt.of_iso`,
  `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`;
- best owner abstraction: the public theorem should stay at the owner predicate
  `HomologicalComplex.Acyclic` on `s[eilenbergMacLaneExtension A k]`;
- primitive data: the upstream owners `eilenbergMacLaneExtensionComplex A k` and
  `eilenbergMacLaneExtension A k`;
- derived API: transfer of the owner-level model acyclicity across the Dold-Kan counit isomorphism
  and then across the normalized-Moore/alternating-face-map homotopy equivalence.

Source/core/bridge triage:
- `source-facing`: the acyclicity statement for the chain complex `s(E)` attached to the extension
  object `E`;
- `core/canonical`: `HomologicalComplex.Acyclic`,
  `eilenbergMacLaneExtensionComplex_acyclic`, and the Dold-Kan homotopy equivalence;
- `bridge/view`: the proof passes through the owner complex
  `eilenbergMacLaneExtensionComplex A k` and the Dold-Kan counit isomorphism, but introduces no
  parallel local model API. -/

private lemma normalizedMooreComplex_eilenbergMacLaneExtension_exactAt
    (A : 𝒜) (k i : ℕ) :
    ((normalizedMooreComplex 𝒜).obj (eilenbergMacLaneExtension A k)).ExactAt i := by
  change
    ((normalizedMooreComplex 𝒜).obj (Γ.obj (eilenbergMacLaneExtensionComplex A k))).ExactAt i
  let η := equivalence.counitIso.app (eilenbergMacLaneExtensionComplex A k)
  exact HomologicalComplex.ExactAt.of_iso
    (eilenbergMacLaneExtensionComplex_acyclic A k i) η.symm

/-- Lemma 14.23.2: if `E` is the simplicial object of Lemma 14.22.4 attached to an object `A` and
an integer `k ≥ 0`, then the associated chain complex `s(E)` is acyclic. -/
theorem alternatingFaceMapComplex_eilenbergMacLaneExtension_acyclic (A : 𝒜) (k : ℕ) :
    s[eilenbergMacLaneExtension A k].Acyclic := by
    intro i
    let e :
        HomotopyEquiv
          ((normalizedMooreComplex 𝒜).obj (eilenbergMacLaneExtension A k))
          s[eilenbergMacLaneExtension A k] :=
      homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    exact (exactAt_iff_of_quasiIsoAt e.hom i).mp
      (normalizedMooreComplex_eilenbergMacLaneExtension_exactAt A k i)

end CategoryTheory

/-! ### Lemma_14_23_3 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open Abelian.DoldKan
open HomologicalComplex
open scoped Simplicial DoldKan

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 14.23.3:
- primary domain: Dold-Kan/Eilenberg-MacLane homology computations in an abelian category.
- sampled owner declarations:
  `HomotopyEquiv.toHomologyIso`,
  `eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle`,
  `HomologicalComplex.singleObjHomologySelfIso`,
  `HomologicalComplex.isZero_single_obj_homology`.
- best owner abstraction: the canonical homology isomorphism from `s[K(A, k)]` to the single
  complex concentrated in degree `k`, obtained by composing the Dold-Kan homotopy-equivalence
  homology isomorphism with the canonical normalized-Moore comparison isomorphism.
- primitive data: the simplicial Eilenberg-MacLane object `K(A, k)` and the chapter bridge
  `eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle`.
- derived API: the degree-`k` homology isomorphism and the off-degree vanishing theorem.

Source/core/bridge triage:
- `source-facing`: the textbook claims `H_k(s(K(A, k))) ≅ A` and `H_i(s(K(A, k))) = 0` for
  `i ≠ k`.
- `core/canonical`: `HomotopyEquiv.toHomologyIso`, `homologyFunctor.mapIso`,
  `HomologicalComplex.singleObjHomologySelfIso`, and
  `HomologicalComplex.isZero_single_obj_homology`.
- `bridge/view`: the chapter comparison from `N(K(A, k))` to the single complex
  concentrated in degree `k`.

The file should therefore expose the canonical homology isomorphism as the main owner and derive
the source-facing vanishing API from it, rather than storing a parallel raw comparison morphism.
-/

/-- Lemma 14.23.3 (1): the canonical isomorphism from `H_k(s(K(A, k)))` to `A`. -/
noncomputable def eilenbergMacLaneObject_homologyIso (A : 𝒜) (k : ℕ) :
    s[K(A, k)].homology k ≅ A :=
  let e :
      HomotopyEquiv ((normalizedMooreComplex 𝒜).obj (K(A, k))) s[K(A, k)] :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  (e.toHomologyIso k).symm ≪≫
    (homologyFunctor 𝒜 (ComplexShape.down ℕ) k).mapIso
      (eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k) ≪≫
    singleObjHomologySelfIso (ComplexShape.down ℕ) k A

-- Proof sketch: pass from the alternating face map complex to the normalized Moore complex via
-- the Dold-Kan homotopy equivalence, identify the normalized Moore complex of `K(A,k)` with the
-- single complex concentrated in degree `k`, and then use
-- `HomologicalComplex.isZero_single_obj_homology` away from degree `k`.
/-- Lemma 14.23.3 (2): for `i ≠ k`, the homology object `H_i(s(K(A, k)))` is zero. -/
theorem eilenbergMacLaneObject_homology_isZero
    (A : 𝒜) (k i : ℕ) (h : i ≠ k) :
    IsZero (s[K(A, k)].homology i) := by
  let e :
      HomotopyEquiv ((normalizedMooreComplex 𝒜).obj (K(A, k))) s[K(A, k)] :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  refine IsZero.of_iso ?_ ((e.toHomologyIso i).symm ≪≫
    (homologyFunctor 𝒜 (ComplexShape.down ℕ) i).mapIso
      (eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k))
  exact isZero_single_obj_homology (ComplexShape.down ℕ) k A i h

end CategoryTheory

/-! ### Lemma_14_23_4 (from Chap14) -/
open AlgebraicTopology

/- Domain-style sampling for Lemma 14.23.4:
- primary domain: simplicial objects in an abelian category and the canonical comparison between
  their normalized Moore and alternating face map complexes;
- sampled same-kind declarations:
  `normalizedMooreComplex`,
  `alternatingFaceMapComplex`,
  `inclusionOfMooreComplexMap`,
  `inclusionOfMooreComplex`;
- best owner abstraction: the objectwise comparison morphism `inclusionOfMooreComplexMap`;
- primitive data: only the simplicial object `U`; the degreewise inclusions are derived from the
  normalized Moore subobjects and do not belong in a separate local wrapper;
- derived API: the natural transformation `inclusionOfMooreComplex`, together with the component
  formula `inclusionOfMooreComplexMap_f`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that the canonical inclusions `N(U)_n ⟶ U_n` assemble to
  a morphism of chain complexes;
- `core/canonical`: `inclusionOfMooreComplexMap`;
- `bridge/view`: the natural transformation `inclusionOfMooreComplex` whose component at `U` is
  that chain map.

This item carries no additional source-defined data beyond that canonical component, so the right
refinement is direct recall of the owner map. -/

/- Lemma 14.23.4: for a simplicial object `U` in an abelian category `A`, the canonical inclusions
`N(U)_n ⟶ U_n` assemble to the canonical morphism of chain complexes
`inclusionOfMooreComplexMap U : N(U) ⟶ s(U)`, where `N(U)` is the normalized
Moore complex and `s(U)` is the alternating face map complex. -/
recall inclusionOfMooreComplexMap

/-! ### Lemma_14_23_5 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Abelian.DoldKan
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 14.23.5:
- primary domain: the Dold-Kan equivalence for simplicial objects in an abelian category and the
  degreewise behavior of the single chain complex;
- sampled same-kind declarations:
  `eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle`,
  `eilenbergMacLaneObjectIsoDoldKanSingle`,
  `Functor.mapIso`,
  `HomologicalComplex.singleObjXSelf`,
  `HomologicalComplex.isZero_single_obj_X`;
- best owner abstraction:
  `source-facing`: the degreewise comparison of the normalized Moore complex of `K(A, k)` with the
    single complex concentrated in degree `k`;
  `core/canonical`: the chapter owner
    `eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k` together with the single-complex
    degree isomorphism;
  `bridge/view`: the degree-`k` objectwise iso and the off-degree vanishing statement below.
- primitive data: only `A` and `k`;
- derived API: the degree-`k` iso and the off-degree zero object result.

This file is therefore a `bridge/view` refinement: it should reuse the canonical normalized-Moore
comparison and single-complex owners directly, rather than duplicating the Dold-Kan comparison
chain locally. -/

-- Proof sketch: the Dold-Kan counit identifies the normalized Moore complex of the simplicial
-- Eilenberg-MacLane object with the chain complex concentrated in degree `k`, and
-- `singleObjXSelf` identifies that degree-`k` term with `A`.
/-- Lemma 14.23.5 (1): the degree-`k` object of the normalized Moore complex of `K(A, k)` is
canonically isomorphic to `A`. -/
noncomputable def eilenbergMacLaneObjectNormalizedMooreComplexXSelfIso
    (A : 𝒜) (k : ℕ) :
    ((normalizedMooreComplex 𝒜).obj (K(A, k))).X k ≅ A :=
  (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) k).mapIso
      (eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k) ≪≫
    singleObjXSelf (ComplexShape.down ℕ) k A

-- Proof sketch: the Dold-Kan counit identifies `N(K(A,k))` with the chain complex concentrated in
-- degree `k`, and `isZero_single_obj_X` shows that every other degree of that
-- single complex is zero.
/-- Lemma 14.23.5 (2): for `i ≠ k`, the degree-`i` object of the normalized Moore complex of
`K(A, k)` is zero. -/
theorem eilenbergMacLaneObjectNormalizedMooreComplexXIsZero
    (A : 𝒜) (k i : ℕ) (h : i ≠ k) :
    IsZero (((normalizedMooreComplex 𝒜).obj (K(A, k))).X i) := by
  let e : ((normalizedMooreComplex 𝒜).obj (K(A, k))).X i ≅
      (((single 𝒜 (ComplexShape.down ℕ) k).obj A).X i) :=
    (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) i).mapIso
        (eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k)
  exact (isZero_single_obj_X (ComplexShape.down ℕ) k A i h).of_iso e

end CategoryTheory

/-! ### Lemma_14_23_6 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Idempotents
open CategoryTheory.Limits
open CategoryTheory.Subobject
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology

namespace DoldKan

/- Domain-style sampling for Lemma 14.23.6:
- primary domain: the Dold-Kan decomposition of the alternating face map complex of a simplicial
  object into the normalized Moore complex and the degenerate subcomplex generated by the
  degeneracy maps;
- sampled owner declarations:
  `imageSubobject`,
  `QInfty`,
  `PInftyToNormalizedMooreComplex`,
  `Karoubi.decomposition`;
- best owner abstraction: the primitive source-facing owner is the degreewise subobject
  `degenerateSubobject U n`, which is only the finite supremum of the image subobjects of the
  degeneracy maps; the chain-complex and Karoubi decomposition data are built on top of that owner;
- primitive data: the degreewise degenerate subobjects `D(U)_n ⊆ U_n`;
- derived API: the degenerate subcomplex `D(U)`, its inclusion `D(U) ⟶ K(U)`, the factorization
  `K(U) ⟶ D(U)` of `Q_\infty`, and the source-facing comparison `K(U) ⟶ N(U) ⊞ D(U)`.

Source/core/bridge triage:
- `source-facing`: the degreewise owner `degenerateSubobject U n`, and the resulting degenerate
  subcomplex `D(U)`;
- `core/canonical`: `N₁.obj U`, its complement `((N₁.obj U).complement)`, and
  `Karoubi.decomposition (N₁.obj U)`;
- `bridge/view`: `D(U)`, `QInftyToDegenerateComplex`, `degenerateComplexι`, and the abelian
  identification of the Karoubi `P_\infty`-summand with `N(U)`.

The review feedback rules out taking a cokernel as the public owner of `D(U)`, so this file keeps
the generated-by-degeneracies subcomplex as the public source-facing object and leaves any quotient
description to future bridge lemmas. -/

section DegenerateSubobject

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasBinaryCoproducts C] [HasImages C]

/-- The degree-`n` degenerate subobject of `U_n`, generated by the images of the degeneracy maps
`σ_i : U_{n-1} ⟶ U_n`. -/
def degenerateSubobject (U : SimplicialObject C) (n : ℕ) : Subobject (U _⦋n⦌) :=
  match n with
  | 0 => ⊥
  | n + 1 => Finset.univ.sup fun i : Fin (n + 1) ↦ imageSubobject (U.σ i)

end DegenerateSubobject

section Degenerate

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryCoproducts C] [HasImages C]

private theorem degenerateSubobject_d_factors (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U n).Factors
      ((degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n) := by
  sorry

private def degenerateComplex_d (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U (n + 1) : C) ⟶ (degenerateSubobject U n : C) :=
  (degenerateSubobject U n).factorThru
    ((degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n)
    (degenerateSubobject_d_factors U n)

private theorem degenerateComplex_d_squared (U : SimplicialObject C) (n : ℕ) :
    degenerateComplex_d U (n + 1) ≫ degenerateComplex_d U n = 0 := by
  sorry

/-- The degenerate subcomplex `D(U)` of the alternating face map complex, generated degreewise by
the images of the degeneracy maps. -/
def degenerateComplex (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of (fun n ↦ (degenerateSubobject U n : C))
    (degenerateComplex_d U) (degenerateComplex_d_squared U)

@[inherit_doc]
scoped[DoldKan] notation "D[" X "]" => AlgebraicTopology.DoldKan.degenerateComplex X

private theorem degenerateComplex_d_arrow (U : SimplicialObject C) (n : ℕ) :
    degenerateComplex_d U n ≫ (degenerateSubobject U n).arrow =
      (degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n := by
  exact factorThru_arrow _ _ (degenerateSubobject_d_factors U n)

/-- The inclusion of the degenerate subcomplex `D(U)` into the alternating face map complex
`K(U)`. -/
def degenerateComplexι (U : SimplicialObject C) : D[U] ⟶ K[U] where
  f n := (degenerateSubobject U n).arrow
  comm' i j hij := by
    have hij' : i = j + 1 := by simpa using hij.symm
    subst hij'
    simpa [degenerateComplex, ChainComplex.of_d] using (degenerateComplex_d_arrow U j).symm

private theorem degenerateSubobject_map_factors
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (degenerateSubobject V n).Factors
      ((degenerateSubobject U n).arrow ≫ f.app (Opposite.op ⦋n⦌)) := by
  sorry

private def degenerateComplexMap_f {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (degenerateSubobject U n : C) ⟶ (degenerateSubobject V n : C) :=
  (degenerateSubobject V n).factorThru
    ((degenerateSubobject U n).arrow ≫ f.app (Opposite.op ⦋n⦌))
    (degenerateSubobject_map_factors f n)

private theorem degenerateComplexMap_f_arrow {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    degenerateComplexMap_f f n ≫ (degenerateSubobject V n).arrow =
      (degenerateSubobject U n).arrow ≫ f.app (Opposite.op ⦋n⦌) := by
  exact factorThru_arrow _ _ (degenerateSubobject_map_factors f n)

/-- The morphism of degenerate complexes induced by a simplicial morphism. -/
def degenerateComplexMap {U V : SimplicialObject C} (f : U ⟶ V) : D[U] ⟶ D[V] where
  f n := degenerateComplexMap_f f n
  comm' i j hij := by
    have hij' : i = j + 1 := by simpa using hij.symm
    subst hij'
    sorry

@[reassoc]
theorem degenerateComplexι_naturality {U V : SimplicialObject C} (f : U ⟶ V) :
    degenerateComplexMap f ≫ degenerateComplexι V =
      degenerateComplexι U ≫ (alternatingFaceMapComplex C).map f := by
  ext n
  simpa [degenerateComplexMap, degenerateComplexι] using degenerateComplexMap_f_arrow f n

private theorem degenerateComplexMap_id (U : SimplicialObject C) :
    degenerateComplexMap (𝟙 U) = 𝟙 D[U] := by
  sorry

private theorem degenerateComplexMap_comp
    {U V W : SimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) :
    degenerateComplexMap (f ≫ g) = degenerateComplexMap f ≫ degenerateComplexMap g := by
  sorry

/-- The degenerate subcomplex construction is functorial in the simplicial object. -/
def degenerateComplexFunctor : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj U := D[U]
  map := fun f ↦ degenerateComplexMap f
  map_id := degenerateComplexMap_id
  map_comp := degenerateComplexMap_comp

/-- The inclusion `D(U) ⟶ K(U)` is natural in `U`. -/
def degenerateComplexιNatTrans : degenerateComplexFunctor (C := C) ⟶ alternatingFaceMapComplex C
    where
  app U := degenerateComplexι U
  naturality _ _ f := degenerateComplexι_naturality f

private theorem degenerateSubobject_factors_QInfty_f (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U n).Factors ((QInfty : K[U] ⟶ K[U]).f n) := by
  sorry

private def QInftyToDegenerateComplex_f (U : SimplicialObject C) (n : ℕ) :
    U _⦋n⦌ ⟶ (degenerateSubobject U n : C) :=
  (degenerateSubobject U n).factorThru ((QInfty : K[U] ⟶ K[U]).f n)
    (degenerateSubobject_factors_QInfty_f U n)

private theorem QInftyToDegenerateComplex_f_arrow (U : SimplicialObject C) (n : ℕ) :
    QInftyToDegenerateComplex_f U n ≫ (degenerateSubobject U n).arrow =
      (QInfty : K[U] ⟶ K[U]).f n := by
  exact factorThru_arrow _ _ (degenerateSubobject_factors_QInfty_f U n)

/-- The canonical factorization of `Q_\infty : K(U) ⟶ K(U)` through the degenerate subcomplex
`D(U)`. -/
def QInftyToDegenerateComplex (U : SimplicialObject C) : K[U] ⟶ D[U] where
  f := QInftyToDegenerateComplex_f U
  comm' i j hij := by
    have hij' : i = j + 1 := by simpa using hij.symm
    subst hij'
    sorry

@[reassoc]
theorem QInftyToDegenerateComplex_naturality
    {U V : SimplicialObject C} (f : U ⟶ V) :
    (alternatingFaceMapComplex C).map f ≫ QInftyToDegenerateComplex V =
      QInftyToDegenerateComplex U ≫ degenerateComplexMap f := by
  sorry

/-- The projection `K(U) ⟶ D(U)` is natural in `U`. -/
def QInftyToDegenerateComplexNatTrans :
    alternatingFaceMapComplex C ⟶ degenerateComplexFunctor (C := C) where
  app U := QInftyToDegenerateComplex U
  naturality _ _ f := QInftyToDegenerateComplex_naturality f

end Degenerate

section AbelianBridge

variable {A : Type u} [Category.{v} A] [Abelian A]

private def complementToDegenerateComplex (U : SimplicialObject A) :
    (N₁.obj U).complement ⟶ (toKaroubi _).obj D[U] where
  f := QInftyToDegenerateComplex U
  comm := by
    sorry

private def degenerateComplexToComplement (U : SimplicialObject A) :
    (toKaroubi _).obj D[U] ⟶ (N₁.obj U).complement where
  f := degenerateComplexι U
  comm := by
    sorry

private def complementIsoDegenerateComplex (U : SimplicialObject A) :
    (N₁.obj U).complement ≅ (toKaroubi _).obj D[U] where
  hom := complementToDegenerateComplex U
  inv := degenerateComplexToComplement U
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

-- Proof sketch: the core owner is the canonical Karoubi decomposition of `N₁.obj U`.
-- The source-facing comparison `K(U) ≅ N(U) ⊞ D(U)` is obtained by identifying the Karoubi
-- complement with `D(U)` via `QInftyToDegenerateComplex`/`degenerateComplexι`; this keeps the
-- public decomposition as a bridge/view statement rather than a second root owner.
/-- Lemma 14.23.6: the alternating face map complex of a simplicial object decomposes as the direct
sum of the normalized Moore complex and the degenerate subcomplex generated by the degeneracies. -/
def decomposition (U : SimplicialObject A) : K[U] ≅ N[U] ⊞ D[U] where
  hom := biprod.lift (PInftyToNormalizedMooreComplex U) (QInftyToDegenerateComplex U)
  inv := biprod.desc (inclusionOfMooreComplexMap U) (degenerateComplexι U)
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

end AbelianBridge

end DoldKan

end AlgebraicTopology

/-! ### Remark_14_23_7 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open scoped Simplicial

noncomputable section

namespace CategoryTheory

/- Domain-style sampling for Remark 14.23.7:
- primary domain: simplicial objects in `AddCommGrpCat`, the Dold-Kan degenerate subobject, and
  the factorization of epimorphisms in `SimplexCategory` through degeneracy maps;
- sampled owner declarations:
  `AlgebraicTopology.DoldKan.degenerateSubobject`,
  `CategoryTheory.SimplicialObject.σ`,
  `SimplexCategory.epi_iff_surjective`,
  `SimplexCategory.eq_σ_comp_of_not_injective`;
- best owner abstraction: the chapter-level owner
  `AlgebraicTopology.DoldKan.degenerateSubobject U (n + 1)`;
- primitive data: the degeneracy maps `U.σ j`;
- derived API: the equivalent source-facing descriptions via surjective simplex morphisms and via
  the subgroup generated by degeneracy images.

Source/core/bridge triage:
- `source-facing`: the subgroup of `U_{n+1}` generated by images of surjective maps
  `[n + 1] → [m]` with `m < n + 1`;
- `core/canonical`: `AlgebraicTopology.DoldKan.degenerateSubobject U (n + 1)`;
- `bridge/view`: the identification of that canonical owner with the source-facing generated
  subgroup, equivalently with the subgroup generated by the degeneracy images. -/

private instance subgroupSubtype_mono {A : AddCommGrpCat} (S : AddSubgroup A) :
    Mono (AddCommGrpCat.ofHom S.subtype) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- In degree `n + 1`, the canonical Dold-Kan degenerate subobject is the subgroup generated by the
images of the degeneracy maps `σ_j : U_n ⟶ U_{n+1}`. -/
theorem degeneracyImageSubgroup_eq_degenerateSubobject
    (U : SimplicialObject AddCommGrpCat) (n : ℕ) :
    Subobject.mk
      (AddCommGrpCat.ofHom
        (AddSubgroup.closure (⋃ j : Fin (n + 1), Set.range (U.σ j))).subtype) =
      degenerateSubobject U (n + 1) := by
  let S : AddSubgroup (U _⦋n + 1⦌) :=
    AddSubgroup.closure (⋃ j : Fin (n + 1), Set.range (U.σ j))
  let D : Subobject (U _⦋n + 1⦌) := degenerateSubobject U (n + 1)
  let DArrow : (D : AddCommGrpCat) ⟶ U _⦋n + 1⦌ := D.arrow
  let DRange : AddSubgroup (U _⦋n + 1⦌) := DArrow.hom.range
  have hS_to_D_range :
      S ≤ DRange := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x (hx : x ∈ ⋃ j : Fin (n + 1), Set.range (U.σ j))
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨j, y, rfl⟩ := hx
    have hle : imageSubobject (U.σ j) ≤ D := by
      let T : Fin (n + 1) → Subobject (U _⦋n + 1⦌) := fun i ↦ imageSubobject (U.σ i)
      change T j ≤ Finset.univ.sup T
      exact Finset.le_sup (by simp : j ∈ Finset.univ)
    have himage : (imageSubobject (U.σ j)).Factors (U.σ j) := by
      simpa using imageSubobject_factors_comp_self (U.σ j) (𝟙 (U _⦋n⦌))
    have hfactor : D.Factors (U.σ j) :=
      Subobject.factors_of_le (U.σ j) hle himage
    change (U.σ j) y ∈ Set.range DArrow.hom
    exact ⟨D.factorThru (U.σ j) hfactor y, by
      change (D.factorThru (U.σ j) hfactor ≫ DArrow) y = (U.σ j) y
      exact ConcreteCategory.congr_hom (Subobject.factorThru_arrow D (U.σ j) hfactor) y⟩
  have himageSubobject : imageSubobject DArrow = D := by
    simpa [D, DArrow, Subobject.mk_arrow] using (imageSubobject_mono DArrow)
  let SToDRange :
      AddCommGrpCat.of ↥S ⟶ AddCommGrpCat.of ↥DRange :=
    AddCommGrpCat.ofHom
      { toFun := fun x ↦ ⟨x.1, hS_to_D_range x.2⟩
        map_zero' := rfl
        map_add' _ _ := rfl }
  let DRangeToSubobject :
      AddCommGrpCat.of ↥DRange ⟶ D :=
    (imageSubobjectIso DArrow ≪≫ AddCommGrpCat.imageIsoRange DArrow).symm.hom ≫
      Subobject.ofLE _ _ himageSubobject.le
  have hDArrowRange :
      (AddCommGrpCat.imageIsoRange DArrow).inv ≫ Limits.image.ι DArrow =
        AddCommGrpCat.ofHom DRange.subtype := by
    simpa [AddCommGrpCat.imageIsoRange, DRange] using
      AddCommGrpCat.image.lift_fac (Image.monoFactorisation DArrow)
  have hDRangeToSubobject :
      DRangeToSubobject ≫ DArrow = AddCommGrpCat.ofHom DRange.subtype := by
    dsimp [DRangeToSubobject]
    rw [Category.assoc, Subobject.ofLE_arrow]
    simp [hDArrowRange]
  have hSToDRange :
      SToDRange ≫ AddCommGrpCat.ofHom DRange.subtype =
        AddCommGrpCat.ofHom S.subtype := by
    ext x
    rfl
  apply le_antisymm
  · simpa [D, DArrow, Subobject.mk_arrow] using
      (Subobject.mk_le_mk_of_comm (SToDRange ≫ DRangeToSubobject) (by
        rw [Category.assoc, hDRangeToSubobject, hSToDRange]) :
        Subobject.mk (AddCommGrpCat.ofHom S.subtype) ≤ Subobject.mk DArrow)
  · change D ≤
      Subobject.mk
        (AddCommGrpCat.ofHom
          (AddSubgroup.closure (⋃ j : Fin (n + 1), Set.range (U.σ j))).subtype)
    change Finset.univ.sup (fun i : Fin (n + 1) ↦ imageSubobject (U.σ i)) ≤ _
    refine Finset.sup_le fun j _ ↦ ?_
    let σj := U.σ j
    let σjRange : AddSubgroup (U _⦋n + 1⦌) := σj.hom.range
    let rangeToS :
        AddCommGrpCat.of ↥σjRange ⟶ AddCommGrpCat.of ↥S :=
      AddCommGrpCat.ofHom
        { toFun := fun x ↦ ⟨x.1, AddSubgroup.subset_closure (Set.mem_iUnion.2 ⟨j, x.2⟩)⟩
          map_zero' := rfl
          map_add' _ _ := rfl }
    let imageToS :
        (imageSubobject σj : AddCommGrpCat) ⟶ AddCommGrpCat.of ↥S :=
      (imageSubobjectIso σj).hom ≫ (AddCommGrpCat.imageIsoRange σj).hom ≫ rangeToS
    have hσjRange :
        (AddCommGrpCat.imageIsoRange σj).hom ≫ AddCommGrpCat.ofHom σjRange.subtype =
          Limits.image.ι σj := by
      change (AddCommGrpCat.imageIsoRange σj).hom ≫ AddCommGrpCat.ofHom σj.hom.range.subtype =
        Limits.image.ι σj
      exact IsImage.isoExt_hom_m (Image.isImage σj) (AddCommGrpCat.isImage σj)
    have hrangeToS :
        rangeToS ≫ AddCommGrpCat.ofHom S.subtype =
          AddCommGrpCat.ofHom σjRange.subtype := by
      ext x
      rfl
    simpa [σj, Subobject.mk_arrow] using
      (Subobject.mk_le_mk_of_comm imageToS (by
        dsimp [imageToS]
        rw [Category.assoc, Category.assoc, hrangeToS, hσjRange]
        exact imageSubobject_arrow σj) :
        Subobject.mk (imageSubobject σj).arrow ≤
          Subobject.mk (AddCommGrpCat.ofHom S.subtype))

-- Proof sketch: a surjective map `φ : [n + 1] ⟶ [m]` with `m < n + 1` cannot be injective, so the
-- canonical simplex-category factorization theorem writes `φ = σ_j ≫ θ`. Hence every source-facing
-- generator already lies in the image of some `σ_j`. Conversely, each `σ_j` is itself surjective.
/-- The degree-`n + 1` simplices obtained from surjective simplex maps `[n + 1] ⟶ [m]` with
`m < n + 1` are exactly the simplices in the union of the degeneracy images `Set.range (U.σ j)`. -/
theorem surjectiveSimplexImageSet_succ_eq_iUnion_range_σ
    (U : SimplicialObject AddCommGrpCat) (n : ℕ) :
    {x | ∃ (m : ℕ) (_hm : m < n + 1) (φ : ⦋n + 1⦌ ⟶ ⦋m⦌),
        Function.Surjective φ.toOrderHom ∧ ∃ y : U _⦋m⦌, U.map φ.op y = x} =
      ⋃ j : Fin (n + 1), Set.range (U.σ j) := by
  ext x
  constructor
  · rintro ⟨m, hm, φ, hφ, y, rfl⟩
    have hnotinj : ¬ Function.Injective φ.toOrderHom := by
      intro hmono
      have hmono' : Mono φ := (SimplexCategory.mono_iff_injective).2 hmono
      have : n + 1 ≤ m := SimplexCategory.le_of_mono φ
      omega
    obtain ⟨j, θ, hφ'⟩ := SimplexCategory.eq_σ_comp_of_not_injective φ hnotinj
    refine Set.mem_iUnion.2 ⟨j, Set.mem_range.2 ⟨U.map θ.op y, ?_⟩⟩
    rw [hφ', op_comp, Functor.map_comp]
    rfl
  · simp only [Set.mem_iUnion, Set.mem_range]
    rintro ⟨j, y, rfl⟩
    refine ⟨n, Nat.lt_succ_self n, SimplexCategory.σ j, ?_, y, rfl⟩
    simpa [SimplexCategory.epi_iff_surjective] using
      (show Epi (SimplexCategory.σ j) from inferInstance)

-- Proof sketch: first identify the subgroup generated by the degeneracies with the concrete
-- subobject underlying `degenerateSubobject U (n + 1)`, then rewrite the source-facing subgroup of
-- surjective simplex images using the companion equality above.
/-- Remark 14.23.7: in degree `n + 1`, the canonical Dold-Kan owner
`AlgebraicTopology.DoldKan.degenerateSubobject U (n + 1)` is exactly the source-facing subgroup of
`U_{n+1}` generated by all surjective simplex morphisms `[n + 1] → [m]` with `m < n + 1`. -/
theorem surjectiveSimplexImageSubgroup_succ_eq_degenerateSubobject
    (U : SimplicialObject AddCommGrpCat) (n : ℕ) :
    Subobject.mk
      (AddCommGrpCat.ofHom
        (AddSubgroup.closure
          {x | ∃ (m : ℕ) (_hm : m < n + 1)
              (φ : ⦋n + 1⦌ ⟶ ⦋m⦌),
              Function.Surjective φ.toOrderHom ∧ ∃ y : U _⦋m⦌, U.map φ.op y = x}).subtype) =
      degenerateSubobject U (n + 1) := by
  rw [surjectiveSimplexImageSet_succ_eq_iUnion_range_σ]
  exact degeneracyImageSubgroup_eq_degenerateSubobject U n

end CategoryTheory

/-! ### Lemma_14_23_8 (from Chap14) -/
open CategoryTheory
open Abelian.DoldKan

universe v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.23.8:
- primary domain: exact functors in the Dold-Kan equivalence between simplicial objects and chain
  complexes of an abelian category;
- sampled owner declarations:
  `exactFunctor`,
  `ExactFunctor.of`,
  `N`,
  `equivalence`;
- best owner abstraction: the canonical bundled exact functor
  `ExactFunctor.of (equivalence.functor : SimplicialObject A ⥤ ChainComplex A ℕ)`;
- primitive data: the ambient abelian category `A`;
- derived API: the source-facing exactness theorem for the normalized Moore complex functor.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the normalized Moore complex functor `N` is exact;
- `core/canonical`: the bundled exact functor `ExactFunctor.of equivalence.functor`;
- `bridge/view`: this theorem takes the property field of that canonical owner and transports it to
  `N` via the definitional equality built into `Abelian.DoldKan.equivalence`, so no parallel local
  exactness wrapper is needed. -/

-- Proof sketch: the Dold-Kan equivalence functor is exact by the canonical owner
-- `ExactFunctor.of equivalence.functor`, since equivalence functors preserve finite limits and
-- finite colimits. The functor `equivalence.functor` is definitionally `N`, so the exactness
-- property transfers by `simpa [equivalence]`.
/-- Lemma 14.23.8: the normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` is exact. -/
theorem doldKan_N_exact :
    exactFunctor (SimplicialObject A) (ChainComplex A ℕ)
      (N : SimplicialObject A ⥤ ChainComplex A ℕ) := by
  simpa [equivalence] using
    (ExactFunctor.of
      (equivalence.functor : SimplicialObject A ⥤ ChainComplex A ℕ)).property

end

end CategoryTheory

/-! ### Lemma_14_23_9 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open HomologicalComplex
open scoped DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.23.9:
- primary domain: the Dold-Kan splitting of the alternating face map complex into the normalized
  Moore complex and the degenerate summand;
- sampled same-kind owner declarations:
  `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`,
  `decomposition`,
  `QInftyToDegenerateComplex`,
  `cokernelBiprodInlIso`;
- best owner abstraction: the canonical owner for the quotient of `K(U)` by `N(U)` is the
  degenerate complex `D[U]`, with the source-facing cokernel identified via the decomposition
  `K(U) ≅ N(U) ⊞ D(U)`;
- primitive data: the Dold-Kan owners `inclusionOfMooreComplexMap U`, `decomposition U`,
  `QInftyToDegenerateComplex U`, and `degenerateComplexι U`;
- derived API: the homotopy-triviality and acyclicity of `D[U]`, and the source-facing acyclicity
  of the cokernel of `N(U) ⟶ K(U)`.

Source/core/bridge triage:
- `source-facing`: the textbook quasi-isomorphism and cokernel-acyclicity statements for
  `inclusionOfMooreComplexMap U`;
- `core/canonical`: the Dold-Kan homotopy equivalence and the source-facing owner `D[U]`;
- `bridge/view`: the decomposition `K(U) ≅ N(U) ⊞ D(U)` together with `cokernelBiprodInlIso`.
-/

private theorem inclusionOfMooreComplexMap_comp_decomposition_hom (V : SimplicialObject A) :
    inclusionOfMooreComplexMap V ≫ (decomposition V).hom = biprod.inl := by
  apply (cancel_mono (decomposition V).inv).1
  have h₁ :
      (inclusionOfMooreComplexMap V ≫ (decomposition V).hom) ≫ (decomposition V).inv =
        inclusionOfMooreComplexMap V := by
    simpa [Category.assoc] using
      show inclusionOfMooreComplexMap V ≫
          ((decomposition V).hom ≫ (decomposition V).inv) =
        inclusionOfMooreComplexMap V ≫ 𝟙 _ from
        congrArg (fun t ↦ inclusionOfMooreComplexMap V ≫ t)
          (decomposition V).hom_inv_id
  have h₂ : biprod.inl ≫ (decomposition V).inv = inclusionOfMooreComplexMap V := by
    simp [decomposition]
  exact h₁.trans h₂.symm

private theorem qInftyToDegenerateComplex_comp_degenerateComplexι
    (V : SimplicialObject A) :
    QInftyToDegenerateComplex V ≫ degenerateComplexι V = QInfty := by
  let K' : ChainComplex A ℕ := (alternatingFaceMapComplex A).obj V
  have hpq :
      ((PInftyToNormalizedMooreComplex V ≫ inclusionOfMooreComplexMap V : K' ⟶ K')) +
        ((QInftyToDegenerateComplex V ≫ degenerateComplexι V : K' ⟶ K')) =
      𝟙 K' := by
    simpa [K', decomposition, Category.assoc, biprod.lift_desc] using
      (decomposition V).hom_inv_id
  change
      ((PInftyToNormalizedMooreComplex V ≫ inclusionOfMooreComplexMap V : K[V] ⟶ K[V]) +
        (QInftyToDegenerateComplex V ≫ degenerateComplexι V : K[V] ⟶ K[V]) =
      𝟙 K[V]) at hpq
  have hcomp :
      PInftyToNormalizedMooreComplex V ≫ inclusionOfMooreComplexMap V =
        (PInfty : K[V] ⟶ K[V]) :=
    PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap V
  have hpq' :
      (PInfty : K[V] ⟶ K[V]) + (QInftyToDegenerateComplex V ≫ degenerateComplexι V) =
      𝟙 K[V] := by
    rw [← hcomp]
    exact hpq
  have hpQ : (PInfty : K[V] ⟶ K[V]) + QInfty = 𝟙 K[V] :=
    PInfty_add_QInfty
  exact add_left_cancel (hpq'.trans hpQ.symm)

private theorem qInfty_eq_qInftyToDegenerateComplex_comp_degenerateComplexι
    (V : SimplicialObject A) :
    (QInfty : K[V] ⟶ K[V]) =
      QInftyToDegenerateComplex V ≫ degenerateComplexι V :=
  (qInftyToDegenerateComplex_comp_degenerateComplexι V).symm

private theorem degenerateComplexι_comp_qInftyToDegenerateComplex (V : SimplicialObject A) :
    degenerateComplexι V ≫ QInftyToDegenerateComplex V = 𝟙 D[V] := by
  simpa [decomposition, Category.assoc] using
    congrArg (fun k ↦ biprod.inr ≫ k ≫ biprod.snd) (Iso.inv_hom_id (decomposition V))

private theorem degenerateComplex_id_homotopic_zero (V : SimplicialObject A) :
    Nonempty (Homotopy (𝟙 D[V]) (0 : D[V] ⟶ D[V])) := by
  let hQ : Homotopy (QInfty : K[V] ⟶ K[V]) 0 :=
    Homotopy.equivSubZero.toFun (homotopyPInftyToId V).symm
  -- Transport the null-homotopy of `Q∞` across the retract data for the degenerate summand.
  refine ⟨?_⟩
  simpa [Category.assoc, qInfty_eq_qInftyToDegenerateComplex_comp_degenerateComplexι,
    degenerateComplexι_comp_qInftyToDegenerateComplex] using
    (hQ.compRight (QInftyToDegenerateComplex V)).compLeft (degenerateComplexι V)

/-- The degenerate summand `D(U)` in the Dold-Kan decomposition is acyclic. -/
theorem degenerateComplex_acyclic (V : SimplicialObject A) :
    D[V].Acyclic := by
  classical
  let h : Homotopy (𝟙 D[V]) (0 : D[V] ⟶ D[V]) :=
    Classical.choice (degenerateComplex_id_homotopic_zero V)
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  -- The identity map vanishes on homology because it is homotopic to zero.
  simpa using h.homologyMap_eq n

end AlgebraicTopology.DoldKan

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

-- Proof sketch: this is the forward map of the canonical Dold-Kan homotopy equivalence between
-- the normalized Moore complex and the alternating face map complex.
/-- Lemma 14.23.9: for a simplicial object `V` in an abelian category, the canonical morphism of
chain complexes `N(V) ⟶ s(V)` given by `inclusionOfMooreComplexMap V` is a quasi-isomorphism. -/
theorem inclusionOfMooreComplexMap_quasiIso (V : SimplicialObject A) :
    QuasiIso (inclusionOfMooreComplexMap V) := by
  let e :
      HomotopyEquiv
        ((normalizedMooreComplex A).obj V)
        ((alternatingFaceMapComplex A).obj V) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  simpa [e] using (show QuasiIso e.hom from inferInstance)

-- Proof sketch: `K(V) ≅ N(V) ⊞ D(V)` identifies `inclusionOfMooreComplexMap V` with
-- `biprod.inl`, so its cokernel is canonically `D(V)`. The degenerate complex is acyclic by the
-- owner theorem `AlgebraicTopology.DoldKan.degenerateComplex_acyclic`.
/-- The cokernel of the canonical inclusion `N(V) ⟶ s(V)` is acyclic. -/
theorem cokernel_inclusionOfMooreComplexMap_acyclic (V : SimplicialObject A) :
    (cokernel (inclusionOfMooreComplexMap V)).Acyclic := by
  let α : N[V] ⟶ K[V] := inclusionOfMooreComplexMap V
  let e₀ : cokernel (inclusionOfMooreComplexMap V) ≅
      cokernel (biprod.inl : N[V] ⟶ N[V] ⊞ D[V]) :=
    cokernel.mapIso α
      (biprod.inl : N[V] ⟶ N[V] ⊞ D[V])
      (Iso.refl _)
      (decomposition V)
      (by simpa [α] using inclusionOfMooreComplexMap_comp_decomposition_hom V)
  let e : cokernel (inclusionOfMooreComplexMap V) ≅ D[V] :=
    e₀ ≪≫ cokernelBiprodInlIso
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_iso
    ((degenerateComplex_acyclic V n).isZero_homology)
    (show (cokernel (inclusionOfMooreComplexMap V)).homology n ≅ D[V].homology n from
      (homologyFunctor A (ComplexShape.down ℕ) n).mapIso e)

end CategoryTheory
