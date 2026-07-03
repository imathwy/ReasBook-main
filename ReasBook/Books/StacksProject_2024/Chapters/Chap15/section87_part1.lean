import Mathlib
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_87_1 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "Ab" => AddCommGrpCat
local notation "AbSeq" => SequentialInverseSystem Ab
local notation "Qish" => HomotopyCategory.quasiIso AbSeq (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived (lim : AbSeq ⥤ Ab)
local notation "RightAcyclic" =>
  IsRightAcyclicForAdditiveFunctor (lim : AbSeq ⥤ Ab)

-- Proof sketch: apply the explicit embedding of an arbitrary inverse system into a
-- Mittag-Leffler inverse system from the Stacks Project argument, and use the preceding
-- Mittag-Leffler acyclicity statement to see that the target of that monomorphism is right
-- acyclic for `lim`.
/-- The Chapter `13` right-acyclicity owner for inverse limit on sequential inverse systems of
abelian groups has monomorphic envelopes. -/
instance abelianGroupLimit_rightAcyclic_hasMonoEmbedding :
    HasMonoEmbedding RightAcyclic where
  exists_mono A := by
    sorry

-- Proof sketch: this is the Stacks Project vanishing statement `R^p lim = 0` for `p > 1`,
-- expressed as vanishing of the positive cohomology of `R lim(A[0])`.
/-- For an inverse system of abelian groups, the cohomology objects `H^p(R lim(A[0]))` vanish in
degrees strictly greater than `1`. -/
theorem abelianGroupInverseLimit_rightDerived_isZero_of_one_lt
    (A : AbSeq) (p : ℕ) (hp : 1 < p) :
    IsZero (R^p lim((DerivedCategory.singleFunctor AbSeq 0).obj A)) :=
  sorry

-- Proof sketch: the Stacks Project identifies the degree-zero object `A[0]` in the derived
-- category with the standard Milnor triangle built from the two products `∏ A_n` and the
-- difference map `(x_n) ↦ (x_n - f_{n+1}(x_{n+1}))`.
/-- Applying `R lim` to an inverse system of abelian groups viewed in degree `0` yields the
standard derived-limit object characterized by the Milnor triangle, equivalently by the two-term
complex `\prod A_n \to \prod A_n` in degrees `0` and `1`. -/
theorem abelianGroupDerivedInverseLimit_isDerivedLimit_of_inverseSystem
    (A : AbSeq) :
    CategoryTheory.IsDerivedLimit
      (A ⋙ DerivedCategory.singleFunctor Ab 0)
      (R lim((DerivedCategory.singleFunctor AbSeq 0).obj A)) :=
  sorry

-- Proof sketch: for a Mittag-Leffler inverse system, the Stacks Project identifies the
-- obstruction group `R^1 lim` with zero; the higher derived functors already vanish above degree
-- `1`, so all positive right-derived functors vanish and the system is right acyclic for `lim`.
/-- A Mittag-Leffler inverse system of abelian groups is right acyclic for inverse limit. -/
theorem abelianGroupLimit_rightAcyclic_of_isMittagLeffler
    (A : AbSeq) (hA : SequentialInverseSystem.IsMittagLeffler A) :
    RightAcyclic A := sorry

-- Proof sketch: specialize Lemma 13.32.2 to the inverse-limit functor, using the preceding
-- `HasMonoEmbedding RightAcyclic` instance together with the vanishing of `R^2 lim`.
/-- Every cochain complex of inverse systems of abelian groups is quasi-isomorphic to one whose
terms are right acyclic for inverse limit. -/
theorem exists_quasiIso_to_termwise_abelianGroupLimit_rightAcyclic
    (K : CochainComplex AbSeq ℤ) :
    ∃ (L : CochainComplex AbSeq ℤ) (α : K ⟶ L), QuasiIso α ∧ ∀ i : ℤ, RightAcyclic (L.X i) :=
  sorry

-- Proof sketch: this is Lemma 13.32.2 specialized to the inverse-limit functor. Once each term
-- `K.X i` is right acyclic for `lim`, the ordinary termwise inverse-limit complex computes the
-- chosen derived inverse limit in the canonical Chapter 13 sense
-- `Functor.ComputesRightDerivedAt`.
/-- Lemma 15.87.1: if each degree `K^p = (K_n^p)` of a cochain complex of inverse systems of
abelian groups is right acyclic for inverse limit, then the homotopy-category class of `K`
computes `R lim(K)`, formalized by the canonical Chapter `13` owner
`Functor.ComputesRightDerivedAt` for `mapHomotopyCategoryToDerived`. Equivalently, the canonical
comparison map from the ordinary termwise inverse-limit complex to the chosen derived inverse
limit is an isomorphism, so `R lim(K)` is represented by the complex whose degree-`p` term is
`\varprojlim_n K_n^p`. -/
theorem abelianGroupDerivedInverseLimit_computes_of_termwise_rightAcyclic
    (K : CochainComplex AbSeq ℤ) (hK : ∀ i : ℤ, RightAcyclic (K.X i)) :
    Functor.ComputesRightDerivedAt KtoD Qish
      ((HomotopyCategory.quotient AbSeq (up ℤ)).obj K) :=
  sorry

/-! ### Lemma_15_87_2 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open ComposableArrows
open Opposite
open SequentialInverseSystem

noncomputable section

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/- Domain-style sampling for Lemma 15.87.2:
- primary domain: the Milnor `lim` / `lim¹` exact sequence for a short exact sequence of
  sequential inverse systems of abelian groups;
- sampled owner declarations:
  `SequentialInverseSystem.firstDerivedLimit`,
  `SequentialInverseSystem.inverseLimit_exact_and_mono_of_shortExact`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `ShortComplex.SnakeInput.δ`,
  `ShortComplex.SnakeInput.snake_lemma`;
- best owner abstraction on this theorem surface: the degree-zero term is the canonical inverse
  limit object `limit A`, while the degree-one obstruction is the chapter owner
  `A.firstDerivedLimit`; the connecting morphism should therefore be the snake-lemma boundary map
  on the canonical Milnor difference-map diagram whose kernel row is `S.map lim` and whose
  cokernel row is expressed by `firstDerivedLimit`;
- primitive data: only the short exact sequence `S : ShortComplex AbSeq`;
- derived API: the canonical map on `firstDerivedLimit`, the named connecting morphism
  `lim C ⟶ lim¹ A`, the five-term exact segment for `lim`, and the endpoint mono/epi
  consequences.

Source/core/bridge triage:
  `source-facing`: the exact five-term segment and six-term endpoint consequences for
  `lim` / `lim¹`;
  `core/canonical`: `limit`, `firstDerivedLimit`, `derivedLimitDifferenceMap`, and the snake-lemma
  owner `ShortComplex.SnakeInput`;
  `bridge/view`: the Milnor ambient-product diagram attached to `S`, whose top kernel row is
  `S.map lim` and whose bottom cokernel row is the induced short complex on `firstDerivedLimit`.
  -/

namespace SequentialInverseSystem

private abbrev productMap {A B : AbSeq} (φ : A ⟶ B) :
    ∏ᶜ inverseSystemFamily A ⟶ ∏ᶜ inverseSystemFamily B :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily A) n ≫ φ.app (op n)

private theorem productMap_π {A B : AbSeq} (φ : A ⟶ B) (n : ℕ) :
    productMap φ ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) n ≫ φ.app (op n) := by
  rw [productMap, Pi.lift_π]

private theorem productMap_zero (S : ShortComplex AbSeq) :
    productMap S.f ≫ productMap S.g = 0 := by
  sorry

private theorem productMap_comm {A B : AbSeq} (φ : A ⟶ B) :
    derivedLimitDifferenceMap A ≫ productMap φ =
      productMap φ ≫ derivedLimitDifferenceMap B := by
  sorry

/-- The canonical map on `R^1 \!\varprojlim` induced by a morphism of sequential inverse systems
of abelian groups. -/
abbrev firstDerivedLimitMap {A B : AbSeq} (φ : A ⟶ B) :
    A.firstDerivedLimit ⟶ B.firstDerivedLimit :=
  cokernel.map (derivedLimitDifferenceMap A) (derivedLimitDifferenceMap B)
    (productMap φ) (productMap φ) (productMap_comm φ)

private abbrev productShortComplex (S : ShortComplex AbSeq) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk (productMap S.f) (productMap S.g) (productMap_zero S)

private abbrev limitToProduct (A : AbSeq) :
    limit A ⟶ ∏ᶜ inverseSystemFamily A :=
  Pi.lift fun n ↦ limit.π A (op n)

private theorem limitToProduct_π (A : AbSeq) (n : ℕ) :
    limitToProduct A ≫ Pi.π (inverseSystemFamily A) n =
      limit.π A (op n) := by
  rw [limitToProduct, Pi.lift_π]

private theorem limitToProduct_comp_difference (A : AbSeq) :
    limitToProduct A ≫ derivedLimitDifferenceMap A = 0 := by
  sorry

private abbrev limitToProductHom (S : ShortComplex AbSeq) :
    S.map lim ⟶ productShortComplex S where
  τ₁ := limitToProduct S.X₁
  τ₂ := limitToProduct S.X₂
  τ₃ := limitToProduct S.X₃
  comm₁₂ := by
    sorry
  comm₂₃ := by
    sorry

private abbrev milnorDifferenceHom (S : ShortComplex AbSeq) :
    productShortComplex S ⟶ productShortComplex S where
  τ₁ := derivedLimitDifferenceMap S.X₁
  τ₂ := derivedLimitDifferenceMap S.X₂
  τ₃ := derivedLimitDifferenceMap S.X₃
  comm₁₂ := productMap_comm S.f
  comm₂₃ := productMap_comm S.g

private abbrev firstDerivedLimitShortComplex (S : ShortComplex AbSeq) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk (firstDerivedLimitMap S.f) (firstDerivedLimitMap S.g) (by
    sorry)

private theorem productToFirstDerivedLimit_comm_f (S : ShortComplex AbSeq) :
    cokernel.π (derivedLimitDifferenceMap S.X₁) ≫ firstDerivedLimitMap S.f =
      productMap S.f ≫ cokernel.π (derivedLimitDifferenceMap S.X₂) := by
  sorry

private theorem productToFirstDerivedLimit_comm_g (S : ShortComplex AbSeq) :
    cokernel.π (derivedLimitDifferenceMap S.X₂) ≫ firstDerivedLimitMap S.g =
      productMap S.g ≫ cokernel.π (derivedLimitDifferenceMap S.X₃) := by
  sorry

private abbrev productToFirstDerivedLimitHom (S : ShortComplex AbSeq) :
    productShortComplex S ⟶ firstDerivedLimitShortComplex S where
  τ₁ := cokernel.π (derivedLimitDifferenceMap S.X₁)
  τ₂ := cokernel.π (derivedLimitDifferenceMap S.X₂)
  τ₃ := cokernel.π (derivedLimitDifferenceMap S.X₃)
  comm₁₂ := productToFirstDerivedLimit_comm_f S
  comm₂₃ := productToFirstDerivedLimit_comm_g S

private noncomputable def limitSnakeInput
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    ShortComplex.SnakeInput AddCommGrpCat where
  L₀ := S.map lim
  L₁ := productShortComplex S
  L₂ := productShortComplex S
  L₃ := firstDerivedLimitShortComplex S
  v₀₁ := limitToProductHom S
  v₁₂ := milnorDifferenceHom S
  v₂₃ := productToFirstDerivedLimitHom S
  w₀₂ := by
    sorry
  w₁₃ := by
    sorry
  h₀ := by
    -- `\varprojlim` is the kernel of the Milnor difference map.
    sorry
  h₃ := by
    -- `R^1 \!\varprojlim` is the cokernel of the Milnor difference map.
    sorry
  L₁_exact := by
    -- Products preserve short exact sequences in abelian groups.
    sorry
  epi_L₁_g := by
    -- Products of epimorphisms in `AddCommGrpCat` are epimorphisms.
    sorry
  L₂_exact := by
    -- `L₂` is the same product row as `L₁`.
    sorry
  mono_L₂_f := by
    -- Products of monomorphisms in `AddCommGrpCat` are monomorphisms.
    sorry

end SequentialInverseSystem

/-- The canonical connecting morphism
`lim C_i ⟶ lim¹ A_i` attached to a short exact sequence of sequential inverse systems of abelian
groups. -/
noncomputable abbrev sequentialAbelianGroupLimitδ
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    limit S.X₃ ⟶ S.X₁.firstDerivedLimit :=
  (SequentialInverseSystem.limitSnakeInput S hS).δ

/-- Lemma 15.87.2: a short exact sequence of sequential inverse systems of abelian groups induces
an exact five-term segment
`lim A_i ⟶ lim B_i ⟶ lim C_i ⟶ lim¹ A_i ⟶ lim¹ B_i`,
where the connecting morphism is the canonical snake-lemma boundary map on the Milnor
difference-map diagram and the degree-one terms are expressed by the chapter owner
`SequentialInverseSystem.firstDerivedLimit`. -/
theorem sequentialAbelianGroupLimit_exact₅
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    (mk₅
      (lim.map S.f)
      (lim.map S.g)
      (sequentialAbelianGroupLimitδ S hS)
      (SequentialInverseSystem.firstDerivedLimitMap S.f)
      (SequentialInverseSystem.firstDerivedLimitMap S.g)).Exact := by
  sorry

/-- In the six-term exact sequence of Lemma 15.87.2, the first map
`lim A_i ⟶ lim B_i` is monic. -/
theorem sequentialAbelianGroupLimit_mono_map_f
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    Mono (lim.map S.f) := by
  exact (SequentialInverseSystem.inverseLimit_exact_and_mono_of_shortExact S hS).2

/-- In the six-term exact sequence of Lemma 15.87.2, the last displayed map
`lim¹ B_i ⟶ lim¹ C_i` is epic. -/
theorem sequentialAbelianGroupLimit_epi_map_g
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    Epi (SequentialInverseSystem.firstDerivedLimitMap S.g) := by
  sorry

/-! ### Lemma_15_87_3 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbCpxSeq" => SequentialInverseSystem (CochainComplex AddCommGrpCat ℤ)
local notation "H" => HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ)
local notation "ev" => HomologicalComplex.eval AddCommGrpCat (up ℤ)

/- Domain-style sampling for Lemma 15.87.3:
- primary domain: derived inverse limits of sequential inverse systems of abelian groups and the
  comparison map from cohomology of a termwise inverse limit to the inverse limit of cohomology;
- sampled owner declarations:
  `SequentialInverseSystem.firstDerivedLimit`,
  `SequentialInverseSystem.IsMittagLeffler`,
  `HomologicalComplex.eval`,
  `HomologicalComplex.homologyFunctor`,
  `ShortComplex.ShortExact.isIso_g_iff`;
- best owner abstraction: the vanishing hypotheses are canonically owned by
  `SequentialInverseSystem.firstDerivedLimit`, while the degree and cohomology towers are
  derived from the input tower of cochain complexes by postcomposing with
  `HomologicalComplex.eval` and `HomologicalComplex.homologyFunctor`; the source-facing
  comparison morphism itself is the canonical `limit.post A (H 0)`, and the `IsIso` conclusion is
  derived API from the more primitive short exact sequence via
  `ShortComplex.ShortExact.isIso_g_iff`;
- primitive data: the tower `A : AbCpxSeq`;
- derived API: the three `R^1 lim` objects, the canonical comparison morphism
  `limit.post A (H 0)`, the short exact sequence it fits into, and the resulting `IsIso`
  criterion.

Source/core/bridge triage:
- `source-facing`: the short exact sequence and its `IsIso` corollary with explicit vanishing
  hypotheses;
- `core/canonical`: `SequentialInverseSystem.firstDerivedLimit`, `limit.post`, and
  `ShortComplex.ShortExact.isIso_g_iff`;
- `bridge/view`: the Mittag-Leffler sufficient criterion below. -/

/-- Under the vanishing of `R^1 \!\varprojlim` for the degree `-2` and `-1` towers, the canonical
comparison map `H^0(\lim_n A_n^\bullet) ⟶ \lim_n H^0(A_n^\bullet)` sits in the expected Milnor
short exact sequence with left term `R^1 \!\varprojlim H^{-1}(A_n^\bullet)`. -/
theorem inverse_limit_zero_cohomology_shortExact_of_vanishing_degree_r1lim
    (A : AbCpxSeq)
    (hAnegTwo : IsZero <| firstDerivedLimit (A ⋙ ev (-2)))
    (hAnegOne : IsZero <| firstDerivedLimit (A ⋙ ev (-1))) :
    ∃ (ι :
        firstDerivedLimit (A ⋙ H (-1)) ⟶
          (H 0).obj (limit A))
      (hι :
        ι ≫ limit.post A (H 0) = 0),
      (ShortComplex.mk ι (limit.post A (H 0)) hι).ShortExact := sorry

-- Proof sketch: first produce the canonical short exact sequence above from the vanishing of the
-- degree `-2` and `-1` obstruction towers. Then apply the owner criterion
-- `ShortComplex.ShortExact.isIso_g_iff`: vanishing of `R^1 \!\varprojlim H^{-1}(A_n^\bullet)`
-- identifies the left term with zero, so the right map is an isomorphism.
/-- Lemma 15.87.3: for a sequential inverse system of cochain complexes of abelian groups, if the
`R^1 \!\varprojlim` terms of the degree `-2`, degree `-1`, and `H^{-1}` towers vanish, then the
canonical comparison map `H^0(\lim_n A_n^\bullet) ⟶ \lim_n H^0(A_n^\bullet)` is an isomorphism.
-/
theorem inverse_limit_zero_cohomology_comparison_isIso_of_vanishing_r1lim
    (A : AbCpxSeq)
    (hAnegTwo : IsZero <| firstDerivedLimit (A ⋙ ev (-2)))
    (hAnegOne : IsZero <| firstDerivedLimit (A ⋙ ev (-1)))
    (hHnegOne : IsZero <| firstDerivedLimit (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := by
  rcases inverse_limit_zero_cohomology_shortExact_of_vanishing_degree_r1lim
      A hAnegTwo hAnegOne with
    ⟨ι, hι, hshort⟩
  exact (ShortComplex.ShortExact.isIso_g_iff hshort).2 hHnegOne

-- Proof sketch: the Mittag-Leffler criterion from the preceding Chapter 15 development implies
-- the vanishing of `R^1 \!\varprojlim` for each of the three towers, so the main theorem above
-- applies directly.
/-- A sufficient criterion for Lemma 15.87.3: it is enough that the degree `-2`, degree `-1`,
and `H^{-1}` towers are Mittag-Leffler. -/
theorem inverse_limit_zero_cohomology_comparison_isIso_of_isMittagLeffler
    (A : AbCpxSeq)
    (hAnegTwo : IsMittagLeffler (A ⋙ ev (-2)))
    (hAnegOne : IsMittagLeffler (A ⋙ ev (-1)))
    (hHnegOne : IsMittagLeffler (A ⋙ H (-1))) :
    IsIso (limit.post A (H 0)) := by
  have hAnegTwo' : IsZero <| firstDerivedLimit (A ⋙ ev (-2)) :=
    ((isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
      (A ⋙ ev (-2))).1 hAnegTwo).1
  have hAnegOne' : IsZero <| firstDerivedLimit (A ⋙ ev (-1)) :=
    ((isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
      (A ⋙ ev (-1))).1 hAnegOne).1
  have hHnegOne' : IsZero <| firstDerivedLimit (A ⋙ H (-1)) :=
    ((isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
      (A ⋙ H (-1))).1 hHnegOne).1
  exact inverse_limit_zero_cohomology_comparison_isIso_of_vanishing_r1lim
    A hAnegTwo' hAnegOne' hHnegOne'

end SequentialInverseSystem

end CategoryTheory

/-! ### Lemma_15_87_4 (from Chap15) -/
open CategoryTheory Limits Opposite OrderHom
open scoped BigOperators

noncomputable section

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 15.87.4:
- primary domain: sequential inverse systems of abelian groups, their associated sequential
  pro-objects, and the Milnor presentations of `\varprojlim` and `R^1 \!\varprojlim`;
- sampled owner declarations:
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `exists_representative`,
  `represents_eq_iff_equivalent`,
  `derivedLimitDifferenceMap`,
  `limit`,
  `cokernel.map`;
- best owner abstraction: a morphism of the associated sequential pro-objects, written directly as
  the canonical Chapter 4 pro-object morphism type
  `colimit (B.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor A ⋙ uliftFunctor.{0}`;
  a sequential representative is only bridge data used to construct the Milnor comparison maps;
- primitive data: the towers `A`, `B`, and the pro-morphism `η`;
- derived API: the induced maps on `limit A` and
  `SequentialInverseSystem.firstDerivedLimit A`, with representative-level `CommSq` and cokernel
  maps used only to descend those constructions from `η`.

Source/core/bridge triage:
- `source-facing`: the maps induced on `\varprojlim` and on `R^1 \!\varprojlim` by a morphism of
  pro-systems;
- `core/canonical`: `SequentialProObjectMorphismRep.toProObjectHom`, `limit`,
  `derivedLimitDifferenceMap`, and `cokernel.map`;
- `bridge/view`: the Milnor `CommSq` and the representative-level maps attached to a chosen
  sequential representative. -/

namespace SequentialProObjectMorphismRep

section

variable {C : Type u} [Category.{v} C] [HasLimitsOfShape ℕᵒᵖ C]
variable {A B : SequentialInverseSystem C}

/-- The representative-level map on inverse limits attached to a sequential representative of a
pro-system morphism. This is bridge data for the owner-level map `inducedLimitMap`. -/
def limitMap (r : SequentialProObjectMorphismRep A B) :
    limit A ⟶ limit B :=
  limit.pre A (toFunctor r.reindex).op ≫ limMap r.hom

/-- The induced map on inverse limits of a sequential representative is computed componentwise by
the representative-level maps. -/
theorem limitMap_π (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    r.limitMap ≫ limit.π B (op n) =
      limit.π A (op (r.reindex n)) ≫ r.map n := by
  rw [limitMap, Category.assoc, limMap_π, ← Category.assoc, limit.pre_π]
  simp [toFunctor]

-- Proof sketch: if two representatives define the same pro-object morphism, Example `4.22.6`
-- identifies them after common refinement; the Stacks Project argument shows that the induced map
-- on the canonical inverse-limit object is unchanged by passing to such a refinement.
/-- Representatives defining the same pro-object morphism induce the same map on inverse limits.
-/
private theorem limitMap_eq_of_toProObjectHom_eq
    {r₁ r₂ : SequentialProObjectMorphismRep A B}
    (h : r₁.toProObjectHom = r₂.toProObjectHom) :
    r₁.limitMap = r₂.limitMap := sorry

end

section

variable {A B : SequentialInverseSystem AddCommGrpCat.{v}}

/-- The map on ambient products given by the component maps
`A_{m_n} ⟶ B_n` of a sequential representative. -/
private abbrev firstProductMap (r : SequentialProObjectMorphismRep A B) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n

/-- The `n`-th component of the second Milnor product map attached to a sequential representative,
given by summing the transition maps over the interval `[m_n, m_{n + 1})`. -/
private abbrev secondProductComponent (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    (∏ᶜ inverseSystemFamily A) ⟶ B.obj (op n) :=
  Finset.sum (Finset.range (r.reindex (n + 1) - r.reindex n)) fun k ↦
    Pi.π (inverseSystemFamily A) (r.reindex n + k) ≫
      A.transitionMap (Nat.le_add_right (r.reindex n) k) ≫ r.map n

/-- The second map on ambient products attached to a sequential representative, making the Milnor
square commute. -/
private def secondProductMap (r : SequentialProObjectMorphismRep A B) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦ secondProductComponent r n

-- Proof sketch: compare the `n`-th product projection on both sides. Expanding the definition of
-- `derivedLimitDifferenceMap` and the finite sum in `secondProductComponent`, the terms telescope,
-- and the compatibility relation `r.comm` identifies the remaining boundary terms with the
-- `n`-th component of `firstProductMap r ≫ derivedLimitDifferenceMap B`.
/-- The two product maps attached to a sequential representative form a commutative square with
the Milnor difference maps. -/
private theorem milnorDifferenceCommSq (r : SequentialProObjectMorphismRep A B) :
    CommSq (derivedLimitDifferenceMap A) (firstProductMap r) (secondProductMap r)
      (derivedLimitDifferenceMap B) := sorry

/-- The representative-level map on `R^1 \!\varprojlim`, obtained from the Milnor square attached
to a sequential representative. -/
abbrev firstDerivedLimitMap (r : SequentialProObjectMorphismRep A B) :
    A.firstDerivedLimit ⟶ B.firstDerivedLimit :=
  cokernel.map (derivedLimitDifferenceMap A) (derivedLimitDifferenceMap B)
    (firstProductMap r) (secondProductMap r) (milnorDifferenceCommSq r).w

-- Proof sketch: use the same common-refinement argument as for `limitMap`; after passing to
-- cokernels of the Milnor difference maps, the two second product maps define the same morphism.
/-- Representatives defining the same pro-object morphism induce the same map on
`R^1 \!\varprojlim`. -/
private theorem firstDerivedLimitMap_eq_of_toProObjectHom_eq
    {r₁ r₂ : SequentialProObjectMorphismRep A B}
    (h : r₁.toProObjectHom = r₂.toProObjectHom) :
    r₁.firstDerivedLimitMap = r₂.firstDerivedLimitMap := sorry

end

end SequentialProObjectMorphismRep

section

variable {C : Type u} [Category.{v} C] [HasLimitsOfShape ℕᵒᵖ C]
variable {A B : SequentialInverseSystem C}
variable (η : colimit (B.op ⋙ uliftCoyoneda.{0}) ⟶
  proSystemHomColimitFunctor A ⋙ uliftFunctor.{0})

private noncomputable abbrev chosenRepresentative :
    SequentialProObjectMorphismRep A B :=
  Classical.choose (exists_representative η)

set_option linter.unusedSectionVars false in
private theorem chosenRepresentative_spec :
    (chosenRepresentative η).toProObjectHom = η :=
  Classical.choose_spec (exists_representative η)

/-- The map on inverse limits induced by a morphism between the sequential pro-objects associated
to `A` and `B`. -/
noncomputable def inducedLimitMap :
    limit A ⟶ limit B :=
  (chosenRepresentative η).limitMap

/-- The owner-level map `inducedLimitMap η` is characterized by any sequential representative of
`η`. -/
theorem inducedLimitMap_eq_limitMap
    (r : SequentialProObjectMorphismRep A B) (h : r.toProObjectHom = η) :
    inducedLimitMap η = r.limitMap := by
  exact SequentialProObjectMorphismRep.limitMap_eq_of_toProObjectHom_eq
    ((chosenRepresentative_spec η).trans h.symm)

-- Proof sketch: choose a sequential representative `r` of `η` using Example `4.22.6`. If `η` is
-- an isomorphism in the pro-category, then `inducedLimitMap η` may be computed using `r.limitMap`;
-- applying the same construction to `inv η` gives the inverse map on inverse limits.
/-- An isomorphism between sequential pro-objects induces an isomorphism on inverse limits. -/
theorem inducedLimitMap_isIso_of_isIso
    [IsIso η] :
    IsIso (inducedLimitMap η) := sorry

end

section

variable {A B : SequentialInverseSystem AddCommGrpCat.{v}}
variable (η : colimit (B.op ⋙ uliftCoyoneda.{0}) ⟶
  proSystemHomColimitFunctor A ⋙ uliftFunctor.{0})

/-- The map on `R^1 \!\varprojlim` induced by a morphism between the sequential pro-objects
associated to `A` and `B`. -/
noncomputable def inducedFirstDerivedLimitMap :
    A.firstDerivedLimit ⟶ B.firstDerivedLimit :=
  (chosenRepresentative η).firstDerivedLimitMap

/-- The owner-level map `inducedFirstDerivedLimitMap` agrees with the representative-level bridge
map for any sequential representative of `η`. -/
theorem inducedFirstDerivedLimitMap_eq_firstDerivedLimitMap
    (r : SequentialProObjectMorphismRep A B) (h : r.toProObjectHom = η) :
    inducedFirstDerivedLimitMap η = r.firstDerivedLimitMap := by
  exact SequentialProObjectMorphismRep.firstDerivedLimitMap_eq_of_toProObjectHom_eq
    ((chosenRepresentative_spec η).trans h.symm)

-- Proof sketch: choose a sequential representative `r` of `η` using Example `4.22.6`. If `η` is
-- an isomorphism in the pro-category, then the induced maps on `limit` and on `R^1 \!\varprojlim`
-- are independent of the chosen representative and hence may be computed using any representative
-- of `η`; for that representative, the Stacks Project argument gives inverse maps induced by a
-- representative of `inv η`.
/-- Lemma 15.87.4: a morphism of pro-systems of abelian groups induces maps on
`\varprojlim` and on `R^1 \!\varprojlim`. If the corresponding morphism of sequential
pro-objects is an isomorphism, then both induced maps are isomorphisms. -/
theorem inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso
    [IsIso η] :
    IsIso (inducedLimitMap η) ∧
      IsIso (inducedFirstDerivedLimitMap η) := sorry

end

end CategoryTheory

/-! ### Lemma_15_87_5 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 15.87.5:
- primary domain: the Milnor short exact sequence obtained by applying the represented Hom functor
  `Hom_D(L, -)` to a chosen Milnor triangle for a derived inverse limit in a triangulated
  category;
- sampled owner declarations:
  `CategoryTheory.HasMilnorTriangle.WithMap`,
  `preadditiveCoyonedaObj`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `CategoryTheory.IsDerivedLimit`,
  `SequentialInverseSystem.firstDerivedLimit`;
- best owner abstraction: the primitive source-facing data are the chosen Milnor triangle
  `K ⟶ ∏ K_n ⟶ ∏ K_n ⟶ K[1]`, while the intrinsic derived API is the Hom tower
  `n ↦ Hom_D(L, K_n)` and its shifted variant `n ↦ Hom_D(L, K_n[-1])`, together with their
  canonical Milnor owners `limit (Ksys ⋙ preadditiveCoyonedaObj L)` and
  `firstDerivedLimit ((Ksys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L)`;
  the theorem surface should therefore expose those owners directly, with only the represented Hom
  functor itself appearing explicitly where no shorter ambient owner already exists;
- primitive-vs-derived split:
  primitive data are the chosen Milnor triangle and its relation `ι ≫ (1 - shift) = 0`;
  derived API are the owner-level `firstDerivedLimit` model for the shifted Hom tower
  `n ↦ Hom_D(L, K_n[-1])` and the
  comparison morphism from `Hom_D(L, K)` to `\varprojlim_n Hom_D(L, K_n)`.

Source/core/bridge triage:
- `source-facing`: the Milnor short exact sequence for `Hom_D(L, -)` attached to a chosen Milnor
  triangle;
- `core/canonical`: `derivedLimitDifferenceMap`, `IsDerivedLimit`, `preadditiveCoyonedaObj`,
  and `firstDerivedLimit`;
- `bridge/view`: the comparison morphism
  `Hom_D(L, K) ⟶ \varprojlim_n Hom_D(L, K_n)` induced by the first map of the chosen Milnor
  triangle. -/

/-- The sequential inverse system `n ↦ Hom_D(L, K_n)`. -/
private abbrev representedHomTower
    (Ksys : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  Ksys ⋙ preadditiveCoyonedaObj L

/-- The sequential inverse system `n ↦ Hom_D(L, K_n[-1])`. -/
private abbrev shiftedRepresentedHomTower
    (Ksys : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  (Ksys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L

private theorem homToDerivedLimit_comp_zero
    {Ksys : SequentialInverseSystem D} {K : D}
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    ι ≫ derivedLimitDifferenceMap Ksys = 0 := by
  rcases hι with ⟨δ, hδ⟩
  exact comp_distTriang_mor_zero₁₂ (Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ) hδ

private theorem homToDerivedLimitCone_naturality
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (n : ℕ) :
    (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n) =
      (preadditiveCoyonedaObj L).map
          (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1)) ≫
        (Ksys ⋙ preadditiveCoyonedaObj L).map (homOfLE (Nat.le_succ n)).op := by
  let F := preadditiveCoyonedaObj L
  have hdiff : ι ≫ derivedLimitDifferenceMap Ksys = 0 :=
    homToDerivedLimit_comp_zero hι
  have hcomp : ι ≫ Pi.π (inverseSystemFamily Ksys) n =
      ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
        Ksys.map (homOfLE (Nat.le_succ n)).op := by
    have hπ :
        ι ≫ Pi.π (inverseSystemFamily Ksys) n -
            ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
              Ksys.map (homOfLE (Nat.le_succ n)).op = 0 := by
      have hπ'' :
          ι ≫ derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n =
            ι ≫
              (Pi.π (inverseSystemFamily Ksys) n -
                Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
                  Ksys.map (homOfLE (Nat.le_succ n)).op) := by
        exact congrArg (fun f ↦ ι ≫ f) (derivedLimitDifferenceMap_comp_π Ksys n)
      have hπ' :
          0 =
            ι ≫ Pi.π (inverseSystemFamily Ksys) n -
              ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
                Ksys.map (homOfLE (Nat.le_succ n)).op := by
        rw [← Category.assoc] at hπ''
        rw [hdiff, zero_comp] at hπ''
        simpa [Preadditive.comp_sub] using hπ''
      exact hπ'.symm
    exact sub_eq_zero.mp hπ
  calc
    F.map (ι ≫ Pi.π (inverseSystemFamily Ksys) n) =
        F.map
          (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
            Ksys.map (homOfLE (Nat.le_succ n)).op) := by
        exact congrArg F.map hcomp
    _ =
        F.map (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1)) ≫
          (Ksys ⋙ F).map (homOfLE (Nat.le_succ n)).op := by
        simpa using
          (Functor.map_comp F
            (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1))
            (Ksys.map (homOfLE (Nat.le_succ n)).op))

private def homToDerivedLimitCone
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    Cone (representedHomTower Ksys L) where
  pt := (preadditiveCoyonedaObj L).obj K
  π := NatTrans.ofOpSequence
    (fun n ↦ (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n))
    (fun n ↦ homToDerivedLimitCone_naturality L hι n)

private def homToDerivedLimitComparison
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    (preadditiveCoyonedaObj L).obj K ⟶
      limit (representedHomTower Ksys L) :=
  limit.lift _ (homToDerivedLimitCone L hι)

-- Proof sketch: apply the homological functor `Hom_D(L, -)` to the chosen Milnor triangle
-- `K ⟶ ∏ K_n ⟶ ∏ K_n ⟶ K[1]`. The first map gives the comparison morphism from `Hom_D(L, K)` to
-- the inverse limit of the Hom tower, while the left term is the standard cokernel model for
-- `R^1 \!\varprojlim_n Hom_D(L, K_n[-1])`, canonically exposed as
-- `(shiftedRepresentedHomTower Ksys L).firstDerivedLimit`.
private theorem homToDerivedLimit_shortExact_of_triangle
    {Ksys : SequentialInverseSystem D} {K : D}
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (L : D) :
    ∃ (ι' :
        (shiftedRepresentedHomTower Ksys L).firstDerivedLimit ⟶
          (preadditiveCoyonedaObj L).obj K)
      (h :
        ι' ≫ homToDerivedLimitComparison L hι = 0),
      (ShortComplex.mk ι' (homToDerivedLimitComparison L hι) h).ShortExact := by
  rcases hι with ⟨δ, hδ⟩
  sorry

-- Proof sketch: unpack the chosen Milnor triangle from `hK` and apply the previous bridge-level
-- result. The public surface keeps only the canonical owner hypothesis `IsDerivedLimit Ksys K`,
-- while the specific Milnor presentation remains internal.
/-- Lemma 15.87.5: if `K` is a derived limit of a sequential inverse system `(K_n)_n`, then for
every object `L` there is a short exact sequence
`0 ⟶ R^1 \!\varprojlim \operatorname{Hom}_D(L, K_n[-1]) ⟶ \operatorname{Hom}_D(L, K) ⟶
\varprojlim_n \operatorname{Hom}_D(L, K_n) ⟶ 0`. -/
theorem homToDerivedLimit_hasMilnorShortExactSequence
    (Ksys : SequentialInverseSystem D) {K : D}
    (hK : IsDerivedLimit Ksys K) (L : D) :
    ∃ (ι :
        (shiftedRepresentedHomTower Ksys L).firstDerivedLimit ⟶
          (preadditiveCoyonedaObj L).obj K)
      (π :
        (preadditiveCoyonedaObj L).obj K ⟶
          limit (representedHomTower Ksys L))
      (h :
        ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  rcases hK with ⟨_, ⟨ι, δ, hδ⟩⟩
  let hι : HasMilnorTriangle.WithMap Ksys ι := ⟨δ, hδ⟩
  rcases homToDerivedLimit_shortExact_of_triangle hι L with ⟨ι', h, hshort⟩
  exact ⟨ι', homToDerivedLimitComparison L hι, h, hshort⟩

end

end CategoryTheory

/-! ### Lemma_15_87_6 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]

/- Domain-style sampling for Lemma 15.87.6:
- primary domain: derived limits in a triangulated category and isomorphisms of the associated
  sequential pro-objects;
- sampled owner declarations:
  `exists_representative`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso`,
  `CategoryTheory.homToDerivedLimit_hasMilnorShortExactSequence`;
- best owner abstraction: the public pro-isomorphism hypothesis belongs to the canonical
  pro-object morphism `η`; a sequential representative of `η` is private bridge data used only to
  pass to inverse systems of abelian groups;
- primitive data: the towers `Ksys`, `Msys`, their chosen derived limits `K`, `M`, and a
  pro-object morphism
  `η : colimit (Msys.op ⋙ uliftCoyoneda.{0}) ⟶
    proSystemHomColimitFunctor Ksys ⋙ uliftFunctor.{0}`;
- derived API: the owner-level isomorphism hypothesis `IsIso η`, a chosen representative of `η`,
  the induced represented-Hom representative, and the Milnor short exact sequences from Lemma
  `15.87.5`.

Source/core/bridge triage:
- `source-facing`: the existence of a non-canonical isomorphism between chosen derived limits of
  pro-isomorphic towers;
- `core/canonical`: `η`, `IsDerivedLimit`, and the owner theorem
  `inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso`;
- `bridge/view`: a chosen representative `a` of `η` and the represented-Hom representative
  `preadditiveCoyonedaRep a L`. -/

namespace SequentialProObjectMorphismRep

variable {Ksys Msys : ℕᵒᵖ ⥤ D}

local notation "SeqRep" => _root_.CategoryTheory.SequentialProObjectMorphismRep

-- Proof sketch: apply the additive covariant functor `preadditiveCoyoneda.obj (op L)` to the
-- compatibility square defining `a`. This transports the levelwise commutativity relation from
-- `D` to the inverse systems of abelian groups `Hom_D(L, K_n)` and `Hom_D(L, M_n)`.
/-- Applying `preadditiveCoyoneda.obj (op L)` to the defining compatibility square of `a` yields
the compatibility square on the represented-Hom towers. -/
private theorem preadditiveCoyonedaRep_comm
    (a : SeqRep Ksys Msys) (L : D) :
    ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      (Ksys ⋙ preadditiveCoyoneda.obj (op L)).map (homOfLE (a.reindex.monotone h)).op ≫
          (preadditiveCoyoneda.obj (op L)).map (a.map n) =
        (preadditiveCoyoneda.obj (op L)).map (a.map n') ≫
          (Msys ⋙ preadditiveCoyoneda.obj (op L)).map (homOfLE h).op := sorry

/-- The induced representative on the sequential inverse systems of abelian groups
`Hom_D(L, K_n)` and `Hom_D(L, M_n)`. -/
private def preadditiveCoyonedaRep
    (a : SeqRep Ksys Msys) (L : D) :
    SeqRep
      (Ksys ⋙ preadditiveCoyoneda.obj (op L))
      (Msys ⋙ preadditiveCoyoneda.obj (op L)) where
  reindex := a.reindex
  hom :=
    { app := fun n ↦ (preadditiveCoyoneda.obj (op L)).map (a.map n.unop)
      naturality := fun n n' g ↦ by
        let h : n'.unop ≤ n.unop := leOfHom g.unop
        simpa [h] using preadditiveCoyonedaRep_comm a L h }

end SequentialProObjectMorphismRep

-- Proof sketch: choose a representative `a` of `η` by Example `4.22.6`, then use Remark 13.34.4
-- to extend the product maps attached to `a` to some comparison morphism `f : K ⟶ M` between
-- chosen derived-limit triangles. For every `L`, Lemma 15.87.5 gives Milnor short exact
-- sequences for `K` and `M`, while the owner-level hypothesis `IsIso η` implies, after passing to
-- the represented-Hom towers via `preadditiveCoyonedaRep a L` and applying Lemma 15.87.4, that
-- the outer vertical maps are isomorphisms. Hence `(preadditiveCoyoneda.obj (op L)).map f` is an
-- isomorphism for every `L`, so Yoneda implies that `f` itself is an isomorphism.
/-- Lemma 15.87.6: let `D` be a triangulated category, let `(K_n)` and `(M_n)` be inverse systems
of objects of `D` with derived limits `K` and `M`, and let `η` be an isomorphism between the
associated pro-objects. Then `η` induces a non-canonical isomorphism `K ⟶ M` between the chosen
derived limits. -/
theorem exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit
    {Ksys Msys : ℕᵒᵖ ⥤ D} {K M : D}
    (hK : IsDerivedLimit Ksys K) (hM : IsDerivedLimit Msys M)
    (η : colimit (Msys.op ⋙ uliftCoyoneda.{0}) ⟶
      proSystemHomColimitFunctor Ksys ⋙ uliftFunctor.{0}) [IsIso η] :
    ∃ f : K ⟶ M, IsIso f := sorry

end

end CategoryTheory

/-! ### Lemma_15_87_7 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 15.87.7:
- primary domain: triangulated-category homotopy colimits and the Milnor inverse-limit sequence
  for represented contravariant Hom functors;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `preadditiveYoneda.obj`,
  `Functor.ofSequence`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`;
- best owner abstraction:
  `source-facing`: the Milnor short exact sequence attached to the owner predicate
    `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`;
  `core/canonical`: the represented functor `preadditiveYoneda.obj L`, its inverse-system image
    `(Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L`, together with
    `SequentialInverseSystem.firstDerivedLimit`;
  `bridge/view`: the comparison morphism
    `Hom_D(Khocolim, L) ⟶ \varprojlim_n Hom_D(K_n, L)` attached to that chosen telescope
    presentation.
- primitive data: the sequential system `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` together with the owner hypothesis
  `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`;
- derived API: the represented inverse system `(Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L`,
  its canonical owner-level `firstDerivedLimit`, and the presentation-dependent bridge
  `homFromHomotopyColimitComparison`.

Source/core/bridge triage:
- `source-facing`: the Milnor short exact sequence for `Hom_D(-, L)` evaluated on an object
  equipped with `IsHomotopyColimitOf (Functor.ofSequence f)`;
- `core/canonical`: `preadditiveYoneda.obj L`, `(Functor.ofSequence f).op`, and
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: `homFromHomotopyColimitComparison`, the comparison map supplied by that chosen
  telescope presentation. -/

private theorem homFromHomotopyColimitCone_naturality
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D)
    (n : ℕ) :
    (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj (n + 1) ≫ g)) ≫
      ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L).map (homOfLE (Nat.le_succ n)).op =
    (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj n ≫ g)) := by
  sorry

private def homFromHomotopyColimitCone
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    Cone ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L) where
  pt := (preadditiveYoneda.obj L).obj (op Khocolim)
  π := NatTrans.ofOpSequence
    (fun n ↦ (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj n ≫ g)))
    (fun n ↦ (homFromHomotopyColimitCone_naturality L f g h hKhocolim n).symm)

/-- The comparison morphism
`Hom_D(Khocolim, L) ⟶ \varprojlim_n Hom_D(K_n, L)` induced by a chosen distinguished telescope
triangle presenting `Khocolim` as a homotopy colimit of the sequence
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`. -/
private def homFromHomotopyColimitComparison
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    (preadditiveYoneda.obj L).obj (op Khocolim) ⟶
      limit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L) :=
  limit.lift _ (homFromHomotopyColimitCone L f g h hKhocolim)

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]

-- Proof sketch: apply the contravariant Hom functor `Hom_D(-, L)` to the opposite of the
-- distinguished telescope triangle presenting `Khocolim`. Lemma 13.4.2 identifies this as a
-- homological functor, so one gets a long exact sequence. The two terms
-- `Hom_D(\bigoplus_n K_n, L)` and `Hom_D(\bigoplus_n K_n, L⟦-1⟧)` identify with the products of
-- `Hom_D(K_n, L)` and `Hom_D(K_n, L⟦-1⟧)`, and Lemma 15.87.1 identifies the kernel and cokernel
-- of the Milnor difference maps with `\varprojlim` and `R^1 \!\varprojlim`. The left term is
-- therefore best exposed through the owner
-- `firstDerivedLimit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj _)`, not as
-- a raw cokernel of `derivedLimitDifferenceMap`.
/-- The bridge-level Milnor short exact sequence attached to a chosen distinguished telescope
triangle. The chosen presentation stays internal; the public source-facing theorem below is
phrased only over `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`. -/
private theorem hom_from_homotopyColimit_shortExact_of_triangle
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    ∃ (ι :
        firstDerivedLimit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)) ⟶
          (preadditiveYoneda.obj L).obj (op Khocolim))
      (hι :
        ι ≫ homFromHomotopyColimitComparison L f g h hKhocolim = 0),
      (ShortComplex.mk ι (homFromHomotopyColimitComparison L f g h hKhocolim) hι).ShortExact :=
  sorry

/-- Lemma 15.87.7: if `Khocolim` is a homotopy colimit of a sequential system
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`, then for every `L` there is a short exact sequence
`0 ⟶ R^1 \!\varprojlim Hom_D(K_n, L⟦-1⟧) ⟶ Hom_D(Khocolim, L) ⟶
\varprojlim_n Hom_D(K_n, L) ⟶ 0`. -/
theorem hom_from_homotopyColimit_shortExact
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (hKhocolim : IsHomotopyColimitOf (Functor.ofSequence f) Khocolim) :
    ∃ (ι :
        firstDerivedLimit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)) ⟶
          (preadditiveYoneda.obj L).obj (op Khocolim))
      (π :
        (preadditiveYoneda.obj L).obj (op Khocolim) ⟶
          limit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L))
      (h :
        ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  obtain ⟨g, hδ, htriangle⟩ := hKhocolim
  rcases hom_from_homotopyColimit_shortExact_of_triangle L f g hδ htriangle with
    ⟨ι, hι, hshort⟩
  exact ⟨ι, homFromHomotopyColimitComparison L f g hδ htriangle, hι, hshort⟩

end

end CategoryTheory

/-! ### Remark_15_87_8_Rlim_as_cohomology (from Chap15) -/
open CategoryTheory Limits
open CategoryTheory.Sheaf

noncomputable section

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat
local notation "NatSite" => (⊥ : GrothendieckTopology ℕ)
private abbrev rightDerivedLimitOnSequentialAbelianGroups (p : ℕ) :
    AbSeq ⥤ AddCommGrpCat :=
  ((lim : AbSeq ⥤ AddCommGrpCat).rightDerived p)

local notation:max "R^" p:max " lim(" A ")" =>
  Functor.obj (rightDerivedLimitOnSequentialAbelianGroups p) A

/- Domain-style sampling for Remark 15.87.8:
- primary domain: inverse limit on sequential inverse systems of abelian groups, compared with
  sheaf cohomology on the chaotic site of `ℕ`;
- sampled owner declarations:
  `SequentialInverseSystem`,
  `CategoryTheory.Limits.lim`,
  `sheafBotEquivalence`,
  `Sheaf.ΓNatIsoLim`,
  `Sheaf.Γ`,
  `Sheaf.cohomologyFunctor`,
  `Functor.rightDerived`;
- best owner abstraction: the source-facing sheaf-side owner is
  `Sheaf.cohomologyFunctor NatSite p`; the inverse-limit side owner is
  `lim : AbSeq ⥤ AddCommGrpCat`; the passage from inverse systems to sheaves is the bridge
  `(sheafBotEquivalence AddCommGrpCat).inverse`, while `Sheaf.ΓNatIsoLim` is the canonical
  underived comparison identifying global sections with inverse limit on the chaotic site;
- primitive data: the inverse-limit functor, the global-sections functor on the chaotic site, the
  bottom-topology sheaf equivalence, and the sheaf-cohomology owner `Sheaf.cohomologyFunctor`;
- derived API: `Functor.rightDerived`, plus the bridge from right derived global sections to
  `Sheaf.cohomologyFunctor`.

Source/core/bridge triage:
- `source-facing`: the comparison between `R lim` and the sheaf cohomology functors
  `Sheaf.cohomologyFunctor NatSite p` on the chaotic site;
- `core/canonical`: `lim : AbSeq ⥤ AddCommGrpCat` and `Sheaf.cohomologyFunctor NatSite p`;
- `bridge/view`: `(sheafBotEquivalence AddCommGrpCat).inverse`, `Sheaf.ΓNatIsoLim NatSite
  AddCommGrpCat`, and the comparison from right derived global sections to sheaf cohomology. -/

/-- The bottom-topology equivalence identifies global sections of the corresponding sheaf on
`NatSite` with inverse limit on sequential inverse systems of abelian groups. -/
noncomputable def naturalNumbersSiteInverseΓIsoLim :
    (sheafBotEquivalence AddCommGrpCat).inverse ⋙ Sheaf.Γ NatSite AddCommGrpCat ≅
      (lim : AbSeq ⥤ AddCommGrpCat) :=
  Functor.isoWhiskerLeft
      ((sheafBotEquivalence AddCommGrpCat).inverse)
      (Sheaf.ΓNatIsoLim NatSite AddCommGrpCat) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafBotEquivalence AddCommGrpCat).counitIso _ ≪≫
    Functor.leftUnitor _

local instance sheafBotEquivalenceInverse_additive :
    ((sheafBotEquivalence AddCommGrpCat).inverse :
      AbSeq ⥤ Sheaf NatSite AddCommGrpCat).Additive where
  map_add := by
    intro A B f g
    rfl

local instance gammaNatSite_additive :
    (Sheaf.Γ NatSite AddCommGrpCat).Additive :=
  Functor.additive_of_iso (Sheaf.ΓNatIsoLim NatSite AddCommGrpCat).symm

/- The Ext-based sheaf-cohomology owner on `NatSite` is `Sheaf.cohomologyFunctor NatSite`. -/
recall Sheaf.cohomologyFunctor

/-- Bridge/view companion for Remark 15.87.8: the `p`-th right derived functor of inverse limit is
canonically isomorphic to the `p`-th right derived functor of global sections of the corresponding
sheaf on the chaotic site of `ℕ`. -/
noncomputable def rightDerivedLimitIsoRightDerivedGlobalSectionsOfNaturalNumbersSite
    (p : ℕ) :
    ((lim : AbSeq ⥤ AddCommGrpCat).rightDerived p) ≅
      (((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.Γ NatSite AddCommGrpCat).rightDerived p) := by
  refine
    { hom := NatTrans.rightDerived naturalNumbersSiteInverseΓIsoLim.symm.hom p
      inv := NatTrans.rightDerived naturalNumbersSiteInverseΓIsoLim.hom p
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · simpa using
      (NatTrans.rightDerived_comp
        naturalNumbersSiteInverseΓIsoLim.symm.hom
        naturalNumbersSiteInverseΓIsoLim.hom
        p).symm
  · simpa using
      (NatTrans.rightDerived_comp
        naturalNumbersSiteInverseΓIsoLim.hom
        naturalNumbersSiteInverseΓIsoLim.symm.hom
        p).symm

/-- Bridge/view companion for Remark 15.87.8: after identifying a sequential inverse system of
abelian groups with its sheaf on the chaotic site of `ℕ`, the right derived functors of global
sections agree with the canonical sheaf-cohomology owner `Sheaf.cohomologyFunctor NatSite`. -/
theorem rightDerivedGlobalSectionsOfNaturalNumbersSite_isIsomorphic_toCohomology
    (p : ℕ) :
    IsIsomorphic
      (((sheafBotEquivalence AddCommGrpCat).inverse ⋙
          Sheaf.Γ NatSite AddCommGrpCat).rightDerived p)
      ((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.cohomologyFunctor NatSite p) := by
  sorry

/-- Remark 15.87.8, functor form: the `p`-th right derived functor of inverse limit on sequential
inverse systems of abelian groups is canonically isomorphic to the `p`-th sheaf cohomology functor
of the associated sheaf on the chaotic site of `ℕ`. -/
theorem rightDerivedLimit_isIsomorphic_toNaturalNumbersSiteCohomology
    (p : ℕ) :
    IsIsomorphic
      ((lim : AbSeq ⥤ AddCommGrpCat).rightDerived p)
      ((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.cohomologyFunctor NatSite p) := by
  rcases rightDerivedGlobalSectionsOfNaturalNumbersSite_isIsomorphic_toCohomology p with ⟨e⟩
  exact ⟨rightDerivedLimitIsoRightDerivedGlobalSectionsOfNaturalNumbersSite p ≪≫ e⟩

/-- Remark 15.87.8, source-facing object form: for a sequential inverse system `A` of abelian
groups, the object `R^p lim(A)` is canonically isomorphic to the sheaf cohomology
`H^p(\mathbf N, \mathcal F_A)` of the corresponding sheaf on the chaotic site of `ℕ`. -/
theorem rightDerivedLimitObj_isIsomorphic_toNaturalNumbersSiteCohomology
    (A : AbSeq) (p : ℕ) :
    IsIsomorphic
      (R^p lim(A))
      ((Sheaf.cohomologyFunctor NatSite p).obj
        ((sheafBotEquivalence AddCommGrpCat).inverse.obj A)) := by
  rcases rightDerivedLimit_isIsomorphic_toNaturalNumbersSiteCohomology p with ⟨e⟩
  exact ⟨e.app A⟩

/-! ### Lemma_15_87_9 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "Ab" => AddCommGrpCat
local notation "AbSeq" => SequentialInverseSystem Ab
local notation "DAbSeq" => DerivedCategory AbSeq

/- Domain-style sampling for Lemma 15.87.9:
- primary domain: derived inverse limits of sequential inverse systems of abelian groups and
  their stagewise realization in `D(\operatorname{Ab})`;
- sampled owner declarations:
  `CategoryTheory.IsDerivedLimit`,
  `stagewiseAbelianGroupDerivedTower`,
  `CategoryTheory.additiveFunctorTotalRightDerived`,
  `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`;
- best owner abstraction: the source-facing statement should stay a specialization asserting that
  the chosen object `R lim(K)` is a derived limit, while the actual owner remains the canonical
  Chapter `13` predicate `IsDerivedLimit` applied to the chapter owner
  `stagewiseAbelianGroupDerivedTower K`;
- primitive data: only the object `K : D(\operatorname{Ab}(\mathbf N))`;
- derived API: the stagewise tower `stagewiseAbelianGroupDerivedTower K` and the chosen derived
  inverse-limit object `R lim(K)`.

Source/core/bridge triage:
- `source-facing`: the specialization of the Stacks Project statement to
  `K ∈ D(\operatorname{Ab}(\mathbf N))`;
- `core/canonical`: `IsDerivedLimit`;
- `bridge/view`: `stagewiseAbelianGroupDerivedTower`. -/

-- Proof sketch: choose a representing inverse system of cochain complexes for `K`, evaluate it
-- stagewise to obtain the tower `(K_n^\bullet)_n` in `D(Ab)`, and apply the Milnor
-- distinguished-triangle formalism of Definition 13.34.1. The chosen right derived inverse-limit
-- functor from Lemma 15.87.1 identifies its value on `K` with the resulting derived limit object.
/-- Lemma 15.87.9: for `K ∈ D(\operatorname{Ab}(\mathbf N))`, the chosen object `R lim(K)` is a
derived limit of the inverse system `(K_n^\bullet)_n` in `D(\operatorname{Ab})` obtained by
evaluating `K` stagewise. Equivalently, `R lim(K)` fits into the canonical Milnor distinguished
triangle `R lim(K) ⟶ \prod_n K_n^\bullet ⟶ \prod_n K_n^\bullet ⟶ R lim(K)[1]`. -/
theorem abelianGroupDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
    (K : DAbSeq) :
    IsDerivedLimit (stagewiseAbelianGroupDerivedTower K) (R lim(K)) := sorry

/-! ### Lemma_15_87_10 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem

noncomputable section

namespace CategoryTheory

/- Domain-style sampling for Lemma 15.87.10:
- primary domain: Milnor short exact sequences for sequential derived limits in derived categories
  of abelian categories;
- sampled owner declarations:
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: the source-facing theorem should remain the Milnor short exact sequence
  for a chosen `IsDerivedLimit`, while the left term is canonically owned by
  `SequentialInverseSystem.firstDerivedLimit` on the tower of cohomology objects;
- primitive data: an abelian category `C` with countable products, the tower `Ksys`, the chosen
  derived-limit object `Klim`, and the witness `hKlim : IsDerivedLimit Ksys Klim`;
- derived API: the cohomology tower `Ksys ⋙ H p` and its owner-level Milnor term
  `(Ksys ⋙ H (p - 1)).firstDerivedLimit`.

Source/core/bridge triage:
- `source-facing`: the Milnor short exact sequence in degree `p`;
- `core/canonical`: `IsDerivedLimit`, `derivedLimitDifferenceMap`, and
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: the explicit cokernel presentation already packaged by
  `SequentialInverseSystem.firstDerivedLimit`. -/

section

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [HasCountableProducts C] [HasLimitsOfShape ℕᵒᵖ C]

local notation "DC" => DerivedCategory C
local notation "H" => DerivedCategory.homologyFunctor C

-- Proof sketch: start from the Milnor distinguished triangle defining `hKlim`, apply the
-- cohomology functor `H^p`, and read the relevant three-term segment of the resulting long exact
-- sequence. In any abelian category with countable products, the kernel of the Milnor difference
-- map is `lim_n H^p(K_n^•)` and its cokernel is the standard model for
-- `R^1 lim_n H^{p-1}(K_n^•)`.
/-- Lemma 15.87.10: if `Klim` is the chosen derived limit of a sequential inverse system
`(K_n^\bullet)_n` in `D(C)`, then the long exact cohomology sequence of the associated
distinguished triangle breaks into a short exact sequence
`0 \to R^1 \!\varprojlim_n H^{p-1}(K_n^\bullet) \to H^p(Klim) \to
\varprojlim_n H^p(K_n^\bullet) \to 0`, canonically realized as
`(Ksys ⋙ H (p - 1)).firstDerivedLimit`. -/
theorem derivedLimit_cohomology_shortExact
    (Ksys : SequentialInverseSystem DC) (Klim : DC) (hKlim : IsDerivedLimit Ksys Klim) (p : ℤ) :
    ∃ (ι : SequentialInverseSystem.firstDerivedLimit (Ksys ⋙ H (p - 1)) ⟶ (H p).obj Klim)
      (π : (H p).obj Klim ⟶ limit (Ksys ⋙ H p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end

end CategoryTheory

/-! ### Lemma_15_87_11 (from Chap15) -/
noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 15.87.11 in the sequential derived inverse-system domain:
- sampled chapter owner declarations:
  * `stagewiseAbelianGroupDerivedEvaluation`
  * `stagewiseAbelianGroupDerivedTower`
  * `stagewiseAbelianGroupDerivedTowerFunctor`
  * `Functor.EssSurj`
- source/core/bridge triage:
  * `source-facing`: a tower `(K_n)` in `D(Ab)`
  * `core/canonical`: essential surjectivity of
    `stagewiseAbelianGroupDerivedTowerFunctor : D(Ab(\mathbf N)) ⥤ \mathbf N^{op} ⥤ D(Ab)`
  * `bridge/view`: the objectwise existence statement for a fixed tower `K`

The primitive data of the present item are only the tower `K`. The stagewise tower functor is
already provided by the upstream owner file `15_87_1_1`, and objectwise existence up to
isomorphism is canonically owned by `Functor.EssSurj`. The public statement should therefore live
at that owner level rather than as a parallel existential wrapper.
-/
-- Proof sketch: Lemma 15.87.11 says exactly that every tower `K` of objects of `D(Ab)` is
-- isomorphic to one in the image of the stagewise evaluation functor from `D(Ab(\mathbf N))`.
/-- Lemma 15.87.11: the stagewise evaluation functor from `D(\operatorname{Ab}(\mathbf N))` to
sequential inverse systems in `D(\operatorname{Ab})` is essentially surjective. -/
theorem stagewiseAbelianGroupDerivedTowerFunctor_essSurj :
    (stagewiseAbelianGroupDerivedTowerFunctor).EssSurj := sorry

end

end CategoryTheory

/-! ### Remark_15_87_12 (from Chap15) -/
/-
Domain-style sampling:
- primary domain: Milnor short exact sequences for sequential derived limits in `D(Ab)`;
- sampled owner API:
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`;
- best owner abstraction: the source-facing content of this remark is already exactly the
  canonical theorem `CategoryTheory.derivedLimit_cohomology_shortExact`, with no extra
  source-defined data beyond a chosen derived-limit witness;
- source/core/bridge triage:
  `source-facing`: the Milnor short exact sequence for the chosen derived limit of a sequential
  tower in `D(\operatorname{Ab})`;
  `core/canonical`: `IsDerivedLimit`, `SequentialInverseSystem.firstDerivedLimit`, and the owner
  theorem `CategoryTheory.derivedLimit_cohomology_shortExact`;
  `bridge/view`: none in this file.

Primitive data are only the tower `(K_n)`, the chosen derived limit `K`, the witness that `K` is
a derived limit of the tower, and the cohomological degree `p`. Since the displayed short exact
sequence is already formalized upstream with exactly that interface, this file should recall the
canonical owner directly rather than introduce a parallel local theorem or compatibility wrapper.
-/

/- Remark 15.87.12: for a sequential inverse system `(K_n)` in `D(\operatorname{Ab})` with chosen
derived limit `K`, the canonical Milnor short exact sequence
`0 \to R^1 \!\varprojlim H^{p-1}(K_n) \to H^p(K) \to \varprojlim H^p(K_n) \to 0`
is already formalized by `CategoryTheory.derivedLimit_cohomology_shortExact`. This is the
concrete formal content retained from the remark; the preceding discussion about independence of
the lift
`M ∈ D(\operatorname{Ab}(\mathbf N))` explains why Lemma 15.87.10 applies to an arbitrary derived
limit of the tower. -/
recall CategoryTheory.derivedLimit_cohomology_shortExact

/-! ### Lemma_15_87_13 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SequentialProObjectMorphismRep

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat
local notation "DAbSeq" => DerivedCategory AbSeq

/- Domain-style sampling for Lemma 15.87.13:
- primary domain: stagewise towers in `D(Ab)` attached to objects of `D(Ab(\mathbf N))`, viewed as
  sequential pro-objects;
- sampled owner declarations:
  `stagewiseAbelianGroupDerivedTowerFunctor`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `abelianGroupDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`,
  `exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit`;
- best owner abstraction: the pro-object comparison should be owned by the Chapter 4/15 canonical
  representative type `SequentialProObjectMorphismRep` and its pro-morphism
  `(ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)).toProObjectHom`, not by a
  parallel local wrapper;
- primitive data: the stagewise towers
  `stagewiseAbelianGroupDerivedTower E` and `stagewiseAbelianGroupDerivedTower D`;
- derived API: the canonical stagewise tower functor
  `stagewiseAbelianGroupDerivedTowerFunctor`, the strict identity-reindex representative induced by
  `φ`, and the resulting morphism between the associated sequential pro-objects.

Source/core/bridge triage:
- `source-facing`: the theorem that a stagewise pro-isomorphism induces an isomorphism on `R lim`;
- `core/canonical`: `IsDerivedLimit` for the stagewise towers and `SequentialProObjectMorphismRep`
  together with `.toProObjectHom`;
- `bridge/view`: the canonical identity-reindex representative
  `ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)`. -/
-- Proof sketch: Lemma 15.87.9 identifies `R lim(E)` and `R lim(D)` with derived limits of the
-- stagewise towers `(E_n)` and `(D_n)`. Applying the Milnor short exact sequences of
-- Lemma 15.87.10 together with the pro-isomorphism invariance of `\varprojlim` and
-- `R^1 \!\varprojlim` from Lemma 15.87.4 shows that the induced map on every cohomology object is
-- an isomorphism, hence the canonical map on derived inverse limits is an isomorphism in
-- `D(\operatorname{Ab})`.
/-- Lemma 15.87.13: if a morphism `E ⟶ D` in `D(\operatorname{Ab}(\mathbf N))` induces an
isomorphism of the associated stagewise pro-objects `(E_n) ⟶ (D_n)` in
`D(\operatorname{Ab})`, then the induced morphism `R lim(E) ⟶ R lim(D)` is an isomorphism in
`D(\operatorname{Ab})`. -/
theorem isIso_map_derivedInverseLimit_of_stagewise_proIsomorphism
    {E D : DAbSeq} (φ : E ⟶ D)
    (hφ : IsIso (ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)).toProObjectHom) :
    IsIso ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ) := sorry

/-! ### Lemma_15_87_14_Emmanouil (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

namespace SequentialInverseSystem

/- Domain-style sampling for Lemma 15.87.14:
- primary domain: sequential inverse systems of abelian groups, stagewise countable coproducts,
  and the degree-one derived inverse limit;
- sampled owner declarations:
  `SequentialInverseSystem`,
  `SequentialInverseSystem.IsMittagLeffler`,
  `SequentialInverseSystem.countableCoproduct`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.Functor.const`,
  `CategoryTheory.Limits.colim`;
- best owner abstraction: the stagewise countable-coproduct tower is the generic owner
  `SequentialInverseSystem.countableCoproduct` on inverse systems in a category with countable
  coproducts, while the degree-one obstruction is the chapter owner
  `SequentialInverseSystem.firstDerivedLimit`; the Emmanouil criterion is the source-facing
  specialization of those owners to `AddCommGrpCat`;
- primitive-vs-derived split: the primitive data are only an inverse system `A`; the
  countable-coproduct tower and the two `R^1 \!\varprojlim` objects are derived API on that
  owner.

Source/core/bridge triage:
- `source-facing`: Emmanouil's two-clause criterion for one inverse system `A`;
- `core/canonical`: the owners `SequentialInverseSystem`, `SequentialInverseSystem.countableCoproduct`,
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: the countable direct-sum wording in abelian groups for the generic stagewise
  countable-coproduct owner.
-/

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

-- Proof sketch: one direction uses Lemma `15.87.1` to deduce the vanishing of `R^1 lim` from the
-- Mittag-Leffler condition, both for `A` and for the countable direct-sum tower. For the converse,
-- Emmanouil's argument constructs from a failure of the Mittag-Leffler condition a nonzero class
-- in `R^1 lim` of the countable direct-sum tower, forcing the conjunction clause to fail.
/-- Lemma 15.87.14 (Emmanouil): for a sequential inverse system `A` of abelian groups, the
following are equivalent:
`A` is Mittag-Leffler, and both `R^1 \!\varprojlim A` and
`R^1 \!\varprojlim (A.countableCoproduct)` vanish, where `A.countableCoproduct` is the stagewise
countable direct-sum tower. -/
theorem isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
    (A : AbSeq) :
    A.IsMittagLeffler ↔ IsZero A.firstDerivedLimit ∧ IsZero A.countableCoproduct.firstDerivedLimit :=
  sorry

end SequentialInverseSystem

end CategoryTheory
