import StacksProject_2024.stacks_project.Chap21.Definition_21_13_4
import StacksProject_2024.stacks_project.Chap21.Lemma_21_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped CategoryTheory.Sheaf
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable [HasSheafify J (Type (max u v))]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

/- Domain-style sampling for Lemma 21.13.5:
- primary domain: total acyclicity of abelian sheaves on a site, decomposed into objectwise
  vanishing and exactness of the extended Čech complex on `H^0(-, F)` for locally surjective
  morphisms of sheaves of sets;
- sampled owner declarations:
  `IsTotallyAcyclicOne`,
  `Sheaf.H'`,
  `Arrow.cechNerve`,
  `Arrow.augmentedCechNerve`,
  `composeAndSheafify`,
  `preadditiveYoneda.obj`,
  `AlgebraicTopology.alternatingCofaceMapComplex`,
  `CochainComplex.fromSingle₀AsComplex`,
  `exists_cechSpectralSequence_of_isLocallySurjective`;
- best owner abstraction:
  `source-facing`: the theorem below, with the objectwise vanishing clause stated directly via the
    canonical owner `F.H'` and the Čech exactness clause stated directly via the canonical
    extended Čech complex on the represented degree-zero cohomology functor `K ↦ H^0(K, F)`;
  `core/canonical`: `IsTotallyAcyclicOne`, `Sheaf.H'`, `Arrow.cechNerve`,
    `Arrow.augmentedCechNerve`, `composeAndSheafify`, `preadditiveYoneda.obj`,
    `AlgebraicTopology.alternatingCofaceMapComplex`, `CochainComplex.fromSingle₀AsComplex`, and
    `exists_cechSpectralSequence_of_isLocallySurjective`;
  `bridge/view`: the canonical augmented Čech complex `extendedCechComplexOnH0 α F` on the
    represented degree-zero cohomology functor, which is the source-facing exactness clause used
    below.

Primitive data versus derived API:
- primitive data: an abelian sheaf `F`, an object `U : C`, and a locally surjective morphism
  `α : K' ⟶ K` of sheaves of sets;
- derived API: the source-facing equivalence theorem below, relating the canonical owner
  `IsTotallyAcyclicOne` to objectwise vanishing plus exactness of the canonical extended Čech
  complex on `H^0(-, F)`.
-/

section ExtendedCechOnH0

/-- The canonical represented degree-zero cohomology functor `K ↦ H^0(K, F)`, formalized by the
degree-zero `Ext` owner `preadditiveYoneda.obj F` after free-abelian sheafification. -/
def h0Functor (F : Sheaf J AddCommGrpCat.{max u v}) :
    (Sheaf J (Type (max u v)))ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (composeAndSheafify J AddCommGrpCat.free).op ⋙ preadditiveYoneda.obj F

/-- The ordinary alternating Čech complex on the represented degree-zero cohomology functor
`K ↦ H^0(K, F)` attached to a morphism `α : K' ⟶ K` of sheaves of sets. -/
def cechComplexOnH0 {K K' : Sheaf J (Type (max u v))} (α : K' ⟶ K)
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max u v}).obj
    ((Arrow.mk α).cechNerve.rightOp ⋙ h0Functor F)

/-- The degree-zero augmentation from `H^0(K, F)` to the ordinary Čech complex on
`K ↦ H^0(K, F)`, given by the canonical pullback map along `α`. This is the degree-zero part of
the augmented Čech nerve of `α` after applying the represented `H^0(-, F)` functor. -/
def extendedCechComplexOnH0AugmentationMap {K K' : Sheaf J (Type (max u v))}
    (α : K' ⟶ K) (F : Sheaf J AddCommGrpCat.{max u v}) :
    (h0Functor F).obj (op K) ⟶ (cechComplexOnH0 α F).X 0 :=
  (h0Functor F).map (((Arrow.mk α).augmentedCechNerve.hom.app (op (SimplexCategory.mk 0))).op)

-- Proof sketch: the augmentation is induced by the augmented Čech nerve, so after passing to the
-- represented `H^0(-, F)` functor its composite with the first Čech differential is the usual
-- alternating sum of two identical pullbacks and vanishes.
/-- The canonical degree-zero augmentation on `H^0(-, F)` is a cocycle in the ordinary Čech
complex. -/
theorem extendedCechComplexOnH0AugmentationMap_comp_d_zero_one
    {K K' : Sheaf J (Type (max u v))} (α : K' ⟶ K) (F : Sheaf J AddCommGrpCat.{max u v}) :
    extendedCechComplexOnH0AugmentationMap α F ≫ (cechComplexOnH0 α F).d 0 1 = 0 := by
  sorry

/-- The augmentation from `H^0(K, F)` to the ordinary Čech complex on `K ↦ H^0(K, F)`, viewed as
a morphism from a single-term complex in degree `0`. -/
def extendedCechComplexOnH0Augmentation {K K' : Sheaf J (Type (max u v))}
    (α : K' ⟶ K) (F : Sheaf J AddCommGrpCat.{max u v}) :
    (CochainComplex.single₀ AddCommGrpCat.{max u v}).obj ((h0Functor F).obj (op K)) ⟶
      cechComplexOnH0 α F where
  f n := by
    cases n with
    | zero =>
        exact extendedCechComplexOnH0AugmentationMap α F
    | succ _ =>
        exact 0
  comm' i j hij := by
    cases i with
    | zero =>
        cases j with
        | zero =>
            cases hij
        | succ j =>
            cases j with
            | zero =>
                simpa using extendedCechComplexOnH0AugmentationMap_comp_d_zero_one α F
            | succ _ =>
                simp
    | succ _ =>
        simp

/-- The extended Čech complex on the degree-zero cohomology functor `K ↦ H^0(K, F)` attached to a
morphism `α : K' ⟶ K`, obtained by adjoining the canonical augmentation in degree `0`. In the
source-facing criterion below, this complex is applied to locally surjective `α`. -/
def extendedCechComplexOnH0 {K K' : Sheaf J (Type (max u v))} (α : K' ⟶ K)
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.fromSingle₀AsComplex (cechComplexOnH0 α F) ((h0Functor F).obj (op K))
    (extendedCechComplexOnH0Augmentation α F)

end ExtendedCechOnH0

-- Lemma `21.13.2` supplies the surrounding Čech-spectral-sequence context for locally surjective
-- morphisms, but it does not itself force exactness of the augmented degree-zero Čech complex for
-- an arbitrary abelian sheaf `F`. The source-facing criterion below therefore keeps the exactness
-- of `extendedCechComplexOnH0 α F` as an explicit condition rather than packaging it as a
-- separate automatic bridge theorem.
section ProofRoute

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

-- Proof sketch: for the forward implication, apply total acyclicity to the representable sheaves
-- `h_U^#` and to the Čech nerve levels of a locally surjective map of sheaves, then combine the
-- resulting vanishing with the Čech-spectral-sequence formalism of Lemma `21.13.2` to recover the
-- explicit exactness condition on `extendedCechComplexOnH0 α F`. For the converse, start
-- from a locally surjective resolution of an arbitrary sheaf of sets by coproducts of
-- representables and repeat the source induction on the cohomological degree, using the
-- vanishing on objects and the exactness of the canonical extended Čech complex on `H^0(-, F)` to
-- force
-- all relevant higher cohomology groups to vanish.
--
-- As in nearby Chapter 21 owners such as `Lemma_21_14_1` and `Lemma_21_37_4`,
-- `[J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]` is a proof-route hypothesis rather than
-- source-facing input data, so it is omitted from the exported theorem surface.
omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Lemma 21.13.5: an abelian sheaf `F` on a site is totally acyclic if and only if all higher
cohomology groups `H^p(U, F)` vanish for every object `U` of the site and, for every surjective
morphism of sheaves of sets, the extended Čech complex on `H^0(-, F)` is exact. The Čech
exactness clause is formalized here by vanishing of the homology of the canonical extended Čech
complex `extendedCechComplexOnH0 α F`; Lemma `21.13.2` provides only the surrounding
spectral-sequence context for this criterion and does not by itself imply the exactness clause. -/
@[stacks 07A1]
theorem isTotallyAcyclicOne_iff_objectwiseHigherCohomologyVanishes_and_exactExtendedCechComplex
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    IsTotallyAcyclicOne F ↔
      (∀ (U : C) (n : ℕ), IsZero (F.H' (n + 1) U)) ∧
      ∀ ⦃K K' : Sheaf J (Type (max u v))⦄ (α : K' ⟶ K)
        (hα : Sheaf.IsLocallySurjective α) (p : ℕ),
        IsZero ((extendedCechComplexOnH0 α F).homology p) := by
  sorry

end ProofRoute

end Sheaf
end CategoryTheory
