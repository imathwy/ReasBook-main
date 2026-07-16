import StacksProject_2024.stacks_project.Chap07.Remark_7_17_9
import StacksProject_2024.stacks_project.Chap21.Lemma_21_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Remark 21.16.3:
- primary domain: finite coproduct test sets of sheafified representables used to control filtered
  colimits in sheaf cohomology on a site;
- sampled owner declarations:
  `J.sheafifiedRepresentable`,
  `FiniteSheafifiedRepresentableCoproductsFrom`,
  `HasFiniteRefinementBasisQuasiCompactProducts`,
  `IsCohomologyColimitTestSet`;
- best owner abstraction: the Chapter 7 owner
  `FiniteSheafifiedRepresentableCoproductsFrom J B`, with the basis data already organized by
  `HasFiniteRefinementBasisQuasiCompactProducts`;
- primitive data here: the basis `B` together with the extra equalizer-cover condition needed in
  addition to the Chapter 7 terminal/refinement/product data;
- derived API: the resulting Chapter 21 cohomology-colimit test set.

Source/core/bridge triage:
- `source-facing`: `HasFiniteSheafifiedRepresentableCohomologyBasis`;
- `core/canonical`: `FiniteSheafifiedRepresentableCoproductsFrom` and
  `HasFiniteRefinementBasisQuasiCompactProducts`;
- `bridge/view`: the theorem below showing that this canonical finite-coproduct set satisfies
  `IsCohomologyColimitTestSet`.
-/

/-- A subset `B` of objects of a site satisfies the finite sheafified-representable basis
criterion from Remark `21.16.3` if it has the Chapter 7 finite-refinement basis data and, in
addition, finite coproducts of sheafified representables from `B` locally surject onto the
equalizers of maps between sheafified representables attached to objects of `B`. -/
@[mk_iff hasFiniteSheafifiedRepresentableCohomologyBasis_iff]
class HasFiniteSheafifiedRepresentableCohomologyBasis (B : Set C) : Prop
    extends HasFiniteRefinementBasisQuasiCompactProducts J B where
  surjective_equalizer :
    ∀ ⦃U U' : C⦄ (a b : U ⟶ U'), U ∈ B → U' ∈ B →
      ∃ K : Sheaf J (Type (max u v)), K ∈ FiniteSheafifiedRepresentableCoproductsFrom J B ∧
        ∃ π : K ⟶ equalizer (J.sheafifiedRepresentableMap a) (J.sheafifiedRepresentableMap b),
          Sheaf.IsLocallySurjective π

-- Proof sketch: reuse the Chapter 7 owner
-- `FiniteSheafifiedRepresentableCoproductsFrom J B` and the terminal/refinement/product data
-- already packaged by `HasFiniteRefinementBasisQuasiCompactProducts`. The only extra source-facing
-- input needed here is the equalizer-surjection clause above. As in the remark, cover refinement
-- upgrades locally surjective maps onto finite coproducts of sheafified representables by
-- refining over each summand, and the finite-refinement basis hypothesis supplies the
-- quasi-compactness input for those coproducts.
/-- Remark 21.16.3: if a subset `B` of objects of a site satisfies the finite cover-refinement,
product, and equalizer conditions from the remark, then the sheaves which are finite coproducts of
sheafified representables `h_U^#` with `U ∈ B` satisfy the hypotheses of Lemma `21.16.2`. -/
@[stacks 0GN4]
instance instIsCohomologyColimitTestSetFiniteSheafifiedRepresentableCoproductsFrom
    (B : Set C) [HasFiniteSheafifiedRepresentableCohomologyBasis J B] :
    IsCohomologyColimitTestSet J (FiniteSheafifiedRepresentableCoproductsFrom J B) := by
  sorry

end CategoryTheory.GrothendieckTopology
