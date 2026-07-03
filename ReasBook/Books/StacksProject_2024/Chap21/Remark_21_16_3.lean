import Mathlib
import StacksProject_2024.Chap21.Lemma_21_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe v u

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-- The sheafified representable sheaf `h_U^#` on the site `(C, J)`. -/
abbrev sheafifiedRepresentableSheaf (U : C) : Sheaf J (Type (max u v)) :=
  (presheafToSheaf J (Type (max u v))).obj (CategoryTheory.uliftYoneda.{max u v}.obj U)

/-- A sheaf belongs to the finite representable test set attached to `B` if it is a finite
coproduct of sheafified representables `h_U^#` with `U ∈ B`, exhibited by an explicit coproduct
cocone. -/
def IsFiniteCoproductOfSheafifiedRepresentables (B : Set C)
    (K : Sheaf J (Type (max u v))) : Prop :=
  ∃ n : ℕ, ∃ U : Fin n → C,
    (∀ i, U i ∈ B) ∧
      ∃ ι : (i : Fin n) → sheafifiedRepresentableSheaf J (U i) ⟶ K,
        Nonempty (IsColimit (Cofan.mk K ι))

/-- The set of sheaves on `(C, J)` which are finite coproducts of sheafified representables
`h_U^#` with `U ∈ B`. -/
abbrev finiteSheafifiedRepresentableSet (B : Set C) : Set (Sheaf J (Type (max u v))) :=
  { K | IsFiniteCoproductOfSheafifiedRepresentables J B K }

/-- A subset `B` of objects of a site satisfies the finite sheafified-representable basis criterion
if it provides the terminal-cover, cover-refinement, product, and equalizer data from the remark. -/
class IsFiniteSheafifiedRepresentableCohomologyBasis (B : Set C) : Prop where
  exists_surjective_to_terminal :
    ∃ K : Sheaf J (Type (max u v)), K ∈ finiteSheafifiedRepresentableSet J B ∧
      ∃ π : K ⟶ ⊤_ (Sheaf J (Type (max u v))), Sheaf.IsLocallySurjective π
  refine_cover :
    ∀ ⦃U : C⦄, U ∈ B → ∀ ⦃ι : Type u⦄ (family : ι → Over U),
      (J.over U).CoversTop family →
        ∃ n : ℕ, ∃ cover : Fin n → Over U,
          (∀ i, (cover i).left ∈ B) ∧
          (J.over U).CoversTop cover ∧
          Nonempty (
            ((FormalCoproduct.mk (ULift (Fin n)) (fun i ↦ cover i.down) :
                FormalCoproduct (Over U)) ⟶
              (FormalCoproduct.mk ι family : FormalCoproduct (Over U))))
  surjective_product :
    ∀ ⦃U U' : C⦄, U ∈ B → U' ∈ B →
      ∃ K : Sheaf J (Type (max u v)), K ∈ finiteSheafifiedRepresentableSet J B ∧
        ∃ π : K ⟶ sheafifiedRepresentableSheaf J U ⨯ sheafifiedRepresentableSheaf J U',
          Sheaf.IsLocallySurjective π
  surjective_equalizer :
    ∀ ⦃U U' : C⦄ (a b : U ⟶ U'), U ∈ B → U' ∈ B →
      ∃ K : Sheaf J (Type (max u v)), K ∈ finiteSheafifiedRepresentableSet J B ∧
        ∃ π : K ⟶ equalizer (J.sheafifiedRepresentableMap a) (J.sheafifiedRepresentableMap b),
          Sheaf.IsLocallySurjective π

-- Proof sketch: use the coproduct presentations built into
-- `finiteSheafifiedRepresentableSet J B` together with the four basis hypotheses on `B`. The
-- terminal, product, and equalizer clauses are supplied directly by the corresponding fields of
-- `IsFiniteSheafifiedRepresentableCohomologyBasis`. The cover-refinement clause upgrades any
-- locally surjective map onto a finite coproduct of representables by refining the cover over each
-- summand. Finally, part (2) of the remark makes every `U ∈ B` quasi-compact, and then finite
-- coproducts of the corresponding `h_U^#` are quasi-compact as well.
/-- Remark 21.16.3: if a subset `B` of objects of a site satisfies the finite cover-refinement,
product, and equalizer conditions from the remark, then the sheaves which are finite coproducts of
sheafified representables `h_U^#` with `U ∈ B` satisfy the hypotheses of Lemma `21.16.2`. -/
theorem finiteSheafifiedRepresentableSet_isCohomologyColimitTestSet
    (B : Set C) [IsFiniteSheafifiedRepresentableCohomologyBasis J B] :
    IsCohomologyColimitTestSet J (finiteSheafifiedRepresentableSet J B) := sorry

end CategoryTheory.GrothendieckTopology
