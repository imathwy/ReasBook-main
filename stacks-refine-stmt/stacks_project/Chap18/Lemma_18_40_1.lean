import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap18.Definition_18_40_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 18.40.1:
- primary domain: local surjectivity of morphisms of set-valued sheaves attached to the structure
  sheaf of a ringed site;
- sampled owner declarations:
  `HasLocalUnitDichotomy`,
  `Sheaf.IsLocallySurjective`,
  `GrothendieckTopology.sheafifiedRepresentableCoverMap`,
  `Limits.coprod.desc`,
  `Limits.prod.lift`;
- best owner abstraction: the intrinsic binary factorization morphism in `Sheaf J (Type _)`
  from the coproduct of two copies of `O ⨯ O` to `O ⨯ O`, where `O` is the underlying
  set-valued structure sheaf;
- primitive data: the two component morphisms `O ⨯ O ⟶ O ⨯ O` sending `(f, a)` to `(f, af)` and
  `(f, b)` to `(f, b(1 - f))`;
- derived API: local surjectivity of the canonical coproduct map and its sectionwise
  factorization reformulation.
-/

variable (𝒪 : Sheaf J CommRingCat.{max u v})

private abbrev underlyingTypeSheaf (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  (sheafCompose J (forget CommRingCat)).obj 𝒪

local notation "O" => underlyingTypeSheaf 𝒪

private def binaryFactorizationLeftSecond : O ⨯ O ⟶ O :=
  { hom :=
      { app := fun U x ↦ by
          let a : 𝒪.obj.obj U := (prod.snd : O ⨯ O ⟶ O).hom.app U x
          let f : 𝒪.obj.obj U := (prod.fst : O ⨯ O ⟶ O).hom.app U x
          show 𝒪.obj.obj U
          exact a * f
        naturality := by
          intro U V f
          ext x
          have hsnd : (prod.snd : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.snd : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.snd : O ⨯ O ⟶ O).hom.naturality f) x
          have hfst : (prod.fst : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.fst : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.fst : O ⨯ O ⟶ O).hom.naturality f) x
          dsimp
          rw [hsnd, hfst]
          simp } }

private def binaryFactorizationRightSecond : O ⨯ O ⟶ O :=
  { hom :=
      { app := fun U x ↦ by
          let b : 𝒪.obj.obj U := (prod.snd : O ⨯ O ⟶ O).hom.app U x
          let f : 𝒪.obj.obj U := (prod.fst : O ⨯ O ⟶ O).hom.app U x
          show 𝒪.obj.obj U
          exact b * (1 - f)
        naturality := by
          intro U V f
          ext x
          have hsnd : (prod.snd : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.snd : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.snd : O ⨯ O ⟶ O).hom.naturality f) x
          have hfst : (prod.fst : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.fst : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.fst : O ⨯ O ⟶ O).hom.naturality f) x
          dsimp
          rw [hsnd, hfst]
          simp } }

private def binaryFactorizationLeft : O ⨯ O ⟶ O ⨯ O :=
  prod.lift prod.fst (binaryFactorizationLeftSecond 𝒪)

private def binaryFactorizationRight : O ⨯ O ⟶ O ⨯ O :=
  prod.lift prod.fst (binaryFactorizationRightSecond 𝒪)

local instance binaryFactorizationHasColimit : HasColimit (pair (O ⨯ O) (O ⨯ O)) := by
  let _ : HasColimitsOfShape (Discrete WalkingPair) (Type (max u v)) := inferInstance
  let _ : HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type (max u v))) :=
    (Sheaf.instHasColimitsOfShape :
      HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type (max u v))))
  infer_instance

/-- The binary factorization morphism from Stacks `18.40.1 (3)`, expressed as a morphism of
set-valued sheaves. With `O` the underlying set-valued sheaf of `𝒪`, this is the canonical
morphism `((O ⨯ O) ⨿ (O ⨯ O)) ⟶ (O ⨯ O)` whose left summand sends `(f, a)` to `(f, af)` and
whose right summand sends `(f, b)` to `(f, b(1 - f))`. -/
def binaryFactorizationMap : (O ⨯ O) ⨿ (O ⨯ O) ⟶ O ⨯ O :=
  coprod.desc (binaryFactorizationLeft 𝒪) (binaryFactorizationRight 𝒪)

variable {𝒪}

/-- Unfolding `Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪)` gives the sectionwise local
factorization formula from Stacks `18.40.1 (3)`. This remains companion API, while the main owner
clause is the local surjectivity of the named sheaf morphism. -/
theorem isLocallySurjective_binaryFactorizationMap_iff :
    Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪) ↔
      ∀ (U : C) (f c : 𝒪.obj.obj (op U)),
        ∃ S : J.Cover U, ∀ I : S.Arrow,
          (∃ a : 𝒪.obj.obj (op I.Y),
              (𝒪.obj.map I.f.op).hom c = a * (𝒪.obj.map I.f.op).hom f) ∨
            ∃ b : 𝒪.obj.obj (op I.Y),
              (𝒪.obj.map I.f.op).hom c = b * (1 - (𝒪.obj.map I.f.op).hom f) := sorry

-- Proof sketch: `(1) → (2)` is the induction on the number of generators from the source text.
-- `(2) → (1)` is the singleton case applied to the finite set `{f, 1 - f}`. Clause `(3)` is the
-- owner-level local-surjectivity statement for `binaryFactorizationMap 𝒪`.
/-- Lemma 18.40.1: for a ringed site `(\mathcal C, \mathcal O)`, the local dichotomy that every
section is locally either invertible or complementary-invertible, the local unit-ideal criterion
for finitely many sections, and the local surjectivity of the binary factorization map are
equivalent. -/
theorem ringed_site_local_unit_tfae
    (𝒪 : Sheaf J CommRingCat) :
    List.TFAE [
      HasLocalUnitDichotomy J 𝒪,
      ∀ (U : C) (s : Set (𝒪.obj.obj (op U))), s.Finite → s.Nonempty →
        Ideal.span s = ⊤ →
          ∃ S : J.Cover U, ∀ I : S.Arrow,
            ∃ g ∈ s, IsUnit ((𝒪.obj.map I.f.op).hom g),
      Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪)
    ] := sorry

end CategoryTheory
