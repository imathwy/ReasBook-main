import StacksProject_2024.stacks_project.Chap20.Lemma_20_9_3

open CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}
variable [LinearOrder ι]

/- Domain-style sampling for Definition 20.23.2:
- primary domain: ordered Čech cochain complexes for abelian presheaves on a family of opens;
- sampled owner API:
  `CategoryTheory.cechComplexFunctor`,
  `Limits.FormalCoproduct.cochainComplexFunctor`,
  `AlgebraicTopology.AlternatingCofaceMapComplex.objD`,
  `CochainComplex.of`;
- best owner abstraction for this item: the ordered Čech complex
  `orderedCechComplex 𝒰 F` for the ambient linear-order instance; explicit choices of order are
  bridge-level instance specializations.

Source/core/bridge triage:
- `source-facing`: the ordered Čech complex attached to a linearly ordered index set;
- `core/canonical`: the instance-parametric owner `orderedCechComplex 𝒰 F`;
- `bridge/view`: explicit instance specialization when comparing different linear orders.

Primitive data versus derived API:
- primitive data: the ambient total-order instance on the index type, the family `𝒰`, and the presheaf `F`;
- derived API: ordered Čech terms, restrictions, differentials, and the full complex. -/

/-- A degree-`p` ordered Čech index for the ambient linear order on the index set. -/
abbrev OrderedCechIndex (ι : Type v) [LinearOrder ι] (p : ℕ) : Type v :=
  Fin (p + 1) ↪o ι

/-- Short source-facing name for a strictly increasing Čech tuple. -/
abbrev StrictCechTuple (p : ℕ) :=
  OrderedCechIndex ι p

namespace OrderedCechIndex

/-- Delete the `j`th entry of a strictly increasing Čech tuple. -/
def delete {p : ℕ} (σ : OrderedCechIndex ι (p + 1)) (j : Fin (p + 2)) :
    OrderedCechIndex ι p :=
  OrderEmbedding.ofStrictMono (σ ∘ j.succAboveEmb)
    (fun _ _ hab ↦ σ.strictMono (Fin.strictMono_succAbove j hab))

@[simp] theorem coe_delete {p : ℕ} (σ : OrderedCechIndex ι (p + 1)) (j : Fin (p + 2)) :
    ⇑(σ.delete j) = σ ∘ j.succAboveEmb :=
  rfl

end OrderedCechIndex

/-- The degree-`p` term of the ordered Čech complex. -/
private abbrev orderedCechTerm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) : AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of ((σ : OrderedCechIndex ι p) → F.obj (op (cechIntersection 𝒰 σ)))

/-- Regard an ordered Čech cochain as an ordinary Čech cochain by extending it by zero on
non-strict tuples. -/
private def orderedCechToCechCochain (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTerm 𝒰 F p → cechTerm 𝒰 F p :=
  fun s τ ↦
    if hτ : StrictMono τ then
      s (OrderEmbedding.ofStrictMono τ hτ)
    else
      0

/-- Evaluating the zero-extended ordered cochain on a deleted strict tuple recovers the original
ordered value. -/
private theorem orderedCechToCechCochain_apply_deleteTuple
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : orderedCechTerm 𝒰 F p) (σ : OrderedCechIndex ι (p + 1)) (j : Fin (p + 2)) :
    orderedCechToCechCochain 𝒰 F p s (σ ∘ j.succAboveEmb) = s (σ.delete j) := by
  let hτ : StrictMono (σ ∘ j.succAboveEmb) := fun a b hab ↦
    σ.strictMono (Fin.strictMono_succAbove j hab)
  rw [orderedCechToCechCochain, dif_pos hτ]
  simp [OrderedCechIndex.delete]

/-- The `j`th ordered Čech coface map. -/
private abbrev orderedCechCoface (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (j : Fin (p + 2)) :
    orderedCechTerm 𝒰 F p ⟶ orderedCechTerm 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun s σ ↦ cechRestriction 𝒰 F σ j (s (σ.delete j)))
      (fun s t ↦ by
        funext σ
        exact (ConcreteCategory.hom (cechRestriction 𝒰 F σ j)).map_add
          (s (σ.delete j))
          (t (σ.delete j)))

/-- The degree-`p` ordered Čech differential is the alternating sum of the ordered coface maps. -/
private abbrev orderedCechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTerm 𝒰 F p ⟶ orderedCechTerm 𝒰 F (p + 1) :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • orderedCechCoface 𝒰 F p j

/-- The ordered Čech differential is the alternating sum of the ordered restriction maps. -/
private theorem orderedCechDifferential_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : orderedCechTerm 𝒰 F p) (σ : OrderedCechIndex ι (p + 1)) :
    orderedCechDifferential 𝒰 F p s σ =
      ∑ j : Fin (p + 2),
        (-1 : ℤ) ^ (j : ℕ) • cechRestriction 𝒰 F σ j (s (σ.delete j)) := by
  let ev :
      (orderedCechTerm 𝒰 F p ⟶ orderedCechTerm 𝒰 F (p + 1)) →+
        F.obj (op (cechIntersection 𝒰 σ)) :=
    AddMonoidHom.mk' (fun f ↦ f s σ) (fun _ _ ↦ rfl)
  change ev (orderedCechDifferential 𝒰 F p) =
      ∑ j : Fin (p + 2),
        (-1 : ℤ) ^ (j : ℕ) • cechRestriction 𝒰 F σ j (s (σ.delete j))
  rw [show orderedCechDifferential 𝒰 F p =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • orderedCechCoface 𝒰 F p j by
        rfl]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [ev]

/-- On a strictly increasing tuple, the ordinary Čech differential of the zero-extended ordered
cochain is the ordered Čech differential. -/
private theorem cechDifferentialToFun_apply_ordered (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : orderedCechTerm 𝒰 F p) (σ : OrderedCechIndex ι (p + 1)) :
    cechDifferentialToFun 𝒰 F p (orderedCechToCechCochain 𝒰 F p s) σ =
      orderedCechDifferential 𝒰 F p s σ := by
  rw [cechDifferentialToFun]
  rw [orderedCechDifferential_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [orderedCechToCechCochain_apply_deleteTuple]

/-- Two successive ordered Čech differentials compose to zero. -/
private theorem orderedCechDifferential_comp (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechDifferential 𝒰 F p ≫ orderedCechDifferential 𝒰 F (p + 1) = 0 :=
  by
    ext s σ
    have hzero :
        cechDifferentialToFun 𝒰 F (p + 1)
            (cechDifferentialToFun 𝒰 F p (orderedCechToCechCochain 𝒰 F p s)) σ =
          0 := by
      have hcomp := congrArg
          (fun f ↦ f (orderedCechToCechCochain 𝒰 F p s))
          (cechDifferential_comp_cechDifferential 𝒰 F p)
      have hcomp' := congrArg (fun t ↦ t σ) hcomp
      simpa [cechDifferential] using hcomp'
    calc
      orderedCechDifferential 𝒰 F (p + 1)
          (orderedCechDifferential 𝒰 F p s) σ =
        cechDifferentialToFun 𝒰 F (p + 1)
          (orderedCechToCechCochain 𝒰 F (p + 1)
            (orderedCechDifferential 𝒰 F p s)) σ := by
              symm
              exact cechDifferentialToFun_apply_ordered 𝒰 F (p + 1)
                (orderedCechDifferential 𝒰 F p s) σ
      _ = cechDifferentialToFun 𝒰 F (p + 1)
            (cechDifferentialToFun 𝒰 F p (orderedCechToCechCochain 𝒰 F p s)) σ := by
              rw [cechDifferentialToFun]
              refine Finset.sum_congr rfl ?_
              intro j _
              have hleft :
                  orderedCechToCechCochain 𝒰 F (p + 1)
                      (orderedCechDifferential 𝒰 F p s) (σ ∘ j.succAboveEmb) =
                    orderedCechDifferential 𝒰 F p s (σ.delete j) := by
                simpa using
                  orderedCechToCechCochain_apply_deleteTuple 𝒰 F (p + 1)
                    (orderedCechDifferential 𝒰 F p s) σ j
              have hright :
                  orderedCechDifferential 𝒰 F p s (σ.delete j) =
                    cechDifferentialToFun 𝒰 F p
                      (orderedCechToCechCochain 𝒰 F p s) (σ ∘ j.succAboveEmb) := by
                simpa using
                  (cechDifferentialToFun_apply_ordered 𝒰 F p s (σ.delete j)).symm
              exact congrArg
                (fun x ↦ (-1 : ℤ) ^ (j : ℕ) • cechRestriction 𝒰 F σ j x)
                (hleft.trans hright)
      _ = 0 := hzero

/-- Definition 20.23.2: the ordered Čech complex attached to the ambient linear order on the
index set. -/
@[stacks 01FI]
def orderedCechComplex (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) : CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.of
    (orderedCechTerm 𝒰 F)
    (orderedCechDifferential 𝒰 F)
    (orderedCechDifferential_comp 𝒰 F)

/-- The degree-`p` term of the ordered Čech complex is the group of cochains on strictly
increasing `p`-tuples. -/
@[simp] theorem orderedCechComplex_X (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplex 𝒰 F).X p =
      AddCommGrpCat.of ((σ : StrictCechTuple p) → F.obj (op (cechIntersection 𝒰 σ))) := rfl

/-- The ordered Čech differential is the usual alternating sum over deleted strictly increasing
tuples. -/
theorem orderedCechComplex_d_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p) (σ : StrictCechTuple (p + 1)) :
    (orderedCechComplex 𝒰 F).d p (p + 1) s σ =
      ∑ j : Fin (p + 2),
        (-1 : ℤ) ^ (j : ℕ) • cechRestriction 𝒰 F σ j (s (σ.delete j)) := by
  rw [show (orderedCechComplex 𝒰 F).d p (p + 1) =
      orderedCechDifferential 𝒰 F p by
        simp [orderedCechComplex]]
  exact orderedCechDifferential_apply 𝒰 F p s σ

/-- The ordered Čech complex for a specified linear order, obtained by choosing that order as the
local instance. This is a bridge for statements comparing two order choices; routine APIs should use
`orderedCechComplex` with `[LinearOrder ι]`. -/
abbrev orderedCechComplexOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) : CochainComplex AddCommGrpCat.{max u v} ℕ :=
  let _ : LinearOrder ι := o
  orderedCechComplex 𝒰 F

section

omit [LinearOrder ι]

variable (o : LinearOrder ι)

local instance : LinearOrder ι := o

/-- The degree-`p` term of the ordered Čech complex for a specified order is the group of cochains
on strictly increasing `p`-tuples for that order. -/
@[simp] theorem orderedCechComplexOfOrder_X (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplexOfOrder o 𝒰 F).X p =
      AddCommGrpCat.of ((σ : StrictCechTuple p) → F.obj (op (cechIntersection 𝒰 σ))) := rfl

/-- The ordered Čech differential for a specified order is the alternating sum over deleted strict
tuples for that order. -/
theorem orderedCechComplexOfOrder_d_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplexOfOrder o 𝒰 F).X p) (σ : StrictCechTuple (p + 1)) :
    (orderedCechComplexOfOrder o 𝒰 F).d p (p + 1) s σ =
      ∑ j : Fin (p + 2),
        (-1 : ℤ) ^ (j : ℕ) • cechRestriction 𝒰 F σ j (s (σ.delete j)) := by
  simpa [orderedCechComplexOfOrder] using orderedCechComplex_d_apply 𝒰 F p s σ

end

end
