import Mathlib
import StacksProject_2024.Chap20.Lemma_20_9_3

open CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Definition 20.23.2:
- primary domain: ordered Čech cochain complexes for abelian presheaves on a family of opens;
- sampled owner API:
  `CategoryTheory.cechComplexFunctor`,
  `Limits.FormalCoproduct.cochainComplexFunctor`,
  `AlgebraicTopology.AlternatingCofaceMapComplex.objD`,
  `CochainComplex.of`;
- best owner abstraction for this item: the explicit-order ordered Čech complex
  `orderedCechComplexOfOrder o 𝒰 F`, with the ambient-order specialization
  `orderedCechComplex 𝒰 F` as the source-facing surface.

Source/core/bridge triage:
- `source-facing`: the ordered Čech complex attached to a linearly ordered index set;
- `core/canonical`: the explicit-order owner `orderedCechComplexOfOrder o 𝒰 F`;
- `bridge/view`: specialization along the ambient instance `[LinearOrder ι]`.

Primitive data versus derived API:
- primitive data: a total order `o` on the index type, the family `𝒰`, and the presheaf `F`;
- derived API: ordered Čech terms, restrictions, differentials, and the full complex. -/

/-- A degree-`p` ordered Čech index for the explicit linear order `o` on the index set. -/
abbrev OrderedCechIndex (o : LinearOrder ι) (p : ℕ) :=
  letI := o
  {σ : Fin (p + 1) → ι // StrictMono σ}

/-- The order-embedding view of an ordered Čech index. -/
def orderedCechIndexOrderEmbedding (o : LinearOrder ι) {p : ℕ} (σ : OrderedCechIndex o p) :
    Fin (p + 1) ↪o ι :=
  letI := o
  OrderEmbedding.ofStrictMono σ.1 σ.2

/-- Omitting one entry from an ordered Čech index again yields an ordered Čech index. -/
abbrev orderedCechIndexSuccAbove (o : LinearOrder ι) {p : ℕ}
    (σ : OrderedCechIndex o (p + 1)) (j : Fin (p + 2)) : OrderedCechIndex o p :=
  letI := o
  ⟨σ.1 ∘ j.succAboveEmb, σ.2.comp (Fin.strictMono_succAbove j)⟩

/-- The degree-`p` term of the ordered Čech complex for the explicit order `o`. -/
abbrev orderedCechTermOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) : AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of
    (∀ σ : OrderedCechIndex o p, F.obj (op (cechIntersection 𝒰 σ.1)))

/-- The restriction map obtained by omitting one index from an ordered Čech tuple. -/
abbrev orderedCechRestrictionOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (σ : OrderedCechIndex o (p + 1)) (j : Fin (p + 2)) :
    F.obj (op (cechIntersection 𝒰 (orderedCechIndexSuccAbove o σ j).1)) ⟶
      F.obj (op (cechIntersection 𝒰 σ.1)) :=
  F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ.1 j)).op

/-- The underlying function of the degree-`p` ordered Čech differential for the order `o`. -/
def orderedCechDifferentialToFunOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o 𝒰 F p → orderedCechTermOfOrder o 𝒰 F (p + 1) :=
  fun s σ ↦
    ∑ j : Fin (p + 2),
      (-1 : ℤ) ^ (j : ℕ) •
        orderedCechRestrictionOfOrder o 𝒰 F σ j (s (orderedCechIndexSuccAbove o σ j))

-- Proof sketch: each summand in the ordered alternating sum is additive in the cochain, and
-- finite sums preserve additivity.
/-- The ordered Čech differential is additive on cochains. -/
theorem orderedCechDifferentialToFunOfOrder_map_add (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : orderedCechTermOfOrder o 𝒰 F p) :
    orderedCechDifferentialToFunOfOrder o 𝒰 F p (s + t) =
      orderedCechDifferentialToFunOfOrder o 𝒰 F p s +
        orderedCechDifferentialToFunOfOrder o 𝒰 F p t := sorry

/-- The degree-`p` differential in the ordered Čech complex for the order `o`. -/
abbrev orderedCechDifferentialOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o 𝒰 F p ⟶ orderedCechTermOfOrder o 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (orderedCechDifferentialToFunOfOrder o 𝒰 F p)
      (orderedCechDifferentialToFunOfOrder_map_add o 𝒰 F p))

-- Proof sketch: the ordered differential satisfies the same alternating-face cancellation as the
-- ordinary Čech differential, now restricted to strictly increasing tuples.
/-- Two successive ordered Čech differentials compose to zero. -/
theorem orderedCechDifferentialOfOrder_comp (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechDifferentialOfOrder o 𝒰 F p ≫ orderedCechDifferentialOfOrder o 𝒰 F (p + 1) = 0 :=
  sorry

/-- The ordered Čech complex attached to the explicit order `o` on the index set. -/
def orderedCechComplexOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) : CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.of (orderedCechTermOfOrder o 𝒰 F) (orderedCechDifferentialOfOrder o 𝒰 F)
    (orderedCechDifferentialOfOrder_comp o 𝒰 F)

section

variable [LinearOrder ι]

/-- A degree-`p` ordered Čech index for the ambient linear order on `ι`. -/
abbrev StrictCechTuple (p : ℕ) :=
  OrderedCechIndex inferInstance p

/-- Omitting one entry from a strictly increasing Čech tuple again yields a strictly increasing
tuple. -/
abbrev strictCechTupleSuccAbove {p : ℕ} (σ : StrictCechTuple (p + 1))
    (j : Fin (p + 2)) : StrictCechTuple p :=
  orderedCechIndexSuccAbove inferInstance σ j

/-- The degree-`p` term of the ordered Čech complex for the ambient linear order. -/
abbrev orderedCechTerm (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  orderedCechTermOfOrder inferInstance 𝒰 F p

/-- The restriction map in the ordered Čech complex for the ambient linear order. -/
abbrev orderedCechRestriction (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (σ : StrictCechTuple (p + 1)) (j : Fin (p + 2)) :
    F.obj (op (cechIntersection 𝒰 (strictCechTupleSuccAbove σ j).1)) ⟶
      F.obj (op (cechIntersection 𝒰 σ.1)) :=
  orderedCechRestrictionOfOrder inferInstance 𝒰 F σ j

/-- The underlying function of the ordered Čech differential for the ambient linear order. -/
abbrev orderedCechDifferentialToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTerm 𝒰 F p → orderedCechTerm 𝒰 F (p + 1) :=
  orderedCechDifferentialToFunOfOrder inferInstance 𝒰 F p

/-- The degree-`p` ordered Čech differential for the ambient linear order. -/
abbrev orderedCechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTerm 𝒰 F p ⟶ orderedCechTerm 𝒰 F (p + 1) :=
  orderedCechDifferentialOfOrder inferInstance 𝒰 F p

/-- Two successive ordered Čech differentials compose to zero. -/
theorem orderedCechDifferential_comp_orderedCechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechDifferential 𝒰 F p ≫ orderedCechDifferential 𝒰 F (p + 1) = 0 :=
  orderedCechDifferentialOfOrder_comp inferInstance 𝒰 F p

/-- The ordered Čech complex attached to the ambient linear order on the index set. -/
abbrev orderedCechComplex (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  orderedCechComplexOfOrder inferInstance 𝒰 F

/-- The degree-`p` object of the ordered Čech complex is the ordered Čech term in degree `p`. -/
theorem orderedCechComplex_X (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplex 𝒰 F).X p = orderedCechTerm 𝒰 F p :=
  rfl

end

end
