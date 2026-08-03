module

public import Topology_Munkres_2000.Book.Definition_69_1.Generators
public import Topology_Munkres_2000.Book.Definition_69_6.Relations
import all Topology_Munkres_2000.Book.Definition_69_6.Relations
public import Mathlib.GroupTheory.FinitelyPresentedGroup

public section

universe u v w

namespace QuotientGroup

/-- Helper for Definition 69.7: the first-isomorphism equivalence evaluates a quotient
representative by the original surjective homomorphism. -/
theorem quotientKerEquivOfSurjective_apply_mk {A : Type u} {B : Type v}
    [Group A] [Group B] (f : A →* B) (hf : Function.Surjective f) (x : A) :
    QuotientGroup.quotientKerEquivOfSurjective f hf (QuotientGroup.mk x) = f x := by
  -- The forward map of the first-isomorphism equivalence is the kernel lift.
  exact QuotientGroup.kerLift_mk f x

end QuotientGroup

namespace Group

/-- Definition 69.7. A presentation of a group consists of indexed generators together with
indexed relators that normally generate the kernel of evaluation. -/
structure Presentation (G : Type u) [Group G] (J : Type v) (R : Type w) where
  generators : J → G
  relators : R → FreeGroup J
  generates : Generates generators
  complete :
    FreeGroup.Relations.NormallyGeneratesKernel generators (Set.range relators)

namespace Presentation

variable {G : Type u} [Group G] {J : Type v} {R : Type w}

/-- A consequence of Definition 69.7: the chosen generator family generates the presented
group. -/
theorem closure_range_generators (p : Presentation G J R) :
    Subgroup.closure (Set.range p.generators) = ⊤ :=
  (generates_iff p.generators).1 p.generates

/-- A consequence of Definition 69.7: evaluation from the free group on the chosen generators
is surjective. -/
theorem lift_surjective (p : Presentation G J R) :
    Function.Surjective (FreeGroup.lift p.generators) :=
  (generates_iff_lift_surjective p.generators).1 p.generates

/-- A consequence of Definition 69.7: the generation and completeness conditions defining a
group presentation hold. -/
theorem spec (p : Presentation G J R) :
    Generates p.generators ∧
      FreeGroup.Relations.NormallyGeneratesKernel
        p.generators (Set.range p.relators) :=
  ⟨p.generates, p.complete⟩

/-- A consequence of Definition 69.7: every indexed relator of a presentation lies in the
kernel of evaluation. -/
theorem relation_mem_ker (p : Presentation G J R) (i : R) :
    p.relators i ∈ (FreeGroup.lift p.generators).ker := by
  -- Apply the global completeness invariant to this member of the relator range.
  exact FreeGroup.Relations.subset_ker p.complete (Set.mem_range_self i)

/-- Helper for Definition 69.7: completeness identifies the evaluation-kernel quotient with the
quotient by the normal closure of the indexed relators. -/
def normalClosureQuotientEquiv (p : Presentation G J R) :
    (FreeGroup J ⧸ (FreeGroup.lift p.generators).ker) ≃*
      PresentedGroup (Set.range p.relators) :=
  QuotientGroup.quotientMulEquivOfEq p.complete.symm

/-- Helper for Definition 69.7: the quotient-change equivalence preserves every canonical
free-group representative. -/
theorem normalClosureQuotientEquiv_apply_mk (p : Presentation G J R) (x : FreeGroup J) :
    p.normalClosureQuotientEquiv
        (QuotientGroup.mk x : FreeGroup J ⧸ (FreeGroup.lift p.generators).ker) =
      PresentedGroup.mk (Set.range p.relators) x := by
  -- Use the quotient equivalence's representative computation rule directly.
  exact QuotientGroup.quotientMulEquivOfEq_mk p.complete.symm x

/-- Helper for Definition 69.7: the inverse quotient-change equivalence preserves a canonical
free generator representative. -/
theorem normalClosureQuotientEquiv_symm_apply_of (p : Presentation G J R) (j : J) :
    p.normalClosureQuotientEquiv.symm (PresentedGroup.of j) =
      (QuotientGroup.mk (FreeGroup.of j) :
        FreeGroup J ⧸ (FreeGroup.lift p.generators).ker) := by
  -- Apply the forward equivalence so both sides are canonical quotient representatives.
  apply p.normalClosureQuotientEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  -- The forward computation rule identifies their common free-group representative.
  exact (p.normalClosureQuotientEquiv_apply_mk (FreeGroup.of j)).symm

/-- A consequence of Definition 69.7: the group specified by a presentation is multiplicatively
equivalent to the quotient by the normal closure of its indexed relators. -/
noncomputable def mulEquivPresentedGroup (p : Presentation G J R) :
    G ≃* PresentedGroup (Set.range p.relators) :=
  -- First identify `G` with the evaluation-kernel quotient, then change the quotient subgroup.
  (QuotientGroup.quotientKerEquivOfSurjective
      (FreeGroup.lift p.generators) p.lift_surjective).symm.trans
    p.normalClosureQuotientEquiv

/-- A consequence of Definition 69.7: the presentation equivalence sends each chosen generator
to its presented-group generator. -/
theorem mulEquivPresentedGroup_apply_generator (p : Presentation G J R) (j : J) :
    p.mulEquivPresentedGroup (p.generators j) = PresentedGroup.of j := by
  -- Compare the two elements after returning through the presentation equivalence.
  apply p.mulEquivPresentedGroup.symm.injective
  rw [p.mulEquivPresentedGroup.symm_apply_apply]
  -- The quotient interface exposes the representative, which the first isomorphism evaluates.
  rw [mulEquivPresentedGroup, MulEquiv.symm_trans_apply,
    normalClosureQuotientEquiv_symm_apply_of,
    MulEquiv.symm_symm, QuotientGroup.quotientKerEquivOfSurjective_apply_mk,
    FreeGroup.lift_apply_of]

/-- A consequence of Definition 69.7: a presentation with a finite generator index type makes
the group finitely generated. -/
theorem fg (p : Presentation G J R) [Finite J] : Group.FG G :=
  p.generates.fg

/-- A consequence of Definition 69.7: a presentation with finite generator and relator index
types makes the group finitely presented. -/
theorem isFinitelyPresented (p : Presentation G J R) [Finite J] [Finite R] :
    Group.IsFinitelyPresented G := by
  -- The relator range is finite, so the canonical presented group has mathlib's instance.
  -- Transport that finite presentation back along the canonical equivalence.
  exact Group.IsFinitelyPresented.equiv p.mulEquivPresentedGroup.symm

end Presentation

end Group

namespace PresentedGroup

variable {J : Type u}

/-- Helper for Definition 69.7: the canonical generators generate a presented group. -/
theorem canonicalGeneratorsGenerate (rels : Set (FreeGroup J)) :
    Group.Generates (PresentedGroup.of : J → PresentedGroup rels) := by
  -- Express generation through subgroup closure and use the canonical closure theorem.
  exact (Group.generates_iff PresentedGroup.of).2 (PresentedGroup.closure_range_of rels)

/-- A canonical instance of Definition 69.7: the presentation of `PresentedGroup rels` by its
generators and defining relators. -/
def presentation (rels : Set (FreeGroup J)) :
    Group.Presentation (PresentedGroup rels) J rels where
  generators := PresentedGroup.of
  relators := Subtype.val
  -- The canonical quotient generators span the whole presented group.
  generates := PresentedGroup.canonicalGeneratorsGenerate rels
  -- Indexing the relation set by its subtype has exactly the original relation range.
  complete := Subtype.range_val.symm ▸ PresentedGroup.normallyGeneratesKernel rels

end PresentedGroup
