import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_1_1 (from Items/Chap02) -/
-- Layer triage:
-- `source-facing`: a group `G`, a type `X` of defining generators, a set `R` of relators in the
-- free group on `X`, and the assertion that `(X; R)` presents `G` via a chosen equivalence
-- `PresentedGroup R ≃* G`.
-- `core/canonical`: `PresentedGroup R`, `PresentedGroup.of`, `PresentedGroup.closure_range_of`,
-- `PresentedGroup.mk_eq_one_iff`, and `Subgroup.normalClosure`.
-- `bridge/view`: the chosen presentation equivalence transports the canonical generators of
-- `PresentedGroup R` to the defining generators in `G`, and `FreeGroup.lift` evaluates words in
-- those generators.
-- Domain sampling:
-- 1. `PresentedGroup R` is mathlib's owner abstraction for a group given by generators `X` and
--    relators `R`.
-- 2. `PresentedGroup.of` is the canonical image of a defining generator in the presented group.
-- 3. `PresentedGroup.closure_range_of` is the canonical statement that these images generate the
--    presented group.
-- 4. `PresentedGroup.mk_eq_one_iff` identifies the consequences of the relators with the normal
--    closure of `R`.
-- Primitive vs. derived:
-- the primitive source data are the generators `X`, the relator set `R`, and the chosen
-- identification `PresentedGroup R ≃* G`; the defining-generator subset of `G` and the
-- relator/consequence equations are derived from that canonical owner-side datum, so no parallel
-- alias for the equivalence is introduced.

variable {G : Type u} [Group G] {X : Type v} {R : Set (FreeGroup X)}

namespace PresentedGroup

/-- A presented group on finitely many generators is finitely generated. -/
instance instFG [Finite X] (R : Set (FreeGroup X)) : Group.FG (PresentedGroup R) := by
  change Group.FG (FreeGroup X ⧸ Subgroup.normalClosure R)
  infer_instance

end PresentedGroup

/- Definition 2-1-1: a presentation of `G` with defining generators `X` and defining relators `R`
is a chosen multiplicative equivalence from the canonical presented group `PresentedGroup R` to
`G`. The file uses the canonical type expression `PresentedGroup R ≃* G` directly rather than
introducing a duplicate alias. -/
#check (PresentedGroup R ≃* G)

namespace GroupPresentation

variable (P : PresentedGroup R ≃* G)

/-- The image in `G` of a defining generator under a chosen presentation. -/
abbrev generatorImage : X → G :=
  fun x ↦ P (PresentedGroup.of x)

private theorem generatorImage_comp_mk :
    P.toMonoidHom.comp (PresentedGroup.mk R) = FreeGroup.lift (generatorImage P) := by
  ext x
  simp [generatorImage, PresentedGroup.of]

-- Proof sketch: transport `PresentedGroup.closure_range_of R` across the presentation equivalence
-- `P`; the image of the canonical generator set is exactly `Set.range (generatorImage P)`, so its
-- subgroup closure is all of `G`.
/-- The images of the defining generators generate the whole group. -/
theorem closure_range_generatorImage_eq_top :
    Subgroup.closure (Set.range (generatorImage P)) = ⊤ := by
  have hmap :
      Subgroup.map P.toMonoidHom
          (Subgroup.closure (Set.range (PresentedGroup.of : X → PresentedGroup R))) =
        Subgroup.closure (Set.range (generatorImage P)) := by
    rw [MonoidHom.map_closure]
    change
      Subgroup.closure
          (P.toMonoidHom '' Set.range (PresentedGroup.of : X → PresentedGroup R)) =
      Subgroup.closure (Set.range (generatorImage P))
    congr 1
    ext g
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨PresentedGroup.of x, ⟨x, rfl⟩, rfl⟩
  calc
    Subgroup.closure (Set.range (generatorImage P)) =
        Subgroup.map P.toMonoidHom
          (Subgroup.closure (Set.range (PresentedGroup.of : X → PresentedGroup R))) := by
            exact hmap.symm
    _ = Subgroup.map P.toMonoidHom ⊤ := by
          rw [PresentedGroup.closure_range_of]
    _ = MonoidHom.range P.toMonoidHom := by
          rw [← MonoidHom.range_eq_map]
    _ = ⊤ := MonoidHom.range_eq_top.2 P.surjective

-- Proof sketch: in `PresentedGroup R`, every relator maps to `1` by
-- `PresentedGroup.one_of_mem`. Apply the presentation equivalence `P` to that equality and
-- identify the resulting evaluation map on `FreeGroup X` with `FreeGroup.lift (generatorImage P)`.
/-- Every defining relator evaluates to the identity in the presented group. -/
theorem relator_eq_one {r : FreeGroup X} (hr : r ∈ R) :
    FreeGroup.lift (generatorImage P) r = 1 := by
  have hmk : PresentedGroup.mk R r = 1 := PresentedGroup.one_of_mem hr
  rw [← generatorImage_comp_mk]
  change P (PresentedGroup.mk R r) = 1
  simpa using congrArg P hmk

-- Proof sketch: membership in `Subgroup.normalClosure R` is equivalent to triviality in
-- `PresentedGroup R` by `PresentedGroup.mk_eq_one_iff`. Apply `P` to that canonical equality and
-- rewrite the resulting map as `FreeGroup.lift (generatorImage P)`.
/-- Every consequence of the defining relators evaluates to the identity in the presented group. -/
theorem consequence_eq_one {w : FreeGroup X}
    (hw : w ∈ Subgroup.normalClosure R) :
    FreeGroup.lift (generatorImage P) w = 1 := by
  have hmk : PresentedGroup.mk R w = 1 := PresentedGroup.mk_eq_one_iff.mpr hw
  rw [← generatorImage_comp_mk]
  change P (PresentedGroup.mk R w) = 1
  simpa using congrArg P hmk

end GroupPresentation

/-! ### Definition_2_1_2 (from Items/Chap02) -/
universe v

-- Layer triage:
-- `source-facing`: a presentation datum consisting of a generator type `X` and a relator set
-- `R : Set (FreeGroup X)`, together with the textbook finiteness terminology for that datum.
-- `core/canonical`: `Finite X` for finiteness of the generator type and `Set.Finite R` for
-- finiteness of the relator set.
-- `bridge/view`: the textbook phrase "finite presentation" is exactly the conjunction of these
-- two owner predicates.
-- Domain sampling:
-- 1. `PresentedGroup R` is mathlib's owner abstraction for generators-and-relations data from
--    Definition `2-1-1`, but the present item adds only finiteness conditions on the source data.
-- 2. `Finite X` is the canonical finiteness predicate for a type of generators.
-- 3. `Set.Finite R` is the canonical finiteness predicate for a relator set.
-- Primitive vs. derived:
-- the primitive source data are only `X` and `R`; the three textbook finiteness phrases below are
-- direct uses of the owner predicates above, so the file keeps the raw canonical predicates
-- `Finite X` and `Set.Finite R` rather than introducing parallel names such as
-- `GroupPresentation.IsFinitelyGenerated` or `GroupPresentation.IsFinitelyRelated`.

namespace GroupPresentation

variable {X : Type v} {R : Set (FreeGroup X)}

/- Definition 2-1-2 (1): a presentation is finitely generated exactly when its generator type is
finite. -/
#check (Finite X)

/- Definition 2-1-2 (2): a presentation is finitely related exactly when its relator set is
finite. -/
#check (Set.Finite R)

/- Definition 2-1-2 (3): a presentation is finite exactly when it is both finitely generated and
finitely related, i.e. when `Finite X ∧ Set.Finite R`. -/
#check (Finite X ∧ Set.Finite R)

end GroupPresentation

/-! ### Definition_2_1_3 (from Items/Chap02) -/
universe u

namespace GroupPresentation

variable {X : Type u} [Primcodable X]

-- Layer triage:
-- `source-facing`: a presentation datum consisting of a generator type `X` and relator set
-- `R : Set (FreeGroup X)`, together with the textbook condition that the relators are recursively
-- enumerable from finite signed words.
-- `core/canonical`: the chapter owner namespace `GroupPresentation` for presentation-level
-- properties, `FreeGroup.mk` as the canonical map from signed words to the free group, and
-- `REPred` as mathlib's recursively enumerable predicate.
-- `bridge/view`: the source phrase "the presentation `(X; R)` is recursive" is expressed by the
-- predicate on signed words sending `L` to `FreeGroup.mk L ∈ R`.
-- Domain sampling:
-- 1. `Finite X` and `Set.Finite R` from Definition `2-1-2` are the canonical finiteness
--    predicates on the underlying generator type and relator set.
-- 2. `FreeGroup.mk` is the canonical word-to-element map on the free group.
-- 3. `REPred` is mathlib's owner predicate for recursively enumerable subsets of a `Primcodable`
--    type.
-- Primitive vs. derived:
-- the primitive source data are only `X` and `R`; the recursively enumerable word-membership
-- predicate is the derived owner-side API, so no separate wrapper around the presentation data is
-- introduced.

/-- Definition 2-1-3: a presentation with generators indexed by `X` and relator set
`R : Set (FreeGroup X)` is recursive when the set of finite signed words whose image under
`FreeGroup.mk` lies in `R` is recursively enumerable. -/
def IsRecursive (R : Set (FreeGroup X)) : Prop :=
  REPred (fun L : List (X × Bool) ↦ FreeGroup.mk L ∈ R)

end GroupPresentation

/-! ### Definition_2_1_4 (from Items/Chap02) -/
universe u

namespace GroupPresentation

section

variable {X : Type u} [Primcodable X]

-- Layer triage:
-- `source-facing`: a presentation datum `(X; R)` together with the textbook assertions that
-- triviality and conjugacy of words on the generators are algorithmically decidable from finite
-- signed-word input.
-- `core/canonical`: the chapter owner namespace `GroupPresentation`, the word model
-- `List (X × Bool)` with canonical evaluation `FreeGroup.mk`, the canonical normal form map
-- `FreeGroup.toWord`, and the canonical owner quotient `PresentedGroup R` with its map
-- `PresentedGroup.mk`.
-- `bridge/view`: quotient triviality is the source-facing word problem, normal-closure membership
-- is the equivalent owner-side reformulation given by `PresentedGroup.mk_eq_one_iff`, and
-- quotient-level decidability of conjugacy is only a derived view obtained by choosing word
-- representatives through `PresentedGroup.mk_surjective`.
-- Domain sampling:
-- 1. Definition `2-1-2` keeps the finiteness conditions for presentations at the canonical owner
--    predicates `Finite X` and `Set.Finite R`, while Definition `2-1-3` adds the presentation-
--    level predicate `IsRecursive` in the `GroupPresentation` namespace.
-- 2. `FreeGroup.mk` is the canonical map from finite signed words to `FreeGroup X`.
-- 3. `PresentedGroup R` with `PresentedGroup.mk` is the owner abstraction for the quotient by the
--    normal closure of `R`.
-- 4. `PresentedGroup.mk_eq_one_iff` is the canonical bridge from quotient triviality to
--    membership in `Subgroup.normalClosure R`.
-- 5. `ComputablePred` is mathlib's canonical computability predicate on coded finite input.
-- 6. `FreeGroup.toWord` is the canonical reduced-word representative of a free-group element.
-- Primitive vs. derived:
-- the primitive data are the generator type `X` and relator set `R`; the owner-side computable
-- predicates are quotient triviality on signed words and quotient conjugacy on pairs of signed
-- words, while normal-closure membership and quotient-level decidability are derived bridges.

/-- Definition 2-1-4: a presentation has solvable word problem when the set of finite signed words
whose image in the canonical presented group is trivial is computable. -/
def HasSolvableWordProblem (R : Set (FreeGroup X)) : Prop :=
  ComputablePred fun L : List (X × Bool) ↦ PresentedGroup.mk R (FreeGroup.mk L) = 1

/-- A presentation has solvable word problem exactly when triviality of the canonical quotient image
of a signed word is computable. -/
theorem hasSolvableWordProblem_iff_computable_mk_eq_one (R : Set (FreeGroup X)) :
    HasSolvableWordProblem R ↔
      ComputablePred fun L : List (X × Bool) ↦ PresentedGroup.mk R (FreeGroup.mk L) = 1 :=
  Iff.rfl

/-- A presentation has solvable word problem exactly when membership of a signed word in the normal
closure of the relators is computable. -/
theorem hasSolvableWordProblem_iff_computable_mem_normalClosure (R : Set (FreeGroup X)) :
    HasSolvableWordProblem R ↔
      ComputablePred fun L : List (X × Bool) ↦ FreeGroup.mk L ∈ Subgroup.normalClosure R := by
  constructor
  · intro h
    exact ComputablePred.of_eq h fun L ↦
      (PresentedGroup.mk_eq_one_iff :
        PresentedGroup.mk R (FreeGroup.mk L) = 1 ↔
          FreeGroup.mk L ∈ Subgroup.normalClosure R)
  · intro h
    exact ComputablePred.of_eq h fun L ↦
      (PresentedGroup.mk_eq_one_iff :
        PresentedGroup.mk R (FreeGroup.mk L) = 1 ↔
          FreeGroup.mk L ∈ Subgroup.normalClosure R).symm

/-- A presentation has solvable conjugacy problem when conjugacy of pairs of finite signed words in
the canonical presented group is computable. -/
def HasSolvableConjugacyProblem (R : Set (FreeGroup X)) : Prop :=
  ComputablePred fun L : List (X × Bool) × List (X × Bool) ↦
    IsConj (PresentedGroup.mk R (FreeGroup.mk L.1)) (PresentedGroup.mk R (FreeGroup.mk L.2))

/-- A presentation has solvable conjugacy problem exactly when conjugacy of the canonical quotient
images of a pair of signed words is computable. -/
theorem hasSolvableConjugacyProblem_iff_computable_isConj_mk (R : Set (FreeGroup X)) :
    HasSolvableConjugacyProblem R ↔
      ComputablePred fun L : List (X × Bool) × List (X × Bool) ↦
        IsConj (PresentedGroup.mk R (FreeGroup.mk L.1)) (PresentedGroup.mk R (FreeGroup.mk L.2)) :=
  Iff.rfl

/-- The source-facing word-level conjugacy algorithm induces a concrete quotient-level decider for
conjugacy in the canonical presented group. -/
noncomputable instance decidableRelIsConjOfHasSolvableConjugacyProblem
    (R : Set (FreeGroup X)) (h : HasSolvableConjugacyProblem R) :
    DecidableRel (IsConj : PresentedGroup R → PresentedGroup R → Prop) :=
  let _ : DecidableEq X := Classical.decEq _
  let _ : DecidableEq (PresentedGroup R) := Classical.decEq _
  let p : List (X × Bool) × List (X × Bool) → Prop := fun L ↦
    IsConj (PresentedGroup.mk R (FreeGroup.mk L.1)) (PresentedGroup.mk R (FreeGroup.mk L.2))
  have hp : ComputablePred p := h
  let rep : PresentedGroup R → List (X × Bool) := fun g ↦
    FreeGroup.toWord (Classical.choose (PresentedGroup.mk_surjective R g))
  have hrep : ∀ g : PresentedGroup R, PresentedGroup.mk R (FreeGroup.mk (rep g)) = g := by
    intro g
    dsimp [rep]
    rw [FreeGroup.mk_toWord]
    exact Classical.choose_spec (PresentedGroup.mk_surjective R g)
  fun g h' ↦ by
    have hg : PresentedGroup.mk R (FreeGroup.mk (rep g)) = g := hrep g
    have hh : PresentedGroup.mk R (FreeGroup.mk (rep h')) = h' := hrep h'
    simpa [p, hg, hh] using hp.choose (rep g, rep h')

end

end GroupPresentation
