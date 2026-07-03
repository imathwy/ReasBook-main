import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_8_1 (from Items/Chap01) -/
universe u v

open scoped Monoid.Coprod
open Monoid.Coprod

/-- A split retraction of `R` onto the infinite cyclic group. -/
structure SplitToInfiniteCyclic (R : Type u) [Group R] where
  hom : R →* Multiplicative ℤ
  section_ : Multiplicative ℤ →* R
  id : hom.comp section_ = MonoidHom.id (Multiplicative ℤ)

instance (R : Type u) [Group R] : CoeOut (SplitToInfiniteCyclic R) (R →* Multiplicative ℤ) :=
  ⟨SplitToInfiniteCyclic.hom⟩

section

variable {F : Type u} {R : Type v}
variable [Group F] [Group R]

-- Primary domain: Section `8` ambient words in the free product `F ∗ R` and the canonical induced
-- coproduct maps obtained from split retractions of the parameter group `R` onto the infinite
-- cyclic group.
-- Layer triage:
-- `source-facing`: a Section `8` ambient word `w : F ∗ R` together with the assertion that if all
-- its specializations along split retractions `R ⟶ Multiplicative ℤ` are trivial, then `w = 1`.
-- `core/canonical`: `F ∗ R` is the owner ambient object, `map (MonoidHom.id F)` is the canonical
-- induced coproduct map from a homomorphism on the parameter factor, and a split retraction is
-- recorded canonically by its homomorphism, section, and the identity `hom.comp section_ = id`.
-- `bridge/view`: later one-variable evaluation in Proposition `1-8-3` composes this canonical
-- induced map with `lift (MonoidHom.id F) (zpowersHom F x)`, but that evaluation layer is derived
-- from the coproduct owner map below.
-- Domain sampling:
-- 1. `F ∗ R` is the chapter/mathlib owner for Section `8` parametric words; compare Proposition
--    `1-8-3`.
-- 2. `map (MonoidHom.id F)` is the canonical induced map on a coproduct word when only the
--    parameter factor changes.
-- 3. The canonical algebraic content of a split retraction is a homomorphism with a specified
--    section and identity equation, avoiding the earlier existential witness packaging.
-- 4. Proposition `1-8-3` evaluates parametric words by first applying exactly this coproduct map
--    and then the one-variable evaluation homomorphism.
-- Primitive vs. derived:
-- the primitive source data are the ambient word `w : F ∗ R` and the split retractions of `R`
-- onto `Multiplicative ℤ`. The induced coproduct homomorphism is derived canonically by
-- `Monoid.Coprod.map`; there is no extra wrapper predicate in the public API beyond the
-- proposition's own statement.

/-- The canonical Section `8` coproduct homomorphism induced by a split retraction of the
parameter factor `R` onto the infinite cyclic group. -/
def inducedSplitRetraction (ρ : SplitToInfiniteCyclic R) : F ∗ R →* F ∗ Multiplicative ℤ :=
  map (MonoidHom.id F) ρ.hom

/-- The family of Section `8` induced maps obtained from split retractions of `R` onto the
infinite cyclic group. This is the canonical function family to which the separation hypothesis is
applied. -/
def inducedRetractionMaps (F : Type u) [Group F] (R : Type v) [Group R] :
    Set (F ∗ R → F ∗ Multiplicative ℤ) :=
  Set.range fun ρ : SplitToInfiniteCyclic R ↦
    (inducedSplitRetraction ρ : F ∗ R → F ∗ Multiplicative ℤ)

/-- Proposition 1-8-1: if a Section `8` ambient word maps to `1` under every induced homomorphism
coming from a split retraction of `R` onto the infinite cyclic group, and those induced maps
separate points of `F ∗ R`, then the word itself is `1`. -/
-- Proof sketch: if `w ≠ 1`, point separation for the family of induced maps provides one split
-- retraction whose induced map takes `w` away from the value at `1`. Since every monoid
-- homomorphism sends `1` to `1`, this contradicts the universal vanishing hypothesis.
theorem eq_one_of_forall_induced_retraction_eq_one
    (hsep : (inducedRetractionMaps F R).SeparatesPoints)
    (w : F ∗ R)
    (hw : ∀ ρ : SplitToInfiniteCyclic R, inducedSplitRetraction ρ w = 1) :
    w = 1 := by
  by_contra hw_ne
  rcases hsep hw_ne with ⟨f, ⟨ρ, rfl⟩, hf⟩
  exact hf (by simpa using hw ρ)

end

/-! ### Proposition_1_8_2 (from Items/Chap01) -/
universe u v

open scoped Monoid.Coprod

section

variable {F : Type u} {R : Type v}
variable [Group F] [Group R]

-- Layer triage:
-- `source-facing`: the word problem in the Section `8` ambient free product `F ∗ R`, tested via
-- the canonical induced coproduct maps attached to split retractions of `R`.
-- `core/canonical`: Proposition `1-8-1` is the owner implication from the universal induced test
-- to `w = 1` under the canonical point-separation hypothesis on those maps,
-- `inducedSplitRetraction` is the induced coproduct map, `inducedRetractionMaps` is the
-- associated family of functions, and `DecidablePred` is Lean's canonical interface for
-- decidability of the word problem.
-- `bridge/view`: the universal induced-retraction test is the contraposed form of Proposition
-- `1-8-1`, derived internally here rather than exposed as a second public owner theorem.
-- Domain sampling:
-- 1. Proposition `1-8-1` supplies the owner implication from the universal test to `w = 1`.
-- 2. `SplitToInfiniteCyclic R` is the chapter owner vocabulary for the split retractions tested in
--    Section `8`.
-- 3. `Set.SeparatesPoints` is mathlib's owner abstraction for the missing separation hypothesis on
--    a family of functions.
-- 4. `DecidablePred` is the canonical owner API for a solvable yes/no problem on a fixed type.

/-- Proposition 1-8-2: in the Section `8` ambient free product `F ∗ R`, the word problem is
decidable once one can decide whether a word maps to `1` under every induced homomorphism coming
from a split retraction of `R` onto the infinite cyclic group, provided those induced maps
separate points of `F ∗ R`. -/
-- Proof sketch: Proposition `1-8-1` turns the universal induced-retraction vanishing test into a
-- sufficient criterion for `w = 1` once the induced maps separate points. The given decision
-- procedure transports across that implication.
@[reducible] def word_problem_decidable_of_decidable_induced_retraction_test
    (hsep : (inducedRetractionMaps F R).SeparatesPoints)
    (htest : DecidablePred fun w : F ∗ R ↦
      ∀ ρ : SplitToInfiniteCyclic R, inducedSplitRetraction ρ w = 1) :
    DecidablePred fun w : F ∗ R ↦ w = 1 :=
  fun w ↦ by
    let _ := htest w
    exact
      decidable_of_iff
        (∀ ρ : SplitToInfiniteCyclic R, inducedSplitRetraction ρ w = 1)
        ⟨fun hw ↦ eq_one_of_forall_induced_retraction_eq_one hsep w hw
          , fun hw ρ ↦ by simp [hw]⟩

end

/-! ### Proposition_1_8_3 (from Items/Chap01) -/
universe u v

open scoped Monoid.Coprod
open Monoid.Coprod

section

variable {F : Type u} [Group F]

-- Layer triage:
-- `source-facing`: a one-variable equation `equation : F ∗ Multiplicative ℤ` over the free group
-- `F`, together with Section `8` parametric words and their value sets in `F`.
-- `core/canonical`: `F ∗ Multiplicative ℤ` is the chapter/mathlib owner object for one-variable
-- equations, `SplitToInfiniteCyclic` is the upstream chapter owner for a split retraction onto
-- `Multiplicative ℤ`, `lift (MonoidHom.id F) (zpowersHom F x)` is the canonical evaluation map at
-- `x : F`, `Set.range` is the canonical owner construction for the value set of a fixed
-- parametric word, and `IsFreeGroup F` is the source-faithful freeness hypothesis.
-- `bridge/view`: a parametric word carries a fixed `SplitToInfiniteCyclic` datum, and the
-- associated one-variable equation is the derived bridge `ParametricWord.toEquation`.
-- Domain sampling:
-- 1. Proposition `1-8-1` introduces the owner abstraction `SplitToInfiniteCyclic` and the
--    canonical bridge `inducedSplitRetraction`.
-- 2. Proposition `2-5-3` evaluates one-variable words directly by `lift φ (zpowersHom G g)`,
--    again using `F ∗ Multiplicative ℤ` as the owner object.
-- 3. `Set.range` is the canonical owner of the set of values attained by a fixed parametric word.
-- Primitive vs. derived:
-- the primitive public data of Proposition `1-8-3` are the equation `equation : F ∗
-- Multiplicative ℤ` and a parametric word with its fixed parameter group, split retraction, and
-- ambient coproduct word. Its associated one-variable equation, evaluation map, and value set are
-- derived canonically from that owner object.

/-- The solution set of a one-variable equation `equation : F ∗ Multiplicative ℤ`, evaluated in
the free group `F` by sending the distinguished infinite-cyclic factor to `x : F`. -/
def equationSolutionSet (equation : F ∗ Multiplicative ℤ) : Set F :=
  { x | lift (MonoidHom.id F) (zpowersHom F x) equation = 1 }

@[simp] theorem mem_equationSolutionSet_iff (equation : F ∗ Multiplicative ℤ) (x : F) :
    x ∈ equationSolutionSet equation ↔
      lift (MonoidHom.id F) (zpowersHom F x) equation = 1 := by
  rfl

end

section

variable {F : Type u} [Group F]

/-- A Section `8` parametric word over `F` consists of a parameter group with a fixed split
retraction onto the infinite cyclic group, together with a coproduct word in `F ∗ R`. -/
structure ParametricWord (F : Type u) [Group F] where
  parameterGroup : Type v
  instGroupParameterGroup : Group parameterGroup
  specialization : @SplitToInfiniteCyclic parameterGroup instGroupParameterGroup
  word : F ∗ parameterGroup

attribute [instance] ParametricWord.instGroupParameterGroup

namespace ParametricWord

/-- The canonical bridge from a parametric word to its associated one-variable equation. -/
def toEquation (paramWord : ParametricWord F) : F ∗ Multiplicative ℤ :=
  inducedSplitRetraction paramWord.specialization paramWord.word

/-- Evaluate a parametric word at `x : F` by evaluating its associated one-variable equation in
`F`. -/
def eval (paramWord : ParametricWord F) (x : F) : F :=
  lift (MonoidHom.id F) (zpowersHom F x) paramWord.toEquation

/-- The value set of a parametric word consists of all values it attains under evaluation in `F`.
-/
def valueSet (paramWord : ParametricWord F) : Set F :=
  Set.range paramWord.eval

@[simp] theorem mem_valueSet_iff (paramWord : ParametricWord F) (g : F) :
    g ∈ paramWord.valueSet ↔ ∃ x : F, paramWord.eval x = g := by
  rfl

end ParametricWord

/-- Proposition 1-8-3: for a one-variable equation `equation : F ∗ Multiplicative ℤ` over a free
group `F`, there exists a finite set of Section `8` parametric words whose value sets cover
exactly the solution set of `equation`. -/
-- Proof sketch: Section `8` analyzes a one-variable equation over a free group by passing to a
-- finite family of parametric words. Each such word carries its own fixed parameter group and
-- split retraction onto the infinite cyclic group, hence a canonical associated equation and value
-- set. The union of those value sets is exactly the solution set of the original equation.
theorem exists_finite_parametric_word_set [IsFreeGroup F] (equation : F ∗ Multiplicative ℤ) :
    ∃ W : Set (ParametricWord F),
      W.Finite ∧
        (⋃ paramWord ∈ W, paramWord.valueSet) = equationSolutionSet equation := sorry

end

/-! ### Proposition_1_8_4 (from Items/Chap01) -/
universe u

noncomputable section

variable {X : Type u}

-- Layer triage:
-- `source-facing`: an element `g : FreeGroup X` together with a cyclically reduced conjugate whose
-- canonical cyclic word has the textbook Wicks form `u v w u⁻¹ v⁻¹ w⁻¹`.
-- `core/canonical`: mathlib's owner notion `commutatorSet (FreeGroup X)` for “`g` is a
-- commutator”.
-- `bridge/view`: the chapter owner `CyclicWord X` for cyclically reduced conjugacy data, together
-- with `CyclicWord.conjClassesEquiv` and the cycle quotient `Cycle (X × Bool)`.
-- Domain sampling:
-- 1. `commutatorSet (FreeGroup X)` with `mem_commutatorSet_iff` is the owner abstraction for the
--    statement that `g` is a commutator.
-- 2. `CyclicWord X` from Definition `1-4-17` is the chapter owner abstraction for cyclically
--    reduced words modulo cyclic permutation.
-- 3. `CyclicWord.toConjClasses` is the canonical bridge from a reduced cyclic word to the
--    conjugacy class it represents.
-- 4. `CyclicWord.conjClassesEquiv` is the owner equivalence showing that the cyclic-word witness
--    is canonically determined by the conjugacy class of `g`, so an existential witness should
--    not remain primitive public data.
-- Primitive vs. derived:
-- the primitive data are only the element `g` and the Wicks-form predicate on its canonical cyclic
-- word. The concrete six-block list is bridge-level data inside the cyclic-word owner, and the
-- cyclic-word witness itself is derived from `CyclicWord.conjClassesEquiv`.

namespace CyclicWord

/-- A cyclic word has Wicks triple factorization when one cyclic representative is
`u v w u⁻¹ v⁻¹ w⁻¹`. -/
def HasWicksTripleFactorization (q : CyclicWord X) : Prop :=
  ∃ u v w : List (X × Bool),
    ((u ++ v ++ w ++ FreeGroup.invRev u ++ FreeGroup.invRev v ++ FreeGroup.invRev w :
      List (X × Bool)) : Cycle (X × Bool)) = q.1

end CyclicWord

/-- Proposition 1-8-4: an element of a free group is a commutator exactly when some cyclically
reduced conjugate has cyclic word `u v w u⁻¹ v⁻¹ w⁻¹` for suitable blocks `u`, `v`, and `w`. The
statement is phrased using the canonical cyclic word of the conjugacy class of `g`. -/
-- Proof sketch: for a commutator `g = ⁅a, b⁆`, pass from the conjugacy class of `g` to its
-- canonical cyclic-word representative via `CyclicWord.conjClassesEquiv`, and read that cyclic
-- word in Wicks form. For the converse, a cyclic representative of the displayed six-block form is
-- itself a commutator, and commutatorhood is preserved under conjugacy, so the original element
-- lies in `commutatorSet`.
theorem mem_commutatorSet_iff_exists_reduced_triple_factorization (g : FreeGroup X) :
    g ∈ commutatorSet (FreeGroup X) ↔
      (CyclicWord.conjClassesEquiv.symm
        (ConjClasses.mk g)).HasWicksTripleFactorization :=
  sorry

end

/-! ### Proposition_1_8_5 (from Items/Chap01) -/
universe u v

open MulEquiv

section

variable {F : Type u} {G : Type v} [Group F] [Group G]

-- Layer triage:
-- `source-facing`: a binary word `w : FreeGroup (Fin 2)` together with its value set in the free
-- group `F` under all substitutions of the two generators.
-- `core/canonical`: `FreeGroup (Fin 2)` is the owner object of binary words, `FreeGroup.lift` is
-- the owner abstraction turning a substitution `Fin 2 → F` into the corresponding evaluation
-- homomorphism, and `Set.range` is the canonical owner of the resulting value set in `F`.
-- `bridge/view`: the equivalent homomorphism-level formulation
-- `∃ φ : FreeGroup (Fin 2) →* F, φ w = g`, and transport of the value set across `MulEquiv`s.
-- Domain sampling:
-- 1. `FreeGroup (Fin 2)` is the canonical owner of words in two generators.
-- 2. `FreeGroup.lift` is the canonical evaluation map determined by a substitution
--    `Fin 2 → F`.
-- 3. `Set.range` is the chapter/mathlib owner construction for a value set; compare
--    `ParametricWord.valueSet` in Proposition `1-8-3`.
-- 4. `FreeGroup.mk` is the canonical bridge from signed words to elements of a concrete free
--    group, and `ComputablePred` is the chapter owner for algorithmic membership on such coded
--    inputs.
-- Primitive vs. derived:
-- the primitive source data are only the word `w`, the ambient group `F`, and a substitution
-- `x : Fin 2 → F`; the homomorphism `FreeGroup.lift x`, the existential homomorphism
-- formulation `∃ φ, φ w = g`, and any later computability interface on coded free-group words are
-- derived API from the owner set below.

/-- The value set of a binary word is the set of all values it attains under substitutions of the
two free generators into the ambient group. -/
def binaryWordValueSet (w : FreeGroup (Fin 2)) : Set F :=
  Set.range fun x : Fin 2 → F ↦ FreeGroup.lift x w

/-- Membership in the binary-word value set is exactly solvability of the corresponding word
equation by a substitution of the two generators. -/
@[simp] theorem mem_binaryWordValueSet_iff (w : FreeGroup (Fin 2)) (g : F) :
    g ∈ binaryWordValueSet w ↔ ∃ x : Fin 2 → F, FreeGroup.lift x w = g := by
  rfl

/-- The substitution-based value-set condition is equivalent to the homomorphism-level
formulation. -/
theorem mem_binaryWordValueSet_iff_exists_hom (w : FreeGroup (Fin 2)) (g : F) :
    g ∈ binaryWordValueSet w ↔ ∃ φ : FreeGroup (Fin 2) →* F, φ w = g := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨FreeGroup.lift x, rfl⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨φ ∘ FreeGroup.of, ?_⟩
    have hlift : FreeGroup.lift (φ ∘ FreeGroup.of) w = φ w := by
      exact DFunLike.congr_fun (FreeGroup.lift.apply_symm_apply φ) w
    exact hlift.trans hφ

/-- Group isomorphisms transport the value set of a binary word. -/
theorem mem_binaryWordValueSet_iff_map (e : F ≃* G) (w : FreeGroup (Fin 2)) (g : F) :
    g ∈ binaryWordValueSet w ↔ e g ∈ binaryWordValueSet w := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨fun i ↦ e (x i), ?_⟩
    have hlift :
        FreeGroup.lift (fun i ↦ e (x i)) =
          monoidHomCongrRightEquiv e (FreeGroup.lift x) := by
      ext i
      simp [monoidHomCongrRightEquiv, MonoidHom.comp_apply]
    simpa [monoidHomCongrRightEquiv, MonoidHom.comp_apply] using
      congrArg (fun φ : FreeGroup (Fin 2) →* G ↦ φ w) hlift
  · rintro ⟨x, hx⟩
    refine ⟨fun i ↦ e.symm (x i), ?_⟩
    have hlift :
        FreeGroup.lift (fun i ↦ e.symm (x i)) =
          (monoidHomCongrRightEquiv e).symm (FreeGroup.lift x) := by
      ext i
      simp [monoidHomCongrRightEquiv, MonoidHom.comp_apply]
    calc
      FreeGroup.lift (fun i ↦ e.symm (x i)) w = e.symm (FreeGroup.lift x w) := by
        simpa [monoidHomCongrRightEquiv, MonoidHom.comp_apply] using
          congrArg (fun φ : FreeGroup (Fin 2) →* F ↦ φ w) hlift
      _ = g := by simpa using congrArg e.symm hx

section

variable {X : Type u} [Primcodable X]

/-- Proposition 1-8-5: for a fixed binary word `w`, there is an algorithm deciding whether a
signed word on `X` represents an element of the value set of `w` in the canonical free group
`FreeGroup X`. -/
-- Layer: `source-facing`.
-- `core/canonical`: `binaryWordValueSet`, `FreeGroup.mk`, and `ComputablePred`.
-- `bridge/view`: Section `8` reduces binary-word value-set membership to the one-variable
-- equation machinery summarized in Proposition `1-8-3`.
theorem computable_represents_element_of_binaryWordValueSet (w : FreeGroup (Fin 2)) :
    ComputablePred fun L : List (X × Bool) ↦
      FreeGroup.mk L ∈ binaryWordValueSet w := sorry

end

end
