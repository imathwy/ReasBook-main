import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_4_8_1 (from Items/Chap04) -/
universe u v

open scoped Monoid.Coprod

set_option autoImplicit false

section

/-!
Primary domain: countable-group embedding theorems together with existential closure properties of
groups.

Layer triage:
- `source-facing`: the countable embedding theorem together with the chapter definition of an
  algebraically closed group.
- `core/canonical`: `G ∗ FreeGroup ι` for coefficient words, `Monoid.Coprod.lift` for evaluation
  in an overgroup, `Finset` for finite systems, `Countable` for countability, and
  `Function.Injective` on a homomorphism `C →* A` for an embedding.
- `bridge/view`: the textbook finite systems of equations and inequations over `G` are expressed as
  finite `Finset`s of coefficient words in `G ∗ FreeGroup ι`.

Domain sampling:
1. `Countable` is the canonical mathlib owner for countability of a type.
2. A group embedding is canonically represented by a homomorphism together with
   `Function.Injective`, as in earlier embedding theorems in this chapter.
3. `Monoid.Coprod.lift` is the canonical owner for evaluating a coefficient word in a target group
   once coefficient values and variable values are fixed.
4. Theorems `4-3-3`, `4-3-5`, and `4-3-6` in this chapter already use the source-facing
   existential-overgroup pattern, so Theorem `4-8-1` should keep that surface while deriving its
   algebraic-closedness hypothesis from the owner predicate defined here.

Primitive vs. derived:
- primitive public data for algebraic closedness: the ambient group `G`, a variable type `ι`, an
  overgroup `H`, an embedding `e : G →* H`, and finite sets of equations and inequations in
  `G ∗ FreeGroup ι`; the finiteness of the system is already carried by the two `Finset`s, so no
  separate finiteness hypothesis on `ι` belongs in the owner field;
- primitive owner-side relation on that data: `IsAlgebraicallyClosedGroup.IsSolution`;
- primitive public data for Theorem `4-8-1`: the ambient overgroup `A` and the embedding
  `f : C →* A`;
- derived public properties: countability of `A`, algebraic closedness of `A`, and injectivity
  of `f`.
-/

variable {G : Type u} [Group G] {ι : Type v}

namespace IsAlgebraicallyClosedGroup

/-- A valuation satisfies a finite coefficient system over `G` when it solves every equation and
avoids every inequation after evaluation in the target group. -/
def IsSolution {H : Type u} [Group H] (e : G →* H)
    (equations inequations : Finset (G ∗ FreeGroup ι)) (x : ι → H) : Prop :=
  let φ := Monoid.Coprod.lift e (FreeGroup.lift x)
  (∀ w ∈ equations, φ w = 1) ∧ ∀ w ∈ inequations, φ w ≠ 1

end IsAlgebraicallyClosedGroup

/-- An algebraically closed group is one in which every finite system of equations and inequations
with coefficients in the group that has a solution in some extension already has a solution in the
group itself. -/
class IsAlgebraicallyClosedGroup (G : Type u) [Group G] : Prop where
  /-- Any finite satisfiable system of equations and inequations over `G` already has a solution
  in `G`. -/
  exists_solution_of_satisfiable {ι : Type v} {H : Type u} [Group H]
      (e : G →* H) (_ : Function.Injective e)
      (equations inequations : Finset (G ∗ FreeGroup ι))
      (hsol : ∃ x : ι → H, IsAlgebraicallyClosedGroup.IsSolution e equations inequations x) :
      ∃ x : ι → G,
        IsAlgebraicallyClosedGroup.IsSolution (MonoidHom.id G) equations inequations x

variable (C : Type u) [Group C] [Countable C]

/-- Theorem 4-8-1: every countable group can be embedded in a countable algebraically closed
group. -/
-- Proof sketch: enumerate all finite systems of equations and inequations with coefficients in the
-- current countable group, solve each system whenever it is consistent in some extension, and take
-- the union of the resulting countable chain. Iterating that construction yields a countable union
-- in which every finitely consistent coefficient system over the final group already has a
-- solution, giving a countable algebraically closed overgroup of `C`.
theorem countable_group_embeds_in_countable_algebraically_closed_group :
    ∃ (A : Type u) (_ : Group A) (f : C →* A),
      Countable A ∧ IsAlgebraicallyClosedGroup A ∧ Function.Injective f := sorry

end

/-! ### Theorem_4_8_2 (from Items/Chap04) -/
universe u

set_option autoImplicit false

namespace IsAlgebraicallyClosedGroup

/-!
Primary domain: group-theoretic algebraic closure.

Layer triage:
- `source-facing`: the textbook notion of an algebraically closed group, meaning that every finite
  system of equations and inequations with coefficients in `G` that is solvable in some extension
  already has a solution in `G`, together with the two consequences in Theorem `4-8-2`.
- `core/canonical`: the owner predicate `IsAlgebraicallyClosedGroup` imported from Theorem
  `4-8-1`, together with the coefficient-word owner `G ∗ FreeGroup ι`,
  `Monoid.Coprod.lift`, `IsSimpleGroup`, and `Group.FG`.
- `bridge/view`: this file is a consequence layer over the owner from Theorem `4-8-1`; the
  source's finite systems of equations and inequations are already encoded there as finite sets of
  coefficient words in `G ∗ FreeGroup ι`.

Domain sampling:
1. `IsAlgebraicallyClosedGroup` from Theorem `4-8-1` is the chapter owner for the finite-system
   extension property.
2. `G ∗ FreeGroup ι` from Theorem `4-8-1` is the canonical owner for coefficient words with
   coefficients in `G` and variables in `ι`.
3. `Monoid.Coprod.lift` from Theorem `4-8-1` is the canonical evaluation map for such words in an
   extension group.
4. `IsSimpleGroup` and `Group.FG` are mathlib's owners for the two conclusions of Theorem `4-8-2`.

Primitive vs. derived:
- primitive public data in this file: the ambient group `G` and the imported owner hypothesis
  `IsAlgebraicallyClosedGroup G`;
- derived API: the induced owner instance `IsSimpleGroup G` and the theorem that `G` is not
  finitely generated.
-/

variable {G : Type u} [Group G]

/-- Theorem 4-8-2 (1): every algebraically closed group is simple. -/
-- Proof sketch: for nontrivial `w a : G`, consider in the free product `G ∗ FreeGroup PUnit` the
-- one-variable equation expressing that a stable letter conjugates the commutator
-- `w x w⁻¹ x⁻¹` to `a x w⁻¹ x⁻¹`. This equation is solvable in an HNN extension, hence by
-- algebraic closedness it is solvable already in `G`. Rearranging shows that `a` lies in the
-- normal closure of `w`, so every nontrivial element normally generates `G`.
instance isSimpleGroup [IsAlgebraicallyClosedGroup G] : IsSimpleGroup G := by
  sorry

/-- Theorem 4-8-2 (2): an algebraically closed group cannot be finitely generated. -/
-- Proof sketch: algebraic closedness lets one solve `a * x ≠ x * a` in `G`, so the center is
-- trivial. On the other hand, for any finite generating set `{a₁, ..., aₙ}` the finite system
-- `aᵢ * y = y * aᵢ` together with `y ≠ 1` has a solution in an extension and therefore already in
-- `G`. Thus every finitely generated subgroup has a nontrivial centralizer, so `G` itself cannot
-- be finitely generated.
theorem not_fg [IsAlgebraicallyClosedGroup G] : ¬ Group.FG G := by
  sorry

end IsAlgebraicallyClosedGroup

/-! ### Theorem_4_8_3 (from Items/Chap04) -/
universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: algebraically closed groups and recursive presentations on countably many
generators.

Layer triage:
- `source-facing`: an algebraically closed group `G` together with the source claim that `G`
  cannot admit an infinite recursive presentation
  `⟨x_i, i ∈ ℕ ; r₁, r₂, ...⟩`.
- `core/canonical`: `PresentedGroup R` is the owner object attached to a relator set
  `R : Set (FreeGroup ℕ)`, `GroupPresentation.IsRecursive R` is the owner predicate for recursive
  enumerability of the relators, and `IsAlgebraicallyClosedGroup G` imported from Theorem
  `4-8-1` records the chapter's finite-system extension property for `G`.
- `bridge/view`: the source phrase “`G` admits an infinite recursive presentation” is expressed
  directly by a chosen equivalence `PresentedGroup R ≃* G` for some recursive relator set on
  generators indexed by `ℕ`.

Domain sampling:
1. `GroupPresentation.IsRecursive R` from Definition `2-1-3` is the chapter owner predicate for
   recursive relator sets.
2. `PresentedGroup R ≃* G` is the project's canonical presentation bridge from Chapter II.
3. `Group.IsRecursivelyPresented` from Theorem `4-7-1` is the earlier chapter owner for the
   finite-generator variant, so the present `ℕ`-indexed notion should remain only the countable
   source-facing companion.
4. `IsAlgebraicallyClosedGroup` from Theorem `4-8-1` is the chapter owner for algebraic
   closedness.

Primitive vs. derived:
- primitive public data for algebraic closedness: the imported owner predicate
  `IsAlgebraicallyClosedGroup G`;
- primitive public data for an infinite recursive presentation: a relator set
  `R : Set (FreeGroup ℕ)` and a presentation equivalence `PresentedGroup R ≃* G`;
- derived API is unnecessary here: the theorem can be stated directly on the canonical
  presentation data, so no extra group-level wrapper around the existential presentation data is
  introduced.
-/

variable (G : Type u) [Group G]

/-- Theorem 4-8-3: if `PresentedGroup R ≃* G` presents an algebraically closed group `G` on
generators indexed by `ℕ`, then the relator set `R` is not recursive. Equivalently, no
algebraically closed group admits an infinite recursive presentation. -/
-- Proof sketch: assume `G` has a recursive presentation `PresentedGroup R ≃* G` on generators
-- `ℕ`. The algebraic-closedness hypothesis implies the simplicity reduction used in the preceding
-- item, so Theorem `4-3-7` gives a solvable word problem for that recursive presentation. The
-- textbook diagonal argument then uses this decision procedure to solve the word problem for a
-- finitely presented group known to have unsolvable word problem, contradiction.
theorem not_isRecursive_of_presentation_of_algebraicallyClosedGroup
    (hG : IsAlgebraicallyClosedGroup G) {R : Set (FreeGroup ℕ)} (P : PresentedGroup R ≃* G) :
    ¬ GroupPresentation.IsRecursive R := sorry

end Group

/-! ### Theorem_4_8_4 (from Items/Chap04) -/
universe u v w

set_option autoImplicit false

namespace Group

/-!
Primary domain: algebraically closed groups and embedding theorems for finitely generated groups
with solvable word problem.

Layer triage:
- `source-facing`: the group-level property that `G` embeds in every algebraically closed group,
  together with the theorem that solvable word problem implies that property.
- `core/canonical`: `IsAlgebraicallyClosedGroup A` from Theorem `4-8-1` is the chapter owner for
  algebraic closedness, `Group.FG` is mathlib's owner for finite generation, and
  `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the project owner for solvability of the
  word problem.
- `bridge/view`: for a fixed ambient group `A`, a group embedding is a homomorphism `G →* A`
  together with `Function.Injective`.

Domain sampling:
1. `IsAlgebraicallyClosedGroup` in `Theorem_4_8_1` is the chapter owner abstraction for the
   finite-system extension property, so this file should reuse it rather than rebuilding a local
   algebraic-system API.
2. The class field `IsAlgebraicallyClosedGroup.exists_solution_of_satisfiable` in
   `Theorem_4_8_1` is the canonical elimination theorem for that owner abstraction.
3. `Group.FG` is mathlib's owner predicate for finite generation.
4. `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the abstract owner for the source
   hypothesis on `G`.

Primitive vs. derived:
- primitive public data here: the source group `G` and the hypothesis `HasSolvableWordProblem G`;
- derived public data: the finite generation of `G`, exposed below as
  `HasSolvableWordProblem.fg`, and for each algebraically closed ambient group `A` an embedding
  witness `f : G →* A` together with its injectivity. Since algebraic closedness is already owned
  by the class `IsAlgebraicallyClosedGroup`, the ambient hypothesis should be carried by an
  instance binder rather than by a separate explicit argument, and the target universe should
  remain arbitrary because the textbook statement ranges over every algebraically closed group; the
  hidden variable universe used by `IsAlgebraicallyClosedGroup` should remain arbitrary as well.
-/

/-- The source-facing property that `G` embeds in every algebraically closed group. -/
def EmbedsInAllAlgebraicallyClosedGroups (G : Type u) [Group G] : Prop :=
  ∀ (A : Type v) [Group A] [IsAlgebraicallyClosedGroup.{v, w} A],
    ∃ f : G →* A, Function.Injective f

namespace HasSolvableWordProblem

/-- A group with solvable word problem is finitely generated, because the owner predicate is built
from a finite-generator presentation. -/
theorem fg {G : Type u} [Group G] (hG : Group.HasSolvableWordProblem G) : FG G := by
  rcases hG with ⟨n, R, P, _⟩
  have hfg : FG (PresentedGroup R) := by
    change FG (FreeGroup (Fin n) ⧸ Subgroup.normalClosure R)
    infer_instance
  letI : FG (PresentedGroup R) := hfg
  let f : PresentedGroup R →* G := P.toMonoidHom
  have hf : Function.Surjective f := P.surjective
  exact Group.fg_of_surjective hf

-- Proof sketch: Boone-Higman embeds `G` in a simple subgroup of a finitely presented group.
-- Interpreting the resulting finite presentation over `A` gives a finite coefficient system, and
-- the ambient algebraic-closedness owner from Theorem `4-8-1` realizes that system in `A`.
-- Simplicity then forces the induced map on the simple subgroup, hence on `G`, to be injective.
/-- Theorem 4-8-4: every finitely generated group with solvable word problem embeds in every
algebraically closed group. The finite generation in the source statement is derived by `hG.fg`.
-/
theorem embedsInAllAlgebraicallyClosedGroups {G : Type u} [Group G]
    (hG : Group.HasSolvableWordProblem G) :
    EmbedsInAllAlgebraicallyClosedGroups G := sorry

end HasSolvableWordProblem

end Group

/-! ### Theorem_4_8_5 (from Items/Chap04) -/
universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: algebraically closed groups and algorithmic group theory.

Layer triage:
- `source-facing`: a finitely generated group `G` together with the hypothesis that `G` embeds in
  every algebraically closed group and the conclusion that `G` has solvable word problem.
- `core/canonical`: `EmbedsInAllAlgebraicallyClosedGroups` from Theorem `4-8-4` is the chapter
  owner for the embedding hypothesis, and `Group.HasSolvableWordProblem` from Theorem `4-4-8` is
  the abstract owner for the conclusion.
- `bridge/view`: the owner predicate `EmbedsInAllAlgebraicallyClosedGroups G` expands to the
  canonical homomorphism-and-injectivity embedding datum for each ambient algebraically closed
  group `A`.

Domain sampling:
1. `EmbedsInAllAlgebraicallyClosedGroups` from Theorem `4-8-4` is the chapter owner for the
   hypothesis that `G` embeds in every algebraically closed group.
2. `IsAlgebraicallyClosedGroup` from Theorem `4-8-1` remains the underlying owner for algebraic
   closedness of the ambient target.
3. `Group.FG G` is mathlib's owner predicate for finite generation.
4. `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the abstract group-level owner for the
   conclusion.

Primitive vs. derived:
- primitive public data: the ambient group `G` and the imported owner hypothesis
  `EmbedsInAllAlgebraicallyClosedGroups G`;
- derived API: `Group.HasSolvableWordProblem G` as the abstract owner for the conclusion, together
  with the thin `↔` companion theorem pairing this converse with Theorem `4-8-4`.
-/

variable {G : Type u} [Group G]

namespace EmbedsInAllAlgebraicallyClosedGroups

-- Proof sketch: this file introduces no new owner abstraction. It records the converse half of
-- the embedding criterion whose forward direction is Theorem `4-8-4`; the companion `↔` theorem
-- below is then just the direct pairing of those two owner-level implications.
/-- Theorem 4-8-5: if a finitely generated group embeds in every algebraically closed group, then
it has solvable word problem. -/
theorem hasSolvableWordProblem [FG G] (hG : EmbedsInAllAlgebraicallyClosedGroups G) :
    HasSolvableWordProblem G := sorry

end EmbedsInAllAlgebraicallyClosedGroups

/-- A finitely generated group has solvable word problem exactly when it embeds in every
algebraically closed group. -/
theorem hasSolvableWordProblem_iff_embedsInAllAlgebraicallyClosedGroups [FG G] :
    HasSolvableWordProblem G ↔ EmbedsInAllAlgebraicallyClosedGroups G :=
  ⟨HasSolvableWordProblem.embedsInAllAlgebraicallyClosedGroups,
    EmbedsInAllAlgebraicallyClosedGroups.hasSolvableWordProblem⟩

end Group
