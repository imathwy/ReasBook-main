import Mathlib
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PushoutI

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_2_1 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open HNNExtension
open HNNExtension.NormalWord

section

variable {G : Type u} [Group G] (A B : Subgroup G)

/-!
Primary domain: HNN extensions and Britton-style reduced words.

Layer triage:
- `source-facing`: a sequence `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` with no pinch
  `t⁻¹, gᵢ, t` for `gᵢ ∈ A` and no pinch `t, gᵢ, t⁻¹` for `gᵢ ∈ B`.
- `core/canonical`: `HNNExtension.NormalWord.ReducedWord G A' B'` is mathlib's owner family for
  reduced HNN words, with the chain condition forbidding `t, gᵢ, t⁻¹` for `gᵢ ∈ A'` and
  `t⁻¹, gᵢ, t` for `gᵢ ∈ B'`.
- `bridge/view`: the source convention is the specialization with swapped subgroup roles,
  `HNNExtension.NormalWord.ReducedWord G B A`, encoded by `head := g₀` and
  `toList := [(ε₁, g₁), ..., (εₙ, gₙ)]`.

Domain sampling:
1. `HNNExtension.toSubgroup A' B' u` is the subgroup attached to the stable-letter sign `u`, with
   `toSubgroup A' B' 1 = A'` and `toSubgroup A' B' (-1) = B'`.
2. `HNNExtension.NormalWord.ReducedWord G A' B'` is the canonical reduced-word owner for an HNN
   extension.
3. `ReducedWord.chain` stores the no-pinch condition on consecutive syllables by forbidding
   `t^u, gᵢ, t^{-u}` whenever `gᵢ ∈ toSubgroup A' B' u`.
4. `HNNExtension.swapEquiv φ : HNNExtension G B A φ.symm ≃* HNNExtension G A B φ` is the
   canonical stable-letter inversion equivalence, sending `t` to `t⁻¹` and fixing the base group.
5. Specializing `(A', B') := (B, A)` makes the forbidden pinches exactly the source ones, and
   `ReducedWord.toHNNExtension` evaluates such a source word in the original HNN extension through
   `swapEquiv`.

Primitive vs. derived:
the primitive source data are the initial group element `g₀` and the list of syllables
`(εᵢ, gᵢ)`. The no-pinch condition is then the canonical chain field of
`HNNExtension.NormalWord.ReducedWord`. Because the source stable-letter convention attaches `B` to
`t` and `A` to `t⁻¹`, the source-facing recall is the canonical specialization
`HNNExtension.NormalWord.ReducedWord G B A`; evaluation in the original HNN extension is derived
through the stable-letter inversion bridge, with no parallel local wrapper or duplicate predicate.
-/

/- Definition 4-2-1: a reduced sequence in the source HNN-extension convention is mathlib's
canonical reduced-word object `HNNExtension.NormalWord.ReducedWord G B A`.

The textbook sequence `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` is represented by the initial base-group
term `head := g₀` together with the syllable list `toList := [(ε₁, g₁), ..., (εₙ, gₙ)]`. The
stored chain condition in this specialization is exactly the requirement that there be no
consecutive pinch `t⁻¹, gᵢ, t` with `gᵢ ∈ A` and no consecutive pinch `t, gᵢ, t⁻¹` with
`gᵢ ∈ B`, because `toSubgroup B A 1 = B` and `toSubgroup B A (-1) = A`. -/
#check (ReducedWord G B A)

namespace HNNExtension

section

variable {A B}
variable (φ : A ≃* B)

private noncomputable def swapHom : HNNExtension G B A φ.symm →* HNNExtension G A B φ :=
  HNNExtension.lift HNNExtension.of (HNNExtension.t⁻¹) HNNExtension.inv_t_mul_of

private theorem swapHom_symm_comp_swapHom :
    MonoidHom.comp (swapHom φ) (swapHom φ.symm) = MonoidHom.id (HNNExtension G A B φ) := by
  apply HNNExtension.hom_ext
  · ext g
    change
      HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
          (HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
            (HNNExtension.of g)) =
        HNNExtension.of g
    rw [HNNExtension.lift_of, HNNExtension.lift_of]
  · change swapHom φ (swapHom φ.symm HNNExtension.t) = HNNExtension.t
    rw [show swapHom φ.symm HNNExtension.t = HNNExtension.t⁻¹ by
      change
        HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
            HNNExtension.t =
          HNNExtension.t⁻¹
      rw [HNNExtension.lift_t]]
    change
      HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
          HNNExtension.t⁻¹ =
        HNNExtension.t
    rw [map_inv, HNNExtension.lift_t]
    simp

/-- The canonical stable-letter inversion equivalence between the two HNN-extension conventions.
It fixes the embedded base group and sends the stable letter to its inverse. -/
noncomputable def swapEquiv : HNNExtension G B A φ.symm ≃* HNNExtension G A B φ :=
  { toFun := swapHom φ
    invFun := swapHom φ.symm
    left_inv := fun x ↦
      congrArg (fun f : HNNExtension G B A φ.symm →* HNNExtension G B A φ.symm ↦ f x)
        (swapHom_symm_comp_swapHom φ.symm)
    right_inv := fun x ↦
      congrArg (fun f : HNNExtension G A B φ →* HNNExtension G A B φ ↦ f x)
        (swapHom_symm_comp_swapHom φ)
    map_mul' := fun x y ↦ map_mul (swapHom φ) x y }

@[simp] theorem swapEquiv_of (g : G) : swapEquiv φ (HNNExtension.of g) = HNNExtension.of g := by
  change
    HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
        (HNNExtension.of g) =
      HNNExtension.of g
  rw [HNNExtension.lift_of]

@[simp] theorem swapEquiv_t :
    swapEquiv φ (HNNExtension.t : HNNExtension G B A φ.symm) =
      (HNNExtension.t : HNNExtension G A B φ)⁻¹ := by
  change
    HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
        HNNExtension.t =
      HNNExtension.t⁻¹
  rw [HNNExtension.lift_t]

@[simp] theorem swapEquiv_symm_of (g : G) :
    (swapEquiv φ).symm (HNNExtension.of g) = HNNExtension.of g := by
  change
    HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
        (HNNExtension.of g) =
      HNNExtension.of g
  rw [HNNExtension.lift_of]

@[simp] theorem swapEquiv_symm_t :
    (swapEquiv φ).symm (HNNExtension.t : HNNExtension G A B φ) =
      (HNNExtension.t : HNNExtension G B A φ.symm)⁻¹ := by
  change
    HNNExtension.lift HNNExtension.of HNNExtension.t⁻¹ HNNExtension.inv_t_mul_of
        HNNExtension.t =
      HNNExtension.t⁻¹
  rw [HNNExtension.lift_t]

end

end HNNExtension

namespace HNNExtension.NormalWord.ReducedWord

section

variable {A B}
variable (φ : A ≃* B)

/-- Evaluate a reduced word written in the source stable-letter convention in the original HNN
extension `HNNExtension G A B φ`. -/
noncomputable def toHNNExtension (w : ReducedWord G B A) : HNNExtension G A B φ :=
  HNNExtension.swapEquiv φ (w.prod φ.symm)

end

end HNNExtension.NormalWord.ReducedWord

end

/-! ### Lemma_4_2_2 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open HNNExtension
open HNNExtension.NormalWord
open HNNExtension.NormalWord.ReducedWord

section

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

/-!
Primary domain: HNN extensions and Britton's lemma.

Layer triage:
- `source-facing`: a reduced sequence `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` with `n ≥ 1`, viewed as a
  reduced word in the HNN extension.
- `core/canonical`: `ReducedWord G B A` is mathlib's owner abstraction for reduced words in the
  source stable-letter convention, and
  `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` is Britton's lemma for that owner.
- `bridge/view`: the textbook integer `n` counting occurrences of the stable letter is the length
  of `w.toList`, while `w.toHNNExtension φ` evaluates the source word in the original HNN
  extension `HNNExtension G A B φ`.

Domain sampling:
1. `ReducedWord G B A` is the canonical reduced-word owner for the source stable-letter
   convention.
2. `HNNExtension.swapEquiv φ` is the canonical stable-letter inversion equivalence between the two
   HNN-extension conventions.
3. `ReducedWord.toHNNExtension φ` is the project bridge evaluating such a source word in the
   original HNN extension.
4. `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` is the owner Britton theorem asserting
   that a reduced word whose product lies in the embedded base group has no stable letters.

Primitive vs. derived:
- primitive public data: the reduced word `w : ReducedWord G B A`;
- derived source hypothesis: `w.toList ≠ []`, encoding that the reduced sequence has at least one
  stable-letter syllable;
- derived conclusion: `w.toHNNExtension φ ≠ 1`, the thin source-facing contrapositive of Britton's
  lemma transported through `swapEquiv`.
-/

/-- Lemma 4-2-2: if a reduced HNN word has at least one stable-letter syllable, then its product
in the HNN extension is not the identity. Equivalently, a reduced sequence
`g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` with `n ≥ 1` does not represent `1`. -/
theorem reducedWord_toHNNExtension_ne_one_of_toList_ne_nil
    (w : ReducedWord G B A) (hw : w.toList ≠ []) :
    w.toHNNExtension φ ≠ 1 := by
  intro h
  have hprod : w.prod φ.symm = 1 := by
    apply (swapEquiv φ).injective
    simpa [toHNNExtension] using h
  have hrange : w.prod φ.symm ∈ (of.range : Subgroup (HNNExtension G B A φ.symm)) :=
    ⟨1, by simpa using hprod.symm⟩
  exact hw (HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ.symm w hrange)

end

/-! ### Definition_4_2_3 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open HNNExtension
open HNNExtension.NormalWord

section

variable {G : Type u} [Group G] (A B : Subgroup G) (d : TransversalPair G B A)

/-!
Primary domain: HNN extensions and Britton normal forms with chosen transversals.

Layer triage:
- `source-facing`: a normal form is a reduced HNN word
  `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` in which each `gᵢ` is the chosen representative of the
  appropriate right coset of `A` or `B`, and there is no pinch `t^ε, 1, t^{-ε}`.
- `core/canonical`: `TransversalPair G B A` is mathlib's owner for the source choice of
  right-coset representatives, and `NormalWord d` is the canonical owner for words in normal form
  relative to that choice.
- `bridge/view`: the source sequence is encoded by the initial base-group term `head := g₀` and
  the signed syllable list `toList := [(ε₁, g₁), ..., (εₙ, gₙ)]`, with the representative
  condition carried by `mem_set` and the no-pinch condition inherited from `ReducedWord.chain`.

Domain sampling:
1. `TransversalPair G B A` stores the chosen representatives of the right cosets of `B` and `A`,
   with `1` representing the subgroup coset.
2. `NormalWord d` is mathlib's canonical owner for HNN words whose syllable entries lie in that
   chosen transversal.
3. `NormalWord.mem_set` records the representative condition for each non-initial `gᵢ`.
4. `NormalWord` extends `ReducedWord`, so the reduced-word chain field remains the owner of the
   no-pinch condition.

Primitive vs. derived:
the primitive source data are the chosen transversal pair and the normal-form word relative to that
pair. The initial element `g₀`, the signed list of syllables, the representative condition, and
the exclusion of the pinch `t^ε, 1, t^{-ε}` are all already primitive in the canonical
`NormalWord` API, so this item is a direct recall of that owner rather than a new wrapper.
-/

/- Definition 4-2-3: after choosing right-coset representatives for `A` and `B`, a normal form in
the HNN extension is mathlib's canonical type `NormalWord d`.

Here `d : TransversalPair G B A` records the chosen representative of each right coset of `B` and
of `A`, with `1` as the representative of the subgroup coset itself. A value of
`NormalWord d` is exactly a sequence `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` in which the syllable `gᵢ`
lies in the chosen transversal for `B` when `εᵢ = 1` and in the chosen transversal for `A` when
`εᵢ = -1`, and the inherited reduced-word chain condition excludes a consecutive subsequence
`t^ε, 1, t^{-ε}`. -/
#check (NormalWord d)

end

/-! ### Theorem_4_2_4 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open HNNExtension
open HNNExtension.NormalWord
open HNNExtension.NormalWord.ReducedWord

section

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

/-!
Primary domain: HNN extensions and the normal form theorem.

Layer triage:
- `source-facing`: the textbook asserts three atomic facts for an HNN extension:
  the base group embeds, a reduced word with at least one stable letter is nontrivial,
  and every element has a unique normal form.
- `core/canonical`: `HNNExtension.of_injective`,
  `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`, and
  `HNNExtension.NormalWord.equiv φ.symm d`.
- `bridge/view`: the textbook phrase “normal form” depends on the chosen right-coset
  representatives from Definition `4-2-3`, so part `(II)` is expressed relative to a
  source-facing `TransversalPair G B A`, while part `(I)` is the source-convention consequence of
  Britton's lemma obtained through `ReducedWord.toHNNExtension`.

Domain sampling:
1. `HNNExtension.of_injective` is mathlib's canonical embedding theorem for the base group.
2. `reducedWord_toHNNExtension_ne_one_of_toList_ne_nil` from Lemma `4-2-2` is the chapter's
   source-facing Britton bridge in the original stable-letter convention.
3. `HNNExtension.NormalWord.equiv φ.symm d` is the canonical normal-form equivalence for the
   swapped convention, and `HNNExtension.swapEquiv φ` transports it back to the original HNN
   extension.

Primitive vs. derived:
- primitive source data: the base group `G`, the subgroups `A`, `B`, the isomorphism `φ`,
  and for part `(II)` a transversal pair `d`;
- derived API: the embedding statement, the Britton nontriviality statement, and the unique
  normal-form correspondence, with part `(I)`'s second sentence expressed as a thin
  source-facing consequence of Britton's lemma.
-/

/- The canonical embedding clause of the HNN normal-form theorem: the map `g ↦ g` embeds the base
group `G` into the HNN extension.

This clause is already exactly mathlib's theorem `HNNExtension.of_injective`. -/
#check ((of_injective φ : Function.Injective (of : G → HNNExtension G A B φ)))

/-- Theorem 4-2-4: part (I), if a reduced HNN word represents the identity, then it contains
no stable-letter syllables. Equivalently, a reduced sequence with `n ≥ 1` cannot equal `1`. -/
theorem reducedWord_toList_eq_nil_of_toHNNExtension_eq_one
    (w : ReducedWord G B A) (hprod : w.toHNNExtension φ = 1) :
    w.toList = [] := by
  by_contra hnil
  exact (reducedWord_toHNNExtension_ne_one_of_toList_ne_nil w hnil) hprod

variable (d : TransversalPair G B A)

/- The chosen-transversal clause of the HNN normal-form theorem: once a transversal pair of
right-coset representatives is chosen, every element of the HNN extension has a unique normal
form.

This clause is encoded by transporting the canonical equivalence
`HNNExtension.NormalWord.equiv φ.symm d` for the swapped convention along
`HNNExtension.swapEquiv φ`.
-/
#check (((swapEquiv φ).toEquiv.symm.trans (equiv φ.symm d)) :
  HNNExtension G A B φ ≃ HNNExtension.NormalWord d)

end

/-! ### Corollary_4_2_5 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open HNNExtension

section

private def unitsIntEquivBool : ℤˣ ≃ Bool where
  toFun u := decide (u = 1)
  invFun b := if b then 1 else -1
  left_inv u := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  right_inv b := by
    cases b <;> simp

local instance : Primcodable ℤˣ := Primcodable.ofEquiv Bool unitsIntEquivBool

/-!
Primary domain: algorithmic solvability of the word problem for HNN extensions.

Layer triage:
- `source-facing`: the base group `G`, the associated subgroups `A`, `B`, the subgroup-membership
  problems for `A` and `B`, the computable group isomorphism `φ : A ≃* B`, and the word problem
  on finite HNN input words `g₀, t^{ε₁} g₁, ..., t^{εₙ} gₙ`, encoded by `ℤˣ`-signed syllables.
- `core/canonical`: `HNNExtension G A B φ` is mathlib's owner for the HNN extension,
  `HNNExtension.NormalWord.ReducedWord G B A` is the chapter's canonical owner for reduced HNN
  words in the source convention, `Equiv.Computable` is the canonical owner for an effectively
  calculable equivalence, and `ComputablePred` is the canonical owner for algorithmic predicates on
  coded inputs.
- `bridge/view`: the source raw HNN word problem is stated directly as the canonical predicate
  `ComputablePred` on `G × List (ℤˣ × G)`, while the auxiliary computability coding of `ℤˣ` is
  supplied internally through the equivalence with `Bool`, and Britton reduction passes internally
  through the canonical reduced-word owner.

Domain sampling:
1. `HNNExtension G A B φ` is mathlib's canonical owner abstraction for the source HNN extension.
2. `HNNExtension.NormalWord.ReducedWord G B A` is the chapter's canonical owner abstraction for
   reduced HNN words in the source stable-letter convention.
3. `ReducedWord.prod φ.symm` and its transported source-facing variant are the canonical evaluation
   maps from normal-form words to the HNN extension.
4. `ComputablePred fun g : G ↦ g = 1` and `ComputablePred fun g : G ↦ g ∈ H` are the canonical
   computability owners for the ordinary and generalized word problems in the base group.
5. `φ.toEquiv.Computable` is the canonical way to express that both `φ` and `φ⁻¹` are effectively
   calculable.

Primitive vs. derived:
- primitive source data: the group `G`, the subgroups `A`, `B`, the isomorphism `φ`,
  computable triviality in `G`, computable membership in `A` and `B`, and computability of the
  equivalence `φ`;
- derived API: the direct `ComputablePred` on raw HNN words, whose inputs are raw HNN words rather
  than coded quotient elements.
-/

variable {G : Type u} [Group G] [Primcodable G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "t" => (HNNExtension.t : E)

/-- Corollary 4-2-5: if the base group `G` has solvable word problem, the generalized word
problems for `A` and `B` are solvable in `G`, and the subgroup isomorphism `φ : A ≃* B` is
effectively calculable, then the HNN extension has solvable word problem. The conclusion is stated
on raw HNN input words, while Britton reduction through reduced words is a derived internal step.
-/
-- Proof sketch: reduce an arbitrary HNN input word to Britton normal form by using the word
-- problem in `G`, the membership tests for `A` and `B`, and the computable equivalence `φ` to
-- detect and cancel pinches. The normal-form theorem from Theorem `4-2-4` then shows that the
-- resulting reduced word represents the identity exactly when no stable-letter syllables remain
-- and the residual base-group element is trivial in `G`.
theorem hnnExtension_hasSolvableWordProblem
    [Primcodable A] [Primcodable B]
    (hG : ComputablePred fun g : G ↦ g = 1)
    (hA : ComputablePred fun g : G ↦ g ∈ A)
    (hB : ComputablePred fun g : G ↦ g ∈ B)
    (hφ : φ.toEquiv.Computable) :
    ComputablePred fun w : G × List (ℤˣ × G) ↦
      of w.1 * (w.2.map fun x ↦ t ^ (x.1 : ℤ) * of x.2).prod = 1 := sorry

end

/-! ### Lemma_4_2_6 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open HNNExtension
open HNNExtension.NormalWord
open HNNExtension.NormalWord.ReducedWord

section

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

/-!
Primary domain: uniqueness of the stable-letter pattern in reduced HNN words.

Layer triage:
- `source-facing`: two reduced words
  `g₀, t^{ε₁}, g₁, ..., t^{εₙ}, gₙ` and `h₀, t^{δ₁}, h₁, ..., t^{δₘ}, hₘ`
  that represent the same element of the HNN extension.
- `core/canonical`: `ReducedWord G B A` is mathlib's owner abstraction for reduced HNN words in
  the source stable-letter convention.
- `bridge/view`: the sequence of exponents `ε₁, ..., εₙ` is encoded by
  `w.toList.map Prod.fst : List ℤˣ`, while equality of the represented HNN-extension elements is
  expressed by `w.toHNNExtension φ`.

Domain sampling:
1. `ReducedWord G B A` is the canonical owner for reduced HNN words in the source convention.
2. `ReducedWord.toHNNExtension φ` is the project bridge evaluating such a source word in the
   original HNN extension.
3. `ReducedWord.map_fst_eq_and_of_prod_eq` is mathlib's canonical uniqueness theorem for the
   stable-letter sign pattern of reduced words with equal product in the swapped convention.

Primitive vs. derived:
- primitive public data: the reduced words `w₁`, `w₂`;
- source hypothesis: equality of their products in the HNN extension;
- source conclusion: equality of the exponent-sign lists, which is exactly the textbook assertion
  that the two words have the same number of stable letters and the same exponents in order.
-/

/-- Lemma 4-2-6: if two reduced HNN words represent the same element, then their stable-letter
exponent lists agree. Equivalently, the two words have the same number of stable letters and the
same exponent `±1` at each position. -/
-- Proof sketch: apply mathlib's canonical reduced-word uniqueness theorem
-- `ReducedWord.map_fst_eq_and_of_prod_eq` to the swapped-convention words after transporting the
-- hypothesis through the injective equivalence `swapEquiv φ`.
theorem reducedWord_exponentList_eq_of_toHNNExtension_eq
    (w₁ w₂ : ReducedWord G B A) (hprod : w₁.toHNNExtension φ = w₂.toHNNExtension φ) :
    w₁.toList.map Prod.fst = w₂.toList.map Prod.fst := by
  refine (ReducedWord.map_fst_eq_and_of_prod_eq φ.symm ?_).1
  exact (swapEquiv φ).injective hprod

end

/-! ### Theorem_4_2_7 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open HNNExtension

section

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "of" => (HNNExtension.of : G →* E)

/-!
Primary domain: torsion in HNN extensions of groups.

Layer triage:
- `source-facing`: an HNN extension `E = HNNExtension G A B φ` together with a finite-order
  element of `E` and the textbook conclusion that such an element is conjugate to one coming from
  the base group `G`.
- `core/canonical`: mathlib's owner `HNNExtension G A B φ`, the canonical embedding `of`,
  `IsOfFinOrder` and `orderOf` for torsion data, and `IsConj` for conjugacy.
- `bridge/view`: the phrase “an element of the base `G` viewed inside the HNN extension” is
  expressed directly by the canonical map `of`, so no extra wrapper API is needed.

Domain sampling:
1. `HNNExtension G A B φ` is mathlib's canonical owner abstraction for the source HNN extension.
2. `HNNExtension.of` is the canonical embedding of the base group into that HNN extension.
3. `IsOfFinOrder`, `orderOf`, and positive naturals `ℕ+` are the canonical owner APIs for finite
   order and exact positive order.
4. `IsConj` is mathlib's canonical relation for conjugacy in a group.

Primitive vs. derived:
- primitive public data: the base group `G`, the associated subgroups `A`, `B`, the isomorphism
  `φ`, and an element of `E`;
- derived API: the base-group witness whose image is conjugate to the given torsion element, the
  resulting finite-order statement for that base element, and the corresponding exact-order
  consequence for the existence of elements of order `n`.
-/

/-- Theorem 4-2-7 (1): every finite-order element of an HNN extension is conjugate to the image of
an element of the base group. The finite-order conclusion for that base element is derived from
conjugacy and injectivity of `of`. -/
-- Proof sketch: choose a cyclically reduced conjugate of the given torsion element. Britton's
-- lemma rules out any cyclically reduced representative containing the stable letter, because a
-- positive power of such a word would remain nontrivial. Hence the cyclically reduced conjugate
-- lies in the embedded base group, and conjugacy transports finite order back to a base element.
theorem exists_base_isConj_of_hnnExtension_isOfFinOrder (x : E) (hx : IsOfFinOrder x) :
    ∃ g : G, IsConj (of g) x := sorry

/-- Theorem 4-2-7 (2): if an HNN extension has an element of exact order `n`, then the base group
also has an element of exact order `n`. The positivity implicit in “exact order `n`” is recorded
by taking `n : ℕ+`. -/
-- Proof sketch: apply part `(1)` to a torsion element `x` of order `n`. Conjugate elements have
-- the same order, and the canonical embedding `HNNExtension.of` preserves order because it is
-- injective. Therefore the conjugate base element supplied by part `(1)` has order exactly `n`.
theorem exists_base_orderOf_eq_of_exists_hnnExtension_orderOf_eq (n : ℕ+)
    (hx : ∃ x : E, orderOf x = n) :
    ∃ g : G, orderOf g = n := by
  rcases hx with ⟨x, hx⟩
  have hfin : IsOfFinOrder x := by
    rw [← orderOf_pos_iff, hx]
    exact n.pos
  obtain ⟨g, hconj⟩ := exists_base_isConj_of_hnnExtension_isOfFinOrder x hfin
  refine ⟨g, ?_⟩
  calc
    orderOf g = orderOf (of g : E) := by
      symm
      simpa using orderOf_injective of (HNNExtension.of_injective φ) g
    _ = orderOf x := by
      rcases hconj with ⟨c, hc⟩
      simpa using SemiconjBy.orderOf_eq (↑c) hc
    _ = n := hx

end

/-! ### Theorem_4_2_8 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open List
open HNNExtension
open HNNExtension.NormalWord

section

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

/-!
Primary domain: conjugacy theory for HNN extensions.

Layer triage:
- `source-facing`: cyclically reduced reduced words in an HNN extension and the conjugacy theorem
  describing conjugate such words by cyclic permutation and conjugation by an element of `A` or
  `B`.
- `core/canonical`: `HNNExtension.NormalWord.ReducedWord G B A`, its bridge evaluation map
  `ReducedWord.toHNNExtension`, and the group-theoretic conjugacy relation `IsConj`.
- `bridge/view`: the textbook cyclic sequence attached to a reduced HNN word is the derived list
  obtained by merging the initial base term into the terminal syllable. Cyclic permutation is
  then the canonical list-rotation relation `List.IsRotated` on that derived list, while
  conjugation by an element of the base group is expressed by the canonical embedding
  `HNNExtension.of`.

Domain sampling:
1. `HNNExtension.NormalWord.ReducedWord G B A` is mathlib's owner abstraction for reduced HNN
   words in the source stable-letter convention.
2. `ReducedWord.toHNNExtension φ` is the project bridge evaluating such a source word in
   `HNNExtension G A B φ`.
3. `IsConj` is the canonical conjugacy relation in a group.
4. `List.IsRotated` is the canonical list-level owner relation encoding cyclic permutation of the
   source-facing cyclic syllable list.

Primitive vs. derived:
- primitive public data: reduced HNN words `u` and `v`;
- derived bridge data: the private cyclic syllable list obtained by absorbing the initial base
  term into the terminal syllable;
- derived source-facing notions: cyclic permutation and cyclically reducedness, expressed directly
  in terms of reduced words, the canonical rotation relation on that cyclic syllable list, and the
  cyclic boundary no-pinch condition;
- derived conclusion: equality of stable-letter lengths together with the existence of a cyclic
  permutation of `v`, an explicit terminal stable-letter sign `ε`, and a conjugator
  `z : toSubgroup B A ε` whose image in the HNN extension conjugates that cyclic permutation to
  `u.toHNNExtension φ`.
-/

namespace HNNExtension.NormalWord

namespace ReducedWord

local notation "W" => ReducedWord G B A

private def cyclicData (w : W) : List (ℤˣ × G) :=
  match w.toList.getLast? with
  | none => []
  | some (ε, g) => w.toList.dropLast ++ [(ε, g * w.head)]

/-- One cyclically reduced HNN word is obtained from another by cyclic permutation when their
source-facing cyclic syllable lists differ by a list rotation; in the zero-syllable case this
reduces to equality of the base-group words. -/
def IsCyclicPermutation (u v : W) : Prop :=
  match u.toList.getLast?, v.toList.getLast? with
  | none, none => u.head = v.head
  | some _, some _ => cyclicData u ~r cyclicData v
  | _, _ => False

/-- A reduced HNN word is cyclically reduced when its cyclic syllable list has no boundary pinch.
For a word with no stable-letter syllables, this condition is vacuous. -/
def IsCyclicallyReduced (w : W) : Prop :=
  ∀ {a b : ℤˣ × G},
    (cyclicData w).head? = some a →
      (cyclicData w).getLast? = some b →
        b.2 ∈ toSubgroup B A b.1 →
          a.1 = b.1

/-- Theorem 4-2-8 (1): conjugate cyclically reduced reduced words in an HNN extension with at
least one stable-letter syllable have the same stable-letter length. -/
-- Proof sketch: use cyclic reducedness of `v` to choose a reduced cyclic permutation whose final
-- stable-letter sign matches that of `u`, then apply Britton normal-form uniqueness to the
-- resulting conjugacy relation to identify the stable-letter pattern and hence the length.
theorem conjugacy_length_eq_of_isCyclicallyReduced
    (u v : W) (hu_nonempty : u.toList ≠ [])
    (hu_cyclic : u.IsCyclicallyReduced) (hv_cyclic : v.IsCyclicallyReduced)
    (hconj : IsConj (u.toHNNExtension φ) (v.toHNNExtension φ)) :
    u.toList.length = v.toList.length := sorry

/-- Theorem 4-2-8 (2): under the same hypotheses, a suitable cyclic permutation of `v` is
conjugate to `u` by a base-group element lying in the subgroup determined by the final stable
letter of `u`. -/
-- Proof sketch: use cyclic reducedness of `v` to choose a reduced cyclic permutation `v'` whose
-- final stable-letter sign `ε` matches that of `u`; the conjugating element obtained from
-- Britton's analysis then lies directly in the canonical subgroup `toSubgroup B A ε`.
theorem exists_subgroupConjugator_of_isCyclicallyReduced
    (u v : W) (hu_nonempty : u.toList ≠ [])
    (hu_cyclic : u.IsCyclicallyReduced) (hv_cyclic : v.IsCyclicallyReduced)
    (hconj : IsConj (u.toHNNExtension φ) (v.toHNNExtension φ)) :
    ∃ ε : ℤˣ, ∃ z : toSubgroup B A ε, ∃ v' : W,
      v'.IsCyclicPermutation v ∧
        (∃ g : G, u.toList.getLast? = some (ε, g)) ∧
        (∃ g : G, v'.toList.getLast? = some (ε, g)) ∧
        u.toHNNExtension φ = of (z : G) * v'.toHNNExtension φ * (of (z : G))⁻¹ :=
  sorry

end ReducedWord

end HNNExtension.NormalWord

end

/-! ### Definition_4_2_9 (from Items/Chap04) -/
universe u v w

set_option autoImplicit false

open Monoid
open Monoid.CoprodI Monoid.PushoutI
open MulEquiv

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Monoid.CoprodI

/-- The canonical `Bool`-indexed pushout diagram for a two-factor amalgamated product with
amalgamating maps `φG : A →* G` and `φH : A →* H`. -/
abbrev twoFactorAmalgamatingMaps
    {A : Type u} {G : Type v} {H : Type w}
    [Group A] [Group G] [Group H]
    (φG : A →* G)
    (φH : A →* H) :
    (b : Bool) → A →* twoFactorFamily G H b
  | false => (ulift.symm.toMonoidHom : G →* twoFactorFamily G H false).comp φG
  | true => (ulift.symm.toMonoidHom : H →* twoFactorFamily G H true).comp φH

end Monoid.CoprodI

namespace Monoid.PushoutI

section

variable {A : Type u} {G : Type v} {H : Type w}
variable [Group A] [Group G] [Group H]
variable (φG : A →* G) (φH : A →* H)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "Maps" => twoFactorAmalgamatingMaps φG φH

/-- Bridge predicate for the two-factor pushout diagram determined by `φG` and `φH`.

This is not the chapter's main source-facing owner for Definition `4-2-9`; it is the generic
`Bool`-indexed helper that the subgroup specialization reuses. -/
abbrev TwoFactorReduced (w : Word Family) : Prop :=
  w.toList.length ≤ 1 ∨ Reduced Maps w

/-- For words of length greater than one, `TwoFactorReduced` is exactly the canonical condition
that no letter lies in the image of the base-group map. -/
theorem twoFactorReduced_iff_of_one_lt_length
    {w : Word Family}
    (hw : 1 < w.toList.length) :
    TwoFactorReduced φG φH w ↔ Reduced Maps w := by
  constructor
  · intro h
    rcases h with hlen | hred
    · omega
    · exact hred
  · intro h
    exact Or.inr h

end

end Monoid.PushoutI

namespace Subgroup

section

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H}

/-- The free product of `G` and `H` with the subgroups `A` and `B` amalgamated along `e`. -/
abbrev amalgamatedProductAlong (e : A ≃* B) : Type (max u v) :=
  PushoutI (twoFactorAmalgamatingMaps A.subtype (B.subtype.comp e.toMonoidHom))

namespace amalgamatedProductAlong

section

variable (e : A ≃* B)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "P" => Subgroup.amalgamatedProductAlong e
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom
local notation "Maps" => twoFactorAmalgamatingMaps ιA ιB

/-- Definition 4-2-9: a word in the free product of `G` and `H` with `A` and `B` amalgamated
along `e` is reduced when it is an alternating word in the two factors and either has length at
most one or, if it has length greater than one, every letter lies outside the amalgamated
subgroup in its factor.

The alternating nontrivial-word clauses are already carried by `Monoid.CoprodI.Word`; this
source-facing predicate only adds the textbook length-one exception on top of the canonical
owner-side predicate `Monoid.PushoutI.Reduced`. -/
abbrev Reduced (w : Word Family) : Prop :=
  TwoFactorReduced ιA ιB w

/-- For words of length greater than one, Definition `4-2-9` agrees with the canonical owner-side
predicate saying that no letter lies in the image of the amalgamated subgroup. -/
theorem reduced_iff_of_one_lt_length
    {w : Word Family}
    (hw : 1 < w.toList.length) :
    Reduced e w ↔ Monoid.PushoutI.Reduced Maps w := by
  simpa [Subgroup.amalgamatedProductAlong.Reduced] using
    Monoid.PushoutI.twoFactorReduced_iff_of_one_lt_length ιA ιB hw

/-- The canonical left embedding of `G` into `Subgroup.amalgamatedProductAlong e`. -/
abbrev left : G →* P :=
  (PushoutI.of false).comp (ulift.symm.toMonoidHom : G →* Family false)

/-- The canonical right embedding of `H` into `Subgroup.amalgamatedProductAlong e`. -/
abbrev right : H →* P :=
  (PushoutI.of true).comp (ulift.symm.toMonoidHom : H →* Family true)

/-- The canonical embedding of the amalgamated subgroup `A` into
`Subgroup.amalgamatedProductAlong e`. -/
abbrev base : A →* P :=
  PushoutI.base Maps

/-- Evaluate a reduced alternating word in the two-factor amalgamated product along `e`. -/
abbrev ofWord (w : Word Family) : P :=
  ofCoprodI w.prod

end

end amalgamatedProductAlong

end

end Subgroup

/-! ### Theorem_4_2_10 (from Items/Chap04) -/
universe uA uG uH

set_option autoImplicit false

open Monoid
open Monoid.CoprodI Monoid.PushoutI
open MulEquiv

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

section

variable {A : Type uA} {G : Type uG} {H : Type uH}
variable [Group A] [Group G] [Group H]
variable (φG : A →* G) (φH : A →* H)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "Maps" => Monoid.CoprodI.twoFactorAmalgamatingMaps φG φH
local notation "P" => PushoutI Maps
local notation "W" => Word Family

/-!
Primary domain: free products with amalgamation and their normal forms.

Layer triage:
- `source-facing`: a reduced alternating word in the two-factor amalgamated product together with
  the textbook conclusion that a nonempty reduced word represents a nontrivial element.
- `core/canonical`: `Monoid.PushoutI` for the amalgamated product, `Monoid.PushoutI.Reduced` for
  the owner-side reducedness predicate, `Monoid.PushoutI.ofCoprodI` for evaluating a coproduct word
  in the pushout, and `Monoid.PushoutI.of_injective` for the factor embeddings.
- `bridge/view`: `Monoid.PushoutI.TwoFactorReduced` from `Definition_4_2_9` is the generic
  `Bool`-indexed bridge from the textbook two-factor reduced-word condition to the canonical
  predicate `Monoid.PushoutI.Reduced`, while
  `Subgroup.amalgamatedProductAlong.Reduced` is the subgroup-specialized source-facing owner for
  Definition `4-2-9`.

Domain sampling:
1. `Monoid.PushoutI.Reduced.eq_empty_of_mem_range` is the canonical normal-form theorem saying a
   nonempty reduced coproduct word cannot lie in the image of the base group.
2. `Monoid.PushoutI.of_injective` is the canonical injectivity theorem for the factor maps into an
   amalgamated product when the amalgamating maps are injective.
3. `Monoid.CoprodI.twoFactorAmalgamatingMaps` from `Definition_4_2_9` is the project owner for the
   two-factor pushout diagram and should be reused here instead of rebuilt locally.
4. `Monoid.PushoutI.TwoFactorReduced` is the generic bridge predicate used away from the subgroup
   specialization.

Primitive vs. derived:
the primitive public inputs are the common group `A`, the two factor groups `G` and `H`, the maps
`φG : A →* G` and `φH : A →* H`, and a source-facing reduced word `w`. The pushout `P`, the
evaluation map of `w` in `P`, and the two factor embeddings are canonical derived objects, while
the generic reducedness bridge is imported from `Definition_4_2_9` rather than duplicated locally.
-/

/-- Theorem 4-2-10: a reduced sequence of positive length in a free product with amalgamation
represents a nontrivial element of the pushout. -/
-- Proof sketch: if the reduced word has length one, its unique letter is already nontrivial
-- because `Monoid.CoprodI.Word` stores only nonidentity syllables. If the length is greater than
-- one, the source-facing reducedness condition identifies with the canonical
-- predicate `Monoid.PushoutI.Reduced`, via
-- `Monoid.PushoutI.twoFactorReduced_iff_of_one_lt_length`, and the pushout normal-form theorem
-- `Reduced.eq_empty_of_mem_range` rules out the product being the identity.
theorem reduced_sequence_prod_ne_one
    (hφG : Function.Injective φG) (hφH : Function.Injective φH)
    {word : W}
    (hw : TwoFactorReduced φG φH word)
    (hn : 1 ≤ word.toList.length) :
    PushoutI.ofCoprodI word.prod ≠ (1 : P) := sorry

end

section

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H}

namespace Subgroup.amalgamatedProductAlong

open Subgroup.amalgamatedProductAlong

variable (e : A ≃* B)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom
local notation "Maps" => Monoid.CoprodI.twoFactorAmalgamatingMaps ιA ιB

private theorem rightBaseMap_injective :
    Function.Injective (ιB : A →* H) := by
  intro a₁ a₂ h
  exact e.injective (Subtype.coe_injective h)

private theorem amalgamatingMaps_injective :
    ∀ b, Function.Injective (Maps b)
  | false => by
      change Function.Injective
        ((ulift.symm.toMonoidHom : G →* Family false).comp ιA)
      exact (ulift.symm : G ≃* Family false).injective.comp Subtype.coe_injective
  | true => by
      change Function.Injective
        ((ulift.symm.toMonoidHom : H →* Family true).comp ιB)
      exact (ulift.symm : H ≃* Family true).injective.comp (rightBaseMap_injective e)

/-- The canonical left embedding into `Subgroup.amalgamatedProductAlong e` is injective. -/
theorem left_injective :
    Function.Injective (left e : G →* Subgroup.amalgamatedProductAlong e) := by
  dsimp [left]
  exact (PushoutI.of_injective (amalgamatingMaps_injective e) false).comp
    (ulift.symm : G ≃* Family false).injective

/-- The canonical right embedding into `Subgroup.amalgamatedProductAlong e` is injective. -/
theorem right_injective :
    Function.Injective (right e : H →* Subgroup.amalgamatedProductAlong e) := by
  dsimp [right]
  exact (PushoutI.of_injective (amalgamatingMaps_injective e) true).comp
    (ulift.symm : H ≃* Family true).injective

end Subgroup.amalgamatedProductAlong

end

/-! ### Theorem_4_2_11 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open Monoid

section

variable {G H : Type u} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H} (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "P" => Subgroup.amalgamatedProductAlong e

/-!
Primary domain: torsion in free products with amalgamation.

Layer triage:
- `source-facing`: the two-factor amalgamated product determined by `e : A ≃* B`, together with
  the claim that each torsion element is conjugate to a torsion element from the left factor `G`
  or the right factor `H`.
- `core/canonical`: `MulEquiv.amalgamatedProduct` for the underlying pushout construction,
  `IsOfFinOrder` for torsion, and `IsConj` for conjugacy.
- `bridge/view`: `Subgroup.amalgamatedProductAlong e` is the chapter-facing two-factor owner with
  named `left` and `right` embeddings, built as a thin source-facing wrapper over the canonical
  `MulEquiv` pushout API. The internal `Bool`-indexed presentation should not appear in the public
  theorem statement.

Domain sampling:
1. `Subgroup.amalgamatedProduct` from Proposition `3-12-5` is the chapter's owner pattern for a
   two-factor amalgamated product: a named owner type together with named `left` and `right`
   embeddings, not a public `Bool`-indexed interface.
2. `Subgroup.amalgamatedProductAlong` from Definition `4-2-9` is the matching owner specialization
   for an abstract identification `e : A ≃* B`.
3. `MulEquiv.amalgamatedProduct` and `MulEquiv.amalgamatedProductFactor` are the canonical core
   constructions underneath that source-facing owner.
4. `IsOfFinOrder` and `IsConj` are mathlib's canonical predicates for finite order and conjugacy.

Primitive vs. derived:
the primitive public data are the two factor groups `G` and `H`, the subgroups `A ≤ G` and
`B ≤ H`, and the identification `e : A ≃* B`. The internal `Bool`-indexed pushout diagram is
bridge data. The owner `Subgroup.amalgamatedProductAlong e` and its named left/right embeddings are
canonical derived objects, so the main public theorem should speak directly about that source-facing
interface and state the textbook finite-order witness in one factor. The weaker conjugacy-only
alternative is a derived forgetful consequence, not the main numbered entry.
-/

/-- Theorem 4-2-11: every finite-order element of the amalgamated product
`P = ⟨G * H; A = B, e⟩` is conjugate to a finite-order element of one of the two factors. -/
-- Proof sketch: choose a cyclically reduced conjugate of the given torsion element using the
-- normal-form theorem for amalgamated products. A cyclically reduced word of length at least two
-- cannot have finite order, because its nonzero powers remain reduced and nontrivial. Hence a
-- torsion element is conjugate to an element lying in one factor, and conjugacy together with
-- injectivity of the factor embeddings shows that the factor element itself has finite order.
theorem exists_factor_isConj_of_amalgamatedProduct_isOfFinOrder
    (x : P) (hx : IsOfFinOrder x) :
    (∃ g : G, IsOfFinOrder g ∧ IsConj (left e g) x) ∨
      ∃ h : H, IsOfFinOrder h ∧ IsConj (right e h) x := sorry

end

/-! ### Theorem_4_2_12 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open List
open Monoid
open Monoid.CoprodI Monoid.PushoutI

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Monoid.CoprodI.Word

section

variable {A : Type u} {G : Type u} {H : Type u}
variable [Group A] [Group G] [Group H]

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "W" => Word Family

/-- A reduced word in a two-factor amalgamated product is cyclically reduced when it is reduced in
the sense of Definition `4-2-9`, and whenever its first and last syllables lie in the same
factor, the word has at most one syllable. -/
def IsCyclicallyReduced (φG : A →* G) (φH : A →* H) (w : W) : Prop :=
  Monoid.PushoutI.TwoFactorReduced φG φH w ∧
    ∀ {x y : Σ b, Family b}
      (_hx : w.toList.head? = some x)
      (_hy : w.toList.getLast? = some y)
      (_hxy : x.1 = y.1),
        w.toList.length ≤ 1

/-- A cyclically reduced reduced word with at least two syllables begins and ends in different
factors. -/
-- Proof sketch: apply the defining boundary condition in `IsCyclicallyReduced`. If the first and
-- last syllables came from the same factor, that condition would force the word to have length at
-- most `1`, contradicting the hypothesis `2 ≤ w.toList.length`.
theorem firstFactor_ne_lastFactor_of_isCyclicallyReduced_of_two_le
    (φG : A →* G) (φH : A →* H) {w : W}
    (hw : w.IsCyclicallyReduced φG φH) (hwlen : 2 ≤ w.toList.length)
    {x y : Σ b, Family b}
    (hx : w.toList.head? = some x) (hy : w.toList.getLast? = some y) :
    x.1 ≠ y.1 := by
  intro hxy
  have hlen : w.toList.length ≤ 1 := hw.2 hx hy hxy
  omega

end

end Monoid.CoprodI.Word

section

variable {G H : Type u} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H}
variable (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "W" => Word Family
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom

/-!
Primary domain: conjugacy in free products with amalgamation.

Layer triage:
- `source-facing`: cyclically reduced reduced words in the two-factor amalgamated product
  `⟨G * H; A = B, e⟩`, together with the statement that cyclically reduced
  conjugates of length at least `2` differ by cyclic permutation and conjugation from the
  amalgamated subgroup.
- `core/canonical`: `Monoid.CoprodI.Word` for reduced alternating words,
  `Monoid.PushoutI` for the amalgamated product, `Subgroup.amalgamatedProductAlong e` for the
  chapter-facing two-factor owner with named `left`, `right`, `base`, and `ofWord`,
  `Monoid.PushoutI.Reduced` for owner-side reducedness, `List.IsRotated` for cyclic permutation,
  and `IsConj` for conjugacy in the ambient group.
- `bridge/view`: `Monoid.PushoutI.TwoFactorReduced` is the generic `Bool`/`ULift` bridge, while
  `Subgroup.amalgamatedProductAlong.Reduced` is the subgroup-specialized source-facing
  reduced-word predicate from Definition `4-2-9`. The map
  `Subgroup.amalgamatedProductAlong.ofWord e` is the derived conversion from that presentation to
  the owner object. Chosen transversals and `NormalWord` realizations remain proof-internal via
  `Monoid.PushoutI.Reduced.exists_normalWord_prod_eq`.

Domain sampling:
1. `Monoid.CoprodI.Word` is the chapter's intrinsic owner for source reduced words in free-product
   style normal forms.
2. `Subgroup.amalgamatedProductAlong.Reduced` is the upstream source-facing reducedness predicate
   for two-factor amalgamated products over identified subgroups.
3. Proposition `3-12-5` already fixes the chapter owner pattern for two-factor amalgamated
   products: a named `Subgroup` owner with named embeddings rather than a raw `Bool`-indexed
   pushout surface.
4. `List.IsRotated` is the canonical owner for cyclic permutation of syllable lists.

Primitive vs. derived:
the primitive public data are the two factors `G`, `H`, the amalgamating subgroups `A` and `B`,
the identification `e : A ≃* B`, and the source reduced words `u` and `v`. Reducedness and
cyclic reducedness are expressed directly on those words. The owner
`Subgroup.amalgamatedProductAlong e`, its canonical embeddings, and word evaluation are derived
operations.
-/

/-- Theorem 4-2-12: in the free product with amalgamation of `G` and `H`
over `A = B` via `e`, if a reduced word `u` is cyclically reduced and has at least two syllables,
then every cyclically reduced conjugate reduced word `v` is obtained by cyclically permuting the
syllables of `u` and then conjugating by an element of the amalgamated subgroup `A`. -/
-- Proof sketch: pass from the source reduced words to chosen normal forms only internally, using
-- the canonical existence theorem `Reduced.exists_normalWord_prod_eq`. The conjugacy theorem for
-- amalgamated products applied to those normal forms shows that a cyclically reduced conjugate of
-- a cyclically reduced word of length at least two can only arise from rotating the syllable list
-- and then conjugating by an element of the amalgamated subgroup. Translating back to the source
-- reduced-word layer yields the stated conclusion.
theorem exists_amalgamatedConjugator_and_cyclicPermutation_of_isConj_of_cyclicallyReduced
    {u v : W}
    (hu : u.IsCyclicallyReduced ιA ιB)
    (hu_len : 2 ≤ u.toList.length)
    (hv : v.IsCyclicallyReduced ιA ιB)
    (hconj : IsConj (ofWord e u) (ofWord e v)) :
    ∃ a : A, ∃ w : W,
      u.toList ~r w.toList ∧
        ofWord e v = (base e a)⁻¹ * ofWord e w * base e a := sorry

end
