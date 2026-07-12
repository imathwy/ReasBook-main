import Mathlib.Analysis.Convex.Function

noncomputable section

universe u v w z

namespace SaddleFunction

section Shape

variable {𝕜 : Type z} {U : Type u} {X : Type v} {L : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid L] [PartialOrder L] [SMul 𝕜 L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 33.0.1 introduces three primitive slice-wise shape predicates for a
  bifunction on `C × D`: concave-convex, convex-concave, and the disjunctive saddle condition.
- `core/canonical`: the correct owner layer is mathlib's setwise convex-analysis API
  `ConcaveOn 𝕜 C` and `ConvexOn 𝕜 D`, because the source works on subsets `C` and `D` rather than
  only on whole spaces.
- `bridge/view`: the chapter also uses whole-space saddle-shape owners, so thin univ-bridge
  abbreviations are provided below without introducing a second root owner abstraction.

Domain-style sampling used here:
- `ConcaveOn 𝕜 C f`;
- `ConvexOn 𝕜 D g`;
- whole-space specialization through `Set.univ`.

Primitive data vs derived API:
- primitive owner data: the two domain sets `C`, `D` and the bifunction `K`;
- primitive source-facing owners: `IsConcaveConvexOn` and `IsConvexConcaveOn`;
- derived disjunctive owner: `IsSaddleOn`;
- derived bridge API: orientation-swap equivalences and implication lemmas;
- derived bridge API: the whole-space abbreviations `IsConcaveConvex`, `IsConvexConcave`,
  `IsSaddle`.

Layer target: `source-facing` for the main labeled declarations, with a thin `univ` bridge for
later whole-space use.
-/

variable (𝕜) in
/-- Definition33.0.1 (1): a bifunction `K` on `C × D` is concave-convex when each first-variable
slice `u ↦ K u v` is concave on `C` for `v ∈ D`, and each second-variable slice `v ↦ K u v` is
convex on `D` for `u ∈ C`. -/
def IsConcaveConvexOn (C : Set U) (D : Set X) (K : U → X → L) : Prop :=
  (∀ v ∈ D, ConcaveOn 𝕜 C (fun u ↦ K u v)) ∧
    ∀ u ∈ C, ConvexOn 𝕜 D (K u)

variable (𝕜) in
/-- Definition33.0.1 (2): a bifunction `K` on `C × D` is convex-concave when each first-variable
slice `u ↦ K u v` is convex on `C` for `v ∈ D`, and each second-variable slice `v ↦ K u v` is
concave on `D` for `u ∈ C`. -/
def IsConvexConcaveOn (C : Set U) (D : Set X) (K : U → X → L) : Prop :=
  (∀ v ∈ D, ConvexOn 𝕜 C (fun u ↦ K u v)) ∧
    ∀ u ∈ C, ConcaveOn 𝕜 D (K u)

variable (𝕜) in
/-- Definition33.0.1 (3): a bifunction on `C × D` is a saddle function when it is either
concave-convex or convex-concave on `C × D`. -/
abbrev IsSaddleOn (C : Set U) (D : Set X) (K : U → X → L) : Prop :=
  IsConcaveConvexOn 𝕜 C D K ∨ IsConvexConcaveOn 𝕜 C D K

variable (𝕜) in
/-- Whole-space bridge for the concave-convex saddle-shape owner. -/
abbrev IsConcaveConvex (K : U → X → L) : Prop :=
  IsConcaveConvexOn 𝕜 Set.univ Set.univ K

variable (𝕜) in
/-- Whole-space bridge for the convex-concave saddle-shape owner. -/
abbrev IsConvexConcave (K : U → X → L) : Prop :=
  IsConvexConcaveOn 𝕜 Set.univ Set.univ K

variable (𝕜) in
/-- Whole-space bridge for the saddle-function owner. -/
abbrev IsSaddle (K : U → X → L) : Prop :=
  IsSaddleOn 𝕜 Set.univ Set.univ K

-- Proof sketch: unfold `IsConcaveConvexOn`; the statement is definitionally the pair of the two
-- slice-wise hypotheses.
/-- Unfolded form of the concave-convex owner on a product domain. -/
@[simp] theorem isConcaveConvexOn_iff (C : Set U) (D : Set X) (K : U → X → L) :
    IsConcaveConvexOn 𝕜 C D K ↔
      (∀ v ∈ D, ConcaveOn 𝕜 C (fun u ↦ K u v)) ∧
      (∀ u ∈ C, ConvexOn 𝕜 D (K u)) := Iff.rfl

/-- Unfolded form of the convex-concave owner on a product domain. -/
@[simp] theorem isConvexConcaveOn_iff (C : Set U) (D : Set X) (K : U → X → L) :
    IsConvexConcaveOn 𝕜 C D K ↔
      (∀ v ∈ D, ConvexOn 𝕜 C (fun u ↦ K u v)) ∧
      (∀ u ∈ C, ConcaveOn 𝕜 D (K u)) := Iff.rfl

/-- The convex-concave owner is the orientation-swap view of the concave-convex owner. -/
@[simp] theorem isConvexConcaveOn_iff_swap (C : Set U) (D : Set X) (K : U → X → L) :
    IsConvexConcaveOn 𝕜 C D K ↔ IsConcaveConvexOn 𝕜 D C (Function.swap K) := by
  constructor <;> rintro ⟨hFirst, hSecond⟩ <;> exact ⟨hSecond, hFirst⟩

/-- The concave-convex owner is the orientation-swap view of the convex-concave owner. -/
theorem isConcaveConvexOn_iff_swap (C : Set U) (D : Set X) (K : U → X → L) :
    IsConcaveConvexOn 𝕜 C D K ↔ IsConvexConcaveOn 𝕜 D C (Function.swap K) := by
  rw [isConvexConcaveOn_iff_swap]

/-- Unfolded whole-space form of the concave-convex owner. -/
@[simp] theorem isConcaveConvex_iff (K : U → X → L) :
    IsConcaveConvex 𝕜 K ↔
      (∀ v, ConcaveOn 𝕜 Set.univ (fun u ↦ K u v)) ∧
      ∀ u, ConvexOn 𝕜 Set.univ (K u) := by
  rw [IsConcaveConvex, isConcaveConvexOn_iff]
  simp

/-- Unfolded whole-space form of the convex-concave owner. -/
@[simp] theorem isConvexConcave_iff (K : U → X → L) :
    IsConvexConcave 𝕜 K ↔
      (∀ v, ConvexOn 𝕜 Set.univ (fun u ↦ K u v)) ∧
      ∀ u, ConcaveOn 𝕜 Set.univ (K u) := by
  rw [IsConvexConcave, isConvexConcaveOn_iff]
  simp

/-- Whole-space swap bridge for the convex-concave owner. -/
@[simp] theorem isConvexConcave_iff_swap (K : U → X → L) :
    IsConvexConcave 𝕜 K ↔ IsConcaveConvex 𝕜 (Function.swap K) := by
  rw [IsConvexConcave, IsConcaveConvex, isConvexConcaveOn_iff_swap]

/-- Whole-space swap bridge for the concave-convex owner. -/
theorem isConcaveConvex_iff_swap (K : U → X → L) :
    IsConcaveConvex 𝕜 K ↔ IsConvexConcave 𝕜 (Function.swap K) := by
  rw [isConvexConcave_iff_swap]

/-- Unfolded form of the disjunctive saddle owner on a product domain. -/
@[simp] theorem isSaddleOn_iff (C : Set U) (D : Set X) (K : U → X → L) :
    IsSaddleOn 𝕜 C D K ↔
      IsConcaveConvexOn 𝕜 C D K ∨ IsConvexConcaveOn 𝕜 C D K := Iff.rfl

/-- Swap invariance of the disjunctive saddle owner on product domains. -/
theorem isSaddleOn_iff_swap (C : Set U) (D : Set X) (K : U → X → L) :
    IsSaddleOn 𝕜 C D K ↔ IsSaddleOn 𝕜 D C (Function.swap K) := by
  rw [isSaddleOn_iff, isSaddleOn_iff]
  constructor
  · rintro (hCC | hVC)
    · exact Or.inr ((isConcaveConvexOn_iff_swap C D K).1 hCC)
    · exact Or.inl ((isConvexConcaveOn_iff_swap C D K).1 hVC)
  · rintro (hCC | hVC)
    · exact Or.inr (by
        simpa using (isConcaveConvexOn_iff_swap D C (Function.swap K)).1 hCC)
    · exact Or.inl (by
        simpa using (isConvexConcaveOn_iff_swap D C (Function.swap K)).1 hVC)

/-- Unfolded whole-space form of the disjunctive saddle owner. -/
@[simp] theorem isSaddle_iff (K : U → X → L) :
    IsSaddle 𝕜 K ↔ IsConcaveConvex 𝕜 K ∨ IsConvexConcave 𝕜 K := by
  rw [IsSaddle, isSaddleOn_iff, IsConcaveConvex, IsConvexConcave]

/-- Whole-space swap invariance of the disjunctive saddle owner. -/
theorem isSaddle_iff_swap (K : U → X → L) :
    IsSaddle 𝕜 K ↔ IsSaddle 𝕜 (Function.swap K) := by
  rw [IsSaddle, IsSaddle, isSaddleOn_iff_swap]

/-- A concave-convex branch hypothesis yields the disjunctive saddle owner. -/
theorem IsConcaveConvexOn.isSaddleOn {C : Set U} {D : Set X} {K : U → X → L}
    (hK : IsConcaveConvexOn 𝕜 C D K) :
    IsSaddleOn 𝕜 C D K := Or.inl hK

/-- A convex-concave branch hypothesis yields the disjunctive saddle owner. -/
theorem IsConvexConcaveOn.isSaddleOn {C : Set U} {D : Set X} {K : U → X → L}
    (hK : IsConvexConcaveOn 𝕜 C D K) :
    IsSaddleOn 𝕜 C D K := Or.inr hK

/-- Orientation-swap bridge from convex-concave to concave-convex. -/
theorem IsConvexConcaveOn.swap {C : Set U} {D : Set X} {K : U → X → L}
    (hK : IsConvexConcaveOn 𝕜 C D K) :
    IsConcaveConvexOn 𝕜 D C (Function.swap K) :=
  (isConvexConcaveOn_iff_swap C D K).1 hK

/-- Orientation-swap bridge from concave-convex to convex-concave. -/
theorem IsConcaveConvexOn.swap {C : Set U} {D : Set X} {K : U → X → L}
    (hK : IsConcaveConvexOn 𝕜 C D K) :
    IsConvexConcaveOn 𝕜 D C (Function.swap K) :=
  (isConcaveConvexOn_iff_swap C D K).1 hK

/-- Orientation-swap bridge for the disjunctive saddle owner on product domains. -/
theorem IsSaddleOn.swap {C : Set U} {D : Set X} {K : U → X → L}
    (hK : IsSaddleOn 𝕜 C D K) :
    IsSaddleOn 𝕜 D C (Function.swap K) :=
  (isSaddleOn_iff_swap C D K).1 hK

/-- A whole-space concave-convex hypothesis yields the whole-space saddle owner. -/
theorem IsConcaveConvex.isSaddle {K : U → X → L} (hK : IsConcaveConvex 𝕜 K) :
    IsSaddle 𝕜 K :=
  (isSaddle_iff K).2 (Or.inl hK)

/-- A whole-space convex-concave hypothesis yields the whole-space saddle owner. -/
theorem IsConvexConcave.isSaddle {K : U → X → L} (hK : IsConvexConcave 𝕜 K) :
    IsSaddle 𝕜 K :=
  (isSaddle_iff K).2 (Or.inr hK)

/-- Whole-space orientation-swap bridge from convex-concave to concave-convex. -/
theorem IsConvexConcave.swap {K : U → X → L} (hK : IsConvexConcave 𝕜 K) :
    IsConcaveConvex 𝕜 (Function.swap K) :=
  (isConvexConcave_iff_swap K).1 hK

/-- Whole-space orientation-swap bridge from concave-convex to convex-concave. -/
theorem IsConcaveConvex.swap {K : U → X → L} (hK : IsConcaveConvex 𝕜 K) :
    IsConvexConcave 𝕜 (Function.swap K) :=
  (isConcaveConvex_iff_swap K).1 hK

/-- Whole-space orientation-swap bridge for the disjunctive saddle owner. -/
theorem IsSaddle.swap {K : U → X → L} (hK : IsSaddle 𝕜 K) :
    IsSaddle 𝕜 (Function.swap K) :=
  (isSaddle_iff_swap K).1 hK

end Shape

end SaddleFunction

/-!
The shape owners introduced in Definition 33.0.1 are intrinsically predicates on bifunctions.
Expose the same API under `Bifunction` so downstream theorem surfaces can use the intrinsic owner
namespace while preserving existing `SaddleFunction` names.
-/
namespace Bifunction

export SaddleFunction
  (IsConcaveConvexOn IsConvexConcaveOn IsSaddleOn
    IsConcaveConvex IsConvexConcave IsSaddle
    isConcaveConvexOn_iff isConvexConcaveOn_iff
    isConvexConcaveOn_iff_swap isConcaveConvexOn_iff_swap
    isConcaveConvex_iff isConvexConcave_iff
    isConvexConcave_iff_swap isConcaveConvex_iff_swap
    isSaddleOn_iff isSaddleOn_iff_swap
    isSaddle_iff isSaddle_iff_swap
    IsConcaveConvexOn.isSaddleOn IsConvexConcaveOn.isSaddleOn
    IsConvexConcaveOn.swap IsConcaveConvexOn.swap IsSaddleOn.swap
    IsConcaveConvex.isSaddle IsConvexConcave.isSaddle
    IsConvexConcave.swap IsConcaveConvex.swap IsSaddle.swap)

end Bifunction
