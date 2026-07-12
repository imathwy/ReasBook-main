import StacksProject_2024.Chap14.Lemma_14_18_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SimplicialObject
open SimplicialObject.Splitting
open scoped Simplicial

universe u

noncomputable section

namespace SSet

variable {U V : SSet.{u}} (f : U ⟶ V)

/- Domain-style sampling for 14.18.3:
- primary domain: simplicial-set morphisms acting on nondegenerate simplices
- sampled owner API:
  `SimplicialObject.Splitting`,
  `SimplicialObject.Splitting.φ`,
  `SimplicialObject.Split.mk'`,
  `SimplicialObject.Split.Hom`,
  `SSet.nonDegenerateSplitting`
- best owner abstraction: the split simplicial sets `Split.mk' U.nonDegenerateSplitting` and
  `Split.mk' V.nonDegenerateSplitting`, together with the canonical bridge
  `toNonDegenerateSplitHom f hPreserves`
- primitive data: the canonical splittings, the underlying simplicial-set morphism `f`, and the
  proof that `f` sends nondegenerate simplices to nondegenerate simplices
- derived API: the induced degreewise maps on nondegenerate simplices
  `(toNonDegenerateSplitHom f hPreserves).f n`
- source/core/bridge triage: the degreewise injective, surjective, and bijective consequences are
  the `source-facing` statements; the induced maps on nondegenerate summands are only a
  `bridge/view`, so the public statements should use the canonical split-owner bridge rather than
  a parallel local wrapper
-/

section

variable
  (hPreserves :
    ∀ ⦃n : ℕ⦄ (x : U.nonDegenerate n),
      (U.nonDegenerateSplitting.φ f n) x ∈ V.nonDegenerate n)

/-- The canonical morphism between the split simplicial sets attached to the nondegenerate
splittings of `U` and `V`, induced by a simplicial-set morphism that preserves nondegenerate
simplices. -/
abbrev toNonDegenerateSplitHom :
    Split.mk' U.nonDegenerateSplitting ⟶ Split.mk' V.nonDegenerateSplitting where
  F := f
  f := fun n x ↦ ⟨U.nonDegenerateSplitting.φ f n x, hPreserves x⟩
  comm := fun _ ↦ rfl

/-- Helper for Lemma 14.18.3: the coproduct presentation attached to a split simplicial set is
bijection in every degree. -/
private lemma split_cofan_fromSigma_bijective
    {S : Split (Type u)} (n : ℕ) :
    Function.Bijective ((S.s.cofan (op ⦋n⦌)).cofanTypes.fromSigma) := by
  -- The colimit axiom for a splitting says exactly that the cofan is a coproduct in `Type`.
  simpa using
    ((Limits.Cofan.nonempty_isColimit_iff_bijective_fromSigma (S.s.cofan (op ⦋n⦌))).1
      ⟨S.s.isColimit (op ⦋n⦌)⟩)

/-- Helper for Lemma 14.18.3: a morphism of split simplicial sets preserves the coproduct
decomposition in each degree. -/
private lemma split_degree_fromSigma_comm
    {S₁ S₂ : Split (Type u)} (Φ : S₁ ⟶ S₂) (n : ℕ) :
    ((S₂.s.cofan (op ⦋n⦌)).cofanTypes.fromSigma) ∘
        Sigma.map id (fun A : IndexSet (op ⦋n⦌) ↦ Φ.f (unop A.fst).len) =
      Φ.F.app (op ⦋n⦌) ∘ ((S₁.s.cofan (op ⦋n⦌)).cofanTypes.fromSigma) := by
  -- Evaluate both composites on one summand of the sigma coproduct and use naturality of the
  -- distinguished summand injections.
  funext x
  rcases x with ⟨A, x⟩
  simpa [Function.comp, Limits.CofanTypes.fromSigma] using
    (congrFun (Split.cofan_inj_naturality_symm Φ (Δ := op ⦋n⦌) A) x).symm

/-- Helper for Lemma 14.18.3: injectivity on every nondegenerate summand forces injectivity on
the whole degree-`n` simplex set of a split simplicial set. -/
private lemma split_degree_map_injective_of_component_injective
    {S₁ S₂ : Split (Type u)} (Φ : S₁ ⟶ S₂)
    (hΦ : ∀ m : ℕ, Function.Injective (Φ.f m)) :
    ∀ n : ℕ, Function.Injective (Φ.F.app (op ⦋n⦌)) := by
  intro n
  let g₁ := ((S₁.s.cofan (op ⦋n⦌)).cofanTypes.fromSigma)
  let g₂ := ((S₂.s.cofan (op ⦋n⦌)).cofanTypes.fromSigma)
  let m :
      ((A : IndexSet (op ⦋n⦌)) × summand S₁.s.N (op ⦋n⦌) A) →
        ((A : IndexSet (op ⦋n⦌)) × summand S₂.s.N (op ⦋n⦌) A) :=
    Sigma.map id (fun A : IndexSet (op ⦋n⦌) ↦ Φ.f (unop A.fst).len)
  have hg₁ : Function.Bijective g₁ := split_cofan_fromSigma_bijective (S := S₁) n
  have hg₂ : Function.Bijective g₂ := split_cofan_fromSigma_bijective (S := S₂) n
  have hm : Function.Injective m := by
    -- The middle sigma-map is injective because it is identity on the index set and injective on
    -- every summand.
    refine Function.Injective.sigma_map ?_ ?_
    · intro A B hAB
      exact hAB
    · intro A
      simpa [m] using hΦ A.1.unop.len
  have hcomm := split_degree_fromSigma_comm (Φ := Φ) n
  -- Pull both simplices back to the coproduct, compare there, and push the equality forward.
  intro x y hxy
  obtain ⟨x', rfl⟩ := hg₁.2 x
  obtain ⟨y', rfl⟩ := hg₁.2 y
  have hxy' : x' = y' := by
    have hxcomm : g₂ (m x') = Φ.F.app (op ⦋n⦌) (g₁ x') := by
      simpa [g₁, g₂, m, Function.comp] using congrFun hcomm x'
    have hycomm : Φ.F.app (op ⦋n⦌) (g₁ y') = g₂ (m y') := by
      simpa [g₁, g₂, m, Function.comp] using (congrFun hcomm y').symm
    apply hm
    apply hg₂.1
    exact hxcomm.trans (hxy.trans hycomm)
  exact congrArg g₁ hxy'

/-- Helper for Lemma 14.18.3: surjectivity on every nondegenerate summand forces surjectivity on
the whole degree-`n` simplex set of a split simplicial set. -/
private lemma split_degree_map_surjective_of_component_surjective
    {S₁ S₂ : Split (Type u)} (Φ : S₁ ⟶ S₂)
    (hΦ : ∀ m : ℕ, Function.Surjective (Φ.f m)) :
    ∀ n : ℕ, Function.Surjective (Φ.F.app (op ⦋n⦌)) := by
  intro n
  let g₁ := ((S₁.s.cofan (op ⦋n⦌)).cofanTypes.fromSigma)
  let g₂ := ((S₂.s.cofan (op ⦋n⦌)).cofanTypes.fromSigma)
  let m :
      ((A : IndexSet (op ⦋n⦌)) × summand S₁.s.N (op ⦋n⦌) A) →
        ((A : IndexSet (op ⦋n⦌)) × summand S₂.s.N (op ⦋n⦌) A) :=
    Sigma.map id (fun A : IndexSet (op ⦋n⦌) ↦ Φ.f (unop A.fst).len)
  have hg₁ : Function.Bijective g₁ := split_cofan_fromSigma_bijective (S := S₁) n
  have hg₂ : Function.Bijective g₂ := split_cofan_fromSigma_bijective (S := S₂) n
  have hm : Function.Surjective m := by
    -- The middle sigma-map is surjective because it is identity on the index set and surjective on
    -- every summand.
    refine Function.Surjective.sigma_map ?_ ?_
    · intro A
      exact ⟨A, rfl⟩
    · intro A
      simpa [m] using hΦ A.1.unop.len
  have hcomm := split_degree_fromSigma_comm (Φ := Φ) n
  -- Lift a target simplex to the coproduct, solve surjectivity there, and descend back.
  intro y
  obtain ⟨y', rfl⟩ := hg₂.2 y
  obtain ⟨x', hx'⟩ := hm y'
  refine ⟨g₁ x', ?_⟩
  calc
    Φ.F.app (op ⦋n⦌) (g₁ x') = g₂ (m x') := by
      simpa [g₁, g₂, m, Function.comp] using (congrFun hcomm x').symm
    _ = g₂ y' := by simpa [hx']

-- Proof sketch: apply the canonical splittings `U.nonDegenerateSplitting` and
-- `V.nonDegenerateSplitting` by nondegenerate simplices. Hypothesis `hPreserves` makes the
-- canonical split morphism `toNonDegenerateSplitHom f hPreserves` land in the distinguished
-- nondegenerate summands of `V`, and injectivity on those summands implies injectivity on each
-- coproduct component, hence on every degree map `f.app (op ⦋n⦌)`.
/-- Lemma 14.18.3: if a morphism of simplicial sets sends nondegenerate simplices to
nondegenerate simplices and the induced map on nondegenerate simplices is injective, then each
degree map `f_n` is injective. -/
@[stacks 017S]
theorem degreewise_injective_of_nondegenerate_injective
    (hInjective :
      ∀ n : ℕ, Function.Injective ((toNonDegenerateSplitHom f hPreserves).f n)) :
    ∀ n : ℕ, Function.Injective (f.app (op ⦋n⦌)) := by
  -- Apply the generic split-level injectivity transfer to the canonical morphism of
  -- nondegenerate splittings.
  simpa [toNonDegenerateSplitHom] using
    split_degree_map_injective_of_component_injective
      (Φ := toNonDegenerateSplitHom f hPreserves) hInjective

-- Proof sketch: use the same splitting argument as in the injective case. Surjectivity of the map
-- on nondegenerate summands implies surjectivity on each coproduct decomposition coming from
-- `U.nonDegenerateSplitting` and `V.nonDegenerateSplitting`, so every degree map of `f` is
-- surjective.
/-- If a simplicial-set morphism preserves nondegenerate simplices and is surjective on the
nondegenerate simplices, then it is surjective in every degree. -/
theorem degreewise_surjective_of_nondegenerate_surjective
    (hSurjective :
      ∀ n : ℕ, Function.Surjective ((toNonDegenerateSplitHom f hPreserves).f n)) :
    ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)) := by
  -- Apply the same coproduct transfer, now using surjectivity on each nondegenerate summand.
  simpa [toNonDegenerateSplitHom] using
    split_degree_map_surjective_of_component_surjective
      (Φ := toNonDegenerateSplitHom f hPreserves) hSurjective

-- Proof sketch: combine the injective and surjective arguments for the induced map on the
-- nondegenerate summands. The canonical splitting decompositions then yield bijectivity of each
-- degree map.
/-- If a simplicial-set morphism preserves nondegenerate simplices and is bijective on the
nondegenerate simplices, then it is bijective in every degree. -/
theorem degreewise_bijective_of_nondegenerate_bijective
    (hBijective :
      ∀ n : ℕ, Function.Bijective ((toNonDegenerateSplitHom f hPreserves).f n)) :
    ∀ n : ℕ, Function.Bijective (f.app (op ⦋n⦌)) := by
  -- Combine the injective and surjective transfer results for the same split morphism.
  intro n
  refine ⟨?_, ?_⟩
  · exact degreewise_injective_of_nondegenerate_injective (f := f) hPreserves
      (fun m ↦ (hBijective m).1) n
  · exact degreewise_surjective_of_nondegenerate_surjective (f := f) hPreserves
      (fun m ↦ (hBijective m).2) n

end

end SSet
