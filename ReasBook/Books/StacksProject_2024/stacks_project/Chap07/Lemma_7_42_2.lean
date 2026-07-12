import Mathlib
import StacksProject_2024.Chap07.Definition_7_42_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 7.42.2:
- primary domain: Grothendieck topologies, sheafification, and initial/terminal objects in the
  sheaf category;
- sampled owner API:
  `GrothendieckTopology.IsSheafTheoreticallyEmpty`,
  `GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv`,
  `Sheaf.isTerminalOfBotCover`,
  `Presieve.isTerminal_of_isSheafFor_empty_presieve`;
- source/core/bridge triage:
  `source-facing`: the equivalent reformulations and pullback stability of sheaf theoretically
  empty objects;
  `core/canonical`: the owner predicate
  `J.IsSheafTheoreticallyEmpty U := Nonempty (IsInitial (h[U]^#[J]))`;
  `bridge/view`: the unique-sections and bottom-sieve-cover reformulations.

Primitive data are only `J`, `U`, and the canonical owner predicate. The unique-sections and
bottom-sieve clauses are derived API, so local helper declarations for the empty presheaf and its
sheafification are unnecessary duplicate wheel definitions and are removed in favor of the
canonical owners above. -/

-- Proof sketch: the canonical map `∅^# ⟶ h_U^#` is an isomorphism exactly when precomposition
-- with it induces bijections on Hom-sets into every sheaf. By the sheafification adjunction,
-- `Hom(h_U^#, ℱ)` identifies with sections `ℱ(U)`, while `Hom(∅^#, ℱ)` is always a singleton
-- because `∅` is initial in presheaves. This yields the unique-sections formulation.
/-- An object `U` is sheaf theoretically empty exactly when every set-valued sheaf on `(C, J)`
has a unique section over `U`. -/
theorem sheafTheoreticallyEmpty_iff_forall_unique_sections
    (J : GrothendieckTopology C) (U : C) :
    J.IsSheafTheoreticallyEmpty U ↔
      ∀ ℱ : Sheaf J (Type (max u v)), Nonempty (Unique (ℱ.obj.obj (op U))) := by
  sorry

-- Proof sketch: specialize the previous theorem to the sheaf of closed sieves to detect when the
-- bottom sieve is covering, and use the empty-presieve sheaf condition to translate a covering
-- bottom sieve into singleton section sets for any sheaf.
/-- An object `U` is sheaf theoretically empty exactly when the bottom sieve on `U` is covering. -/
@[simp]
theorem isSheafTheoreticallyEmpty_iff_bot_mem
    (J : GrothendieckTopology C) (U : C) :
    J.IsSheafTheoreticallyEmpty U ↔ (⊥ : Sieve U) ∈ J U := by
  sorry

-- Proof sketch: use the characterization of sheaf theoretically empty objects by the canonical
-- map `∅^# ⟶ h_U^#`, identify morphisms from `h_U^#` to a sheaf with sections over `U`, apply the
-- sheaf condition for the bottom sieve to characterize singleton section sets, and specialize to
-- the sheafification of the initial presheaf. The bottom-sieve clause is exactly the empty-family
-- covering condition.
/-- Lemma 7.42.2: for an object `U` of a site `(C, J)`, the following are equivalent: `U` is
sheaf theoretically empty, every set-valued sheaf on `(C, J)` has a unique section over `U`, the
sheafification `∅^#` of the initial presheaf has a unique section over `U`, that section type is
nonempty, and the bottom sieve on `U` is covering. -/
theorem sheafTheoreticallyEmpty_tfae (J : GrothendieckTopology C) (U : C) :
    List.TFAE
      [ J.IsSheafTheoreticallyEmpty U,
        ∀ ℱ : Sheaf J (Type (max u v)), Nonempty (Unique (ℱ.obj.obj (op U))),
        Nonempty (Unique ((J.sheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v)))).obj (op U))),
        Nonempty ((J.sheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v)))).obj (op U)),
        (⊥ : Sieve U) ∈ J U ] := by
  sorry

-- Proof sketch: translate sheaf theoretical emptiness into the bottom-sieve covering condition
-- via `sheafTheoreticallyEmpty_tfae`, pull back the bottom sieve along `f`, use stability of
-- covering sieves and `Sieve.pullback_bot`, and translate back.
namespace IsSheafTheoreticallyEmpty

/-- Pullbacks of sheaf theoretically empty objects are sheaf theoretically empty. -/
theorem of_arrow
    {J : GrothendieckTopology C} {U U' : C}
    (hU : J.IsSheafTheoreticallyEmpty U)
    (f : U' ⟶ U) :
    J.IsSheafTheoreticallyEmpty U' := by
  sorry

end IsSheafTheoreticallyEmpty

end CategoryTheory.GrothendieckTopology
