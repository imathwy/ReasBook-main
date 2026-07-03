import Mathlib
import stacks_project.Chap13.Remark_13_33_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D]

/- Domain-style sampling for Lemma 13.33.4:
- primary domain: sequential diagrams in a triangulated category, together with homotopy colimits
  and the source-facing structure maps from Remark 13.33.2;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.IsHomotopyColimitOf.exists_presentation`,
  `CategoryTheory.exists_iso_between_derived_colimit_presentations`,
  `CategoryTheory.sequentialTelescopeMap`,
  `Preorder.Monotone.functor`;
- best owner abstraction: the original sequential system is the canonical diagram `K : ℕ ⥤ D`;
  `IsHomotopyColimitOf K X` is the core owner, and a subsequence should be only a thin
  reindexing view of `K`, not a new ambient system owner;
- primitive-vs-derived split:
  the primitive data are the sequential diagram `K` and the strictly increasing index function
  `s : ℕ → ℕ`;
  the reindexed subsystem is derived API obtained by precomposing `K` with the monotone functor
  induced by `s`, while the explicit telescope-presentation maps and distinguished-triangle
  witnesses remain bridge-level source-facing data.

Source/core/bridge triage:
- `source-facing`: the sequential system `(K_n, f_n)` and the chosen subsequence of indices;
- `core/canonical`: the predicate `IsHomotopyColimitOf K X`;
- `bridge/view`: the reindexed diagram `hs.monotone.functor ⋙ K`, obtained by precomposing `K`
  along the monotone functor attached to the strictly increasing map `s`, together with the
  explicit telescope-presentation data used to compare chosen structure maps. -/

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

-- Proof sketch: use Remark 13.33.2 to choose source-style telescope presentations from each
-- `IsHomotopyColimitOf` hypothesis, compare them using the subsequence reindexing bridge from
-- Remarks 13.33.2 and 13.33.3, and transport the resulting isomorphism back to the canonical
-- owner predicate. The converse direction is symmetric.
/-- Lemma 13.33.4: an object is a homotopy colimit of a strictly increasing
subsequence if and only if it is a homotopy colimit of the original sequential system. -/
theorem isHomotopyColimitOf_subsequence_iff
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Khocolim : D} :
    IsHomotopyColimitOf (hs.monotone.functor ⋙ K) Khocolim ↔ IsHomotopyColimitOf K Khocolim :=
  sorry

end

end CategoryTheory
