import Mathlib

universe u v

section

variable {K : Type u} [Field K] {A : Type v} [Nonempty A]

/-
Domain triage:
* primary domain: linear algebra over subfields and directed intersections of subfields;
* sampled owner declarations:
  - `Subfield.mem_iInf`,
  - `Submodule.restrictScalars`,
  - `Submodule.pi`,
  - `Subalgebra.mem_bot`;
* best owner abstraction: for a subfield `k ≤ K`, the vectors of `K^n` with all coordinates in `k`
  are the canonical `k`-submodule `k.vectorSubmodule n`;
* primitive data: the family of subfields `Kα` and the `K`-subspace `V`;
* derived API: existence of a nonzero vector in `V` whose coordinates lie in a given subfield;
* layer triage:
  - `source-facing`: the existence criterion of Lemma `15.46.3`;
  - `core/canonical`: `Submodule.restrictScalars`, `Submodule.pi`, and `Subfield.mem_iInf`;
  - `bridge/view`: `Subfield.vectorSubmodule`, the coordinatewise copy of `k` in `K^n`.
-/

namespace Subfield

/-- The coordinatewise copy of `k` inside `K^n`, viewed as a `k`-submodule of `K^n`. -/
abbrev vectorSubmodule (k : Subfield K) (n : ℕ) : Submodule k (Fin n → K) :=
  Submodule.pi Set.univ (fun _ : Fin n ↦ (⊥ : Subalgebra k K).toSubmodule)

end Subfield

-- Proof sketch: for `n = 0`, the coordinatewise submodule `k.vectorSubmodule 0` is trivial, so
-- both
-- sides are false. For `n = 1`, the claim is exactly the statement that membership in
-- `k = ⨅ α, Kα α` is equivalent to membership in every `Kα α` via `Subfield.mem_iInf`; the
-- nonemptiness hypothesis rules out the degenerate empty intersection `⨅ α, Kα α = ⊤`. For the
-- inductive step, first study the intersection of `V` with the last `n - 1` coordinates, then
-- choose an index `α` for which this smaller intersection over `Kα α` is trivial. A nonzero
-- vector in `V` with coordinates in `Kα α` can then be normalized so that its first coordinate is
-- `1`, forcing every other `Kα α`-rational vector in `V` to be a scalar multiple of it. The
-- downward directedness of the family and the hypothesis `k = ⨅ α, Kα α` then show that the
-- remaining coordinates already lie in `k`.
/-- Lemma 15.46.3: for a nonempty downward directed family of subfields of `K` whose intersection
is `k`, a `K`-subspace of `K^n` contains a nonzero vector with all coordinates in `k` if and only
if it contains such a vector over every subfield in the family. -/
theorem exists_nonzero_vector_in_base_subfield_iff_forall_exists_nonzero_vector_in_family
    (k : Subfield K) (Kα : A → Subfield K) (h_inter : k = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) {n : ℕ} (V : Submodule K (Fin n → K)) :
    (∃ v ∈ V.restrictScalars k ⊓ k.vectorSubmodule n, v ≠ 0) ↔
      ∀ α, ∃ v ∈ V.restrictScalars (Kα α) ⊓ (Kα α).vectorSubmodule n, v ≠ 0 := sorry

end
