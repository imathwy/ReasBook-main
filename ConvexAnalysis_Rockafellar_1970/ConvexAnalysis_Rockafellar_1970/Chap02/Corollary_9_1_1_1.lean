import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_1_1

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:
- `source-facing`: Corollary 9.1.1.1 isolates the closedness consequence of Corollary 9.1.1 for a
  finite Minkowski sum `C₁ + ··· + C_m`.
- `core/canonical`: the owner declaration is the already source-faithful theorem
  `Set.ZeroSumRecessionImpLineality.isClosed_sum` from Corollary 9.1.1.
- `bridge/view`: this file contributes no extra mathematics beyond isolating that already existing
  closedness clause, so it should reuse the owner theorem directly rather than restating it as a
  second exact-interface theorem.

Domain-style sampling used here:
- the owner theorem
  `Set.ZeroSumRecessionImpLineality.isClosed_sum`;
- the owner-side recession and lineality operators `0⁺[𝕜]` and `lin[𝕜](·)`;
- the owner-side closedness predicate `IsClosed`.

Primitive data vs derived API:
- this item adds no new primitive data beyond the hypotheses already accepted by the owner theorem;
- the only content is direct canonical reuse of that existing closedness statement.

Layer target: `bridge/view`; the file is a recall-only reuse of the canonical chapter theorem.
-/

/- Corollary 9.1.1.1 isolates the already established closedness clause of Corollary 9.1.1, so
the canonical chapter entry is recalled directly instead of introducing a duplicate theorem. -/
recall Set.ZeroSumRecessionImpLineality.isClosed_sum
