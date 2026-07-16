import StacksProject_2024.stacks_project.Chap09.Example_9_3_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

universe u

/-
Domain-style sampling for meromorphic function fields of Riemann surfaces:
- primary domain: the meromorphic function field `ℂ(X)` and its scalar/field structures;
- best owner abstraction: the source-facing owner `MeromorphicFunctionField`, written `ℂ(X)`,
  defined upstream in Example 9.3.6;
- primitive data: the quotient-field owner `MeromorphicFunctionField X`;
- derived API: the canonical `Algebra ℂ (ℂ(X))` instance, and under connectedness the canonical
  `Field (ℂ(X))` instance.

Layer triage:
- `source-facing`: `MeromorphicFunctionField X`;
- `bridge/view`: the `ℂ`-algebra structure expressing that `ℂ(X)` is an extension of `ℂ`;
- companion derived API: the field structure recalled from Example 9.3.6 when `X` is connected.

This file should therefore only recall those canonical instances, not introduce any parallel local
wrapper or alias. -/

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/- Example 9.6.5: if `X` is a Riemann surface, then its field of meromorphic functions `ℂ(X)` is
an extension field of `ℂ`. This file is a `bridge/view` recall of the canonical `ℂ`-algebra
instance on the source-facing owner `ℂ(X) = MeromorphicFunctionField X` defined upstream in
Example 9.3.6. Connectedness is not needed for this scalar-extension structure. -/
#check (inferInstance : Algebra ℂ (ℂ(X)))

end

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

/- Companion check: by Example 9.3.6, the same meromorphic function field carries its canonical
field structure, so together with the previous scalar-extension recall it is indeed an extension
field of `ℂ`. -/
#check (inferInstance : Field (ℂ(X)))

end
