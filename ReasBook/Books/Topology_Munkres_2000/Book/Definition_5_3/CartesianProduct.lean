module

public import Mathlib.Data.Set.Operations

public section

/- Notation for the Cartesian product of an indexed family of sets. -/
namespace CartesianProduct

scoped syntax "∏ " ident ", " term:67 : term

scoped macro_rules
  | `(∏ $i:ident, $A) => `(Set.pi Set.univ (fun $i ↦ $A))

end CartesianProduct
