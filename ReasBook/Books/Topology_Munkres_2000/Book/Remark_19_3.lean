module

import Topology_Munkres_2000.Book.Definition_19_4

universe u v

variable {J : Type u} {X : Type v}

open scoped CartesianProduct

/- Remark 19.3: As in Definition 19.4, the Cartesian product of an indexed
family `A : J → Set X` is the set `∏ α, A α` of functions whose value at each
index lies in the corresponding set. -/
#check fun (A : J → Set X) ↦ ∏ α, A α

/- Membership in the full indexed product is the pointwise membership
condition. -/
#check fun {J : Type u} {X : Type v} (A : J → Set X) (x : J → X) ↦
  (Set.mem_univ_pi : x ∈ ∏ α, A α ↔ ∀ α, x α ∈ A α)
