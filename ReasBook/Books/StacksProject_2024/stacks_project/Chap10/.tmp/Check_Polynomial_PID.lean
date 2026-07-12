import Mathlib

universe u
section
variable {k : Type u} [Field k]
#check (inferInstance : IsDomain (Polynomial k))
#check (inferInstance : IsPrincipalIdealRing (Polynomial k))
end
