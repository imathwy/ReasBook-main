module

public import Topology_Munkres_2000.Book.Notation_74_1.SignedLetter

public section

open scoped SignedLetter

/- Notation 74.1: Positive orientations omit the exponent `+1`. With labels
`0 = a` and `1 = b`, the three choices of initial vertex give `a⁻¹ba`,
`baa⁻¹`, and `aa⁻¹b`. In a signed-letter context, a bare label denotes positive
orientation, while `a⁻¹` denotes inverse orientation. -/
#check PolygonWord
#check (⟨[(0 : Fin 2)⁻¹, (1 : Fin 2), (0 : Fin 2)], by decide⟩ : PolygonWord (Fin 2))
#check (⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2)⁻¹], by decide⟩ : PolygonWord (Fin 2))
#check (⟨[(0 : Fin 2), (0 : Fin 2)⁻¹, (1 : Fin 2)], by decide⟩ : PolygonWord (Fin 2))
