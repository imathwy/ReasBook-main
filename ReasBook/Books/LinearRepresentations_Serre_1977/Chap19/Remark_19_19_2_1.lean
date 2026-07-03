import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_2_2
import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_3_2
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_3_6

-- Declarations for this item will be appended below by the statement pipeline.

namespace Representation

/- Remark 19-19.2-1 (1): the reference [26] proves part (i) of Theorem 44 by a somewhat more
complicated method, but that method yields the stronger conclusion that the algebra `Q_l[G]` is
quasisplit (cf. 12.2). In the chapter/project API the relevant core owner is the Chapter 12
predicate `Representation.IsQuasisplitGroupAlgebra`; this remark adds no new local owner or bridge
beyond pointing to that canonical notion. -/
recall IsQuasisplitGroupAlgebra

/- Remark 19-19.2-1 (2): one can deduce part (ii) of Theorem 44 from part (i) together with the
Fong-Swan theorem (Theorem 38). In the project API the source-facing theorem-level owner for the
lifting clause used here is the Chapter 16 theorem
`Representation.satisfiesConditionRPrime_of_isPSolvable`; the
remark adds no parallel local implication theorem. -/
recall satisfiesConditionRPrime_of_isPSolvable

/- Remark 19-19.2-1 (3): both the Artin and Swan representations are handled by the Chapter 12
realizability owner theorem
`Representation.isRealizableOver_of_hasEnoughRootsOfUnity`: any chosen finite-dimensional complex
realization is realizable over a field `K` with `HasEnoughRootsOfUnity K (Monoid.exponent G)`,
including Fontaine's Witt-vector field in the source application. The remark adds no Artin- or
Swan-specific wrapper theorem beyond that canonical owner. -/
recall isRealizableOver_of_hasEnoughRootsOfUnity

end Representation
