module

import Mathlib.Order.RelIso.Set

/- Proposition 10.1 (1): A subtype of a well-ordered type is well-ordered by the
restricted relation. -/
#check Subrel.instIsWellOrderSubtype

/- Proposition 10.1 (2): The product of two well-ordered types is well-ordered by
the dictionary order `Prod.Lex`. -/
#check instIsWellOrderProdLex
