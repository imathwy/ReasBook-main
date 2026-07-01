import Mathlib.RingTheory.FinitePresentation
import Mathlib.Tactic.Recall

/- Lemma 10.6.2 (00F4): the permanence properties of finite type and finite presentation are
exactly the canonical mathlib theorems recalled below. -/

/- Lemma 10.6.2 (1): a composition of ring maps of finite type is again of finite type. This is
the canonical mathlib theorem `RingHom.FiniteType.comp`. -/
recall RingHom.FiniteType.comp

/- Lemma 10.6.2 (2): a composition of ring maps of finite presentation is again of finite
presentation. This is the canonical mathlib theorem `RingHom.FinitePresentation.comp`. -/
recall RingHom.FinitePresentation.comp

/- Lemma 10.6.2 (3): given ring maps `R → S' → S`, if the composite `R → S` is of finite type,
then `S' → S` is of finite type. This is the canonical mathlib theorem
`RingHom.FiniteType.of_comp_finiteType`. -/
recall RingHom.FiniteType.of_comp_finiteType

/- Lemma 10.6.2 (4): given ring maps `R → S' → S`, if `R → S` is of finite presentation and
`R → S'` is of finite type, then `S' → S` is of finite presentation. This is the canonical
mathlib theorem `RingHom.FinitePresentation.of_comp_finiteType`. -/
recall RingHom.FinitePresentation.of_comp_finiteType
