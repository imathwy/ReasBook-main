import chapter1_reference_format.Chap01.Lemma_1_1_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {S : Type u}

/- Lemma 1.7.9 (1): for an equivalence relation on `S`, the classes `C_x` and `C_y` intersect
nontrivially if and only if `x` and `y` are equivalent. -/
recall Setoid.equivClass_inter_nonempty_iff (s : Setoid S) (x y : S) :
    (({z | s z x} : Set S) ∩ {z | s z y}).Nonempty ↔ s x y

namespace Setoid

/-- Lemma 1.7.9 (2): if two equivalence classes intersect nontrivially, then they are equal. -/
theorem equivClass_eq_of_inter_nonempty (s : Setoid S) {x y : S}
    (hxy : (({z | s z x} : Set S) ∩ {z | s z y}).Nonempty) :
    ({z | s z x} : Set S) = {z | s z y} :=
  s.equivClass_eq_of_related ((s.equivClass_inter_nonempty_iff x y).1 hxy)

end Setoid
