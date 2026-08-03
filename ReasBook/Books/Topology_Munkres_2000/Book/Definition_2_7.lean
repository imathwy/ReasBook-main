module

import Init

/- Definition 2.7: Given `f : A → B` and `g : B → C`, their composite
`g ∘ f : A → C` is the function obtained by applying `f` and then `g`. -/
#check Function.comp

-- Evaluation of a composite satisfies `(g ∘ f) a = g (f a)`.
#check Function.comp_apply
