import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Lemma 8.2.1 is a `core/canonical` recall in the prestack/descent domain: the source-facing
assignment sending `V/U : Over U` to the morphism type `Hom(V^* x, V^* y)` is already owned by
mathlib as `Pseudofunctor.presheafHom`. -/
recall Pseudofunctor.presheafHom

end CategoryTheory
