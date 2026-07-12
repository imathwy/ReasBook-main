import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.17:
- primary domain: the snake lemma in an abelian category, packaged as a commutative diagram of
  short complexes with exact rows and kernel/cokernel endpoint data;
- sampled owner declarations:
  `ShortComplex.SnakeInput.δ`,
  `ShortComplex.SnakeInput.snd_δ_inr`,
  `ShortComplex.SnakeInput.snake_lemma`,
  `ShortComplex.SnakeInput.mono_L₀_f`,
  `ShortComplex.SnakeInput.epi_L₃_g`;
- best owner abstraction:
  `source-facing`: the connecting morphism, its characteristic square, the exact six-term snake
    sequence, and the endpoint mono/epi consequences stated in Lemma 12.5.17;
  `core/canonical`: the owner `ShortComplex.SnakeInput`;
  `bridge/view`: none is needed here, because the textbook kernel-cokernel sequence already
    appears as owner-derived API;
- primitive data vs derived API: the primitive data are the four short complexes, the vertical
  comparison morphisms, exactness of the middle rows, and the kernel/cokernel endpoint data
  bundled by `ShortComplex.SnakeInput`; the connecting morphism `δ`, the pullback-pushout square
  `snd_δ_inr`, the exact snake sequence `snake_lemma`, and the induced mono/epi results are all
  derived API, so this file should recall those canonical declarations directly rather than
  repackage them through local aliases or wrapper statements.
-/

/- Lemma 12.5.17 (1): for a snake input encoding a commutative diagram with exact rows in an
abelian category, the connecting morphism `ker γ ⟶ coker α` is the canonical boundary map
`S.δ : S.L₀.X₃ ⟶ S.L₃.X₁` provided by the snake-lemma owner abstraction. -/
recall ShortComplex.SnakeInput.δ

/- Companion recall: the canonical connecting morphism `S.δ` satisfies the textbook
pullback-pushout commutative square that characterizes the snake-lemma boundary map. -/
recall ShortComplex.SnakeInput.snd_δ_inr

/- Lemma 12.5.17 (2): the induced sequence on kernels, the connecting morphism, and cokernels is
exact. In the `SnakeInput` notation this is exactly the six-term snake-lemma sequence
`S.L₀.X₁ ⟶ S.L₀.X₂ ⟶ S.L₀.X₃ ⟶ S.L₃.X₁ ⟶ S.L₃.X₂ ⟶ S.L₃.X₃`. -/
recall ShortComplex.SnakeInput.snake_lemma

/- Lemma 12.5.17 (3): if the left map in the top exact row is injective, then the induced map on
kernels `ker α ⟶ ker β` is injective. In `SnakeInput` notation this is the monomorphism
`S.L₀.f`. -/
recall ShortComplex.SnakeInput.mono_L₀_f

/- Lemma 12.5.17 (4): if the right map in the bottom exact row is surjective, then the induced map
on cokernels `coker β ⟶ coker γ` is surjective. In `SnakeInput` notation this is the epimorphism
`S.L₃.g`. -/
recall ShortComplex.SnakeInput.epi_L₃_g

end CategoryTheory
