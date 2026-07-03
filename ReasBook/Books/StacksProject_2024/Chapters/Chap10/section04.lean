import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_4_1 (from Chap10) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : ShortComplex.SnakeInput C)

/- Lemma 10.4.1 is source-facing for abelian groups, but its canonical owner abstraction in
mathlib is a `ShortComplex.SnakeInput C`, encoding the commutative diagram with exact rows and
kernel/cokernel endpoint data. The associated snake-lemma sequence
`Ker α ⟶ Ker β ⟶ Ker γ ⟶ Coker α ⟶ Coker β ⟶ Coker γ` is then exactly the derived lemma
`S.snake_lemma`, stated uniformly for any abelian category. -/
recall ShortComplex.SnakeInput.snake_lemma

/- Derived API from the same owner abstraction: if the top horizontal map is injective, then the
induced map `Ker α ⟶ Ker β` is injective. This is the canonical instance
`ShortComplex.SnakeInput.mono_L₀_f`, upgrading `[Mono S.L₁.f]` to `[Mono S.L₀.f]`. -/
recall ShortComplex.SnakeInput.mono_L₀_f

/- Dually, if the bottom horizontal map is surjective, then the induced map
`Coker β ⟶ Coker γ` is surjective. This is the canonical instance
`ShortComplex.SnakeInput.epi_L₃_g`, upgrading `[Epi S.L₂.g]` to `[Epi S.L₃.g]`. -/
recall ShortComplex.SnakeInput.epi_L₃_g

end CategoryTheory
