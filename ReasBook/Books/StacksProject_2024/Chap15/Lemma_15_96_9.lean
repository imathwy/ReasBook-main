import StacksProject_2024.Chap15.Lemma_15_96_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/-
Domain-style sampling:
- primary domain: composition of the Berthelot-Ogus operator `η_f` on cochain complexes of
  `A`-modules;
- sampled owner declarations in this domain:
  `BerthelotOgusInt.complex`,
  `BerthelotOgusInt.IsTermwiseFTorsionFree`,
  `etaFComplex`;
- best owner abstraction:
  `source-facing`: the bounded-below `ℕ`-indexed statement that iterating `η_g` and then `η_f`
    agrees with `η_(fg)`;
  `core/canonical`: the source-facing owner `etaFComplex` on `NatModuleCochainComplex A`;
  `bridge/view`: the corresponding `ℤ`-indexed extension-by-zero construction
    `BerthelotOgusInt.complex` on `ModuleComplex A` under `[K.IsStrictlyGE 0]`;
- primitive data vs derived API: the primitive inputs are the scalars `f`, `g`, the bounded-below
  complex `M`, and the termwise `(fg)`-torsion-freeness hypothesis. The `ℤ`-indexed equality is
  only a bridge statement for complexes concentrated in nonnegative degrees. -/

namespace BerthelotOgusInt

open scoped BerthelotOgusInt

-- Proof sketch: unfold the degree-`n` defining intersections for `η_f (η_g M)` and `η_{fg} M`.
-- The hypothesis that multiplication by `fg` is injective on every term already forces the
-- iterated range conditions to agree with the single range condition for `(fg)^n`, while the
-- differential condition is unchanged after rewriting powers in the commutative ring `A`. The
-- source nonzerodivisor assumptions on `f` and `g` are therefore redundant for this equality.
/-- Bounded-below `ℤ`-indexed bridge form of Lemma `15.96.9`: if multiplication by `fg` is
injective on every term of a cochain complex concentrated in nonnegative degrees, then applying the
Berthelot-Ogus operator first for `g` and then for `f` agrees with applying it once for `fg`. -/
theorem complex_comp_eq_complex_mul
    (f g : A) (K : ModuleComplex A) [K.IsStrictlyGE 0]
    (hK : IsTermwiseFTorsionFree (f * g) K) :
    η[f] (η[g] K) = η[f * g] K := by
  sorry

end BerthelotOgusInt

-- Proof sketch: transport the owner equality
-- `BerthelotOgusInt.complex f
--     (BerthelotOgusInt.complex g (M.extend ComplexShape.embeddingUpNat)) =
--   BerthelotOgusInt.complex (f * g) (M.extend ComplexShape.embeddingUpNat)` to the source-facing
-- `ℕ`-indexed complexes by restricting to nonnegative degrees and using the defining
-- degreewise transport built into `η[f] M`.
/-- Lemma 15.96.9 in the bounded-below bridge/view: if multiplication by `fg` is injective on
every term of `M^\bullet`, then applying the Berthelot-Ogus operator first for `g` and then for
`f` gives the same `ℕ`-indexed cochain complex as applying it once for `fg`. -/
theorem etaFComplex_comp_eq_etaFComplex_mul
    (f g : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree (f * g) M) :
    η[f] (η[g] M) = η[f * g] M := by
  sorry

end
