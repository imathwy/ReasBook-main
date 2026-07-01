import Mathlib

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}

/-- Lemma 12.5.13 (1): in an abelian category, a cartesian square whose right morphism is an
epimorphism is cocartesian. -/
theorem isPushout_of_isPullback_of_epi_right [Epi k] (sq : IsPullback g f k h) :
    IsPushout g f k h := by
  let S := sq.toCommSq
  let e : S.shortComplex' ≅ S.shortComplex :=
    ShortComplex.isoMk (Iso.refl _) (biprod.mapIso (Iso.refl X) (-Iso.refl Y)) (Iso.refl _)
      (by
        apply biprod.hom_ext <;> simp)
      (by
        apply biprod.hom_ext' <;> simp)
  let T := S.shortComplex
  have hExact : T.Exact :=
    ShortComplex.exact_of_iso e sq.exact_shortComplex'
  letI : Epi T.g := by
    change Epi (biprod.desc k h)
    infer_instance
  obtain ⟨hT⟩ := T.exact_and_epi_g_iff_g_is_cokernel.1 ⟨hExact, inferInstance⟩
  exact IsPushout.of_isColimit (S.isColimitEquivIsColimitCokernelCofork.symm hT)

/-- Lemma 12.5.13 (2): in an abelian category, in a cartesian square, if the right morphism is
an epimorphism, then the left morphism is an epimorphism. -/
theorem epi_left_of_isPullback_of_epi_right [Epi k] (sq : IsPullback g f k h) :
    Epi f := by
  simpa using Abelian.epi_snd_of_isLimit k h sq.isLimit

/-- Lemma 12.5.13 (3): in an abelian category, a cocartesian square whose top morphism is a
monomorphism is cartesian. -/
theorem isPullback_of_isPushout_of_mono_top [Mono g] (sq : IsPushout g f k h) :
    IsPullback g f k h := by
  let sqOp : IsPullback k.op h.op g.op f.op := sq.flip.op
  exact (isPushout_of_isPullback_of_epi_right sqOp).unop.flip

/-- Lemma 12.5.13 (4): in an abelian category, in a cocartesian square, if the top morphism is a
monomorphism, then the bottom morphism is a monomorphism. -/
theorem mono_bottom_of_isPushout_of_mono_top [Mono g] (sq : IsPushout g f k h) :
    Mono h := by
  simpa using Abelian.mono_inr_of_isColimit g f sq.isColimit

end CategoryTheory
