import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory.Sequence
open scoped Pointwise

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}
variable {rs : List R}

private theorem quotSMulTop_map_injective (hS : S.ShortExact) {r : R}
    (hr : IsSMulRegular S.X₃ r) :
    Function.Injective (QuotSMulTop.map r S.f.hom) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hx0 : QuotSMulTop.map r S.f.hom x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (r • (⊤ : Submodule R S.X₁)) x
  rw [QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero] at hx0
  rw [Submodule.Quotient.mk_eq_zero]
  rcases (Submodule.mem_smul_pointwise_iff_exists (S.f.hom x) r
      (⊤ : Submodule R S.X₂)).mp hx0 with ⟨y, -, hy⟩
  have hy0 : S.g.hom y = 0 := by
    let g := S.g.hom
    change g y = 0
    apply hr.right_eq_zero_of_smul
    calc
      r • g y = g (r • y) := by rw [g.map_smul]
      _ = g (S.f.hom x) := by rw [hy]
      _ = 0 := by simp [g, S.moduleCat_zero_apply]
  have hy' : y ∈ LinearMap.range S.f.hom := by
    rw [hS.exact.moduleCat_range_eq_ker]
    simpa [LinearMap.mem_ker] using hy0
  rcases hy' with ⟨z, rfl⟩
  have hx' : x = r • z := by
    let f := S.f.hom
    apply hS.moduleCat_injective_f
    calc
      f x = r • f z := hy.symm
      _ = f (r • z) := by rw [f.map_smul]
  exact (Submodule.mem_smul_pointwise_iff_exists x r
    (⊤ : Submodule R S.X₁)).2 ⟨z, trivial, hx'.symm⟩

private theorem quotSMulTop_shortExact (hS : S.ShortExact) {r : R}
    (hr : IsSMulRegular S.X₃ r) :
    (ModuleCat.shortComplexOfCompEqZero
      (QuotSMulTop.map r S.f.hom) (QuotSMulTop.map r S.g.hom) <| by
        ext x
        simp [QuotSMulTop.map_apply_mk, S.moduleCat_zero_apply]).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (QuotSMulTop.map_exact r
    ((moduleCat_exact_iff_function_exact S).1 hS.exact) hS.moduleCat_surjective_g)
    (quotSMulTop_map_injective hS hr)
    (QuotSMulTop.map_surjective r hS.moduleCat_surjective_g)

-- Proof sketch: proceed by induction on the list `rs`. For the first element, apply
-- Lemma 10.4.1 to the endomorphisms given by multiplication by that element on the short exact
-- sequence to deduce injectivity on `S.X₂`. Modding out by the image of that element preserves
-- short exactness, so the induction hypothesis applies to the quotient short exact sequence.
/-- Lemma 10.68.8: in a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of `R`-modules, if a
sequence `rs` is regular on both end terms, then it is regular on the middle term. -/
@[stacks 0F1T]
theorem isRegular_X₂ (hS : S.ShortExact) (hX₁ : IsRegular S.X₁ rs) (hX₃ : IsRegular S.X₃ rs) :
    IsRegular S.X₂ rs := by
  induction rs generalizing S with
  | nil =>
      letI : Nontrivial S.X₁ := hX₁.nontrivial
      letI : Nontrivial S.X₂ := Function.Injective.nontrivial hS.moduleCat_injective_f
      exact IsRegular.nil R S.X₂
  | cons r rs ih =>
      rcases (isRegular_cons_iff S.X₁ r rs).1 hX₁ with ⟨hX₁r, hX₁rs⟩
      rcases (isRegular_cons_iff S.X₃ r rs).1 hX₃ with ⟨hX₃r, hX₃rs⟩
      have hX₂r : IsSMulRegular S.X₂ r :=
        isSMulRegular_of_range_eq_ker hS.moduleCat_injective_f
          hS.exact.moduleCat_range_eq_ker hX₁r hX₃r
      let T : ShortComplex (ModuleCat.{v} R) := ModuleCat.shortComplexOfCompEqZero
        (QuotSMulTop.map r S.f.hom) (QuotSMulTop.map r S.g.hom) <| by
          ext x
          simp [QuotSMulTop.map_apply_mk, S.moduleCat_zero_apply]
      have hQuot : T.ShortExact := by
        simpa [T] using quotSMulTop_shortExact hS hX₃r
      exact IsRegular.cons hX₂r <| ih hQuot hX₁rs hX₃rs

end ShortExact
end ShortComplex
end CategoryTheory
