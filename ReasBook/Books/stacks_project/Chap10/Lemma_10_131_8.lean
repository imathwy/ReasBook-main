import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {A : Type u} {Aₛ : Type v} {B : Type w}
variable [CommRing A] [CommRing Aₛ] [CommRing B]
variable [Algebra A B]

/-- Lemma 10.131.8 (1): if `S` is a multiplicative subset of `A` whose image in `B` is invertible,
so that `B` is viewed as an `Aₛ`-algebra for a localization `Aₛ` of `A` at `S`, then the
canonical map identifies `Ω[B⁄A]` with `Ω[B⁄Aₛ]`. -/
-- Proof sketch: the localization map `A → Aₛ` is formally étale, hence `Ω[Aₛ⁄A]` vanishes.
-- Applying the Jacobi-Zariski exact sequence to `A → Aₛ → B` shows that the canonical map
-- `Ω[B⁄A] → Ω[B⁄Aₛ]` is bijective.
theorem kaehlerDifferential_map_bijective_of_isLocalization_source
    (S : Submonoid A) [Algebra A Aₛ] [IsLocalization S Aₛ] [Algebra Aₛ B]
    [IsScalarTower A Aₛ B] :
    Function.Bijective (KaehlerDifferential.map A Aₛ B B) := by
  letI : Algebra.FormallyEtale A Aₛ := Algebra.FormallyEtale.of_isLocalization S
  refine ⟨?_, KaehlerDifferential.map_surjective A Aₛ B⟩
  intro x y hxy
  have hzero : KaehlerDifferential.map A Aₛ B B (x - y) = 0 := by
    simp [map_sub, hxy]
  obtain ⟨z, hz⟩ := (KaehlerDifferential.exact_mapBaseChange_map A Aₛ B (x - y)).mp hzero
  have hz0 : z = 0 := Subsingleton.elim _ _
  have hsub : x - y = 0 := by
    simpa [hz0] using hz.symm
  exact sub_eq_zero.mp hsub

/- Lemma 10.131.8 (2): if `S` is a multiplicative subset of `B`, then localizing `Ω[B⁄A]` at `S`
identifies it with `Ω[Localization S⁄A]`; this is the canonical localized-module statement
`KaehlerDifferential.isLocalizedModule_map`. -/
recall KaehlerDifferential.isLocalizedModule_map

end
