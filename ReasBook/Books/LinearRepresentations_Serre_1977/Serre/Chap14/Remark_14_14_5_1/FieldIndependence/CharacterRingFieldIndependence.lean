import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.FieldIndependence.AbsoluteIrreducibleAscends
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.FieldIndependence.Surjectivity

/-!
# Field-independence of the characteristic-`0` character ring (central theorem)

For two algebraically closed fields `L ⊆ E` of characteristic `0` and a finite group `G`, scalar
extension induces an isomorphism of character rings: the coefficientwise image of `R[L](G)` in
`G → E` is exactly `R[E](G)`. Equivalently, every irreducible `E`-representation is already defined
over `L` — the field of definition of the representation theory of `G` is field-independent in
characteristic `0`.

This is the substitute for "Brauer induction over an arbitrary algebraically closed field": rather
than re-proving Brauer's theorem off `ℂ`, we transport it between fields. The endgame
(`characterRing_eq_overlineCharacterRing_of_isSplittingField`, Serre Theorem 24 over an abstract
characteristic-`0` field) follows from this by a cyclotomic descent.

* `⊆` (`characterRingOverFieldInExtension_le_characterRing_of_isAlgClosed`) is proven here: the image
  of `R[L](G)` lands in `R[E](G)` because scalar extension of an `L`-representation is an
  `E`-representation.
* `⊇` is the genuine content (the single remaining hole), reduced to: every irreducible
  `E`-representation is the scalar extension of an irreducible `L`-representation. The proof goes
  through `isIrreducible_scalarExtension_of_isAlgClosed_base` (irreducibility ascends, Brick 1) and
  the Wedderburn count `∑ dᵢ² = |G|` over both fields, which forces the dimension-preserving
  injection on irreducibles to be a bijection.
-/

noncomputable section

universe u

open scoped TensorProduct Representation

namespace Representation

section FieldIndependence

variable {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
variable {E : Type u} [Field E] [Algebra L E] [IsAlgClosed E]
variable {G : Type u} [Group G] [Finite G]

/-- The character of a scalar extension is the coefficientwise image of the original character. -/
private theorem scalarExtension_character_eq_map
    {W : Type u} [AddCommGroup W] [Module L W] [FiniteDimensional L W] (ρ : Representation L G W) :
    (Representation.scalarExtension (k := E) ρ).character
      = fun g ↦ algebraMap L E (ρ.character g) := by
  ext g
  exact LinearMap.trace_baseChange (ρ g) E

/-- **`⊆` direction.** The coefficientwise image of `R[L](G)` in `G → E` is contained in `R[E](G)`:
scalar extension carries an `L`-representation to an `E`-representation, whose character lies in
`R[E](G)`. -/
theorem characterRingOverFieldInExtension_le_characterRing_of_isAlgClosed :
    characterRingOverFieldInExtension L E G ≤ R[E](G) := by
  intro χ hχ
  rcases Subalgebra.mem_map.mp hχ with ⟨χL, hχL, rfl⟩
  change ((IsScalarTower.toAlgHom ℤ L E).compLeft G) χL ∈ R[E](G)
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχL
  · rintro ψ ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional L ρ := hρfd
    have hmap : (Representation.scalarExtension (k := E) ρ.ρ).character
        = fun g ↦ algebraMap L E (ρ.ρ.character g) := scalarExtension_character_eq_map ρ.ρ
    have hmem : (Representation.scalarExtension (k := E) ρ.ρ).character ∈ R[E](G) :=
      rep_character_mem_characterRingOverField (Rep.of (Representation.scalarExtension (k := E) ρ.ρ))
    simpa [hmap] using hmem
  · intro n
    have : ((IsScalarTower.toAlgHom ℤ L E).compLeft G) ((algebraMap ℤ (G → L)) n)
        = (algebraMap ℤ (G → E)) n := by
      ext g; simp
    rw [this]
    exact (R[E](G)).algebraMap_mem n
  · intro f g _ _ hf hg
    simpa [map_add] using (R[E](G)).add_mem hf hg
  · intro f g _ _ hf hg
    simpa [map_mul] using (R[E](G)).mul_mem hf hg

/-- **Field-independence of the characteristic-`0` character ring (central theorem).** For
algebraically closed fields `L ⊆ E` of characteristic `0` and a finite group `G`, the coefficientwise
image of `R[L](G)` in `G → E` equals `R[E](G)`. Equivalently, every irreducible
`E`-representation of `G` is already defined over `L`.

`⊆` is proven; `⊇` (the genuine field-independence content) remains: it reduces, via Brick 1
(`isIrreducible_scalarExtension_of_isAlgClosed_base`, irreducibility ascends) and the Wedderburn
identity `∑ dᵢ² = |G|` over both fields, to the statement that the dimension-preserving injection
`{irreducible L-reps} ↪ {irreducible E-reps}` is a bijection. -/
theorem characterRingOverFieldInExtension_eq_characterRing_of_isAlgClosed :
    characterRingOverFieldInExtension L E G = R[E](G) := by
  refine le_antisymm characterRingOverFieldInExtension_le_characterRing_of_isAlgClosed ?_
  -- `⊇`: every generator of `R[E](G)` (the character of a finite-dimensional irreducible
  -- `E`-representation) is the scalar extension of an `L`-character, hence lies in the image.
  apply Algebra.adjoin_le
  rintro χ ⟨ρ, hρfd, hρirr, rfl⟩
  letI : FiniteDimensional E ρ := hρfd
  exact irreducible_rep_character_mem_characterRingOverFieldInExtension ρ.ρ hρirr

/-- **Descent corollary.** For algebraically closed `L ⊆ E` of characteristic `0`, an `E`-character
that takes values in `L` already lies in `R[L](G)`: the `overline` (reflection) ring over `L`
relative to `E` collapses to `R[L](G)` itself. This is the form consumed by the cyclotomic-descent
endgame. -/
theorem overlineCharacterRingInExtension_eq_characterRing_of_isAlgClosed :
    overlineCharacterRingInExtension L E = R[L](G) := by
  have hinj : Function.Injective (((IsScalarTower.toAlgHom ℤ L E).compLeft G)) := fun a b hab =>
    funext fun g => (algebraMap L E).injective (congrFun hab g)
  apply le_antisymm
  · intro χ hχ
    -- `χ : G → L` with its `E`-image in `R[E](G) = image of R[L](G)`.
    have hE : ((IsScalarTower.toAlgHom ℤ L E).compLeft G) χ
        ∈ characterRingOverFieldInExtension L E G := by
      rw [characterRingOverFieldInExtension_eq_characterRing_of_isAlgClosed]
      exact (mem_overlineCharacterRingInExtension_iff L E χ).1 hχ
    rcases Subalgebra.mem_map.mp hE with ⟨ψ, hψ, hψχ⟩
    -- The coefficient map `L → E` is injective, so `ψ = χ`, whence `χ ∈ R[L](G)`.
    have hψeq : ψ = χ := hinj hψχ
    rwa [hψeq] at hψ
  · -- The image of `R[L](G)` lands in `R[E](G)` (`⊆` direction), i.e. `R[L](G) ⊆ R̄[L](G)` over `E`.
    intro χ hχ
    exact (mem_overlineCharacterRingInExtension_iff L E χ).2
      (characterRingOverFieldInExtension_le_characterRing_of_isAlgClosed
        (Subalgebra.mem_map.2 ⟨χ, hχ, rfl⟩))

end FieldIndependence

end Representation
