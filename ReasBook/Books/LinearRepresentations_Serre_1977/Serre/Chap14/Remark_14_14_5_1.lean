import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.GenericCharacterDescent
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.AbsoluteSimplicity
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.QuasisplitAbsoluteSimplicity
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.FieldIndependence.Endgame
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.Modular.CharPPerfect

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

open CategoryTheory

open scoped Representation

section SplittingField

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- **Serre's Theorem 24 over a characteristic-`0` splitting field (the residual classical input).**
If `k` has characteristic `0` and contains enough roots of unity for the exponent of `G`, then
Serre's intrinsic character ring `R[k](G)` coincides with the ordinary character ring `R̄[k](G)`;
equivalently, `k` is *quasisplit*. This is Brauer's induction theorem (Serre §12.3, Theorem 24):
every virtual `k̄`-character is a `ℤ`-combination of characters induced from degree-`1` characters,
whose values are roots of unity already lying in `k`.

The repository currently proves this only over a base admitting a fixed embedding into `ℂ`
(`Theorem_12_12_3_1`, `Exercise_12_12_3_3`), because its Brauer-induction stack
(`monomialCharacterSpan`) is set up over `ℂ`. The statement here is the expected extension to an
arbitrary characteristic-`0` field, and is the single classical fact still feeding the
characteristic-`0` case of `scalarExtension_isIrreducible_of_isSplittingField` below. -/
theorem characterRing_eq_overlineCharacterRing_of_isSplittingField
    [CharZero k] [HasEnoughRootsOfUnity k (Monoid.exponent G)] :
    R[k](G) = R̄[k](G) :=
  Representation.characterRing_eq_overlineCharacterRing_of_isSplittingField_endgame

/-- **Absolute simplicity (Serre's `d_E = 1`).** If `k` is a *splitting field* for `G` — i.e. for
every divisor `d` of `Monoid.exponent G` that is invertible in `k` (`(d : k) ≠ 0`, the
prime-to-`char k` divisors), `k` already contains enough `d`-th roots of unity — then every simple
finite-dimensional `k[G]`-representation `S` stays irreducible after extending scalars to the
algebraic closure `k̄`. This is Brauer's splitting-field theorem (equivalently, triviality of the
Schur index over a sufficiently large field), the genuine content of Serre §14.5 ("`d_E = 1` when
`k` is sufficiently large").

The proof follows Serre's own method. In **characteristic `0`** it is complete *modulo Theorem 24*:
the splitting hypothesis gives enough roots of unity for the exponent, Theorem 24
(`characterRing_eq_overlineCharacterRing_of_isSplittingField`) turns that into the quasisplit
identity `R[k](G) = R̄[k](G)`, and the proven wiring
`scalarExtension_isIrreducible_of_quasisplit` (quasisplit ⟹ `d_E = 1` ⟹ absolute simplicity, via
Schur orthogonality, flat End base change, and Maschke semisimplicity) concludes. In
**characteristic `p ∣ |G|`** the modular Brauer–Witt content remains; Serre obtains it by
"reduction mod `𝔪`" (method (1)) from the characteristic-`0` statement, which is a
discrete-valuation-ring argument carried out downstream, not at this pure field level. -/
theorem scalarExtension_isIrreducible_of_isSplittingField [PerfectField k]
    (hsplit : ∀ d : ℕ, d ∣ Monoid.exponent G → (d : k) ≠ 0 → HasEnoughRootsOfUnity k d)
    (S : FDRep k G) [Simple S] :
    Representation.IsIrreducible
      (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ) := by
  by_cases hchar : CharZero k
  · -- Characteristic `0`: Serre's Theorem 24 (quasisplit) plus the proven wiring give absolute
    -- simplicity, with no recourse to the modular theory.
    haveI := hchar
    haveI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
    haveI : HasEnoughRootsOfUnity k (Monoid.exponent G) :=
      hsplit _ dvd_rfl (Nat.cast_ne_zero.mpr (NeZero.ne _))
    exact scalarExtension_isIrreducible_of_quasisplit
      characterRing_eq_overlineCharacterRing_of_isSplittingField S
  · -- Characteristic `p`: over a perfect field `k` this is the modular splitting theorem.  Its
    -- proof (`Modular/CharPPerfect.lean`) bootstraps the finite-field case (the closed module-level
    -- Galois descent, `Modular/CharPMain.lean`) to a finite splitting subfield `𝔽_p(ζ) ⊆ k` and
    -- ascends along `𝔽_p(ζ) ↪ k` (split-semisimplicity is preserved by base change).
    obtain ⟨p, hpc⟩ := CharP.exists k
    haveI : CharP k p := hpc
    haveI : Fact p.Prime := ⟨by
      rcases CharP.char_is_prime_or_zero k p with hp | hp
      · exact hp
      · subst hp
        exact absurd (CharP.charP_to_charZero k) hchar⟩
    exact charP_scalarExtension_isIrreducible_of_splitsPrimeToP_perfect hsplit S

/-- **Field-level splitting theorem (Serre's `d_E = 1`).** If `k` is a splitting field for `G` (see
`scalarExtension_isIrreducible_of_isSplittingField`), then every simple finite-dimensional
`k[G]`-representation `S` is absolutely simple, so its endomorphism space is one-dimensional over
`k`. This is the direct project realization of Serre's statement `d_E = 1`.

The proof is the genuine reduction (no remaining hole of its own): absolute simplicity of `S` over
`k̄`, plus the algebraically-closed Schur lemma
`Representation.IsIrreducible.finrank_intertwiningMap_self`, transported back along the injective
Hom-base-change map `Representation.finrank_intertwiningMap_le_scalarExtension`. -/
theorem simple_endomorphism_finrank_eq_one_of_isSplittingField [PerfectField k]
    (hsplit : ∀ d : ℕ, d ∣ Monoid.exponent G → (d : k) ≠ 0 → HasEnoughRootsOfUnity k d)
    (S : FDRep k G) [Simple S] :
    Module.finrank k (S ⟶ S) = 1 := by
  classical
  haveI hirr : Representation.IsIrreducible
      (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ) :=
    scalarExtension_isIrreducible_of_isSplittingField hsplit S
  -- `End_{k[G]}(S)` is identified with the self-intertwiners of `S.ρ`.
  have hequiv :
      Module.finrank k (S ⟶ S) = Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) :=
    LinearEquiv.finrank_eq
      ((Representation.linHom.invariantsEquivFDRepHom S S).symm.trans
        (Representation.invariantsEquivIntertwiningMap S.ρ S.ρ))
  -- Hom base change bounds it by the `k̄`-dimension downstairs, which is `1` by absolute simplicity.
  have hle : Module.finrank k (S ⟶ S) ≤ 1 := by
    rw [hequiv]
    refine (Representation.finrank_intertwiningMap_le_scalarExtension S.ρ).trans ?_
    rw [Representation.IsIrreducible.finrank_intertwiningMap_self]
  -- The endomorphism space is nonzero, so the dimension is exactly `1`.
  have hpos : 1 ≤ Module.finrank k (S ⟶ S) := by
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Module.finrank_pos_iff]
    exact ⟨𝟙 S, 0, CategoryTheory.id_nonzero S⟩
  omega

end SplittingField

section

-- Faithful modular-system form: `A` is a **discrete valuation ring** with `K = Frac A` and
-- `k = ResidueField A`.  Serre's "`K` sufficiently large ⟹ `d_E = 1`" descends to the residue
-- field `k` *only* because `A` is a DVR: the prime-to-`p` roots of unity are units of `A` and
-- reduce injectively mod `𝔪` (Hensel), so `k` inherits "sufficiently large" and is a splitting
-- field, whence every simple `k[G]`-module is absolutely simple.  With only `[IsLocalRing A]` the
-- guard `[HasEnoughRootsOfUnity K …]` (on the fraction field) does NOT reach `k` and the statement
-- is FALSE: e.g. `G = C₃`, `A = π⁻¹(𝔽₂) ⊂ 𝔽₄[t]_(t)` (a non-DVR local domain with
-- `Frac A = 𝔽₄(t) ∋ ζ₃` but `k = 𝔽₂`) gives the simple `S = 𝔽₄` with `End_{𝔽₂[C₃]}(S) = 𝔽₄`, of
-- `k`-dimension `2 ≠ 1`.
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Remark 14-14.5-1: if `K = Frac A` is sufficiently large (with `A` a discrete valuation ring, so
the largeness descends to the residue field), then for every simple finite-dimensional
`k[G]`-representation `S`, the endomorphism space `S ⟶ S` is one-dimensional over
`k = IsLocalRing.ResidueField A`. This is the direct project realization of Serre's statement
`d_E = 1`. -/
theorem simple_finiteRep_endomorphism_finrank_eq_one_of_sufficiently_large
    [PerfectField (IsLocalRing.ResidueField A)] [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (S : FDRep k G) [Simple S] :
    Module.finrank k (S ⟶ S) = 1 := by
  -- The residue field `k` inherits "sufficiently large": for every prime-to-`p` divisor `d` of the
  -- exponent, `K` has enough `d`-th roots (`of_dvd`), and these descend to `k` because `A` is a DVR
  -- (`residueField_hasEnoughRootsOfUnity_of_fraction_of_natCast_ne_zero`).  This exhibits `k` as a
  -- splitting field, and Serre's `d_E = 1` follows from the field-level splitting theorem.
  haveI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  refine simple_endomorphism_finrank_eq_one_of_isSplittingField ?_ S
  intro d hd hdk
  haveI : HasEnoughRootsOfUnity K d := HasEnoughRootsOfUnity.of_dvd K hd
  exact Representation.residueField_hasEnoughRootsOfUnity_of_fraction_of_natCast_ne_zero
    (A := A) (K := K) (n := d) hdk

end

end Representation
