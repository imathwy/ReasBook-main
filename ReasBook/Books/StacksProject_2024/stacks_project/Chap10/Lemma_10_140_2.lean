import Mathlib
import Mathlib.Tactic.TFAE
import StacksProject_2024.stacks_project.Chap10.Definition_10_137_10
import StacksProject_2024.stacks_project.Chap10.Lemma_10_140_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_140_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsAlgClosed k]
variable (m : Ideal S) [m.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/- Domain-style sampling for Lemma 10.140.2:
- primary domain: smoothness and regularity criteria at a closed point of a finite type
  `k`-algebra, expressed via the Kähler fiber and the cotangent space;
- sampled owner declarations:
  `smoothAtPrime_iff_isSmoothAt`,
  `isSmoothAt_tfae_finrank_kaehlerFiber_le_eq`,
  `isRegularLocalRing_of_isSmoothAt`,
  `finrank_kaehlerFiber_eq_finrank_cotangent`;
- best owner abstraction: the core/canonical owner is the primewise criterion
  `IsSmoothAt k q.asIdeal`, with the present file staying `source-facing` by packaging the closed
  point `q = ⟨m, inferInstance⟩`, the quotient-fiber form `κ(m) = S ⧸ m`, and the extra regular
  local clause from the Stacks statement;
- primitive data: the maximal ideal `m` of the finite type `k`-algebra `S`;
- derived API: the quotient presentation of the Kähler fiber at `m`, the cotangent comparison from
  `Lemma 10.140.1`, and the regular-local clause on `Localization.AtPrime m`.

Source/core/bridge triage:
- `source-facing`: the four-way closed-point `List.TFAE` statement in the quotient form used by the
  source text;
- `core/canonical`: `IsSmoothAt k m`, `IsRegularLocalRing (Localization.AtPrime m)`, and the
  prime-level three-way TFAE from `Lemma 10.140.3`;
- `bridge/view`: `smoothAtPrime_iff_isSmoothAt` and the closed-point quotient bridge
  `finrank_kaehlerFiber_eq_finrank_cotangent`. -/

private theorem smoothAtPrime_tfae_finrank_kaehlerFiber_le_eq :
    List.TFAE
      ([ Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) ] :
        List Prop) := by
  letI : Algebra.FinitePresentation k S :=
    (show Algebra.FiniteType k S ↔ Algebra.FinitePresentation k S from
      Algebra.FinitePresentation.of_finiteType).mp inferInstance
  let q : PrimeSpectrum S := ⟨m, inferInstance⟩
  have howner :
      List.TFAE
        [ Algebra.IsSmoothAt k m
        , Module.finrank (Ideal.ResidueField m)
            ((Ideal.ResidueField m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
        , Module.finrank (Ideal.ResidueField m)
            ((Ideal.ResidueField m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) ] :=
    Algebra.isSmoothAt_tfae_finrank_kaehlerFiber_le_eq m
  have hsmooth :
      Algebra.SmoothAtPrime k S q ↔ Algebra.IsSmoothAt k q.asIdeal :=
    Algebra.smoothAtPrime_iff_isSmoothAt k S q
  have hfiber :
      Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
        Module.finrank (S ⧸ m) m.Cotangent :=
    finrank_kaehlerFiber_eq_finrank_cotangent m
  sorry

-- Proof sketch: Lemma `10.140.1` identifies the Kähler-differential fiber
-- `κ(m) ⊗[S] Ω[S⁄k]` with the cotangent space `m / m²`, so clauses `(1)`, `(2)`, and `(3)` are
-- equivalent by the regular-local criterion comparing dimension with embedding dimension. If
-- `SmoothAtPrime k S ⟨m, inferInstance⟩` holds, then standard smoothness on a basic open
-- neighborhood gives a free Kähler module of rank equal to the local dimension, yielding
-- regularity of `S_m`. Conversely, if `S_m` is regular, cut out a local complete intersection
-- presentation near `m` and apply the Jacobian criterion to obtain `SmoothAtPrime k S
-- ⟨m, inferInstance⟩`.
/-- Lemma 10.140.2: for an algebraically closed field `k`, a finite type `k`-algebra `S`, and a
maximal ideal `m ⊂ S`, the following are equivalent: the local ring `Sₘ`, formalized as
`Localization.AtPrime m`, is regular; the fiber of `Ω[S⁄k]` at `m` has dimension at most
`dim(Sₘ)` over `κ(m) = S ⧸ m`; the same fiber dimension equals `dim(Sₘ)`; and `S/k` is smooth at
`m`, formalized as `Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩`. -/
theorem regularLocalRing_finrank_kaehlerFiber_le_eq_and_exists_smoothLocalization_tfae :
    List.TFAE
      ([ IsRegularLocalRing (Localization.AtPrime m)
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m)
      , Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩ ] : List Prop) := by
  letI : Algebra.FinitePresentation k S :=
    (show Algebra.FiniteType k S ↔ Algebra.FinitePresentation k S from
      Algebra.FinitePresentation.of_finiteType).mp inferInstance
  have hcore :
      List.TFAE
        ([ Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩
        , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
        , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) ] :
          List Prop) :=
    smoothAtPrime_tfae_finrank_kaehlerFiber_le_eq m
  let q : PrimeSpectrum S := ⟨m, inferInstance⟩
  have hsmooth :
      Algebra.SmoothAtPrime k S q ↔ Algebra.IsSmoothAt k q.asIdeal :=
    Algebra.smoothAtPrime_iff_isSmoothAt k S q
  have hregular_of_smooth :
      Algebra.SmoothAtPrime k S q → IsRegularLocalRing (Localization.AtPrime m) := by
    intro h
    exact Algebra.isRegularLocalRing_of_isSmoothAt q.asIdeal (hsmooth.mp h)
  have hfiber :
      Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
        Module.finrank (S ⧸ m) m.Cotangent :=
    finrank_kaehlerFiber_eq_finrank_cotangent m
  sorry

end
