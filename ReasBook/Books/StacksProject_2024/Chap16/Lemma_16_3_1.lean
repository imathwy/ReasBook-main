import Mathlib
import StacksProject_2024.Chap10.Definition_10_125_1
import StacksProject_2024.Chap10.Definition_10_135_5
import StacksProject_2024.Chap15.Definition_15_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Algebra

noncomputable section

section

/- Domain-style sampling:
- primary domain: finitely presented algebras, away localizations, cotangent modules, and smooth
  localized comparison maps;
- sampled owner declarations:
  `Localization.awayMapₐ`,
  `Algebra.Generators`,
  `Algebra.Generators.exists_presentation_of_free_cotangent`,
  `RingHom.IsLocalCompleteIntersection`;
- best owner abstraction:
  the localized comparison map is the canonical away map `Localization.awayMapₐ`, while the
  free-cotangent presentation datum should be recorded through the canonical generators/cotangent
  owners rather than via a parallel local wrapper;
- primitive vs. derived:
  primitive data are a finite generator family and freeness of its cotangent module; finite type
  is derived from that witness and should not remain separate primitive local data.

Source/core/bridge triage:
- `source-facing`: the localized existence of a finite generator family with free cotangent module;
- `core/canonical`: `Localization.awayMapₐ` for the localized algebra map and
  `Algebra.Generators.exists_presentation_of_free_cotangent` for derived presentation upgrades;
- `bridge/view`: the theorem below, which applies those owners to the localized `A`-algebras
  `C_a`.
-/

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [FinitePresentation R A]
variable {C : Type w} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

local notation:max "C[" a "]" => Localization.Away ((IsScalarTower.toAlgHom R A C) a)

noncomputable local instance localizedAwayAlgebra (a : A) :
    Algebra (Localization.Away a) C[a] :=
  (Localization.awayMapₐ (IsScalarTower.toAlgHom R A C) a).toAlgebra

-- Proof sketch: choose the symmetric algebra `C = Sym_A^*(I/I²)` for a finite presentation of
-- `A` over `R`. Its degree-zero projection gives the retraction. The localized Jacobi-Zariski
-- sequence and the local complete intersection hypothesis make the localized conormal module free,
-- yielding smoothness over `A_a`; when `A_a` is already smooth over `R`, the localized Kähler
-- differentials of `C_a` become free as well.
/-- Lemma 16.3.1: if `A` is a finitely presented `R`-algebra, there exists a finite type
`A`-algebra `C` together with an `A`-algebra retraction `C → A` such that for every `a : A` with
`R → A_a` a local complete intersection, the localization `C_a` is smooth over `A_a` and admits a
finite generator family over `R` whose cotangent module is free; this can be upgraded to a finite
presentation with free conormal module by
`Algebra.Generators.exists_presentation_of_free_cotangent`. For every `a : A` with `A_a` smooth
over `R`, the module `Ω[C_a⁄R]` is free over `C_a`. -/
theorem exists_finiteType_retraction_with_smoothing_localizations :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Algebra.FiniteType A C) (r : C →ₐ[A] A),
      (∀ a : A,
        (algebraMap R (Localization.Away a)).IsLocalCompleteIntersection →
          Smooth (Localization.Away a) C[a] ∧
            ∃ n : ℕ, ∃ P : Generators R C[a] (Fin n),
              Module.Free C[a] P.toExtension.Cotangent) ∧
      ∀ a : A,
        Smooth R (Localization.Away a) →
          Module.Free C[a] Ω[C[a]⁄R] := sorry

end

end

end Algebra
