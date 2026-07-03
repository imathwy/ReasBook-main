import Mathlib
import StacksProject_2024.Chap16.Lemma_16_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open RamificationOneDvrFactorizationSituation
open scoped TensorProduct

universe u v w

section

variable (S : RamificationOneDvrFactorizationSituation)

/-- The transform of the center prime `𝔭` inside the Néron blowup `A'`. This is the principal-open
library-facing stand-in for the local prime `𝔭'` appearing in the textbook statement. -/
noncomputable def neronBlowupCenterIdeal (π : S.R) (hπ : Irreducible π) :
    Ideal (affineBlowupChart S.p (neronBlowupParameter π hπ)) :=
  Ideal.map (algebraMap S.A (affineBlowupChart S.p (neronBlowupParameter π hπ))) S.p

/-- The local special fiber `(A / π A)_𝔭`, written in the canonical quotient-after-localization
form. -/
abbrev specialFiberLocalRing (π : S.R) :=
  Localization.AtPrime S.p ⧸
    Ideal.span
      ({algebraMap S.A (Localization.AtPrime S.p) (algebraMap S.R S.A π)} :
        Set (Localization.AtPrime S.p))

/-- The dimension `c = dim ((A / π A)_𝔭)` from Lemma `16.4.3`, expressed via Krull dimension. -/
noncomputable abbrev specialFiberLocalDimension (π : S.R) : WithBot ℕ∞ :=
  ringKrullDim (specialFiberLocalRing S π)

/-- The principal-open form of the short exact sequence of Kähler differentials in
Lemma `16.4.3`. In this statement-stage skeleton, this predicate records the rank parameter
`c = dim ((A / π A)_𝔭)` attached to the cokernel of the eventual short exact sequence on a
principal open of the Néron blowup. -/
def HasNeronBlowupPrincipalOpenDifferentialSequence
    (π : S.R) (hπ : Irreducible π)
    (_ : affineBlowupChart S.p (neronBlowupParameter π hπ)) : Prop :=
  ∃ c : ℕ,
    (c : WithBot ℕ∞) = specialFiberLocalDimension S π

/-- A principal open of the Néron blowup carrying both the smoothness conclusion and the
auxiliary differential-sequence clause from Lemma `16.4.3`. -/
private abbrev NeronBlowupPrincipalOpenWitness
    (π : S.R) (hπ : Irreducible π)
    (g : affineBlowupChart S.p (neronBlowupParameter π hπ)) : Prop :=
  Algebra.Smooth S.R (Localization.Away g) ∧
    HasNeronBlowupPrincipalOpenDifferentialSequence S π hπ g

variable {S}

-- Proof sketch: use Lemma `16.4.2` to replace `A` by a localization away from `𝔭`, choose a
-- regular system of parameters in the special fiber `(A / π A)_𝔭`, and present the Néron blowup
-- as the quotient `A[y₁, …, y_c] / (π y_i - g_i)`. The Jacobi-Zariski sequence on a suitable
-- principal open of `A'` gives the displayed exact sequence, and the linear independence of the
-- differentials `dg_i` over the separable residue extension forces injectivity on the left and
-- smoothness on that principal open.
/-- Lemma 16.4.3: in Situation `16.4.1`, if `R → A` is smooth at `𝔭` and the special-fiber field
extension `R / πR ⊆ Λ / πΛ` is separable, then the Néron blowup `A'` is smooth at the center
lying over `𝔭`. In the canonical principal-open formulation, there exists `g ∉ 𝔭 A'` such that
`A'_g` is smooth over `R`; the differential-sequence clause is recorded in this statement-stage
skeleton by the auxiliary proposition
`HasNeronBlowupPrincipalOpenDifferentialSequence S π g`, whose rank parameter is constrained to be
`c = dim ((A / π A)_𝔭)`. -/
theorem smoothAway_center_of_separable_specialFiber_and_hasDifferentialSequence
    (π : S.R) (hπ : Irreducible π)
    [Algebra (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L))]
    (hsep : Algebra.IsSeparable
      (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L)))
    (hsmooth : Algebra.IsSmoothAt S.R S.p) :
    ∃ g : affineBlowupChart S.p (neronBlowupParameter π hπ),
      g ∉ neronBlowupCenterIdeal S π hπ ∧
        NeronBlowupPrincipalOpenWitness S π hπ g := sorry

end
