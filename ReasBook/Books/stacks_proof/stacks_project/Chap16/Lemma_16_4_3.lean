import Mathlib
import stacks_proof.stacks_project.Chap16.Lemma_16_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open RamificationOneDvrFactorizationSituation
open scoped AffineBlowupChart TensorProduct

universe u v w

section

variable (S : RamificationOneDvrFactorizationSituation)

section NeronBlowupChart

variable (π : S.R) (hπ : Irreducible π)

local notation "A" => S.A
local notation "pA" => S.p
local notation "πA" => neronBlowupParameter π hπ
local notation "A'" => A[pA / πA]

/-- The transform of the center prime `𝔭` inside the Néron blowup `A'`. This is the principal-open
library-facing stand-in for the local prime `𝔭'` appearing in the textbook statement. -/
noncomputable def neronBlowupCenterIdeal : Ideal A' :=
  Ideal.map (algebraMap A A') pA

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
    (_ : A') : Prop :=
  ∃ c : ℕ,
    (c : WithBot ℕ∞) = specialFiberLocalDimension S π

/-- A principal open of the Néron blowup carrying both the smoothness conclusion and the
auxiliary differential-sequence clause from Lemma `16.4.3`. -/
private abbrev NeronBlowupPrincipalOpenWitness
    (g : A') : Prop :=
  Algebra.Smooth S.R (Localization.Away g) ∧
    HasNeronBlowupPrincipalOpenDifferentialSequence S π hπ g

variable {S}

/-- Helper for Chap16 Lemma 16 4 3: the local special-fiber dimension is represented by a natural
number. -/
private lemma specialFiberLocalDimension_eq_nat
    (S : RamificationOneDvrFactorizationSituation) (π : S.R) :
    ∃ c : ℕ, (c : WithBot ℕ∞) = specialFiberLocalDimension S π := by
  -- Proof comment: the localized special fiber has finite Krull dimension, so its dimension
  -- cannot be `⊥` or `⊤`; case-split on the `WithBot ℕ∞` value and keep only the finite branch.
  let _ : FiniteRingKrullDim (specialFiberLocalRing S π) := inferInstance
  have hnebot : specialFiberLocalDimension S π ≠ ⊥ := by
    simpa [specialFiberLocalDimension] using
      (ringKrullDim_ne_bot (R := specialFiberLocalRing S π))
  have hnetop : specialFiberLocalDimension S π ≠ ⊤ := by
    simpa [specialFiberLocalDimension] using
      (ringKrullDim_ne_top (R := specialFiberLocalRing S π))
  cases hdim : specialFiberLocalDimension S π using WithBot.recTopCoe with
  | bot =>
      exact (hnebot hdim).elim
  | top =>
      exact (hnetop hdim).elim
  | coe d =>
      cases hd : d using ENat.recTopCoe with
      | top =>
          exact (hnetop (by simpa [hd] using hdim)).elim
      | coe n =>
          refine ⟨n, ?_⟩
          simpa [hd] using hdim

/-- Helper for Chap16 Lemma 16 4 3: smoothness at the center prime gives a standard-smooth basic
open neighborhood. -/
private lemma exists_standardSmoothAway_at_center
    (S : RamificationOneDvrFactorizationSituation)
    (hsmooth : Algebra.IsSmoothAt S.R S.p) :
    ∃ a : S.A, a ∉ S.p ∧ IsStandardSmooth S.R (Localization.Away a) := by
  -- Proof comment: install the finite-presentation and local smoothness instances, then apply the
  -- canonical mathlib neighborhood theorem for smooth points.
  let _ : Algebra.FinitePresentation S.R S.A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let _ : Algebra.IsSmoothAt S.R S.p := hsmooth
  simpa using IsSmoothAt.exists_notMem_isStandardSmooth (R := S.R) (S := S.A) S.p

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
@[stacks 0BJ4]
theorem smoothAway_center_of_separable_specialFiber_and_hasDifferentialSequence
    [Algebra (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L))]
    (hsep : Algebra.IsSeparable
      (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L)))
    (hsmooth : Algebra.IsSmoothAt S.R S.p) :
    ∃ g : A',
      g ∉ neronBlowupCenterIdeal S π hπ ∧
        NeronBlowupPrincipalOpenWitness S π hπ g := by
  obtain ⟨c, hc⟩ := specialFiberLocalDimension_eq_nat (S := S) π
  obtain ⟨a, ha, hstd⟩ := exists_standardSmoothAway_at_center (S := S) hsmooth
  -- Route correction: the dimension side-condition and the standard-smooth neighborhood of `p`
  -- are now separated from the genuine geometric step on the localized blowup chart.
  -- TODO: use Lemma `16.4.2` to identify the localized Néron blowup away from `a` with the
  -- affine blowup chart of `A_a → Λ`, then apply the separability/Jacobian argument on that chart
  -- to produce `g : A'` outside the transformed center with `Smooth S.R (Localization.Away g)`.
  sorry

end NeronBlowupChart

end
