import stacks_project.Chap13.Definition_13_8_1
import stacks_project.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "single₀" => DerivedCategory.singleFunctor Mod (0 : ℤ)

/- Domain-style sampling for Lemma 15.67.8:
- primary domain: tor-amplitude in `D(R)` for objects represented by bounded cochain complexes of
  `R`-modules;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`,
  `ModuleHasFiniteTorDimension`,
  `Compᵇ(Mod)`;
- best owner abstraction: `HasTorAmplitudeIn` is the tor-amplitude owner, while the presenting
  bounded cochain complex should use the chapter owner `Compᵇ(Mod)` rather than an
  unbundled complex plus a separate boundedness witness;
- primitive vs. derived:
  primitive data are the bounded complex `K : Compᵇ(Mod)`, with underlying cochain
  complex `K.obj`, and the termwise tor-amplitude hypotheses on the shifted single-term objects
  `((single₀).obj (K.obj.X i))⟦i⟧`;
  derived API is the finite-tor-dimension statement, which packages the interval choice after the
  main tor-amplitude theorem rather than introducing a second owner;
- source/core/bridge triage:
  `source-facing`: `hasTorAmplitudeIn_of_bounded_of_termwise_hasTorAmplitudeIn`;
  `core/canonical`: `HasTorAmplitudeIn`, `HasFiniteTorDimension`, and
    `Compᵇ(Mod)`;
  `bridge/view`: the forgetful passage from the bounded cochain complex `K` to its underlying
  cochain complex `K.obj`, then to the shifted degree-zero terms `((single₀).obj (K.obj.X i))⟦i⟧`,
  and finally to the derived object `Q.obj K.obj`.

This keeps the textbook theorem source-facing, but moves its boundedness input to the canonical
chapter owner category and its termwise hypothesis to the intrinsic shifted derived objects rather
than the coordinate-level interval formula `a - i, b - i`.
-/

-- Proof sketch: argue by induction on the length of the bounded complex using stupid
-- truncations. The induction step writes the image of `K` in `D(R)` in a distinguished triangle
-- whose left vertex is a shift of a single term `K.obj.X i`, so Lemma `15.67.5` propagates the
-- shifted tor-amplitude bounds from the terms to the whole complex.
/-- Lemma 15.67.8 (1): if a bounded cochain complex of `R`-modules has each term `K^i`
tor-amplitude in `[a - i, b - i]`, equivalently if the shifted single-term object
`K^i[i] = ((single₀).obj (K.obj.X i))⟦i⟧` has tor-amplitude in `[a, b]`, then the associated
object of `D(R)` has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_of_bounded_of_termwise_hasTorAmplitudeIn
    (a b : ℤ)
    (K : Compᵇ(Mod))
    (hterm :
      ∀ i : ℤ,
        HasTorAmplitudeIn (((single₀).obj (K.obj.X i))⟦i⟧) a b) :
    HasTorAmplitudeIn (Q.obj K.obj) a b := sorry

-- Proof sketch: for each nonzero term `K.obj.X i`, choose a finite tor-amplitude interval;
-- boundedness of `K` leaves only finitely many relevant indices, so these intervals admit common
-- endpoints `a ≤ b`. Transport those bounds to the shifted objects `K^i[i]` via
-- `hasTorAmplitudeIn_shift_iff`, apply the first part with the common interval `[a, b]`, and then
-- package the result via `HasTorAmplitudeIn.hasFiniteTorDimension`.
/-- Lemma 15.67.8 (2): a bounded cochain complex of `R`-modules whose terms all have finite tor
dimension has finite tor dimension in `D(R)`. -/
theorem hasFiniteTorDimension_of_bounded_of_termwise_hasFiniteTorDimension
    (K : Compᵇ(Mod))
    (hterm : ∀ i : ℤ, ModuleHasFiniteTorDimension (K.obj.X i)) :
    HasFiniteTorDimension (Q.obj K.obj) := sorry

end

end CategoryTheory
