import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import stacks_project.Chap10.Definition_10_153_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-
Domain-style sampling for Lemma 15.105.23:
- primary domain: local commutative algebra of integral extensions of henselian and strictly
  henselian local rings, together with the induced residue-field extension;
- sampled owner declarations:
  `HenselianLocalRing`,
  `StrictHenselianLocalRing`,
  `finite_local_henselianLocalRing`,
  `algebraMap_isLocalHom_of_finite_local`,
  `IsLocalHom (algebraMap A B)`,
  `IsLocalRing.ResidueField.algebraOfIsIntegral`,
  `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`,
  `Algebra.IsAlgebraic.isSepClosed`;
- best owner abstraction: the integral-domain transfer statements here are `source-facing`, while
  the local/integral and residue-field-purely-inseparable steps are `bridge/view` results that
  should expose the canonical owner classes above rather than source-specific packages;
- primitive data: the integral `A`-algebra structure on the domain `B`;
- derived API: the henselian local structure on `B`, the locality of `A → B`, and the resulting
  purely inseparable residue-field extension.

Source/core/bridge triage:
- `source-facing`:
  `henselianLocalRing_of_henselianLocalRing_of_integral_domain`,
  `strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain`;
- `core/canonical`: `HenselianLocalRing`, `StrictHenselianLocalRing`, `IsLocalHom`,
  `finite_local_henselianLocalRing`, `algebraMap_isLocalHom_of_finite_local`,
  `IsPurelyInseparable`;
- `bridge/view`: the canonical residue-field algebraicity instance for local integral maps and the
  canonical bridge theorems
  `algebraMap_isLocalHom_of_isLocalRing_of_integral` and
  `residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral`, which expose the
  induced residue-field extension through the local-map interface and feed the source-facing
  corollaries below.
 -/

section LocalIntegralBridge

variable [IsLocalRing A] [IsLocalRing B] [Algebra.IsIntegral A B]

/-- An integral algebra map between local rings is a local ring homomorphism. -/
theorem algebraMap_isLocalHom_of_isLocalRing_of_integral :
    IsLocalHom (algebraMap A B) := by
  sorry

end LocalIntegralBridge

section ResidueFieldBridge

variable [IsLocalRing A] [IsSepClosed (ResidueField A)]
variable [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.IsIntegral A B]

/-- The residue-field extension induced by an integral local homomorphism from a local ring with
separably closed residue field is purely inseparable. -/
theorem residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral :
    IsPurelyInseparable (ResidueField A) (ResidueField B) := by
  sorry

end ResidueFieldBridge

section Henselian

variable [HenselianLocalRing A]

-- Proof sketch: write `B` as a filtered colimit of finite `A`-subalgebras and apply the finite
-- henselian case to each stage. Since `B` is a domain, each finite local factor is forced to be
-- unique, and Lemma `10.154.8` upgrades the filtered colimit to a henselian local ring.
/-- Lemma 15.105.23 (1): if `A → B` is an integral ring map, `A` is henselian local, and `B` is a
domain, then `B` is a henselian local ring. -/
theorem henselianLocalRing_of_henselianLocalRing_of_integral_domain
    (A : Type u) [CommRing A] [Algebra A B] [HenselianLocalRing A] [Algebra.IsIntegral A B]
    [IsDomain B] : HenselianLocalRing B := sorry

/-- Lemma 15.105.23 (2): if `A → B` is an integral ring map, `A` is henselian local, and `B` is a
domain, then `A → B` is a local homomorphism. -/
theorem algebraMap_isLocalHom_of_henselianLocalRing_of_integral_domain [Algebra.IsIntegral A B]
    [IsDomain B] : IsLocalHom (algebraMap A B) := by
  let _ : HenselianLocalRing B :=
    henselianLocalRing_of_henselianLocalRing_of_integral_domain A
  exact algebraMap_isLocalHom_of_isLocalRing_of_integral

end Henselian

section StrictHenselian

variable [StrictHenselianLocalRing A]

/-- Lemma 15.105.23 (4): for an integral local homomorphism from a strictly henselian local ring,
the induced residue-field extension is purely inseparable. -/
theorem residueField_isPurelyInseparable_of_strictHenselianLocalRing_of_localHom_of_integral
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.IsIntegral A B] :
    IsPurelyInseparable (ResidueField A) (ResidueField B) := by
  exact residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral

-- Proof sketch: once clause (1) gives that `B` is henselian local and clause (2) gives that
-- `A → B` is local, clause (4) upgrades the induced residue-field extension to a purely
-- inseparable extension. We then reuse the canonical algebraic-extension owner to conclude that
-- `ResidueField B` is separably closed.
/-- Lemma 15.105.23 (3): if `A` is strictly henselian in addition to the integral-domain
hypotheses, then `B` is strictly henselian. -/
theorem strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain
    (A : Type u) [CommRing A] [Algebra A B] [StrictHenselianLocalRing A] [Algebra.IsIntegral A B]
    [IsDomain B] :
    StrictHenselianLocalRing B := by
  let _ : HenselianLocalRing B :=
    henselianLocalRing_of_henselianLocalRing_of_integral_domain A
  let _ : IsLocalHom (algebraMap A B) :=
    algebraMap_isLocalHom_of_isLocalRing_of_integral
  let hPure : IsPurelyInseparable (ResidueField A) (ResidueField B) :=
    residueField_isPurelyInseparable_of_isSepClosed_of_localHom_of_integral
  let _ : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) :=
    hPure.isAlgebraic
  let _ : IsSepClosed (ResidueField B) :=
    Algebra.IsAlgebraic.isSepClosed (F := ResidueField A) (E := ResidueField B)
  exact
    { toHenselianLocalRing := inferInstance
      toIsSepClosed := inferInstance }

end StrictHenselian

section IntegralClosure

variable {L : Type v} [Field L] [Algebra A L]

/-- The integral closure of a henselian local ring in a field is henselian local. -/
instance integralClosure_henselianLocalRing [HenselianLocalRing A] :
    HenselianLocalRing (integralClosure A L) := by
  let _ : Algebra.IsIntegral A (integralClosure A L) := IsIntegralClosure.isIntegral_algebra A L
  exact
    (henselianLocalRing_of_henselianLocalRing_of_integral_domain A :
      HenselianLocalRing (integralClosure A L))

/-- The integral closure of a strictly henselian local ring in a field is strictly henselian. -/
instance integralClosure_strictHenselianLocalRing [StrictHenselianLocalRing A] :
    StrictHenselianLocalRing (integralClosure A L) := by
  let _ : Algebra.IsIntegral A (integralClosure A L) := IsIntegralClosure.isIntegral_algebra A L
  exact
    (strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain A :
      StrictHenselianLocalRing (integralClosure A L))

end IntegralClosure

end
