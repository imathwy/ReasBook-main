import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ChainComplex

universe u v

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {F : ChainComplex (ModuleCat R) ℕ}

local notation "moduleSingle" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Definition 10.71.2 (1): an augmented chain complex of `R`-modules
`π : F ⟶ moduleSingle` is a left resolution of `M`
when `π` is a quasi-isomorphism; this is the canonical mathlib notion `QuasiIso`. -/
recall QuasiIso

namespace ChainComplex

/-- A chain complex of `R`-modules is termwise free when every degree is a free `R`-module. -/
def IsTermwiseFree (F : ChainComplex (ModuleCat R) ℕ) : Prop :=
  ∀ n : ℕ, Module.Free R (F.X n)

/-- A chain complex of `R`-modules is termwise finite when every degree is a finite `R`-module. -/
def IsTermwiseFinite (F : ChainComplex (ModuleCat R) ℕ) : Prop :=
  ∀ n : ℕ, Module.Finite R (F.X n)

/-- Definition 10.71.2 (2): a free resolution of an `R`-module `M` is an augmented chain complex
`π : F ⟶ moduleSingle` which is a quasi-isomorphism and whose terms are all free `R`-modules. -/
@[stacks 00LQ]
class IsFreeResolution (π : F ⟶ moduleSingle) : Prop extends QuasiIso π where
  termwise_free : IsTermwiseFree F

namespace IsFreeResolution

theorem free (π : F ⟶ moduleSingle) [h : IsFreeResolution π] (n : ℕ) :
    Module.Free R (F.X n) :=
  h.termwise_free n

/-- A free resolution gives the canonical projective resolution of `ModuleCat.of R M`. -/
noncomputable def toProjectiveResolution (π : F ⟶ moduleSingle) [h : IsFreeResolution π] :
    ProjectiveResolution (ModuleCat.of R M) where
  complex := F
  projective n := by
    let _ : Module.Free R (F.X n) := h.termwise_free n
    infer_instance
  π := π

end IsFreeResolution

/-- Definition 10.71.2 (3): a finite free resolution of an `R`-module `M` is a free resolution
whose terms are finite `R`-modules. -/
@[stacks 00LQ]
class IsFiniteFreeResolution (π : F ⟶ moduleSingle) : Prop extends IsFreeResolution π where
  termwise_finite : IsTermwiseFinite F

namespace IsFiniteFreeResolution

theorem finite (π : F ⟶ moduleSingle) [h : IsFiniteFreeResolution π] (n : ℕ) :
    Module.Finite R (F.X n) :=
  h.termwise_finite n

end IsFiniteFreeResolution

end ChainComplex

end
