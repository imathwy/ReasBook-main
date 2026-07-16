import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.SemisimpleSchur
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.FieldIndependence.GeneralBaseChange

/-!
# Characteristic-`p` reduction for the splitting-field theorem

In the modular case (`char k = p ∣ |G|`), Maschke fails, so the characteristic-`0` route
(`scalarExtension_isIrreducible_of_quasisplit`) does not apply. This module records the
*characteristic-independent* reduction that anchors the modular case: combining the flat End
base-change equality (`finrank_intertwiningMap_eq_baseChange`, valid in any characteristic) with the
field-general "semisimple + one-dimensional self-intertwiners ⟹ irreducible" lemma
(`SemisimpleSchur`), absolute simplicity of a simple `k[G]`-representation `S` reduces to the two
genuinely modular facts:

* **(A)** `S ⊗ k̄` is **semisimple** over `k̄[G]` (separable / geometric semisimplicity — for finite
  groups this holds because the relevant division algebras are separable; it is automatic when `k`
  is perfect, e.g. finite or algebraically closed);
* **(B)** `dim_k End_{k[G]}(S) = 1` (the **modular Schur index 1** content — Brauer's modular
  splitting-field theorem; provable from the modular-character infrastructure in Chapter 18:
  `modularCharacter`, the Brauer-character basis, and `|simple modules| = |p-regular classes|`).

This anchor is what the char-`p` branch of `scalarExtension_isIrreducible_of_isSplittingField` will
call once (A) and (B) are supplied for a splitting field. It also re-proves the char-`0` conclusion
(there (A) is Maschke and (B) is `finrank_intertwiningMap_eq_one_of_quasisplit`), so it is the common
shape of both characteristics.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory

namespace Representation

variable {k : Type u} [Field k] {G : Type u} [Group G] [Finite G]

/-- **Characteristic-independent reduction of absolute simplicity.** If the scalar extension of a
simple `k[G]`-representation `S` to the algebraic closure `k̄` is semisimple (A) and the
self-intertwiner space of `S` is one-dimensional over `k` (B), then `S ⊗ k̄` is irreducible. The
flat End base-change equality carries (B) up to `dim_k̄ End(S ⊗ k̄) = 1`, and a semisimple
representation with one-dimensional self-intertwiners is irreducible. -/
theorem isIrreducible_scalarExtension_of_isSemisimple_of_finrank_intertwiningMap_eq_one
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V)
    (hss : IsSemisimpleRepresentation (Representation.scalarExtension (k := AlgebraicClosure k) ρ))
    (hdim : Module.finrank k (Representation.IntertwiningMap ρ ρ) = 1) :
    Representation.IsIrreducible (Representation.scalarExtension (k := AlgebraicClosure k) ρ) := by
  have hbar :
      Module.finrank (AlgebraicClosure k)
        (Representation.IntertwiningMap
          (Representation.scalarExtension (k := AlgebraicClosure k) ρ)
          (Representation.scalarExtension (k := AlgebraicClosure k) ρ)) = 1 := by
    rw [finrank_intertwiningMap_eq_baseChange ρ, hdim]
  exact isIrreducible_of_isSemisimpleRepresentation_of_finrank_intertwiningMap_eq_one _ hbar

end Representation
