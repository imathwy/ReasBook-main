import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical local scheme-morphism owner
  `LocallyQuasiFinite` together with `locallyQuasiFinite_iff`;
- direct `#print` checks in the current Lean environment verified the pointwise owner
  `QuasiFiniteAt`;
- there is no existing global scheme-morphism owner `Scheme.Hom.QuasiFinite`, so this file
  introduces the source-faithful quasi-compact strengthening of local quasi-finiteness.
-/

/- Stacks tag `01TD`, Definition 29.20.1 (1) and (2): the pointwise and local notions are the
canonical owners `QuasiFiniteAt` and `LocallyQuasiFinite`; the new source-facing content in this
file is only the global quasi-finite owner below. -/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Stacks tag `01TD`, Definition 29.20.1 (3): a morphism `f : X ⟶ S` is quasi-finite if it is
of finite type and
quasi-finite at every point of `X`; in the scheme API this is packaged as quasi-compactness
together with local quasi-finiteness. -/
@[stacks 01TD, mk_iff quasiFinite_iff]
class QuasiFinite : Prop extends QuasiCompact f, LocallyQuasiFinite f

/-- A quasi-compact locally quasi-finite morphism is quasi-finite. -/
instance instQuasiFinite [QuasiCompact f] [LocallyQuasiFinite f] :
    QuasiFinite f where
  toQuasiCompact := inferInstance
  toLocallyQuasiFinite := inferInstance

attribute [simp] quasiFinite_iff

/-- Build a quasi-finite morphism from quasi-compactness and local quasi-finiteness. -/
theorem quasiFinite_of_quasiCompact_of_locallyQuasiFinite
    (hqc : QuasiCompact f) (hlqf : LocallyQuasiFinite f) :
    QuasiFinite f :=
  { toQuasiCompact := hqc
    toLocallyQuasiFinite := hlqf }

/-- Every point of a quasi-finite morphism is a quasi-finite point. -/
instance instQuasiFiniteAtOfQuasiFinite [QuasiFinite f] (x : X) :
    f.QuasiFiniteAt x := by
  let _ : LocallyQuasiFinite f := inferInstance
  exact Scheme.Hom.quasiFiniteAt f x

/-- Every point of a quasi-finite morphism is a quasi-finite point. -/
theorem QuasiFinite.quasiFiniteAt (hf : QuasiFinite f) (x : X) :
    f.QuasiFiniteAt x := by
  let _ : LocallyQuasiFinite f := hf.toLocallyQuasiFinite
  exact Scheme.Hom.quasiFiniteAt f x

/-- A quasi-finite morphism is quasi-compact and quasi-finite at every source point. -/
theorem QuasiFinite.quasiCompact_and_forall_quasiFiniteAt (hf : QuasiFinite f) :
    QuasiCompact f ∧ ∀ x : X, f.QuasiFiniteAt x := by
  let _ : LocallyQuasiFinite f := hf.toLocallyQuasiFinite
  exact ⟨hf.toQuasiCompact, fun x ↦ Scheme.Hom.quasiFiniteAt f x⟩

end Scheme.Hom
end AlgebraicGeometry
