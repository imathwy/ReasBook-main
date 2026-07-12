import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped TensorProduct

universe u v

section

/-
Domain-style sampling:
- primary domain: descent of unramified tensor-product base change along filtered colimits of
  commutative algebras;
- sampled owner declarations:
  `RingHom.FormallyUnramified`,
  `Algebra.FormallyUnramified.base_change`,
  `Algebra.FiniteType.baseChange`,
  `Algebra.Unramified`,
  `Algebra.unramified_iff_formallyUnramified_and_finiteType`;
- best owner abstraction:
  - `source-facing`: the filtered-colimit descent theorem below
  - `core/canonical`: the tensor-product base-change hom
    `Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)` together with the induced algebra structure on
    the target tensor product and its owner predicate `Algebra.Unramified`
  - `bridge/view`: the owner-level formally-unramified descent theorem below, which supplies the
    primitive part of the canonical unramified owner while finite type is recovered separately by
    base change
- primitive vs. derived:
  - primitive data: the filtered diagram `F`, the map `φ₀ : B₀ →ₐ[A₀] C₀`, and the formal
    unramifiedness of its colimit base-change hom
  - derived API: finite type of each base-changed hom, obtained from `hφ₀ : φ₀.FiniteType` by
    base change; the public source-facing theorem should therefore conclude in the canonical owner
    `Algebra.Unramified`, with the decomposition into formal unramifiedness and finite type kept
    only as a bridge.
-/

variable {A₀ : Type u} [CommRing A₀]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A₀) [HasColimit F]
variable {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀]
variable [Algebra A₀ B₀] [Algebra A₀ C₀]

-- Proof sketch: formal unramifiedness of the colimit base-change hom is the primitive owner
-- input. Interpreting it via Kähler differentials, finite type of `φ₀` gives finitely many
-- generators whose images vanish after tensoring to the colimit, so filtered-colimit finiteness
-- forces those generators to vanish already at some stage. That yields formal unramifiedness of
-- the stage base-change hom; finite type of the same stage hom is then recovered separately from
-- `hφ₀` by base change.
/-- Owner-level form of Lemma 10.168.5: if the colimit tensor-product base-change hom of
`φ₀ : B₀ →ₐ[A₀] C₀` is formally unramified, then some stage base-change hom is already formally
unramified. The finite-type input is kept separate because it is primitive data of `φ₀`, not of
the colimit base change. -/
theorem finite_type_formallyUnramified_baseChangeHom_descends_to_stage
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType)
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).FormallyUnramified) :
    ∃ j : J, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).FormallyUnramified := sorry

/-- Lemma 10.168.5: let `A = colim_i Aᵢ` be a directed colimit of `A₀`-algebras. If the base
change `B₀ ⊗[A₀] A → C₀ ⊗[A₀] A` of a map `φ₀ : B₀ →ₐ[A₀] C₀` is formally unramified and `φ₀`
is of finite type, then for some stage `Aᵢ` the base-changed map
`B₀ ⊗[A₀] Aᵢ → C₀ ⊗[A₀] Aᵢ` is already unramified. This is stated on the canonical base-change
hom through the canonical owner `Algebra.Unramified`; Lemma `10.151.2` supplies the bridge from
this owner to the pair of formal unramifiedness and finite type. -/
theorem finite_type_unramified_baseChange_descends_to_stage
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType)
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).FormallyUnramified) :
    ∃ j : J,
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)) := sorry

end
