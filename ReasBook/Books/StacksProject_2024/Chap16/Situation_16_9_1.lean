import StacksProject_2024.Chap16.Definition_16_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace RingHom

open scoped SingularIdealNotation

variable (R : Type u) {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A]

/-
Domain-style sampling for Situation 16.9.1:
- primary domain: commutative algebra of singular ideals under change of target ring;
- sampled owner declarations:
  `Algebra.singularIdeal`,
  `Ideal.map`,
  `Ideal.radical`;
- best owner abstraction: the bridge owner `g.singularIdealIn R` for a ring map `g : A →+* Λ`;
- primitive data: the source singular ideal `H[A⁄R]` and a ring map out of `A`;
- derived API: the source-facing notation `h(A⁄R, Λ)`, obtained by specializing to the structure
  map `A → Λ`.

Source/core/bridge triage:
- source-facing: `h(A⁄R, Λ)`, the ideal `𝔥_A ⊂ Λ`;
- core/canonical: `H[A⁄R]`, `Ideal.map`, and `Ideal.radical`;
- bridge/view: `g.singularIdealIn R`, the canonical target ideal induced by a ring map
  `g : A →+* Λ`.
-/

/-- Situation 16.9.1, bridge form: for a ring map `g : A → Λ`, the ideal induced by `H_{A/R}` in
the target is the radical of the image of the singular ideal `H_{A/R}`. -/
abbrev singularIdealIn (g : A →+* Λ) : Ideal Λ :=
  Ideal.radical (Ideal.map g (H[A⁄R]))

@[simp] theorem singularIdealIn_def (g : A →+* Λ) :
    g.singularIdealIn R = Ideal.radical (Ideal.map g (H[A⁄R])) := rfl

end RingHom

namespace Algebra

variable (R : Type u) (A : Type v) (Λ : Type w)
variable [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra A Λ]

@[inherit_doc RingHom.singularIdealIn]
scoped[Algebra] notation:max "h(" A "⁄" R ", " Λ ")" =>
  RingHom.singularIdealIn R (algebraMap A Λ)

end Algebra
