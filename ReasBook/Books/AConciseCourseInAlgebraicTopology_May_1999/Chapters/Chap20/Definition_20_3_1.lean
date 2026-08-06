import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1

noncomputable section

universe u

-- Semantic recall: `Definition_20_1_1` already provides the chapter owners
-- `relativeTopHomologyGroup`, `relativeToLocalTopHomologyMap`, and `localTopHomologyGroup`, so
-- this item reuses that upstream relative singular-chain model for `H_n(M, M \ X; R)` and its
-- point-local restriction maps.

section

variable (Coeff : Type u) [CommRing Coeff]
variable (n : ℕ)
variable (M : Type u) [TopologicalSpace M]

/-- A class in `H_n(M, M \ {x}; R)` is a local generator if some identification with the constant
coefficient module `R` sends it to `1`. -/
def isLocalTopHomologyGenerator (x : M) (η : localTopHomologyGroup Coeff n M x) : Prop :=
  ∃ e : localTopHomologyGroup Coeff n M x ≅ ModuleCat.of.{u} Coeff Coeff, e.hom η = 1

/-- Unfolding `isLocalTopHomologyGenerator` gives the explicit local-generator criterion. -/
theorem isLocalTopHomologyGenerator_iff (x : M) (η : localTopHomologyGroup Coeff n M x) :
    isLocalTopHomologyGenerator Coeff n M x η ↔
      ∃ e : localTopHomologyGroup Coeff n M x ≅ ModuleCat.of.{u} Coeff Coeff, e.hom η = 1 :=
  Iff.rfl

/-- A chosen identification sending `η` to `1` exhibits `η` as a local generator. -/
theorem isLocalTopHomologyGenerator_of_iso (x : M) (η : localTopHomologyGroup Coeff n M x)
    (e : localTopHomologyGroup Coeff n M x ≅ ModuleCat.of.{u} Coeff Coeff) (hη : e.hom η = 1) :
    isLocalTopHomologyGenerator Coeff n M x η :=
  ⟨e, hη⟩

/-- A local generator comes equipped with an identification carrying it to `1`. -/
theorem isLocalTopHomologyGenerator.exists_iso {x : M}
    {η : localTopHomologyGroup Coeff n M x}
    (hη : isLocalTopHomologyGenerator Coeff n M x η) :
    ∃ e : localTopHomologyGroup Coeff n M x ≅ ModuleCat.of.{u} Coeff Coeff, e.hom η = 1 :=
  hη

/-- Definition 20.3.1. An `R`-fundamental class of `M` at a subspace `X` is a class in
`H_n(M, M \ X; R)` whose image in `H_n(M, M \ {x}; R)` is a local generator for every `x ∈ X`. -/
def isFundamentalClassAtSubspace (X : Set M) (η : relativeTopHomologyGroup Coeff n M X) : Prop :=
  ∀ ⦃x : M⦄ (hx : x ∈ X),
    isLocalTopHomologyGenerator Coeff n M x
      ((relativeToLocalTopHomologyMap Coeff n M X hx) η)

/-- Unfolding `isFundamentalClassAtSubspace` gives the pointwise local-generator criterion. -/
theorem isFundamentalClassAtSubspace_iff (X : Set M) (η : relativeTopHomologyGroup Coeff n M X) :
    isFundamentalClassAtSubspace Coeff n M X η ↔
      ∀ ⦃x : M⦄ (hx : x ∈ X),
        isLocalTopHomologyGenerator Coeff n M x
          ((relativeToLocalTopHomologyMap Coeff n M X hx) η) :=
  Iff.rfl

/-- A fundamental class at `X` restricts to a local generator at each point of `X`. -/
theorem isFundamentalClassAtSubspace.localGenerator {X : Set M}
    {η : relativeTopHomologyGroup Coeff n M X}
    (hη : isFundamentalClassAtSubspace Coeff n M X η) {x : M} (hx : x ∈ X) :
    isLocalTopHomologyGenerator Coeff n M x
      ((relativeToLocalTopHomologyMap Coeff n M X hx) η) :=
  hη hx

end
