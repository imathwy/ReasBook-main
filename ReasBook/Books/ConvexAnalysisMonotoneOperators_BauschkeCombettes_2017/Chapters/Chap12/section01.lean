import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_1 (from Chap12) -/
universe u

namespace ERealFunction

variable {H : Type u} [AddGroup H]

/-- Definition 12.1 (1): the infimal convolution of two `]-∞,+∞]`-valued functions. -/
noncomputable def infimalConvolution (f g : H → EReal) : H → EReal :=
  fun x ↦ ⨅ y : H, f y + g (x - y)

infixl:70 " □ " => fun f g x ↦
  ERealFunction.infimalConvolution
    (fun y ↦ (f y : EReal))
    (fun y ↦ (g y : EReal))
    x

/-- The value of the infimal convolution at `x` is the infimum of the translated sums
`y ↦ f y + g (x - y)`. -/
theorem infimalConvolution_apply (f g : H → EReal) (x : H) :
    (f □ g) x = ⨅ y : H, f y + g (x - y) := rfl

namespace infimalConvolution

/-- Definition 12.1 (2): infimal convolution is exact at `x` when some point `y` attains the
defining infimum of `(f □ g) x`. -/
def ExactAt (f g : H → Set.Ioi (⊥ : EReal)) (x : H) : Prop :=
  ∃ y : H, (f □ g) x = (f y : EReal) + (g (x - y) : EReal)

/-- Definition 12.1 (3): infimal convolution is exact when it is exact at every point of its
domain. The project records exactness by this predicate rather than by a second infimal-convolution
operator. -/
def Exact (f g : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ∀ ⦃x : H⦄, x ∈ dom (f □ g) → ExactAt f g x

end infimalConvolution

end ERealFunction
