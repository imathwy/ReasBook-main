module

import Mathlib.Logic.Function.Defs

/- Definition 2.8 (1): A function is injective (or one-to-one) when distinct
inputs have distinct images; equivalently, equal images imply equal inputs. -/
#check Function.Injective

/- Definition 2.8 (2): A function is surjective (or maps its domain onto its
codomain) when every codomain element is the image of some domain element. -/
#check Function.Surjective

/- Definition 2.8 (3): A function is bijective (or a one-to-one
correspondence) when it is both injective and surjective. -/
#check Function.Bijective
