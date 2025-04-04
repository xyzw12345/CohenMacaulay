import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.Exact

#check CategoryTheory.ComposableArrows.Exact
open CategoryTheory
variable {C : Type*} [Category C] [Limits.HasZeroMorphisms C]

structure StableSES (P : C -> Prop) : Prop where
  stability : (S : ShortComplex C) -> S.Exact -> P (S.X₁) -> P (S.X₃) -> P (S.X₂)
