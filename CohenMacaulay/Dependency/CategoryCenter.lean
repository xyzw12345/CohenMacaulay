import Mathlib

namespace CategoryTheory

universe u v
variable (C : Type v) [Category.{u,v} C]

def CategoryTheory.CenterZ : Type max u v := End (𝟭 C)

instance CategoryTheory.CenterZ.monoid : Monoid (CategoryTheory.CenterZ C) := CategoryTheory.End.monoid

def CategoryTheory.CenterZ.ring_action : sorry := sorry

def CategoryTheory.CenterZ.complex_map : sorry := sorry
def CategoryTheory.CenterZ.localization_map : sorry := sorry
