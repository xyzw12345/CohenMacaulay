import Mathlib

namespace CategoryTheory

section CenterZ
universe u v
variable (C : Type v) [Category.{u, v} C]

abbrev CenterZ : Type max u v := End (𝟭 C)

instance CenterZ.comm_monoid : CommMonoid (CenterZ C) where
  mul_comm := fun a b => NatTrans.id_comm b a

instance CenterZ.comm_ring [Preadditive C] : CommRing (CenterZ C) where

end CenterZ

def CenterZ.ring_action (R : Type*) [CommRing R] : R →+* CenterZ (ModuleCat R) where
  toFun := fun r => {
    app := fun M => ModuleCat.ofHom (r • LinearMap.id)
    naturality := by aesop
  }
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

def CenterZ.complex_map (A : Type*) : sorry := sorry

def CenterZ.localization_map : sorry := sorry
