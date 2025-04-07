import Mathlib

namespace CategoryTheory

section CenterZ
universe u v
variable (C : Type v) [Category.{u,v} C]

def CenterZ : Type max u v := End (𝟭 C)

instance CenterZ.monoid : Monoid (CenterZ C) := CategoryTheory.End.monoid
instance CenterZ.comm_monoid : CommMonoid (CenterZ C) where
  mul_comm := fun a b => NatTrans.id_comm b a

instance CenterZ.comm_ring [Preadditive C] : CommRing (CenterZ C) := sorry

end CenterZ

def CenterZ.ring_action (R : Type*) [CommRing R] : R →+* CenterZ (ModuleCat R) where
  toFun := fun r => {
    app := fun M => ModuleCat.ofHom (r • LinearMap.id)
    naturality := by -- aesop proof
      intro X Y f
      simp_all only [Functor.id_obj, Functor.id_map]
      ext x : 2
      simp_all only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul]
  }
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
def CenterZ.complex_map (A : Type*) : sorry := sorry
def CenterZ.localization_map : sorry := sorry
