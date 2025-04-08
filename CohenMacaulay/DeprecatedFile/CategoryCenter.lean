import Mathlib

/-!
This file is replaced by the corresponding files in FromPR
-/

namespace CategoryTheory

universe uC uC' v
variable (C : Type uC) [Category.{uC', uC} C]

abbrev CenterZ : Type max uC uC' := End (𝟭 C)

namespace CenterZ

instance comm_monoid : CommMonoid (CenterZ C) where
  mul_comm := fun a b => NatTrans.id_comm b a

instance comm_ring [Preadditive C] : CommRing (CenterZ C) where

def ring_action (R : Type*) [CommRing R] : R →+* CenterZ (ModuleCat R) where
  toFun := fun r => {
    app := fun M => ModuleCat.ofHom (r • LinearMap.id)
    naturality := by aesop
  }
  map_one' := by aesop
  map_mul' x y := by
    rw [NatTrans.ext_iff]; ext M f
    simpa using (show (x * y) • f = x • (y • f) from (smul_smul ..).symm)
  map_zero' := by aesop
  map_add' x y := by simp_rw [add_smul]; rfl

section complex

variable {ι : Type*} (c : ComplexShape ι) [Limits.HasZeroMorphisms C]

def complex_map : CenterZ C →* CenterZ (HomologicalComplex C c) where
  toFun α := NatTrans.mapHomologicalComplex α c
  map_one' := by aesop
  map_mul' := by aesop

end complex

section localization

variable {C} (W : MorphismProperty C)

def localizationMonoidHom : CenterZ C →* CenterZ W.Localization where
  toFun α := by
    apply CategoryTheory.Localization.Construction.natTransExtension
    rw [CategoryTheory.Functor.comp_id, ← CategoryTheory.Functor.id_comp W.Q]
    exact CategoryTheory.NatTrans.hcomp α (NatTrans.id W.Q)
  map_one' := by aesop
  map_mul' α β := by
    rw [NatTrans.ext_iff]; ext M;
    simp only [Functor.id_obj, End.mul_def, eq_mpr_eq_cast, cast_eq,
      Localization.Construction.natTransExtension_app, NatTrans.comp_app]
    nth_rw 1 [show (NatTrans.id W.Q) = (NatTrans.id W.Q).vcomp (NatTrans.id W.Q) from rfl]
    simp only [NatTrans.vcomp_eq_comp, CategoryTheory.NatTrans.exchange]
    rfl

end localization

end CenterZ
