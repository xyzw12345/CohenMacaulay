/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.Basic
import CohenMacaulay.FromPR.Center.Basic

/-!
# Center of a linear category
-/

universe w v u

namespace CategoryTheory

open Category Limits

namespace Linear

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C]

@[simps]
def toCatCenter [Linear R C] : R →+* CatCenter C where
  toFun a :=
    { app := fun X => a • 𝟙 X }
  map_one' := by aesop_cat
  map_mul' a b := by
    rw [CatCenter.mul_comm]
    ext X
    erw [CatCenter.mul_app', Linear.smul_comp, Linear.comp_smul, smul_smul, comp_id]
  map_zero' := by aesop_cat
  map_add' a b := by
    ext X
    dsimp
    rw [NatTrans.app_add, add_smul]

section

variable {R C}
variable (φ : R →+* CatCenter C) (X Y : C)

def smulOfRingMorphism : SMul R (X ⟶ Y) where
  smul a f := (φ a).app X ≫ f

variable {X Y}

lemma smulOfRingMorphism_smul_eq (a : R) (f : X ⟶ Y) :
    letI := smulOfRingMorphism φ X Y
    a • f = (φ a).app X ≫ f := rfl

/-- `a • f = f ≫ (φ a).app Y`. -/
lemma smulOfRingMorphism_smul_eq' (a : R) (f : X ⟶ Y) :
    letI := smulOfRingMorphism φ X Y
    a • f = f ≫ (φ a).app Y := by
  rw [smulOfRingMorphism_smul_eq]
  exact ((φ a).naturality f).symm

variable (X Y)

def homModuleOfRingMorphism : Module R (X ⟶ Y) := by
  letI := smulOfRingMorphism φ X Y
  exact
  { one_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq,
        Functor.id_obj, map_one, End.one_def, NatTrans.id_app, id_comp]
    mul_smul := fun a b f => by
      simp only [smulOfRingMorphism_smul_eq', Functor.id_obj, map_mul, End.mul_def,
        NatTrans.comp_app, assoc]
    smul_zero := fun a => by
      simp only [smulOfRingMorphism_smul_eq, Functor.id_obj, comp_zero]
    zero_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq, Functor.id_obj, map_zero,
        zero_app, zero_comp]
    smul_add := fun a b => by
      simp [smulOfRingMorphism_smul_eq]
    add_smul := fun a b f => by
      simp only [smulOfRingMorphism_smul_eq]
      rw [map_add, NatTrans.app_add, Preadditive.add_comp] }

def ofRingMorphism : Linear R C := by
  letI := homModuleOfRingMorphism φ
  exact
    { smul_comp := fun X Y Z r f g => by simp only [smulOfRingMorphism_smul_eq, assoc]
      comp_smul := fun X Y Z f r g => by simp only [smulOfRingMorphism_smul_eq', assoc] }

end

end Linear

end CategoryTheory
