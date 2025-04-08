import Mathlib
import CohenMacaulay.FromPR.Ext0

universe u v w

namespace CategoryTheory.Abelian.Ext

open CategoryTheory.Abelian.Ext DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section Ring

variable (R : Type*) [Ring R] [Linear R C]

instance {X Y : C} (n : ℕ): Module R (Ext.{w} X Y n) where
  smul := sorry
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

noncomputable def homEquiv₀_linearHom {X Y : C} : Ext X Y 0 ≃ₗ[R] (X ⟶ Y) where
  __ := homEquiv₀_hom X Y
  map_smul' := sorry

end Ring

section CommRing

variable (R : Type*) [CommRing R]

noncomputable def bilinearCompOfLinear [Linear R C] (X Y Z : C) (a b c : ℕ) (h : a + b = c) :
    Ext.{w} X Y a →ₗ[R] Ext.{w} Y Z b →ₗ[R] Ext.{w} X Z c where
  toFun α :=
    { toFun := fun β ↦ α.comp β h
      map_add' := by sorry
      map_smul' := by sorry }
  map_add' := by sorry
  map_smul' := by sorry

noncomputable def postcompOfLinear [Linear R C] {Y Z : C} {a b n : ℕ} (f : Ext.{w} Y Z n) (X : C) (h : a + n = b) :
    Ext.{w} X Y a →ₗ[R] Ext.{w} X Z b := (bilinearCompOfLinear R X Y Z a n b h).flip f

end CommRing

end Ext
