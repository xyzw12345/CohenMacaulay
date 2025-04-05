import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

universe w'' w' w v u

namespace CategoryTheory.Abelian

open CategoryTheory.Abelian.Ext DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (X Y : C)

lemma mk₀_bijective : Function.Bijective (mk₀ (X := X) (Y := Y)) := sorry

/-- The bijection `Ext X Y 0 ≃ (X ⟶ Y)`. -/
@[simps! symm_apply]
noncomputable def homEquiv₀ : Ext X Y 0 ≃ (X ⟶ Y) :=
  (Equiv.ofBijective _ (mk₀_bijective X Y)).symm

end CategoryTheory.Abelian
