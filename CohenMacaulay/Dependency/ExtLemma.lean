import Mathlib
import CohenMacaulay.FromPR.Center.Linear
import CohenMacaulay.FromPR.Center.Localization

namespace CategoryTheory

section Ext

universe uC uC' uD uD' v
variable {C : Type uC} [Category.{uC', uC} C]

section SmallHom

open CategoryTheory Localization
variable {D : Type uD} [Category.{uD', uD} D]
variable {W : MorphismProperty C} {L : C ⥤ D} [L.IsLocalization W]
variable {X Y : C} [HasSmallLocalizedHom.{v} W X X] [HasSmallLocalizedHom.{v} W Y Y] [HasSmallLocalizedHom.{v} W X Y]

private theorem SmallHom.commute_iff {f : X ⟶ X} {g : Y ⟶ Y} :
  (∀ (h : SmallHom.{v} W X Y), (SmallHom.mk.{v} W f).comp h = h.comp (SmallHom.mk.{v} W g)) ↔ (∀ (h : X ⟶ Y), f ≫ h = h ≫ g) := by
  sorry


-- private theorem CategoryTheory.Localization.SmallHom
--   [HasSmallLocalizedHom W X Y] : SmallHom W X Y ≃ (L.obj X ⟶ L.obj Y) := sorry

end SmallHom

variable [Abelian C] [HasExt.{v} C]

open Abelian in
set_option maxHeartbeats 2000000 in
theorem homCommute (M : C) (N : C) (α : CatCenter C) (n : ℕ) :
    (Ext.mk₀ (α.app M)).postcomp N (add_zero n) = (Ext.mk₀ (α.app N)).precomp M (zero_add n) := by
  apply AddMonoidHom.ext
  unfold Abelian.Ext Ext.mk₀ Ext.precomp Ext.postcomp
  unfold Ext.bilinearComp Ext.comp Localization.SmallShiftedHom
  unfold Localization.SmallShiftedHom.comp Localization.SmallShiftedHom.mk₀
  unfold Localization.SmallShiftedHom.shift
  simp
  apply SmallHom.commute_iff.mpr


end Ext

end CategoryTheory
