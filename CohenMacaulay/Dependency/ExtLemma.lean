import Mathlib
import CohenMacaulay.FromPR.Center.Linear
import CohenMacaulay.FromPR.Center.Localization

namespace CategoryTheory

section Ext

universe uC uC' v
variable (C : Type uC) [Category.{uC', uC} C]

variable {C} [Abelian C] [HasExt.{v} C]

open Abelian in
theorem homCommute (M : C) (N : C) (α : CatCenter C) (n : ℕ) :
  (Ext.mk₀ (α.app M)).postcomp N (add_zero n) =
    (Ext.mk₀ (α.app N)).precomp M (zero_add n) := sorry

end Ext

end CategoryTheory
