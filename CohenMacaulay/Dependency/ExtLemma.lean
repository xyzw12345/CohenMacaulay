import Mathlib
import CohenMacaulay.FromPR.Center.Linear
import CohenMacaulay.FromPR.Center.Localization

namespace CategoryTheory

section complex
universe uC uC' v
variable (C : Type uC) [Category.{uC', uC} C]
variable {ι : Type*} (c : ComplexShape ι)

def CatCenter.complexCommMonoidMorphism [Limits.HasZeroMorphisms C] : CatCenter C →* CatCenter (HomologicalComplex C c) where
  toFun α := NatTrans.mapHomologicalComplex α c
  map_one' := rfl
  map_mul' := by aesop_cat

def CatCenter.complexRingMorphism [Preadditive C] : CatCenter C →+* CatCenter (HomologicalComplex C c) where
  __ := CatCenter.complexCommMonoidMorphism C c
  map_zero' := rfl
  map_add' := by aesop_cat

end complex

section Ext

universe uC uC' v
variable (C : Type uC) [Category.{uC', uC} C]

variable {C} [Abelian C] [HasDerivedCategory C] [HasExt.{v} C]

set_option linter.unusedTactic false

open Abelian in
theorem homCommute (M : C) (N : C) (α : CatCenter C) (n : ℕ) :
  (Ext.mk₀ (α.app M)).postcomp N (add_zero n) =
    (Ext.mk₀ (α.app N)).precomp M (zero_add n) := by
      -- We first work under DerivedCategory (not small!)
      let CC := HomologicalComplex C (ComplexShape.up ℤ)
      let WC := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
      let DC := DerivedCategory C -- (WC.Localization')
      let N₀ := (CochainComplex.singleFunctor C 0).obj N
      let M₀ := (CochainComplex.singleFunctor C 0).obj M
      let N₁ := WC.Q'.obj N₀
      let M₁ := WC.Q'.obj M₀
      let M₂ := M₁⟦(n : ℤ)⟧

      -- #check (CatCenter.localizationRingMorphism DerivedCategory.Q WC ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α)).naturality
      have := (CatCenter.localizationRingMorphism DerivedCategory.Q WC ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α)).naturality
      -- simp only [Functor.id_obj, Functor.id_map, OneHom.toFun_eq_coe,
        -- MonoidHom.toOneHom_coe] at this

      #check ((CatCenter.localizationRingMorphism DerivedCategory.Q WC)
            ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)) α)).app N₁

      have sfN : ((CatCenter.localizationRingMorphism DerivedCategory.Q WC)
          ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)) α)).app N₁
          = DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map (α.app N)) := by
        suffices ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)) α).app N₀
            = (CochainComplex.singleFunctor C 0).map (α.app N) by
            -- show α.localization DerivedCategory.Q WC
          -- unfold CatCenter.localizationRingMorphism
          #check CatCenter.localization
          #check Localization.liftNatTrans
          sorry
        #check NatTrans.mapHomologicalComplex
        -- suffices (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app N₀
        --     = (CochainComplex.singleFunctor C 0).map (α.app N) by exact this
        show (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app N₀
            = (CochainComplex.singleFunctor C 0).map (α.app N)
        ext i

        sorry

      have (f : N₁ ⟶ M₂) := (CatCenter.localizationRingMorphism DerivedCategory.Q WC ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α)).naturality f


      -- #check M₀⟦(n : ℤ)⟧
      -- #check M₁⟦(n : ℤ)⟧
      -- have : WC.Q.obj (M₀⟦(n : ℤ)⟧) ≅ M₁⟦(n : ℤ)⟧ := by
      --   sorry

      #check (CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α
      #check ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α)
      have : CatCenter CC →+* CatCenter DC := by
        #check WC.Q'
        #check CatCenter.localizationRingMorphism
        -- apply CatCenter.localizationRingMorphism
        sorry

      #check Abelian.Ext.bilinearComp
      #check Abelian.Ext.comp
      #check Localization.SmallShiftedHom.comp
      #check Localization.SmallHom.comp
      #check Abelian.Ext
      sorry

end Ext

end CategoryTheory
