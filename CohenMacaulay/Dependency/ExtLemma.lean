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

section singleFunctor
#check CochainComplex.singleFunctor
#check NatTrans.mapHomologicalComplex
#check HomologicalComplex.single

universe uC uC' uD uD' v
variable {C : Type uC} [Category.{uC', uC} C] [Limits.HasZeroObject C] [Limits.HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD', uD} D] [Limits.HasZeroObject D] [Limits.HasZeroMorphisms D]
variable {ι : Type*} (c : ComplexShape ι) (j : ι) [DecidableEq ι]

#check HomologicalComplex.single C c j
#check NatTrans.mapHomologicalComplex

open ZeroObject in
noncomputable def HomologicalComplex.singleMapHomologicalComplexeq.X (F : C ⥤ D) [F.PreservesZeroMorphisms] (F₀ : F.obj 0 = 0) (x : C) :
    ((HomologicalComplex.single C c j ⋙ Functor.mapHomologicalComplex F c).obj x).X
    = ((F ⋙ HomologicalComplex.single D c j).obj x).X := by
  unfold HomologicalComplex.single
  ext i
  if h : i = j then
    simp[h]
  else
    simp[h]
    exact F₀


#check HomologicalComplex.singleMapHomologicalComplexeq.X
#check HomologicalComplex

open ZeroObject in
noncomputable def HomologicalComplex.singleMapHomologicalComplexeq.d (F : C ⥤ D) [F.PreservesZeroMorphisms] (F₀ : F.obj 0 = 0) (x : C) :
    ((HomologicalComplex.single C c j ⋙ Functor.mapHomologicalComplex F c).obj x).d
    = fun i i' => eqToHom (congrFun ((HomologicalComplex.singleMapHomologicalComplexeq.X c j F F₀) x) i)
    ≫ ((F ⋙ HomologicalComplex.single D c j).obj x).d i i' ≫
    eqToHom (congrFun ((HomologicalComplex.singleMapHomologicalComplexeq.X c j F F₀) x) i').symm := by
  ext i i'
  if h : i = j then
    simp[h]
  else
    simp[h]

-- Requires F.obj 0 = 0, e.g. id_C
open ZeroObject in
noncomputable def HomologicalComplex.singleMapHomologicalComplexeq (F : C ⥤ D) [F.PreservesZeroMorphisms] (F₀ : F.obj 0 = 0) :
    HomologicalComplex.single C c j ⋙ Functor.mapHomologicalComplex F c
    = F ⋙ HomologicalComplex.single D c j := by
  apply Functor.ext
  unfold HomologicalComplex.single
  intro x y f
  ext i
  if h : i = j then
    simp[h]
    sorry
  else
    sorry
  intro x

  have l₁ := HomologicalComplex.singleMapHomologicalComplexeq.X c j F F₀ x
  have l₂ := HomologicalComplex.singleMapHomologicalComplexeq.d c j F F₀ x

  sorry
  -- exact HomologicalComplex.singleMapHomologicalComplex F c j


  -- exact HomologicalComplex.singleMapHomologicalComplex F c j

end singleFunctor
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

-- open Abelian in
-- set_option maxHeartbeats 2000000 in
-- theorem homCommute (M : C) (N : C) (α : CatCenter C) (n : ℕ) :
--     (Ext.mk₀ (α.app M)).postcomp N (add_zero n) = (Ext.mk₀ (α.app N)).precomp M (zero_add n) := by
--   apply AddMonoidHom.ext
--   unfold Abelian.Ext Ext.mk₀ Ext.precomp Ext.postcomp
--   unfold Ext.bilinearComp Ext.comp Localization.SmallShiftedHom
--   unfold Localization.SmallShiftedHom.comp Localization.SmallShiftedHom.mk₀
--   unfold Localization.SmallShiftedHom.shift
--   simp
--   apply SmallHom.commute_iff.mpr

  -- (Ext.mk₀ (α.app M)).postcomp N (add_zero n) =
  --   (Ext.mk₀ (α.app N)).precomp M (zero_add n) := by
  --     -- We first work under DerivedCategory (not small!)
  --     let CC := HomologicalComplex C (ComplexShape.up ℤ)
  --     let WC := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  --     let DC := DerivedCategory C -- (WC.Localization')
  --     let N₀ := (CochainComplex.singleFunctor C 0).obj N
  --     let M₀ := (CochainComplex.singleFunctor C 0).obj M
  --     let N₁ := WC.Q'.obj N₀
  --     let M₁ := WC.Q'.obj M₀
  --     let M₂ := M₁⟦(n : ℤ)⟧

  --     -- #check (CatCenter.localizationRingMorphism DerivedCategory.Q WC ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α)).naturality
  --     have := (CatCenter.localizationRingMorphism DerivedCategory.Q WC ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α)).naturality
  --     -- simp only [Functor.id_obj, Functor.id_map, OneHom.toFun_eq_coe,
  --       -- MonoidHom.toOneHom_coe] at this

  --     #check ((CatCenter.localizationRingMorphism DerivedCategory.Q WC)
  --           ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)) α)).app N₁

  --     have sfN : ((CatCenter.localizationRingMorphism DerivedCategory.Q WC)
  --         ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)) α)).app N₁
  --         = DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map (α.app N)) := by
  --       suffices ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)) α).app N₀
  --           = (CochainComplex.singleFunctor C 0).map (α.app N) by
  --           -- show α.localization DerivedCategory.Q WC
  --         -- unfold CatCenter.localizationRingMorphism
  --         #check CatCenter.localization
  --         #check Localization.liftNatTrans
  --         sorry
  --       #check NatTrans.mapHomologicalComplex
  --       -- suffices (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app N₀
  --       --     = (CochainComplex.singleFunctor C 0).map (α.app N) by exact this
  --       show (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app N₀
  --           = (CochainComplex.singleFunctor C 0).map (α.app N)
  --       ext i

  --       sorry

  --     have (f : N₁ ⟶ M₂) := (CatCenter.localizationRingMorphism DerivedCategory.Q WC ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α)).naturality f


  --     -- #check M₀⟦(n : ℤ)⟧
  --     -- #check M₁⟦(n : ℤ)⟧
  --     -- have : WC.Q.obj (M₀⟦(n : ℤ)⟧) ≅ M₁⟦(n : ℤ)⟧ := by
  --     --   sorry

  --     #check (CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α
  --     #check ((CatCenter.complexRingMorphism C (ComplexShape.up ℤ)).toFun α)
  --     have : CatCenter CC →+* CatCenter DC := by
  --       #check WC.Q'
  --       #check CatCenter.localizationRingMorphism
  --       -- apply CatCenter.localizationRingMorphism
  --       sorry

  --     #check Abelian.Ext.bilinearComp
  --     #check Abelian.Ext.comp
  --     #check Localization.SmallShiftedHom.comp
  --     #check Localization.SmallHom.comp
  --     #check Abelian.Ext
  --     sorry

end Ext

end CategoryTheory
