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
universe uC uC'
variable {C : Type uC} [Category.{uC', uC} C] [Limits.HasZeroObject C] [Limits.HasZeroMorphisms C]
variable {ι : Type*} (c : ComplexShape ι) (j : ι) [DecidableEq ι]

open ZeroObject in
@[simp]
lemma HomologicalComplex.singleMapHomologicalComplexNatId : (HomologicalComplex.singleMapHomologicalComplex (𝟭 C) c j) = Iso.refl (HomologicalComplex.single C c j) := by
  ext x i
  if h : i = j then
    unfold HomologicalComplex.singleMapHomologicalComplex HomologicalComplex.single
    simp[h]
  else
    unfold HomologicalComplex.singleMapHomologicalComplex HomologicalComplex.single
    simp[h]
    have l₁ : (if i = j then x else 0) = 0 := by simp[h]
    have l₂ (a : C) (e : a = 0) : 𝟙 a = 0 := by
      rw[e]
      exact Limits.id_zero
    exact
      Eq.symm
        (eq_of_comp_right_eq fun {X} h ↦
          congrArg (CategoryStruct.comp h) (l₂ (if i = j then x else 0) l₁))

section
universe uD uD' v
variable {D : Type uD} [Category.{uD', uD} D] [Limits.HasZeroObject D] [Limits.HasZeroMorphisms D]

@[simp]
noncomputable def HomologicalComplex.singleMapHomologicalComplexNatTrans (F G : C ⥤ D) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (α : F ⟶ G) :
    (HomologicalComplex.singleMapHomologicalComplex F c j).hom ≫ (CategoryTheory.whiskerRight α (HomologicalComplex.single D c j))
    = CategoryTheory.whiskerLeft (HomologicalComplex.single C c j) (NatTrans.mapHomologicalComplex α c) ≫ (HomologicalComplex.singleMapHomologicalComplex G c j).hom := by
  ext x i
  unfold HomologicalComplex.singleMapHomologicalComplex HomologicalComplex.single
  if h : i = j then
    simp[h]
    rw [← CategoryTheory.comp_eqToHom_iff, Category.assoc, Category.assoc, CategoryTheory.eqToHom_trans]
    exact Eq.symm (dcongr_arg α.app (by simp[h]))
    simp[h]
  else
    simp[h]
end

variable (α : CatCenter C)
lemma HomologicalComplex.singleMapCenter : whiskerRight α (HomologicalComplex.single C c j) =
    whiskerLeft (HomologicalComplex.single C c j) (NatTrans.mapHomologicalComplex α c) := by
  have l := HomologicalComplex.singleMapHomologicalComplexNatTrans c j (𝟭 C) (𝟭 C) α
  simp only [HomologicalComplex.singleMapHomologicalComplexNatId, Iso.refl_hom] at l
  have : 𝟙 (HomologicalComplex.single C c j) ≫ whiskerRight α (HomologicalComplex.single C c j) = whiskerRight α (HomologicalComplex.single C c j) := by
    exact Category.id_comp (whiskerRight α (HomologicalComplex.single C c j))
  rw [this] at l
  have : whiskerLeft (HomologicalComplex.single C c j) (NatTrans.mapHomologicalComplex α c) ≫ 𝟙 (HomologicalComplex.single C c j) = whiskerLeft (HomologicalComplex.single C c j) (NatTrans.mapHomologicalComplex α c) := by
    exact Category.comp_id (whiskerLeft (HomologicalComplex.single C c j) (NatTrans.mapHomologicalComplex α c))
  rw [this] at l
  exact l




end singleFunctor
