/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Smallness of Ext-groups from the existence of enough projectives
Let `C : Type u` be an abelian category (`Category.{v} C`) that has enough projectives.
If `C` is locally `w`-small, i.e. the type of morphisms in `C` are `Small.{w}`,
then we show that the condition `HasExt.{w}` holds, which means that for `X` and `Y` in `C`,
and `n : ℕ`, we may define `Ext X Y n : Type w`. In particular, this holds for `w = v`.
However, the main lemma `hasExt_of_enoughProjectives` is not made an instance:
for a given category `C`, there may be different reasonable choices for the universe `w`,
and if we have two `HasExt.{w₁}` and `HasExt.{w₂}` instances, we would have
to specify the universe explicitly almost everywhere, which would be an inconvenience.
Then, we must be very selective regarding `HasExt` instances.
-/

universe w v u

open CategoryTheory Category

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CochainComplex

open HomologicalComplex

lemma isSplitEpi_to_singleFunctor_obj_of_projective
    {P : C} [Projective P] {K : CochainComplex C ℤ} {i : ℤ}
    (π : K ⟶ (CochainComplex.singleFunctor C i).obj P) [K.IsStrictlyLE i] [QuasiIsoAt π i] :
    IsSplitEpi π := sorry

end CochainComplex

namespace DerivedCategory

variable [HasDerivedCategory.{w} C]

lemma from_singleFunctor_obj_projective_eq_zero {P : C} [Projective P]
    {L : CochainComplex C ℤ} {i : ℤ}
    (φ : Q.obj ((CochainComplex.singleFunctor C i).obj P) ⟶ Q.obj L)
    (n : ℤ) (hn : n < i) [L.IsStrictlyLE n] :
    φ = 0 := sorry

end DerivedCategory

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]


namespace Abelian.Ext

open DerivedCategory

lemma eq_zero_of_projective [HasExt.{w} C] {P Y : C} {n : ℕ} [Projective P]
    (e : Ext P Y (n + 1)) : e = 0 := by
  letI := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (- (n + 1)) 0
    (by omega)).hom.app _), zero_hom, Limits.zero_comp]
  apply from_singleFunctor_obj_projective_eq_zero
    (L := (CochainComplex.singleFunctor C (-(n + 1))).obj Y) (n := - (n + 1)) _ (by omega)

end Abelian.Ext

variable (C)

open Abelian

lemma hasExt_of_enoughProjectives [LocallySmall.{w} C] [EnoughProjectives C] :
  HasExt.{w} C := sorry

end CategoryTheory
