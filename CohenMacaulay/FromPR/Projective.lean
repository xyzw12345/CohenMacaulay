/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
import Mathlib

/-!
# The category of `R`-modules has enough projectives.
-/

universe v u w

open CategoryTheory LinearMap ModuleCat

namespace ModuleCat

variable {R : Type u} [Ring R] {M : ModuleCat.{v} R}

-- We transport the corresponding result from `Module.Projective`.
/-- Modules that have a basis are projective. -/
theorem projective_of_free' {ι : Type w} (b : Basis ι R M) : Projective M := by
  letI : Module.Projective R (ModuleCat.of R M) := Module.Projective.of_basis b
  refine ⟨fun E X epi => ?_⟩
  obtain ⟨f, h⟩ := Module.projective_lifting_property X.hom E.hom
    ((ModuleCat.epi_iff_surjective _).mp epi)
  exact ⟨ofHom f, hom_ext h⟩

/-- The category of modules has enough projectives, since every module is a quotient of a free
  module. -/
instance enoughProjectives [Small.{v} R] : EnoughProjectives (ModuleCat.{v} R) where
  presentation M :=
    let e : Basis M R (M →₀ Shrink.{v} R) := ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
    ⟨{p := ModuleCat.of R (M →₀ Shrink.{v} R)
      projective := projective_of_free' e
      f := ofHom <| e.constr ℕ _root_.id
      epi := (epi_iff_range_eq_top _).mpr <| range_eq_top.2 fun m => ⟨Finsupp.single m 1, by
        simp only [Basis.constr, Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_single,
          LinearEquiv.coe_mk, Finsupp.lmapDomain_id, id_comp, hom_ofHom, LinearMap.coe_comp,
          Function.comp_apply, LinearEquiv.coe_coe, Shrink.linearEquiv_apply,
          Finsupp.linearCombination_single, e]
        rw [show (equivShrink R).symm 1 = 1 from (equivShrink R).symm_apply_apply 1]
        exact MulAction.one_smul m⟩}⟩

end ModuleCat
