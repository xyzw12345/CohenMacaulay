import Mathlib

universe u

namespace CategoryTheory

section Exact2

variable {C : ShortComplex AddCommGrp.{u}} (h : C.Exact)

include h in
theorem subsingleton_of_subsingleton_subsingleton (h0 : Subsingleton C.X₁)
    (h2 : Subsingleton C.X₃) : Subsingleton C.X₂ := by
  rw [CategoryTheory.ShortComplex.ab_exact_iff] at h
  suffices h : ∀ a : C.X₂, a = 0 from subsingleton_of_forall_eq 0 h
  intro a
  obtain ⟨b, hb⟩ := h a (@Subsingleton.elim _ h2 _ 0)
  rw [show b = 0 from (@Subsingleton.elim _ h0 _ 0), map_zero] at hb
  exact hb.symm

include h in
theorem subsingleton_of_subsingleton_zero_hom (h0 : Subsingleton C.X₁) (hg : C.g = 0) :
    Subsingleton C.X₂ := by

  sorry

section Exact3

noncomputable def isoOfSubsingletonZeroMorphism {C1 C2 : ShortComplex AddCommGrp.{u}} (h1 : C1.Exact)
    (h2 : C2.Exact) (e : Iso C1.X₂ C2.X₁) (e' : Iso C1.X₃ C2.X₂)
    (h'' : (e.hom ≫ C2.f) = (C1.g ≫ e'.hom)) (h_subsingleton : Subsingleton C1.X₁)
    (h_zerohom : C2.g = 0) : C1.X₂ ≃+ C1.X₃ := by
  rw [CategoryTheory.ShortComplex.ab_exact_iff] at h1 h2
  have h1 : Function.Injective C1.g := by
    apply C1.g.hom.ker_eq_bot_iff.mp
    ext x
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_bot]
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
    obtain ⟨x1, hx1⟩ := h1 x h
    rw [show x1 = 0 from (@Subsingleton.elim _ h_subsingleton _ 0), map_zero] at hx1
    exact hx1.symm
  have h2 : Function.Surjective C2.f := fun x ↦ h2 x (by simp [h_zerohom])
  have h3 : Function.Surjective C1.g := by
    have : C1.g = e.hom ≫ C2.f ≫ e'.inv := by
      rw [← CategoryTheory.Category.assoc, h'']
      simp
    simp only [this, AddCommGrp.hom_comp, AddMonoidHom.coe_comp]
    exact Function.Surjective.comp (Function.Surjective.comp (surjective_of_epi ⇑(AddCommGrp.Hom.hom e'.inv)) h2)
      (surjective_of_epi ⇑(AddCommGrp.Hom.hom e.hom))
  have h4 : C1.g.hom.range = ⊤ := AddMonoidHom.range_eq_top.mpr h3
  exact (C1.g.hom.ofInjective h1).trans (h4 ▸ AddSubgroup.topEquiv)
