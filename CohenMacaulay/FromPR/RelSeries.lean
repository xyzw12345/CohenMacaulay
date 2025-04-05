import Mathlib

/- From PR by @chrisflav, #22299 -/
variable {α : Type*} {r : α → α → Prop}

lemma RelSeries.cons_self_tail {p : RelSeries r} (hp : p.length ≠ 0) :
    (p.tail hp).cons p.head (p.3 ⟨0, Nat.zero_lt_of_ne_zero hp⟩) = p := by
  ext n
  · rw [cons_length, tail_length]
    exact (Nat.succ_pred_eq_of_ne_zero hp)
  unfold cons append Fin.append Fin.addCases
  by_cases h : n.1 = 0
  · have : n = 0 := Fin.eq_of_val_eq h
    simp [this]
    rfl
  · simp only [singleton_length, Nat.reduceAdd, Nat.lt_one_iff,
      tail_toFun, Function.comp_apply, Fin.tail, eq_rec_constant, Fin.coe_cast, dif_neg h]
    congr
    exact Fin.val_inj.mp (Nat.succ_pred_eq_of_ne_zero h)

@[elab_as_elim]
def RelSeries.inductionOn (motive : RelSeries r → Sort*)
    (singleton : (x : α) → motive (RelSeries.singleton r x))
    (cons : (p : RelSeries r) → (x : α) → (hx : r x p.head) → (hp : motive p) →
      motive (p.cons x hx)) (p : RelSeries r) :
    motive p := by
  let this {n : ℕ} (heq : p.length = n) : motive p := by
    induction' n with d hd generalizing p
    · convert singleton p.head
      ext n
      exact heq
      simp [show n = 0 by omega]
      rfl
    · have lq := p.tail_length (heq ▸ d.zero_ne_add_one.symm)
      nth_rw 3 [heq] at lq
      convert cons (p.tail (heq ▸ d.zero_ne_add_one.symm)) p.head
        (p.3 ⟨0, heq ▸ d.zero_lt_succ⟩) (hd _ lq)
      exact (p.cons_self_tail (heq ▸ d.zero_ne_add_one.symm)).symm
  exact this rfl

@[elab_as_elim]
def RelSeries.inductionOn' (motive : RelSeries r → Sort*)
    (singleton : (x : α) → motive (RelSeries.singleton r x))
    (snoc : (p : RelSeries r) → (x : α) → (hx : r p.last x) → (hp : motive p) →
      motive (p.snoc x hx)) (p : RelSeries r) :
    motive p := by
  sorry
