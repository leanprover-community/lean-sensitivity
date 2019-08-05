import tactic.fin_cases
import linear_algebra.finite_dimensional
import analysis.normed_space.basic

noncomputable theory

open function

instance : directed_order ℝ :=
{ directed := λ i j, ⟨max i j, le_max_left _ _, le_max_right _ _⟩,
  ..real.linear_order }

@[simp] lemma abs_nonpos_iff {α : Type*} [decidable_linear_ordered_comm_group α] {a : α} :
  abs a ≤ 0 ↔ a = 0 :=
by rw [← not_lt, abs_pos_iff, not_not]

lemma fin.succ_ne_zero {n} (k : fin n) : fin.succ k ≠ 0 :=
begin
  cases k with k hk,
  intro h,
  have : k + 1 = 0 := (fin.ext_iff _ _).1 h,
  finish
end

lemma bxor_of_ne {x y : bool} (h : x ≠ y) : bxor x y = tt :=
by cases x; cases y; refl <|> contradiction

lemma iff.eq_cancel_left {α : Type*} {a b c : α} (h : b = c) :
  (a = b ↔ a = c) := by rw h

lemma iff.eq_cancel_right {α : Type*} {a b c : α} (h : a = b) :
  (a = c ↔ b = c) := by rw h

section cardinal_lemma
universe u

lemma cardinal.monoid_pow_eq_cardinal_pow {κ : cardinal.{u}} {n : ℕ} : κ ^ n = (κ ^ (↑n : cardinal.{u})) :=
begin
  induction n with n ih,
    {simp},
    { rw[nat.cast_succ, cardinal.power_add, ← ih, cardinal.power_one, mul_comm], refl }
end

end cardinal_lemma

lemma abs_sqrt_nat {m : ℕ} : abs (real.sqrt (↑m + 1) : ℝ) = real.sqrt (↑m + 1) :=
  abs_of_pos $ real.sqrt_pos.mpr $ nat.cast_add_one_pos m

lemma finset.card_eq_sum_ones {α} (s : finset α) : s.card = (s.sum $ λ _, 1) :=
by simp

lemma fintype.card_eq_sum_ones {α} [fintype α] : fintype.card α = (fintype.elems α).sum (λ _, 1) :=
finset.card_eq_sum_ones _

lemma refold_coe {α β γ} [ring α] [add_comm_group γ] [add_comm_group β] [module α β] [module α γ] {f : β →ₗ[α] γ} : f.to_fun = ⇑f := rfl

lemma abs_triangle_sum {α : Type*} {s : finset α} {f : α → ℝ} : abs (s.sum f) ≤ (s.sum (λ x, abs (f x))) :=
(norm_triangle_sum _ _ : ∥ _ ∥ ≤ finset.sum s (λ x, ∥ f x∥))

lemma range_restrict {α : Type*} {β : Type*} (f : α → β) (p : α → Prop) : set.range (restrict f p) = f '' (p : set α) :=
by { ext x,  simp [restrict], refl }

example {α} (s : finset α) (H_sub : s ⊆ ∅) : s = ∅ := finset.subset_empty.mp ‹_›

-- TODO(jesse): remove later
-- lemma finset.sum_remove_zeros {α β : Type*} [add_comm_group β] {s : finset α} {f : α → β} (t : finset α) (H_sub : t ⊆ s) (Ht : ∀ x ∈ s, f x = 0 ↔ x ∈ (s \ t)) : s.sum f = t.sum f :=
-- (@finset.sum_subset _ _ t s f _ ‹_› (by finish)).symm

lemma finset.sum_factor_constant {α β : Type*} [field β] {s : finset α} (b : β) :
  (s.sum (λ x, b) = (s.sum (λ x, 1) * b)) := by rw [finset.sum_mul]; simp

