import tactic.fin_cases
import linear_algebra.finite_dimensional
import analysis.normed_space.basic

noncomputable theory

open function

attribute [elim_cast] cardinal.nat_cast_inj
attribute [elim_cast] cardinal.nat_cast_lt
attribute [elim_cast] cardinal.nat_cast_le

lemma ne.symm_iff {α} {a b : α} : a ≠ b ↔ b ≠ a := ⟨ne.symm, ne.symm⟩

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
  { simp },
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

def equiv_unique (α : Type*) (β : Type*) [unique α] [discrete_field β] :
  (α →₀ β) ≃ₗ[β] β :=
{ to_fun := λ f, f (default α),
  inv_fun := finsupp.single (default α),
  add := λ f g, finsupp.add_apply,
  smul := λ b f, rfl,
  left_inv := λ f, (finsupp.unique_single _).symm,
  right_inv := λ b, finsupp.single_eq_same }

lemma linear_map.map_finsupp_total {R : Type*} {β : Type*} {γ : Type*} [ring R] [decidable_eq R] 
  [add_comm_group β] [decidable_eq β] [module R β]
  [add_comm_group γ] [decidable_eq γ] [module R γ] 
  (f : β →ₗ[R] γ) 
  {ι : Type*} [fintype ι] [decidable_eq ι] 
  {g : ι → β} (l : ι →₀ R) : f (finsupp.total ι β R g l) = finsupp.total ι γ R (f ∘ g) l :=
begin
  rw [finsupp.total_apply,
     finsupp.total_apply, finsupp.sum, finsupp.sum, f.map_sum],
  congr,
  ext i,
  exact f.map_smul _ _,
end

lemma finset.sum_ite {α : Type*} [decidable_eq α] {β : Type*} [semiring β] (s : finset α) (P : set α) [decidable_pred P] [fintype ↥P] (f : α → β) : 
  s.sum (λ a, (f a) * (if P a then 1 else 0)) = (s ∩ P.to_finset).sum f :=
begin
  have : s ∩ P.to_finset ⊆ s,
  { exact finset.filter_subset _ },
  rw ← finset.sum_subset this,
  { apply finset.sum_congr rfl,
    intros x x_in,
    cases finset.mem_inter.mp x_in with _ x_in,
    replace x_in : P x := set.mem_to_finset.mp x_in,
    simp [x_in] },
  { intros x x_in x_not_in,
    suffices : ¬ P x, by simp [this],
    intros hPx,
    apply x_not_in,
    rw finset.mem_inter,
    exact ⟨x_in, set.mem_to_finset.mpr hPx⟩ },
end


section

local attribute [instance, priority 1] classical.prop_decidable
local attribute [instance, priority 0] set.decidable_mem_of_fintype

lemma finset.inter_to_finset {α : Type*} [fintype α] (s t : set α) [decidable_eq α] :
  (s ∩ t).to_finset =  s.to_finset ∩ t.to_finset :=
by { ext x, simp }

end

lemma finset.inter_subset_inter {α : Type*} [decidable_eq α] {x y s t : finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t :=
begin
  intros a a_in,
  rw finset.mem_inter at a_in ⊢,
  exact ⟨h a_in.1, h' a_in.2⟩
end

lemma finset.inter_subset_inter_left {α : Type*} [decidable_eq α] {x y s : finset α} (h : x ⊆ y) : x ∩ s ⊆ y ∩ s :=
finset.inter_subset_inter h (finset.subset.refl _)

lemma finset.inter_subset_inter_right {α : Type*} [decidable_eq α] {x y s : finset α} (h : x ⊆ y) : s ∩ x ⊆ s ∩ y :=
finset.inter_subset_inter (finset.subset.refl _) h

lemma module.smul_eq_smul {R : Type*} [ring R] {β : Type*} [add_comm_group β] [module R β] (n : ℕ) (b : β) :
    n • b = (n : R) • b :=
begin
  induction n with n ih,
  { rw [nat.cast_zero, zero_smul, zero_smul] },
  { change (n + 1) • b = (n + 1 : R) • b,
    rw [add_smul, add_smul, one_smul, ih, one_smul] }
end

lemma finset.sum_const' {α : Type*} {R : Type*} [ring R] {β : Type*} [add_comm_group β] [module R β] {s : finset α} (b : β) :
    finset.sum s (λ (a : α), b) = (finset.card s : R) • b :=
begin
  rw [finset.sum_const, ← module.smul_eq_smul], refl,
end

lemma fintype.exists_max {α : Type*} [fintype α] [nonempty α] {β : Type*} [decidable_linear_order β] (f : α → β) :
  ∃ x₀ : α, ∀ x, f x ≤ f x₀ := 
begin
  let r := (set.range f).to_finset,
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (set.range f).to_finset,
  { haveI := classical.inhabited_of_nonempty ‹nonempty α›,
    exact ⟨f (default α), set.mem_to_finset.mpr $ set.mem_range_self _⟩ },
  rcases finset.max_of_mem hy with ⟨y₀, h⟩,
  rcases set.mem_to_finset.1 (finset.mem_of_max h) with ⟨x₀, rfl⟩,
  use x₀,
  intro x,
  apply finset.le_max_of_mem (set.mem_to_finset.mpr $ set.mem_range_self x) h
end