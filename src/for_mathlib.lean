import tactic.fin_cases
import tactic.apply_fun
import linear_algebra.finite_dimensional
import analysis.normed_space.basic
import linear_algebra.dual
noncomputable theory

open function

section duality
open vector_space module module.dual linear_map function

local attribute [instance, priority 1] classical.prop_decidable
local attribute [instance, priority 0] set.decidable_mem_of_fintype

universes u v w
variables {K : Type u} {V : Type v} {ι : Type w} [decidable_eq ι]
variables [discrete_field K] [add_comm_group V] [vector_space K V]
          [decidable_eq V] [decidable_eq (ι → V)] [decidable_eq $ dual K V]


local notation `V'` := dual K V

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
structure dual_pair (e : ι → V) (ε : ι → V') :=
(eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0)
(total : ∀ {v : V}, (∀ i, ε i v = 0) → v = 0)
[finite : ∀ v : V, fintype {i | ε i v ≠ 0}]

variables {e : ι → V} {ε : ι → dual K V} (h : dual_pair e ε)

include  h
/-- The coefficients of `v` on the basis `e` -/
def dual_pair.coeffs (v : V) : ι →₀ K :=
{ to_fun := λ i, ε i v,
  support := by { haveI := h.finite v, exact {i : ι | ε i v ≠ 0}.to_finset },
  mem_support_to_fun := by {intro i, rw set.mem_to_finset, exact iff.rfl } }

omit h

@[simp]
lemma dual_pair.coeffs_apply (v : V) (i : ι) : h.coeffs v i = ε i v := rfl

def help_tcs : has_scalar K V := mul_action.to_has_scalar _ _

local attribute [instance] help_tcs

/-- linear combinations of elements of `e` -/
def dual_pair.lc (e : ι → V) (l : ι →₀ K) : V := l.sum (λ (i : ι) (a : K), a • (e i))

include h

lemma dual_pair.dual_lc (l : ι →₀ K) (i : ι) : ε i (dual_pair.lc e l) = l i :=
begin
  erw linear_map.map_sum,
  simp only [h.eval, map_smul, smul_eq_mul],
  rw finset.sum_eq_single i,
  { simp },
  { intros q q_in q_ne,
    simp [q_ne.symm] },
  { intro p_not_in,
    simp [finsupp.not_mem_support_iff.1 p_not_in] },
end

@[simp]
lemma dual_pair.coeffs_lc (l : ι →₀ K) : h.coeffs (dual_pair.lc e l) = l :=
by { ext i, rw [h.coeffs_apply, h.dual_lc] }

/-- For any v : V n, \sum_{p ∈ Q n} (ε p v) • e p = v -/
lemma dual_pair.decomposition (v : V) : dual_pair.lc e (h.coeffs v) = v :=
begin
  refine eq_of_sub_eq_zero (h.total _),
  intros i,
  simp [-sub_eq_add_neg, linear_map.map_sub, h.dual_lc, sub_eq_zero_iff_eq]
end

lemma dual_pair.mem_of_mem_span {H : set ι} {x : V} (hmem : x ∈ submodule.span K (e '' H)) :
  ∀ i : ι, ε i x ≠ 0 →  i ∈ H :=
begin
  intros i hi,
  rcases (finsupp.mem_span_iff_total _).mp hmem with ⟨l, supp_l, sum_l⟩,
  change dual_pair.lc e l = x at sum_l,
  rw finsupp.mem_supported' at supp_l,
  by_contradiction i_not,
  apply hi,
  rw ← sum_l,
  simpa [h.dual_lc] using supp_l i i_not,
end

lemma dual_pair.is_basis : is_basis K e :=
begin
  split,
  { rw linear_independent_iff,
    intros l H,
    change dual_pair.lc e l = 0 at H,
    ext i,
    apply_fun ε i at H,
    simpa [h.dual_lc] using H },
  { rw submodule.eq_top_iff',
    intro v,
    rw [← set.image_univ, finsupp.mem_span_iff_total],
    exact ⟨h.coeffs v, by simp, h.decomposition v⟩ },
end
omit h


lemma dual_pair.eq_dual  : ε = is_basis.dual_basis h.is_basis :=
begin
  funext i,
  refine h.is_basis.ext _,
  intro j,
  erw [is_basis.to_dual_apply, h.eval]
end

end duality

-- PRed
attribute [elim_cast] cardinal.nat_cast_inj
attribute [elim_cast] cardinal.nat_cast_lt
attribute [elim_cast] cardinal.nat_cast_le

-- PRed
lemma ne.symm_iff {α} {a b : α} : a ≠ b ↔ b ≠ a := ⟨ne.symm, ne.symm⟩

-- not needed
/- instance : directed_order ℝ :=
{ directed := λ i j, ⟨max i j, le_max_left _ _, le_max_right _ _⟩,
  ..real.linear_order } -/

-- PRed
lemma fin.succ_ne_zero {n} : ∀ k : fin n, fin.succ k ≠ 0
| ⟨k, hk⟩ heq := nat.succ_ne_zero k $ (fin.ext_iff _ _).1 heq

-- PRed
lemma bxor_of_ne {x y : bool} (h : x ≠ y) : bxor x y = tt :=
by cases x; cases y; refl <|> contradiction

section cardinal_lemma
universe u

-- PRed
lemma cardinal.monoid_pow_eq_cardinal_pow {κ : cardinal.{u}} {n : ℕ} : κ ^ n = (κ ^ (↑n : cardinal.{u})) :=
begin
  induction n with n ih,
  { simp },
  { rw[nat.cast_succ, cardinal.power_add, ← ih, cardinal.power_one, mul_comm], refl }
end

end cardinal_lemma

-- PRed
lemma range_restrict {α : Type*} {β : Type*} (f : α → β) (p : α → Prop) :
  set.range (restrict f p) = f '' (p : set α) :=
by { ext x,  simp [restrict], refl }

example {α} (s : finset α) (H_sub : s ⊆ ∅) : s = ∅ := finset.subset_empty.mp ‹_›

-- unused. not sure if or where this belongs in mathlib
/- def equiv_unique (α : Type*) (β : Type*) [unique α] [discrete_field β] :
  (α →₀ β) ≃ₗ[β] β :=
{ to_fun := λ f, f (default α),
  inv_fun := finsupp.single (default α),
  add := λ f g, finsupp.add_apply,
  smul := λ b f, rfl,
  left_inv := λ f, (finsupp.unique_single _).symm,
  right_inv := λ b, finsupp.single_eq_same } -/

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

lemma finset.sum_ite {α : Type*} [decidable_eq α] {β : Type*} [semiring β] (s : finset α)
  (P : set α) [decidable_pred P] [fintype ↥P] (f : α → β) :
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

-- type class problems adding this to mathlib at data/set/finite
lemma finset.to_finset_inter {α : Type*} [fintype α] (s t : set α) [decidable_eq α] :
  (s ∩ t).to_finset = s.to_finset ∩ t.to_finset :=
by { ext x, simp }

end

-- PRed
lemma finset.inter_subset_inter {α : Type*} [decidable_eq α] {x y s t : finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t :=
begin
  intros a a_in,
  rw finset.mem_inter at a_in ⊢,
  exact ⟨h a_in.1, h' a_in.2⟩
end

-- PRed
lemma finset.inter_subset_inter_left {α : Type*} [decidable_eq α] {x y s : finset α} (h : x ⊆ y) : x ∩ s ⊆ y ∩ s :=
finset.inter_subset_inter h (finset.subset.refl _)

-- PRed
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