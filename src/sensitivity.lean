import tactic.fin_cases
import linear_algebra.finite_dimensional
import analysis.normed_space.basic
import for_mathlib

noncomputable theory

local attribute [instance, priority 1] classical.prop_decidable
local attribute [instance, priority 0] set.decidable_mem_of_fintype

open function

/-- The hypercube.-/
def Q (n) : Type := fin n → bool

instance : unique (Q 0) :=
⟨⟨λ _, tt⟩, by { intro, ext x, fin_cases x }⟩

namespace Q
variable (n : ℕ)

instance : fintype (Q n) := by delta Q; apply_instance

variable {n}

def xor (x y : Q n) : Q n :=
λ i, bxor (x i) (y i)

@[symm] lemma xor_comm (x y : Q n) : x.xor y = y.xor x :=
funext $ λ i, bool.bxor_comm _ _

/-- The distance between two vertices of the hypercube.-/
def dist (x y : Q n) : ℕ :=
(finset.univ : finset (fin n)).sum $ λ i, cond (x.xor y i) 1 0

@[simp] lemma dist_self (x : Q n) : x.dist x = 0 :=
finset.sum_eq_zero $ λ i hi, by simp only [xor, bxor_self, bool.cond_ff]

@[symm] lemma dist_symm (x y : Q n) : x.dist y = y.dist x :=
congr_arg ((finset.univ : finset (fin n)).sum) $
by { funext i, simp [xor_comm] }

/-- The adjacency relation on Q^n: two vertices of the hypercube are adjacent if their distance is 1.-/
def adjacent : Π {n : ℕ}, Q n → (set $ Q n)
| 0 p q := false
| (n+1) p q := (p 0 = q 0 ∧ adjacent (p ∘ fin.succ) (q ∘ fin.succ)) ∨ (p 0 ≠ q 0 ∧ p ∘ fin.succ = q ∘ fin.succ)

@[simp] lemma not_adjacent_zero (p q : Q 0) : p.adjacent q = false := rfl

lemma adjacent_succ_iff {p q : Q (n+1)} :
  p.adjacent q ↔ (p 0 = q 0 ∧ adjacent (p ∘ fin.succ) (q ∘ fin.succ)) ∨ (p 0 ≠ q 0 ∧ p ∘ fin.succ = q ∘ fin.succ) :=
by rw [adjacent]

lemma adjacent_iff_dist {x y : Q n} : x.adjacent y ↔ x.dist y = 1 :=
begin
  induction n with n ih,
  { rw [adjacent, false_iff],
    convert zero_ne_one, apply_instance },
  { have : (0 : fin (n+1)) ∈ (finset.univ : finset (fin (n+1))) := finset.mem_univ _,
    rw [adjacent_succ_iff, dist, ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _)],
    by_cases h : x 0 = y 0,
    { simp [h, xor, ih], apply iff.eq_cancel_right,
      apply finset.sum_bij (λ (p : fin n) hp, p.succ),
      { intros p hp, rw finset.mem_erase, exact ⟨fin.succ_ne_zero _, finset.mem_univ _⟩ },
      { intros p hp, refl },
      { intros p q hp hq hpq, apply fin.succ.inj hpq, },
      { intros p hp, rw finset.mem_erase at hp, exact ⟨p.pred hp.1, finset.mem_univ _, (fin.succ_pred _ hp.1).symm⟩ } },
    { simp only [h, xor, bxor_of_ne h, false_or, bxor, bool.cond_tt, ne.def, cond, false_and, true_and, bxor, not_false_iff],
      rw [funext_iff, add_comm 1, nat.succ_inj', finset.sum_eq_zero_iff_of_nonneg (λ p hp, nat.zero_le _)],
      { split; intros H p,
        { intros hp, rw finset.mem_erase at hp, dsimp only [function.comp] at H,
          rw [← fin.succ_pred _ hp.1, H (p.pred hp.1)], simp only [bxor_self, bool.cond_ff] },
        { specialize H p.succ, rw finset.mem_erase at H, specialize H ⟨fin.succ_ne_zero _, finset.mem_univ _⟩,
          simp only [function.comp_app], revert H,
          generalize ha : (x p.succ) = a, generalize hb : y p.succ = b, cases a; cases b; simp } },
      { apply_instance } } }
end

@[symm] lemma adjacent_comm {p q : Q n} : p.adjacent q ↔ q.adjacent p :=
by simp only [adjacent_iff_dist, dist_symm]

lemma adjacent.symm {p q : Q n} : p.adjacent q → q.adjacent p := adjacent_comm.1

variable (n)

/-- The (n+1)-dimensional hypercube is equivalent to two copies of the n-dimensional hypercube.-/
def equiv_sum : Q (n+1) ≃ Q n ⊕ Q n :=
{ to_fun := λ x, cond (x 0)
                   (sum.inl (x ∘ fin.succ))
                   (sum.inr (x ∘ fin.succ)),
  inv_fun := λ x, sum.rec_on x
                   (λ y i, if h : i = 0 then tt else y (i.pred h))
                   (λ y i, if h : i = 0 then ff else y (i.pred h)),
  left_inv := λ x,
  begin
    dsimp only, cases h : x 0;
    { funext i, dsimp only [bool.cond_tt, bool.cond_ff],
      split_ifs with H,
      { rw [H, h] },
      { rw [function.comp_app, fin.succ_pred] } }
  end,
  right_inv := by rintro ⟨⟩; { funext, simp [function.comp, fin.pred_succ, fin.succ_ne_zero] } }

lemma equiv_sum_apply (x : Q (n+1)) :
  equiv_sum n x = cond (x 0) (sum.inl (x ∘ fin.succ)) (sum.inr (x ∘ fin.succ)) := rfl

end Q

/-- The free vector space on vertices of a hypercube, defined inductively. -/
def V : ℕ → Type
| 0 := ℝ
| (n+1) := V n × V n

noncomputable instance : Π n, add_comm_group (V n) :=
begin
  apply nat.rec,
  { dunfold V, apply_instance },
  { introsI n IH, dunfold V, apply_instance }
end

noncomputable instance : Π n, vector_space ℝ (V n) :=
begin
  apply nat.rec,
  { dunfold V, apply_instance },
  { introsI n IH, dunfold V, apply_instance }
end

-- These type class short circuts shave ~56% off the compile time
def V.module {n} : module ℝ (V n) := by apply_instance
def V.add_comm_semigroup {n} : add_comm_semigroup (V n) := by apply_instance
def V.add_comm_monoid {n} : add_comm_monoid (V n) := by apply_instance
def V.has_scalar {n} : has_scalar ℝ (V n) := by apply_instance
def V.has_add {n} : has_add (V n) := by apply_instance

local attribute [instance, priority 100000]
  V.module V.add_comm_semigroup V.add_comm_monoid V.has_scalar V.has_add

lemma dim_V {n : ℕ} : vector_space.dim ℝ (V n) = 2^n :=
begin
  induction n with n IH,
  { apply dim_of_field },
  { dunfold V,
    rw [dim_prod, IH, pow_succ, two_mul] }
end

open finite_dimensional

instance {n} : finite_dimensional ℝ (V n) :=
begin
  rw [finite_dimensional_iff_dim_lt_omega, dim_V],
  convert cardinal.nat_lt_omega (2^n),
  norm_cast
end

lemma findim_V {n} : findim ℝ (V n) = 2^n :=
begin
  have := findim_eq_dim ℝ (V n),
  rw dim_V at this,
  rw [← cardinal.nat_cast_inj, this],
  simp [cardinal.monoid_pow_eq_cardinal_pow]
end

/-- The basis of V indexed by the hypercube.-/
noncomputable def e : Π {n}, Q n → V n
| 0     := λ _, (1:ℝ)
| (n+1) := λ x, cond (x 0) (e (x ∘ fin.succ), 0) (0, e (x ∘ fin.succ))

@[simp] lemma e_zero_apply (x : Q 0) : e x = (1 : ℝ) := rfl

lemma e_succ_apply {n} (x : Q (n+1)) :
  e x = cond (x 0) (e (x ∘ fin.succ), 0) (0, e (x ∘ fin.succ)) :=
by rw e

lemma e.is_basis (n) : is_basis ℝ (e : Q n → V n) :=
begin
  induction n with n ih,
  { apply is_basis_singleton_one ℝ,
    apply_instance },
  convert (is_basis_inl_union_inr ih ih).comp (Q.equiv_sum n) (Q.equiv_sum n).bijective,
  funext x,
  rw [e_succ_apply, function.comp_apply, Q.equiv_sum_apply],
  cases h : x 0;
  { simp only [bool.cond_tt, bool.cond_ff, prod.mk.inj_iff, sum.elim_inl, sum.elim_inr, cond,
      linear_map.inl_apply, linear_map.inr_apply, function.comp_apply, and_true],
    exact ⟨rfl, rfl⟩ }
end

/-- The linear operator f_n corresponding to Huang's matrix A_n. -/
noncomputable def f : Π n, V n →ₗ[ℝ] V n
| 0 := 0
| (n+1) :=
  linear_map.pair
    (linear_map.copair (f n) linear_map.id)
    (linear_map.copair linear_map.id (-f n))

@[simp] lemma f_zero : f 0 = 0 := rfl

lemma f_succ_apply : ∀ {n : ℕ} v, (f (n+1) : _) v = (f n v.1 + v.2, v.1 - f n v.2)
| n ⟨v, v'⟩ :=
begin
  rw f,
  simp only [linear_map.id_apply, linear_map.pair_apply, prod.mk.inj_iff,
    linear_map.neg_apply, sub_eq_add_neg, linear_map.copair_apply],
  exact ⟨rfl, rfl⟩
end

lemma f_squared : ∀ {n : ℕ} v, (f n) (f n v) = (n : ℝ) • v
-- The (n : ℝ) is necessary since `n • v` refers to the multiplication defined
-- using only the addition of V.
| 0 v := by { simp only [nat.cast_zero, zero_smul], refl }
| (n+1) ⟨v, v'⟩ := by simp [f_succ_apply, f_squared, add_smul]

/-- The dual basis to e -/
noncomputable def ε : Π {n : ℕ} (p : Q n), V n →ₗ[ℝ] ℝ
| 0 _ := linear_map.id
| (n+1) p := cond (p 0) ((ε $ p ∘ fin.succ).comp $ linear_map.fst _ _ _) ((ε $ p ∘ fin.succ).comp $ linear_map.snd _ _ _)

open bool

lemma Q_succ_n_eq {n} (p q : Q (n+1)) : p = q ↔ (p 0 = q 0 ∧ p ∘ fin.succ = q ∘ fin.succ) :=
begin
  split,
  { intro h, rw h, exact ⟨rfl, rfl⟩, },
  { rintros ⟨h₀, h⟩,
    ext x,
    by_cases hx : x = 0,
    { rwa hx },
    { rw ← fin.succ_pred x hx,
      convert congr_fun h (fin.pred x hx) } }
end

lemma duality {n : ℕ} (p q : Q n) : ε p (e q) = if p = q then 1 else 0 :=
begin
  induction n with n IH,
  { rw (show p = q, from subsingleton.elim p q),
    dsimp [ε, e],
    simp },
  { dsimp [ε, e],
    cases hp : p 0 ; cases hq : q 0,
    all_goals {
      repeat {rw cond_tt},
      repeat {rw cond_ff},
      simp only [cond_tt, cond_ff, linear_map.fst_apply, linear_map.snd_apply, linear_map.comp_apply, IH],
      try { congr'  1, rw Q_succ_n_eq, finish },
      try {
        erw (ε _).map_zero,
        have : p ≠ q, { intro h, rw Q_succ_n_eq p q at h, finish },
        simp [this] } } }
end

lemma f_matrix {n} : ∀ (p q : Q n), abs (ε q (f n (e p))) = if q.adjacent p then 1 else 0 :=
begin
  induction n with n IH,
  { intros p q,
    dsimp [f],
    simp [Q.not_adjacent_zero] },
  { intros p q,
    have ite_nonneg : ite (q ∘ fin.succ = p ∘ fin.succ) (1 : ℝ) 0 ≥ 0,
    { split_ifs ; norm_num },
    have f_map_zero := (show linear_map ℝ (V (n+0)) (V n), from f n).map_zero,
    cases hp : p 0 ; cases hq : q 0,
    all_goals
    { dsimp [e, ε, f],
      rw [hp, hq],
      repeat {rw cond_tt},
      repeat {rw cond_ff},
      simp [Q.adjacent_succ_iff, hp, hq, IH, duality, f_map_zero, abs_of_nonneg ite_nonneg],
      congr } }
end

/-- The linear operator g_n corresponding to Knuth's matrix B_n.
  We adopt the convention n = m+1. -/
noncomputable def g (m : ℕ) : V m →ₗ[ℝ] V (m+1) :=
linear_map.pair (f m + real.sqrt (m+1) • linear_map.id) linear_map.id

lemma g_apply : ∀ {m : ℕ} v, g m v = (f m v + real.sqrt (m+1) • v, v)
| m v := by delta g; simp

lemma g_injective {m : ℕ} : function.injective (g m) :=
begin
  rw g,
  intros x₁ x₂ h,
  simp only [linear_map.pair_apply, linear_map.id_apply, prod.mk.inj_iff] at h,
  exact h.right
end

-- I don't understand why the type ascription is necessary here, when f_squared worked fine
lemma f_image_g {m : ℕ} (w : V (m + 1)) (hv : ∃ v, g m v = w) :
  (f (m + 1) : _) w = real.sqrt (m + 1) • w :=
begin
  rcases hv with ⟨v, rfl⟩,
  have : real.sqrt (m+1) * real.sqrt (m+1) = m+1 :=
    real.mul_self_sqrt (by exact_mod_cast zero_le _),
  simp [-add_comm, this, f_succ_apply, g_apply, f_squared, smul_add, add_smul, smul_smul],
end

lemma injective_e {n} : injective (@e n) :=
linear_independent.injective (by norm_num) (e.is_basis n).1

variables {m : ℕ} (H : set (Q (m + 1))) (hH : fintype.card H ≥ 2^m + 1)
include hH

local notation `d` := vector_space.dim ℝ
local notation `fd` := findim ℝ

attribute [elim_cast] cardinal.nat_cast_inj
attribute [elim_cast] cardinal.nat_cast_lt
attribute [elim_cast] cardinal.nat_cast_le

lemma exists_eigenvalue :
  ∃ y ∈ submodule.span ℝ (e '' H) ⊓ (g m).range, y ≠ (0 : _) :=
begin
  let W := submodule.span ℝ (e '' H),
  let img := (g m).range,
  suffices : 0 < d ↥(W ⊓ img),
  { simp only [exists_prop],
    apply exists_mem_ne_zero_of_dim_pos,
    exact_mod_cast this },
  have dim_le : d ↥(W ⊔ img) ≤ 2 ^ (m + 1),
  { convert ← dim_submodule_le (W ⊔ img),
    apply dim_V },
  have dim_add : d ↥(W ⊔ img) + d ↥(W ⊓ img) = d ↥W + 2^m,
  { convert ← dim_sup_add_dim_inf_eq W img,
    rw ← dim_eq_injective (g m) g_injective,
    apply dim_V },
  have dimW : d ↥W = fintype.card ↥H,
  { have li : linear_independent ℝ (restrict e H) :=
      linear_independent.comp (e.is_basis _).1 _ subtype.val_injective,
    have hdW := dim_span li,
    rw range_restrict at hdW,
    convert hdW,
    rw [cardinal.mk_image_eq injective_e, cardinal.fintype_card] },
  rw ← findim_eq_dim ℝ at ⊢ dim_le dim_add dimW,
  rw [← findim_eq_dim ℝ, ← findim_eq_dim ℝ] at dim_add,
  norm_cast at ⊢ dim_le dim_add dimW,
  rw nat.pow_succ at dim_le,
  linarith
end

theorem degree_theorem :
  ∃ q, q ∈ H ∧ real.sqrt (m + 1) ≤ (H ∩ q.adjacent).to_finset.card :=
begin
  rcases exists_eigenvalue H ‹_› with ⟨y, ⟨⟨H_mem', H_mem''⟩, H_nonzero⟩⟩,
  rcases (finsupp.mem_span_iff_total _).mp H_mem' with ⟨l, H_l₁, H_l₂⟩,

  have hl : ∀ (q : Q (m+1)), l q = (ε q : _) y,
  { intro q, rw ← H_l₂, rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum, finset.sum_eq_single q],
    { rw [linear_map.map_smul, duality, if_pos rfl, smul_eq_mul, mul_one] },
    { intros p hp hne, rw [linear_map.map_smul, duality, if_neg hne.symm, smul_zero] },
    { rw finsupp.not_mem_support_iff, intro h, rw [h, zero_smul, (ε q).map_zero] } },

  have hHe : H ≠ ∅ , { contrapose! hH, rw [hH, set.empty_card'], exact nat.zero_lt_succ _ },

  obtain ⟨q, H_mem_H, H_max⟩ : ∃ q, q ∈ H ∧ ∀ q', q' ∈ H → abs (l q') ≤ abs (l q),
  { cases set.exists_mem_of_ne_empty hHe with r hr,
    cases @finset.max_of_mem _ _ (H.to_finset.image (λ q', abs (l q')))
      (abs (l r)) (finset.mem_image_of_mem _ (set.mem_to_finset.2 hr)) with x hx,
    rcases finset.mem_image.1 (finset.mem_of_max hx) with ⟨q, hq, rfl⟩,
    refine ⟨q, set.mem_to_finset.1 hq,
      λ q' hq', (finset.le_max_of_mem (finset.mem_image_of_mem _ (set.mem_to_finset.2 hq')) hx : _)⟩ },

  have H_q_pos : 0 < abs (l q),
  { rw [abs_pos_iff], contrapose! H_nonzero,
    suffices : l = 0,
    { simp [this] at H_l₂, exact H_l₂.symm },
    ext q', by_cases hq' : q' ∈ H,
    { simpa [H_nonzero] using H_max _ hq' },
    { rw finsupp.mem_supported' at H_l₁, exact H_l₁ _ hq' } },

  refine ⟨q, ‹_›, _⟩,

  suffices : real.sqrt (↑m + 1) * abs (l q) ≤ ↑(_) * abs (l q),
  { exact (mul_le_mul_right H_q_pos).mp ‹_› },

  calc
    real.sqrt (↑m + 1) * (abs (l q))
        = abs (real.sqrt (↑m + 1) * l q) : by rw [abs_mul, abs_sqrt_nat]
    ... = abs (ε q (real.sqrt (↑m + 1) • y)) : by rw [hl, linear_map.map_smul, smul_eq_mul]
    ... ≤ l.support.sum (λ x : Q (m + 1), abs (l x) * abs ((ε q) ((f (m + 1) : _) (e x)))) :
        begin
          rw [← f_image_g y (by simpa using H_mem''), ← H_l₂, finsupp.total_apply,
            finsupp.sum, linear_map.map_sum, linear_map.map_sum],
          refine le_trans abs_triangle_sum _,
          conv_lhs { congr, skip, simp [abs_mul] }
        end
    ... = finset.sum (l.support ∩ set.to_finset H ∩ set.to_finset (Q.adjacent q))
            (λ (x : Q (m + 1)), abs (l x) * abs ((ε q) ((f (m + 1) : _) (e x)))) :
        begin
          rw [← finset.sum_subset],
          { rw finset.inter_assoc, exact finset.inter_subset_left _ _ },
          { intros x H_mem H_not_mem,
            by_cases x ∈ H,
              { simp at H_mem H_not_mem,
                erw [f_matrix, if_neg (H_not_mem ‹_› ‹_›), mul_zero] },
              { suffices : (l x) = 0, {simp [this]},
                rw [finsupp.mem_supported'] at H_l₁, exact H_l₁ _ ‹_› } }
        end
    ... ≤ ↑(l.support ∩ H.to_finset ∩ q.adjacent.to_finset).card * abs (l q) :
        begin
          refine le_trans (finset.sum_le_sum _) _,
          { exact λ p, abs (l q) },
          { intros x Hx, simp at Hx, erw [f_matrix, if_pos Hx.2.2, mul_one], exact H_max x Hx.2.1 },
          { simp only [mul_one, finset.sum_const, add_monoid.smul_one, add_monoid.smul_eq_mul] }
        end
    ... ≤ ↑(H ∩ Q.adjacent q).to_finset.card * abs (l q) :
        begin
          refine (mul_le_mul_right ‹_›).mpr _, norm_cast,
          refine finset.card_le_of_subset (finset.coe_subset.mp _),
          simpa only [finset.coe_inter, finset.coe_to_finset', set.inter_assoc]
            using set.inter_subset_right _ _
        end
end