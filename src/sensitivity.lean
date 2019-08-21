import tactic.fin_cases
import tactic.apply_fun
import linear_algebra.finite_dimensional
import analysis.normed_space.basic
import for_mathlib

noncomputable theory

local attribute [instance, priority 1] classical.prop_decidable
local attribute [instance, priority 0] set.decidable_mem_of_fintype


open function bool linear_map

/-- The hypercube.-/
def Q (n) : Type := fin n → bool

instance : unique (Q 0) :=
⟨⟨λ _, tt⟩, by { intro, ext x, fin_cases x }⟩

namespace Q
variable (n : ℕ)

instance : fintype (Q n) := by delta Q; apply_instance

lemma card : fintype.card (Q n) = 2^n :=
by simp [Q]

instance : inhabited (Q n) := ⟨λ i, tt⟩

instance coeffs_module (n) : module ℝ (Q n →₀ ℝ) := finsupp.module (Q n) ℝ

variable {n}

lemma succ_n_eq (p q : Q (n+1)) : p = q ↔ (p 0 = q 0 ∧ p ∘ fin.succ = q ∘ fin.succ) :=
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

def adjacent {n : ℕ} (p : Q n) : set (Q n) := λ q, ∃! i, p i ≠ q i

lemma not_adjacent_zero (p q : Q 0) : ¬ p.adjacent q :=
by rintros ⟨v, _⟩; apply fin_zero_elim v

lemma adj_succ_of_zero_neq {p q : Q (n+1)} (h0 : p 0 ≠ q 0) :
  p.adjacent q ↔ p ∘ fin.succ = q ∘ fin.succ :=
begin
  split,
  { rintros ⟨i, h_eq, h_uni⟩,
    ext x, by_contradiction hx,
    apply fin.succ_ne_zero x,
    rw [h_uni _ hx, h_uni _ h0] },
    { intro heq,
    use [0, h0],
    intros y hy,
    contrapose! hy,
    rw ←fin.succ_pred _ hy,
    apply congr_fun heq }
end

lemma adj_succ_of_zero_eq {p q : Q (n+1)} (h0 : p 0 = q 0) :
  p.adjacent q ↔ Q.adjacent (p ∘ fin.succ) (q ∘ fin.succ) :=
begin
  split,
  { rintros ⟨i, h_eq, h_uni⟩,
    have h_i : i ≠ 0, from λ h_i, absurd h0 (by rwa h_i at h_eq),
    use [i.pred h_i,
         show p (fin.succ (fin.pred i _)) ≠ q (fin.succ (fin.pred i _)), by rwa [fin.succ_pred]],
    intros y hy, simp [eq.symm (h_uni _ hy)] },
  { rintros ⟨i, h_eq, h_uni⟩,
    use [i.succ, h_eq],
    intros y hy,
    rw [←fin.pred_inj, fin.pred_succ],
    { apply h_uni, change p (fin.pred _ _).succ ≠ q (fin.pred _ _).succ, simp [hy] },
    { contrapose! hy, rw [hy, h0] },
    { apply fin.succ_ne_zero } }
end

@[symm] lemma adjacent.symm {p q : Q n} : p.adjacent q ↔ q.adjacent p :=
by simp only [adjacent, ne.symm_iff]

end Q

/-- The free vector space on vertices of a hypercube, defined inductively. -/
def V : ℕ → Type
| 0 := ℝ
| (n+1) := V n × V n

instance (n) : decidable_eq (V n) := by {induction n; dunfold V; resetI; apply_instance }

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

/-- The basis of V indexed by the hypercube.-/
noncomputable def e : Π {n}, Q n → V n
| 0     := λ _, (1:ℝ)
| (n+1) := λ x, cond (x 0) (e (x ∘ fin.succ), 0) (0, e (x ∘ fin.succ))

@[simp] lemma e_zero_apply (x : Q 0) : e x = (1 : ℝ) := rfl

/-- The dual basis to e -/
noncomputable def ε : Π {n : ℕ} (p : Q n), V n →ₗ[ℝ] ℝ
| 0 _ := linear_map.id
| (n+1) p := cond (p 0) ((ε $ p ∘ fin.succ).comp $ linear_map.fst _ _ _) ((ε $ p ∘ fin.succ).comp $ linear_map.snd _ _ _)

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
      simp only [linear_map.fst_apply, linear_map.snd_apply, linear_map.comp_apply, IH],
      try { congr' 1, rw Q.succ_n_eq, finish },
      try {
        erw (ε _).map_zero,
        have : p ≠ q, { intro h, rw p.succ_n_eq q at h, finish },
        simp [this] } } }
end

lemma epsilon_total {n : ℕ} {v : V n} (h : ∀ p : Q n, (ε p) v = 0) : v = 0 :=
begin
  induction n with n ih,
  { dsimp [ε] at h, exact h (λ _, tt) },
  { cases v with v₁ v₂,
    ext ; change _ = (0 : V n) ; simp only [] ; apply ih ; intro p ;
    [ let q : Q (n+1) := λ i, if h : i = 0 then tt else p (i.pred h),
      let q : Q (n+1) := λ i, if h : i = 0 then ff else p (i.pred h)],
    all_goals {
      specialize h q,
      rw [ε, show q 0 = tt, from rfl, cond_tt] at h <|> rw [ε, show q 0 = ff, from rfl, cond_ff] at h,
      rwa show p = q ∘ fin.succ, by { ext, simp [q, fin.succ_ne_zero] } } }
end

def dual_pair_e_ε (n) : dual_pair (@e n) (@ε n) :=
{ eval := duality,
  total := @epsilon_total _ }

lemma dim_V' {n : ℕ} : vector_space.dim ℝ (V n) = ↑(2^n : ℕ) :=
by convert dim_eq_card (dual_pair_e_ε _).is_basis using 1; rw Q.card 

lemma dim_V {n : ℕ} : vector_space.dim ℝ (V n) = 2^n :=
by simpa [cardinal.monoid_pow_eq_cardinal_pow] using @dim_V' n

open finite_dimensional

instance {n} : finite_dimensional ℝ (V n) :=
fin_dim_of_finite_basis (dual_pair_e_ε _).is_basis

lemma findim_V {n} : findim ℝ (V n) = 2^n :=
have _ := @dim_V' n,
by rwa [←findim_eq_dim, cardinal.nat_cast_inj] at this

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
    dsimp [e, ε, f], cases hp : p 0 ; cases hq : q 0,
    all_goals
    { repeat {rw cond_tt}, repeat {rw cond_ff},
      simp [f_map_zero, hp, hq, IH, duality, abs_of_nonneg ite_nonneg, Q.adj_succ_of_zero_neq,
            Q.adj_succ_of_zero_eq],
      congr' 1 } }
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

variables {m : ℕ} (H : set (Q (m + 1))) (hH : fintype.card H ≥ 2^m + 1)
include hH

local notation `d` := vector_space.dim ℝ
local notation `fd` := findim ℝ

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
      linear_independent.comp (dual_pair_e_ε _).is_basis.1 _ subtype.val_injective,
    have hdW := dim_span li,
    rw range_restrict at hdW,
    convert hdW,
    rw [cardinal.mk_image_eq ((dual_pair_e_ε _).is_basis.injective zero_ne_one), cardinal.fintype_card] },
  rw ← findim_eq_dim ℝ at ⊢ dim_le dim_add dimW,
  rw [← findim_eq_dim ℝ, ← findim_eq_dim ℝ] at dim_add,
  norm_cast at ⊢ dim_le dim_add dimW,
  rw nat.pow_succ at dim_le,
  linarith
end

open dual_pair

lemma calc_lemma {m : ℕ} (H : set (Q (m + 1))) (hH : fintype.card ↥H ≥ 2 ^ m + 1)
  (y : V (m + 1)) (y_mem_g : y ∈ (range (g m)))
  (coeffs_support : (dual_pair.coeffs (dual_pair_e_ε (m + 1)) y).support ⊆ set.to_finset H)
  (q : Q (m + 1)) (H_max : ∀ (q' : Q (m + 1)), abs ((ε q').to_fun y) ≤ abs ((ε q) y))
  (H_q_pos : 0 < abs ((ε q) y)) :
  real.sqrt (↑m + 1) * abs ((ε q) y) ≤ ↑(finset.card (set.to_finset (H ∩ Q.adjacent q))) * abs ((ε q) y) :=
let coeffs := (dual_pair_e_ε (m+1)).coeffs,
    φ : V (m+1) → V (m+1) := f (m+1) in
begin
  set s := real.sqrt (↑m + 1),
  calc
    s * (abs (ε q y))
        = abs (ε q (s • y)) : by rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (real.sqrt_nonneg _)]
    ... = abs (ε q (φ y)) : by rw [← f_image_g y (by simpa using y_mem_g)]
    ... = abs (ε q (φ (lc _ (coeffs y)))) : by rw (dual_pair_e_ε _).decomposition y
    ... = abs ((coeffs y).sum (λ (i : Q (m + 1)) (a : ℝ), a • ((ε q) ∘ (f (m + 1)) ∘ λ (i : Q (m + 1)), e i) i)): by
                  { dsimp only [φ],
                    erw [(f $ m+1).map_finsupp_total, (ε q).map_finsupp_total, finsupp.total_apply] ; apply_instance }
    ... ≤ (coeffs y).support.sum (λ p,
           abs ((coeffs y p) * (ε q $ φ $ e p))) : norm_triangle_sum _ $ λ p, coeffs y p * _
    ... = (coeffs y).support.sum (λ p, abs (coeffs y p) * ite (q.adjacent p) 1 0) : by simp only [abs_mul, f_matrix]
    ... = ((coeffs y).support ∩ (Q.adjacent q).to_finset).sum (λ p, abs (coeffs y p)) : finset.sum_ite _ _ _
    ... ≤ ((coeffs y).support ∩ (Q.adjacent q).to_finset).sum (λ p, abs (coeffs y q)) : finset.sum_le_sum (λ p _, H_max p)
    ... = (finset.card ((coeffs y).support ∩ (Q.adjacent q).to_finset): ℝ) * abs (coeffs y q) : by rw [← smul_eq_mul, ← finset.sum_const']
    ... ≤ (finset.card ((H ∩ Q.adjacent q).to_finset )) * abs (ε q y) :
     (mul_le_mul_right H_q_pos).mpr (by {
             norm_cast,
             exact finset.card_le_of_subset (by rw finset.to_finset_inter ; apply finset.inter_subset_inter_left coeffs_support) })
end

theorem degree_theorem :
  ∃ q, q ∈ H ∧ real.sqrt (m + 1) ≤ (H ∩ q.adjacent).to_finset.card :=
begin
  rcases exists_eigenvalue H hH with ⟨y, ⟨⟨y_mem_H, y_mem_g⟩, y_ne⟩⟩,
  have coeffs_support : ((dual_pair_e_ε (m+1)).coeffs y).support ⊆ H.to_finset,
  { intros p p_in,
    rw finsupp.mem_support_iff at p_in,
    rw set.mem_to_finset,
    exact (dual_pair_e_ε _).mem_of_mem_span y_mem_H p p_in },
  obtain ⟨q, H_max⟩ : ∃ q : Q (m+1), ∀ q' : Q (m+1), abs ((ε q' : _) y) ≤ abs (ε q y),
    from fintype.exists_max _,
  have H_q_pos : 0 < abs (ε q y),
  { contrapose! y_ne,
    exact epsilon_total (λ p,  abs_nonpos_iff.mp (le_trans (H_max p) y_ne)) },
  refine ⟨q, (dual_pair_e_ε _).mem_of_mem_span y_mem_H q (abs_pos_iff.mp H_q_pos), _⟩,
  let s := real.sqrt (m+1),
  suffices : s * abs (ε q y) ≤ ↑(_) * abs (ε q y),
    from (mul_le_mul_right H_q_pos).mp ‹_›,
  apply calc_lemma; assumption
end