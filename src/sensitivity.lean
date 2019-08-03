import tactic
import tactic.fin_cases
import data.real.basic
import linear_algebra.dual
import ring_theory.ideals

local attribute [instance, priority 1] classical.prop_decidable
noncomputable theory
local attribute [instance, priority 1] classical.prop_decidable
local attribute [instance, priority 0] set.decidable_mem_of_fintype

/-- The hypercube.-/
def Q (n) : Type := fin n → bool

/-- The only element of Q0 -/
def eQ0 : Q 0 := λ _, tt

lemma Q0_unique (p : Q 0) : p = eQ0 :=
by { ext x, fin_cases x }

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
(finset.univ : finset (fin n)).sum $ λ i, cond (x.xor y i) 1  0

@[simp] lemma dist_self (x : Q n) : x.dist x = 0 :=
finset.sum_eq_zero $ λ i hi, by simp only [xor, bxor_self, bool.cond_ff]

@[symm] lemma dist_symm (x y : Q n) : x.dist y = y.dist x :=
congr_arg ((finset.univ : finset (fin n)).sum) $
by { funext i, simp [xor_comm] }

/-- Two vertices of the hypercube are adjacent if their distance is 1.-/
def adjacent (x y : Q n) : Prop := x.dist y = 1

/-- The set of n-/
def neighbours (x : Q n) : set (Q n) := {y | x.adjacent y}

variable (n)

/-- The cardinality of the hypercube.-/
@[simp] lemma card : fintype.card (Q n) = 2^n :=
calc _ = _ : fintype.card_fun
   ... = _ : by simp only [fintype.card_fin, fintype.card_bool]

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
    { funext i, dsimp only [bool.cond_tt, bool.cond_ff], split_ifs with H,
      { rw [H, h] },
      { rw [function.comp_app, fin.succ_pred] } }
  end,
  right_inv := λ x,
  begin
    cases x;
    { simp only [dif_pos, bool.cond_tt, bool.cond_ff, cond, function.comp],
      funext i, rw [dif_neg, i.pred_succ], rw [fin.ext_iff, fin.succ_val],
      exact nat.succ_ne_zero _ }
  end }

lemma equiv_sum_apply (x : Q (n+1)) :
  equiv_sum n x = cond (x 0) (sum.inl (x ∘ fin.succ)) (sum.inr (x ∘ fin.succ)) := rfl

end Q

/-- The free vector space on vertices of a hypercube, defined inductively. -/
def V : ℕ → Type
| 0 := ℝ
| (n+1) := V n × V n

instance : Π n, add_comm_group (V n) :=
begin
  apply nat.rec,
  { dunfold V, apply_instance },
  { introsI n IH, dunfold V, apply_instance }
end

instance : Π n, vector_space ℝ (V n) :=
begin
  apply nat.rec,
  { dunfold V, apply_instance },
  { introsI n IH, dunfold V, apply_instance }
end

lemma dim_V {n : ℕ} : vector_space.dim ℝ (V n) = 2^n :=
begin
  induction n with n IH,
  { apply dim_of_field },
  { dunfold V,
    rw [dim_prod, IH, pow_succ, two_mul] }
end

/-- The basis of V indexed by the hypercube.-/
def e : Π {n}, Q n → V n
| 0     := λ _, (1:ℝ)
| (n+1) := λ x, cond (x 0) (e (x ∘ fin.succ), 0) (0, e (x ∘ fin.succ))

@[simp] lemma e_zero_apply (x : Q 0) :
  e x = (1 : ℝ) := rfl

lemma e_succ_apply {n} (x : Q (n+1)) :
  e x = cond (x 0) (e (x ∘ fin.succ), 0) (0, e (x ∘ fin.succ)) := rfl

lemma e.is_basis (n) : is_basis ℝ (e : Q n → V n) :=
begin
  induction n with n ih,
  { split,
    { apply linear_map.ker_eq_bot'.mpr,
      intros v hv, ext i,
      rw [finsupp.total_apply] at hv,
      simp only [e_zero_apply, smul_eq_mul, mul_one] at hv,
      sorry
      },
    { refine (ideal.eq_top_iff_one _).mpr (submodule.subset_span _),
      rw set.mem_range, exact ⟨(λ _, tt), rfl⟩ } },
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

lemma f_squared {n : ℕ} : ∀ v, (f n) (f n v) = (n : ℝ) • v :=
-- The (n : ℝ) is necessary since `n • v` refers to the multiplication defined
-- using only the addition of V.
begin
  induction n with n IH,
  { intro v, dunfold f, simp, refl },
  { rintro ⟨v, v'⟩,
    ext,
    { dunfold f V,
      conv_rhs { change ((n : ℝ) + 1) • v, rw add_smul },
      simp [IH] },
    { dunfold f V,
      conv_rhs { change ((n : ℝ) + 1) • v', rw add_smul },
      have : Π (x y : V n), -x + (y + x) = y := by { intros, abel }, -- ugh
      simp [IH, this] } }
end

/-- The dual basis to e -/
noncomputable def ε : Π {n : ℕ} (p : Q n), V n →ₗ[ℝ] ℝ
| 0 _ := linear_map.id
| (n+1) p := cond (p 0) ((ε $ p ∘ fin.succ).comp $ linear_map.fst _ _ _) ((ε $ p ∘ fin.succ).comp $ linear_map.snd _ _ _)

lemma fin.succ_ne_zero {n} (k : fin n) : fin.succ k ≠ 0 :=
begin
  cases k with k hk,
  intro h,
  have : k + 1 = 0 := (fin.ext_iff _ _).1 h,
  finish
end

open bool

lemma Q_succ_n_eq {n} (p q : Q (n+1)) : p = q ↔ (p 0 = q 0 ∧ p ∘ fin.succ = q ∘ fin.succ) :=
begin
  split,
  { intro h, split ; rw h ; refl, },
  { rintros ⟨h₀, h⟩,
    ext x,
    by_cases hx : x = 0,
    { rwa hx },
    rw ← fin.succ_pred x hx,
    convert congr_fun h (fin.pred x hx) }
end

lemma duality {n : ℕ} (p q : Q n) : ε p (e q) = if p = q then 1 else 0 :=
begin
  induction n with n IH,
  { dsimp [ε, e],
    simp [Q0_unique p, Q0_unique q] },
  { cases hp : p 0 ; cases hq : q 0,
    all_goals { 
      dsimp [ε, e],
      rw [hp, hq],
      repeat {rw cond_tt},
      repeat {rw cond_ff},
      simp only [linear_map.fst_apply, linear_map.snd_apply, linear_map.comp_apply] }, 
    { rw IH,
      congr'  1,
      rw Q_succ_n_eq,
      finish },
    { erw (ε _).map_zero,
      have : p ≠ q,
      { intro h,
        rw Q_succ_n_eq p q at h,
        finish },
      simp [this] },
    { erw (ε _).map_zero,
      have : p ≠ q,
      { intro h,
        rw Q_succ_n_eq p q at h,
        finish },
      simp [this] },
    { rw IH,
      congr'  1,
      rw Q_succ_n_eq,
      finish } }
end

/-- The adjacency relation on Q^n. -/
def adjacent : Π {n : ℕ}, Q n → Q n → Prop
| 0 p q := false
| (n+1) p q := (p 0 = q 0 ∧ adjacent (p ∘ fin.succ) (q ∘ fin.succ)) ∨ (p 0 ≠ q 0 ∧ p ∘ fin.succ = q ∘ fin.succ)

lemma f_matrix {n} : ∀ (p q : Q n), abs (ε q (f n (e p))) = if adjacent p q then 1 else 0 :=
begin
  induction n with n IH,
  { intros p q,
    dsimp [f, adjacent],
    simp [Q0_unique p, Q0_unique q] },
  { intros p q,
    have ite_nonneg : ite (q ∘ fin.succ = p ∘ fin.succ) (1 : ℝ) 0 ≥ 0,
    { by_cases h : q ∘ fin.succ = p ∘ fin.succ; simp [h] ; norm_num },
    cases hp : p 0 ; cases hq : q 0,
    all_goals { 
      dsimp [e, ε, f, adjacent],
      rw [hp, hq],
      repeat { rw cond_tt },
      repeat { rw cond_ff },
      simp only [add_zero, linear_map.id_apply, linear_map.fst_apply, linear_map.snd_apply,
                cond, cond_tt, cond_ff, linear_map.neg_apply,
                linear_map.copair_apply, linear_map.comp_apply],
      try { erw (f n).map_zero },
      try { simp only [abs_neg, abs_of_nonneg ite_nonneg, add_comm, add_zero, duality,
              false_and, false_or, IH, linear_map.map_add, linear_map.map_neg, linear_map.map_zero,
              neg_zero, not_false_iff, not_true, or_false, true_and, zero_add] },
      try { congr' 1, apply propext, rw eq_comm },
      try { simp } } }
end

/-- The linear operator g_n corresponding to Knuth's matrix B_n.
  We adopt the convention n = m+1. -/
def g (m : ℕ) : V m →ₗ[ℝ] V (m+1) :=
linear_map.pair (f m + real.sqrt (m+1) • linear_map.id) linear_map.id

lemma g_injective {m : ℕ} : function.injective (g m) :=
begin
  rw[g], intros x₁ x₂ H_eq, simp at *, exact H_eq.right
end

-- I don't understand why the type ascription is necessary here, when f_squared worked fine
lemma f_image_g {m : ℕ} (w : V (m + 1)) (hv : ∃ v, w = g m v) :
  (f (m + 1) : V (m + 1) → V (m + 1)) w = real.sqrt (m + 1) • w :=
begin
  rcases hv with ⟨v, rfl⟩,
  dsimp [g],
  erw f,
  simp [f_squared],
  rw [smul_add, smul_smul, real.mul_self_sqrt (by exact_mod_cast zero_le _ : 0 ≤ (1 : ℝ) + m), add_smul, one_smul], 
  abel,
end

variables {m : ℕ} (H : set (Q (m + 1))) (hH : fintype.card H ≥ 2^m + 1)
include hH

lemma exists_eigenvalue :
  ∃ y ∈ submodule.span ℝ (e '' H) ⊓ (g m).range, y ≠ (0 : _) :=
sorry                           -- Dimension argument

theorem degree_theorem :
  ∃ q, q ∈ H ∧ real.sqrt (m + 1) ≤ fintype.card {p // p ∈ H ∧ q.adjacent p} :=
sorry
