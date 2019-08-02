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
  sorry
  -- dsimp only [function.comp, Q.equiv_sum, e_apply],
  -- cases h : x 0;
  -- { simp only [bool.cond_tt, bool.cond_ff, prod.mk.inj_iff, sum.elim_inl, sum.elim_inr, cond],
  --   exact ⟨rfl, rfl⟩ }
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

-- Where is this in the lib??
lemma bool_cases (b : bool) : b = tt ∨ b = ff :=
by cases b ; finish

lemma duality {n : ℕ} (p q : Q n) : ε p (e q) = if p = q then 1 else 0 :=
begin
  induction n with n IH,
  { dsimp [ε, e],
    simp [Q0_unique p, Q0_unique q] },
  { cases bool_cases (p 0) with hp hp ; cases bool_cases (q 0) with hq hq,
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
    cases bool_cases (p 0) with hp hp ; cases bool_cases (q 0) with hq hq,
    all_goals { 
      dsimp [e, ε, f, adjacent],
      rw [hp, hq],
      repeat { rw cond_tt },
      repeat { rw cond_ff },
      simp only [add_zero, linear_map.id_apply, linear_map.fst_apply, linear_map.snd_apply,
                 cond, cond_tt, cond_ff, linear_map.neg_apply,
                 linear_map.copair_apply, linear_map.comp_apply],
      try { erw (f n).map_zero },
      try { simp only [linear_map.map_zero, add_comm, zero_add, linear_map.map_add, neg_zero, add_zero] } },
    { rw IH,
      congr' 1, apply propext,
      simp [hp, hq] },
    { rw [duality, abs_of_nonneg ite_nonneg], 
      simp only [true_and, false_or, not_false_iff, false_and],
      congr' 1,
      apply propext, 
      rw eq_comm, },
    { rw [duality, abs_of_nonneg ite_nonneg], 
      simp only [true_and, false_or, not_false_iff, false_and],
      congr' 1,
      apply propext, 
      rw eq_comm, },
    { simp only [linear_map.map_neg, abs_neg],
      rw IH,
      simp, 
      congr' 1 } }
end

/-- The linear operator g_n corresponding to Knuth's matrix B_n.
  We adopt the convention n = m+1. -/
def g (m : ℕ) : V m →ₗ[ℝ] V (m+1) :=
linear_map.pair (f m + real.sqrt (m+1) • linear_map.id) linear_map.id

lemma g_injective {m : ℕ} : function.injective (g m) :=
begin
  rw[g], intros x₁ x₂ H_eq, simp at *, exact H_eq.right
end

@[simp] lemma f_0 {x} : (f 0).to_fun x = 0 := rfl

@[simp]lemma f_neg {m} {x} : (f m).to_fun x + (-f m).to_fun x = 0 := by change (f m) x + (-f m) x = 0; simp

lemma cast_lemma_1 {m : ℕ} : 0 ≤ (1 + (nat.cast m) : ℝ) :=
by {change (0 : ℝ) ≤ (1 + ↑m : ℝ), suffices this : 0 ≤ (↑m : ℝ), by {linarith}, simp}

lemma cast_lemma_2 {m : ℕ} : (nat.cast (nat.succ m) : ℝ) = (1 + nat.cast m : ℝ) :=
by change ↑(nat.succ m) = (1 + ↑m : ℝ); simp

lemma f_image_g_aux₅ (m : ℕ) (v₁ v₂ : V m) (ih : ∀ (w_snd : V (m + 0)), (1 + nat.cast m : ℝ) • w_snd = w_snd + (f m).to_fun ((f m).to_fun w_snd)) :
 (1 + nat.cast (nat.succ m) : ℝ) • v₁ =
    v₁ +
      ((linear_map.pair (linear_map.copair (f m) linear_map.id) (linear_map.copair linear_map.id (-f m))).to_fun
         ((linear_map.pair (linear_map.copair (f m) linear_map.id) (linear_map.copair linear_map.id (-f m))).to_fun
            (v₁, v₂))).fst :=
begin
  change _ = v₁ + (_ + _), /- `tidy` says -/ dsimp at *, simp at *, simp at *, unfold_coes, 
  change _ = v₁ + ((v₁ + (-f m).to_fun (v₂)) + ((f m).to_fun ((f m).to_fun v₁ + v₂))),
  specialize ih v₁, rw[add_smul],
  have this : ((nat.cast (nat.succ m) : ℝ) • v₁) = (1 + nat.cast m : ℝ) • v₁,
    by { rw[cast_lemma_2] }, rw[this],
  rw[ih], simp[(f m).add],
  ac_change _ = ((f m).to_fun v₂ + (-f m).to_fun v₂) + ((f m).to_fun ((f m).to_fun v₁)),
  simp
end

lemma f_image_g_aux₄ (m : ℕ) (v₁ v₂ : V m) (ih : ∀ (w_snd : V (m + 0)), (1 + nat.cast m : ℝ) • w_snd = w_snd + (f m).to_fun ((f m).to_fun w_snd)) :
  (1 + nat.cast (nat.succ m) : ℝ) • v₂ =
    v₂ +
      ((linear_map.pair (linear_map.copair (f m) linear_map.id) (linear_map.copair linear_map.id (-f m))).to_fun
         ((linear_map.pair (linear_map.copair (f m) linear_map.id) (linear_map.copair linear_map.id (-f m))).to_fun
            (v₁, v₂))).snd :=
begin
  change _ = v₂ + (_ + _), /- `tidy` says -/ dsimp at *, unfold_coes, 
  change _ = v₂ + (((f m).to_fun v₁ + v₂) + ((-f m).to_fun (v₁ + (-f m).to_fun v₂))),
  specialize ih v₂, rw[add_smul],
  have this : ((nat.cast (nat.succ m) : ℝ) • v₂) = (1 + nat.cast m : ℝ) • v₂,
    by { rw[cast_lemma_2] }, rw[this],
  rw[ih], simp[(- f m).add],
  ac_change _ = ((f m).to_fun v₁ + (-f m).to_fun v₁) + (-f m).to_fun ((-f m).to_fun v₂),
  simp,
  have this₂ : ∀ {x}, (-f m).to_fun x = (-1 : ℝ) • ((f m).to_fun x),
    by {/- `tidy` says -/ intros x, simp at *, refl},
  rw this₂, rw this₂, rw[(f m).smul], simp
end

lemma f_image_g_aux₃ (m : ℕ) (w_snd : V (m + 0)) : (1 + nat.cast m : ℝ) • w_snd = w_snd + (f m).to_fun ((f m).to_fun w_snd) :=
begin
  induction m with m ih,
    {tidy, change (1 + 0 : ℝ) * _ = _, simp},
    {rw[f], cases w_snd with v₁ v₂,
    /- `tidy` says -/ dsimp at *, simp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
    work_on_goal 0 { dsimp at *, simp at *, simp at * },
    work_on_goal 1 { dsimp at *, simp at *, simp at * },
      { apply f_image_g_aux₅, exact ih },
      { apply f_image_g_aux₄, exact ih },
      }
end

lemma f_image_g_aux₁ (m : ℕ) (w_fst w_snd : V (m + 0)) (hv_w : V m) (h_1 : w_fst = (f m) w_snd + real.sqrt (1 + ↑m) • w_snd)
: ((f (m + 1)).to_fun (w_fst, w_snd)).fst = real.sqrt (1 + nat.cast m) • w_fst :=
begin
  subst h_1, simp at *, unfold_coes,
  rw[f], change (linear_map.copair (f m) linear_map.id).to_fun _ = _,
  change _ + _ = _, /- `tidy` says -/ dsimp at *, simp at *, unfold_coes,
  suffices this : (1 + nat.cast m : ℝ) • w_snd = w_snd + (f m).to_fun ((f m).to_fun w_snd),
    by { rw[smul_add, smul_smul],
         simp[show real.sqrt (1 + nat.cast m) * real.sqrt (1 + nat.cast m) = (1 + nat.cast m : ℝ),
              by rw[real.mul_self_sqrt cast_lemma_1], this]},
  apply f_image_g_aux₃
end

lemma f_image_g_aux₂ (m : ℕ) (w_fst w_snd : V (m + 0)) (h_1 : w_fst = (f m) w_snd + real.sqrt (1 + ↑m) • w_snd)
  : ((f (m + 1)).to_fun (w_fst, w_snd)).snd = real.sqrt (1 + nat.cast m) • w_snd :=
by {rw[f], change (linear_map.copair _ _).to_fun _ = _, change _ + _ = _, subst h_1, /- `tidy` says -/ dsimp at *, simp at *, refl}

-- I don't understand why the type ascription is necessary here, when f_squared worked fine
lemma f_image_g {m : ℕ} (w : V (m + 1)) (hv : ∃ v, w = g m v) :
  (f (m + 1) : V (m + 1) → V (m + 1)) w = real.sqrt (m + 1) • w :=
begin -- tidy, take the wheel!
  /- `tidy` says -/ cases hv, cases w, dsimp at *, simp at *,
  tactic.ext1 [] {new_goals := tactic.new_goals.all}, work_on_goal 0
  { dsimp at *, injections_and_clear, dsimp at *, induction h_2,
    simp at *, unfold_coes }, work_on_goal 1
    { dsimp at *, injections_and_clear, dsimp at *,
      induction h_2, simp at *, unfold_coes },
  { apply f_image_g_aux₁; from ‹_› },
  { apply f_image_g_aux₂; from ‹_› }
end

variables {m : ℕ} (H : set (Q (m + 1))) (hH : fintype.card H ≥ 2^m + 1)
include hH

lemma exists_eigenvalue :
  ∃ y ∈ submodule.span ℝ (e '' H) ⊓ (g m).range, y ≠ (0 : _) :=
sorry                           -- Dimension argument

theorem degree_theorem :
  ∃ q, q ∈ H ∧ real.sqrt (m + 1) ≤ fintype.card {p // p ∈ H ∧ q.adjacent p} :=
sorry
