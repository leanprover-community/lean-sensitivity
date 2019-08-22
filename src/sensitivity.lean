/-
A formalization of Hao Huang's sensitivity theorem: in the hypercube of
dimension n ≥ 1, if one colors more than half the vertices then at least one
vertex has at least √n colored neighbors.

A fun summer collaboration by
Reid Barton, Johan Commelin, Jesse Han, Chris Hugues, Rob Lewis, and Patrick Massot,
based on Don Knuth's account of the story
(https://www.cs.stanford.edu/~knuth/papers/huang.pdf),
using the Lean theorem prover (http://leanprover.github.io/),
by Leonardo de Moura at Microsoft Research, and his collaborators
(https://leanprover.github.io/people/),
and using Lean's user maintained mathematics library
(https://github.com/leanprover-community/mathlib).
-/
import tactic.fin_cases
import tactic.apply_fun
import linear_algebra.finite_dimensional
import analysis.normed_space.basic
import for_mathlib

-- The next three lines assert we do not want to give a constructive proof,
-- but rather use classical logic.
noncomputable theory
local attribute [instance, priority 1] classical.prop_decidable
local attribute [instance, priority 0] set.decidable_mem_of_fintype

notation `|`x`|` := abs x
notation `√` := real.sqrt

open function bool linear_map fintype finite_dimensional dual_pair

/- -------------------------------------------------------------------------\
|  The hypercube.                                                           |
\---------------------------------------------------------------------------/

/-
Notations:
ℕ denotes natural numbers (including zero).
fin n = {0, ⋯ , n - 1}.
bool = {tt, ff}.
-/

/-- The hypercube in dimension n. -/
def Q (n : ℕ) : Type := fin n → bool

/-- The projection from Q (n + 1) to Q n forgetting the first value
(ie. the image of zero). -/
def π {n : ℕ} : Q (n + 1) → Q n := λ p, p ∘ fin.succ

namespace Q
-- n will always denote a natural number.
variable (n : ℕ)

/-- Q n is not empty -/
instance : inhabited (Q n) := ⟨λ i, tt⟩

/-- Q 0 has a unique element. -/
instance : unique (Q 0) :=
⟨⟨λ _, tt⟩, by { intro, ext x, fin_cases x }⟩

/-- Q n is finite. -/
instance : fintype (Q n) := by delta Q; apply_instance

/-- Q n has 2^n elements. -/
lemma card : card (Q n) = 2^n :=
by simp [Q]

/-- The ℝ-module structure on functions from Q n to ℝ (with finite support). -/
instance coeffs_module (n) : module ℝ (Q n →₀ ℝ) := finsupp.module (Q n) ℝ

-- Until the end of this namespace, n will be an implicit argument (still
-- a natural number).
variable {n}

lemma succ_n_eq (p q : Q (n+1)) : p = q ↔ (p 0 = q 0 ∧ π p = π q) :=
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

/-- The adjacency relation defining the graph structure on Q n:
p.adjacent q if there is an edge from p to q in Q n -/
def adjacent {n : ℕ} (p : Q n) : set (Q n) := λ q, ∃! i, p i ≠ q i

/-- In Q 0 no two vertices are adjacent. -/
lemma not_adjacent_zero (p q : Q 0) : ¬ p.adjacent q :=
by rintros ⟨v, _⟩; apply fin_zero_elim v

/-- If p and q in Q (n+1) have different value at zero then they are adjacent
iff their projections to Q n are equal. -/
lemma adj_succ_of_zero_neq {p q : Q (n+1)} (h₀ : p 0 ≠ q 0) :
  p.adjacent q ↔ π p = π q :=
begin
  split,
  { rintros ⟨i, h_eq, h_uni⟩,
    ext x, by_contradiction hx,
    apply fin.succ_ne_zero x,
    rw [h_uni _ hx, h_uni _ h₀] },
    { intro heq,
    use [0, h₀],
    intros y hy,
    contrapose! hy,
    rw ←fin.succ_pred _ hy,
    apply congr_fun heq }
end

/-- If p and q in Q (n+1) have the same value at zero then they are adjacent
iff their projections to Q n are adjacent. -/
lemma adj_succ_of_zero_eq {p q : Q (n+1)} (h₀ : p 0 = q 0) :
  p.adjacent q ↔ (π p).adjacent (π q) :=
begin
  split,
  { rintros ⟨i, h_eq, h_uni⟩,
    have h_i : i ≠ 0, from λ h_i, absurd h₀ (by rwa h_i at h_eq),
    use [i.pred h_i,
         show p (fin.succ (fin.pred i _)) ≠ q (fin.succ (fin.pred i _)),
           by rwa fin.succ_pred],
    intros y hy,
    simp [eq.symm (h_uni _ hy)] },
  { rintros ⟨i, h_eq, h_uni⟩,
    use [i.succ, h_eq],
    intros y hy,
    rw [←fin.pred_inj, fin.pred_succ],
    { apply h_uni,
      change p (fin.pred _ _).succ ≠ q (fin.pred _ _).succ,
      simp [hy] },
    { contrapose! hy,
      rw [hy, h₀] },
    { apply fin.succ_ne_zero } }
end

@[symm] lemma adjacent.symm {p q : Q n} : p.adjacent q ↔ q.adjacent p :=
by simp only [adjacent, ne_comm]

end Q

/- -------------------------------------------------------------------------\
|  The vector space.                                                        |
\---------------------------------------------------------------------------/

/-- The free vector space on vertices of a hypercube, defined inductively. -/
def V : ℕ → Type
| 0 := ℝ
| (n+1) := V n × V n

namespace V
variables (n : ℕ)

-- V n is a real vector space whose equality relation is computable.

instance : decidable_eq (V n) :=
by { induction n ; { dunfold V, resetI, apply_instance } }

instance : add_comm_group (V n) :=
by { induction n ; { dunfold V, resetI, apply_instance } }

instance : vector_space ℝ (V n) :=
by { induction n ; { dunfold V, resetI, apply_instance } }

-- The next five definitions are short circuts helping Lean to quickly find
-- relevant structures on V n
def module : module ℝ (V n) := by apply_instance
def add_comm_semigroup : add_comm_semigroup (V n) := by apply_instance
def add_comm_monoid : add_comm_monoid (V n) := by apply_instance
def has_scalar : has_scalar ℝ (V n) := by apply_instance
def has_add : has_add (V n) := by apply_instance

local attribute [instance, priority 100000]
  V.module V.add_comm_semigroup V.add_comm_monoid V.has_scalar V.has_add
end V

/-- The basis of V indexed by the hypercube, defined inductively. -/
noncomputable def e : Π {n}, Q n → V n
| 0     := λ _, (1:ℝ)
| (n+1) := λ x, cond (x 0) (e (π x), 0) (0, e (π x))

@[simp] lemma e_zero_apply (x : Q 0) : e x = (1 : ℝ) := rfl

/-- The dual basis to e, defined inductively. -/
noncomputable def ε : Π {n : ℕ} (p : Q n), V n →ₗ[ℝ] ℝ
| 0 _ := linear_map.id
| (n+1) p := cond (p 0) ((ε $ π p).comp $ linear_map.fst _ _ _) ((ε $ π p).comp $ linear_map.snd _ _ _)

variable {n : ℕ}

lemma duality (p q : Q n) : ε p (e q) = if p = q then 1 else 0 :=
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

/-- Any vector in V n annihilated by all ε p's is zero. -/
lemma epsilon_total {v : V n} (h : ∀ p : Q n, (ε p) v = 0) : v = 0 :=
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
      rwa show p = π q, by { ext, simp [q, fin.succ_ne_zero, π] } } }
end

/-- e and ε are dual families of vectors. It implies that e is indeed a basis
and ε computes coefficients of decompositions of vectors on that basis. -/
def dual_pair_e_ε (n : ℕ) : dual_pair (@e n) (@ε n) :=
{ eval := duality,
  total := @epsilon_total _ }

-- We will now derive the dimension of V, first as a cardinal in dim_V and,
-- since this cardinal is finite, as a natural number in findim_V

lemma dim_V : vector_space.dim ℝ (V n) = 2^n :=
have vector_space.dim ℝ (V n) = ↑(2^n : ℕ),
  by convert dim_eq_card (dual_pair_e_ε _).is_basis using 1; rw Q.card,
by assumption_mod_cast

instance : finite_dimensional ℝ (V n) :=
fin_dim_of_finite_basis (dual_pair_e_ε _).is_basis

-- TODO: fix this in mathlib, if it's really wrong
local attribute [-elim_cast] cardinal.nat_cast_pow

lemma findim_V : findim ℝ (V n) = 2^n :=
have _ := @dim_V n,
by rw [←findim_eq_dim] at this; assumption_mod_cast

/- -------------------------------------------------------------------------\
|  The linear map.                                                          |
\---------------------------------------------------------------------------/

/-- The linear operator f_n corresponding to Huang's matrix A_n,
defined inductively as a ℝ-linear map from V n to V n. -/
noncomputable def f : Π n, V n →ₗ[ℝ] V n
| 0 := 0
| (n+1) := linear_map.pair
             (linear_map.copair (f n) linear_map.id)
             (linear_map.copair linear_map.id (-f n))

-- The preceding definition use linear map constructions to automatically
-- get that f is linear, but its values are somewhat buried as a side-effet.
-- The next two lemmas unburry them.

@[simp] lemma f_zero : f 0 = 0 := rfl

lemma f_succ_apply (v : V (n+1)) :
  (f (n+1) : V (n+1) → V (n+1)) v = (f n v.1 + v.2, v.1 - f n v.2) :=
begin
  cases v,
  rw f,
  simp only [linear_map.id_apply, linear_map.pair_apply, prod.mk.inj_iff,
    linear_map.neg_apply, sub_eq_add_neg, linear_map.copair_apply],
  exact ⟨rfl, rfl⟩
end

-- In the next statement, rhe (n : ℝ) is necessary since `n • v` refers to the
-- multiplication defined using only the addition of V.

lemma f_squared : ∀ v : V n, (f n) (f n v) = (n : ℝ) • v :=
begin
  induction n with n IH; intro,
  { simpa only [nat.cast_zero, zero_smul] },
  { cases v, simp [f_succ_apply, IH, add_smul] }
end

-- We now compute the matrix of f in the e basis (p is the line index,
-- q the column index.)

lemma f_matrix :
  ∀ (p q : Q n), |ε q (f n (e p))| = if q.adjacent p then 1 else 0 :=
begin
  induction n with n IH,
  { intros p q,
    dsimp [f],
    simp [Q.not_adjacent_zero] },
  { intros p q,
    have ite_nonneg : ite (π q = π p) (1 : ℝ) 0 ≥ 0,
    { split_ifs ; norm_num },
    have f_map_zero := (show linear_map ℝ (V (n+0)) (V n), from f n).map_zero,
    dsimp [e, ε, f], cases hp : p 0 ; cases hq : q 0,
    all_goals
    { repeat {rw cond_tt}, repeat {rw cond_ff},
      simp [f_map_zero, hp, hq, IH, duality, abs_of_nonneg ite_nonneg, Q.adj_succ_of_zero_neq,
            Q.adj_succ_of_zero_eq],
      congr' 1 } }
end

/-- The linear operator g_n corresponding to Knuth's matrix B_n. In order to
enforce that n is positive, we write it as m + 1 for some natural number m. -/
noncomputable def g (m : ℕ) : V m →ₗ[ℝ] V (m+1) :=
linear_map.pair (f m + √(m+1) • linear_map.id) linear_map.id

-- in the following lemmas, m will denote a natural number
variables {m : ℕ}

-- again we unpack what are the values of g
lemma g_apply : ∀ v, g m v = (f m v + √(m+1) • v, v) :=
by delta g; simp

lemma g_injective : function.injective (g m) :=
begin
  rw g,
  intros x₁ x₂ h,
  simp only [linear_map.pair_apply, linear_map.id_apply, prod.mk.inj_iff] at h,
  exact h.right
end

lemma f_image_g (w : V (m + 1)) (hv : ∃ v, g m v = w) :
  (f (m + 1) : _) w = √(m + 1) • w :=
begin
  rcases hv with ⟨v, rfl⟩,
  have : √(m+1) * √(m+1) = m+1 :=
    real.mul_self_sqrt (by exact_mod_cast zero_le _),
  simp [-add_comm, this, f_succ_apply, g_apply, f_squared, smul_add, add_smul, smul_smul],
end

/- -------------------------------------------------------------------------\
|  The main proof.                                                          |
\---------------------------------------------------------------------------/

-- in the following, H will denote a subset of Q (m + 1) with cardinal
-- at least 2^m + 1
variables (H : set (Q (m + 1))) (hH : card H ≥ 2^m + 1)
include hH

-- dim X will denote the dimension of a subspace X as a cardinal
local notation `dim` X:70 := vector_space.dim ℝ ↥X
-- fdim X will denote the (finite) dimension of a subspace X as a natural number
local notation `fdim` := findim ℝ

lemma exists_eigenvalue :
  ∃ y ∈ submodule.span ℝ (e '' H) ⊓ (g m).range, y ≠ (0 : _) :=
begin
  let W := submodule.span ℝ (e '' H),
  let img := (g m).range,
  suffices : 0 < dim (W ⊓ img),
  { simp only [exists_prop],
    apply exists_mem_ne_zero_of_dim_pos,
    exact_mod_cast this },
  have dim_le : dim (W ⊔ img) ≤ 2^(m + 1),
  { convert ← dim_submodule_le (W ⊔ img),
    apply dim_V },
  have dim_add : dim (W ⊔ img) + dim (W ⊓ img) = dim W + 2^m,
  { convert ← dim_sup_add_dim_inf_eq W img,
    rw ← dim_eq_injective (g m) g_injective,
    apply dim_V },
  have dimW : dim W = card H,
  { have li : linear_independent ℝ (restrict e H) :=
      linear_independent.comp (dual_pair_e_ε _).is_basis.1 _ subtype.val_injective,
    have hdW := dim_span li,
    rw set.range_restrict at hdW,
    convert hdW,
    rw [cardinal.mk_image_eq ((dual_pair_e_ε _).is_basis.injective zero_ne_one), cardinal.fintype_card] },
  rw ← findim_eq_dim ℝ at ⊢ dim_le dim_add dimW,
  rw [← findim_eq_dim ℝ, ← findim_eq_dim ℝ] at dim_add,
  norm_cast at ⊢ dim_le dim_add dimW,
  rw nat.pow_succ at dim_le,
  linarith
end

theorem huang_degree_theorem :
  ∃ q, q ∈ H ∧ √(m + 1) ≤ (H ∩ q.adjacent).to_finset.card :=
begin
  rcases exists_eigenvalue H hH with ⟨y, ⟨⟨y_mem_H, y_mem_g⟩, y_ne⟩⟩,
  have coeffs_support : ((dual_pair_e_ε (m+1)).coeffs y).support ⊆ H.to_finset,
  { intros p p_in,
    rw finsupp.mem_support_iff at p_in,
    rw set.mem_to_finset,
    exact (dual_pair_e_ε _).mem_of_mem_span y_mem_H p p_in },
  obtain ⟨q, H_max⟩ : ∃ q : Q (m+1), ∀ q' : Q (m+1), |(ε q' : _) y| ≤ |ε q y|,
    from fintype.exists_max _,
  have H_q_pos : 0 < |ε q y|,
  { contrapose! y_ne,
    exact epsilon_total (λ p, abs_nonpos_iff.mp (le_trans (H_max p) y_ne)) },
  refine ⟨q, (dual_pair_e_ε _).mem_of_mem_span y_mem_H q (abs_pos_iff.mp H_q_pos), _⟩,
  let s := √(m+1),
  suffices : s * |ε q y| ≤ ↑(_) * |ε q y|,
    from (mul_le_mul_right H_q_pos).mp ‹_›,

  let coeffs := (dual_pair_e_ε (m+1)).coeffs,
  let φ : V (m+1) → V (m+1) := f (m+1),
  set s := √(↑m + 1),
  calc
    s * (abs (ε q y))
        = abs (ε q (s • y)) : by rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (real.sqrt_nonneg _)]
    ... = abs (ε q (φ y)) : by rw [← f_image_g y (by simpa using y_mem_g)]
    ... = abs (ε q (φ (lc _ (coeffs y)))) : by rw (dual_pair_e_ε _).decomposition y
    ... = abs ((coeffs y).sum (λ (i : Q (m + 1)) (a : ℝ), a • ((ε q) ∘ (f (m + 1)) ∘ λ (i : Q (m + 1)), e i) i)): by
                  { dsimp only [φ],
                    erw [(f $ m+1).map_finsupp_total, (ε q).map_finsupp_total, finsupp.total_apply] ; apply_instance }
    ... ≤ (coeffs y).support.sum (λ p,
           |(coeffs y p) * (ε q $ φ $ e p)| ) : norm_triangle_sum _ $ λ p, coeffs y p * _
    ... = (coeffs y).support.sum (λ p, |coeffs y p| * ite (q.adjacent p) 1 0) : by simp only [abs_mul, f_matrix]
    ... = ((coeffs y).support ∩ (Q.adjacent q).to_finset).sum (λ p, |coeffs y p| ) : finset.sum_ite _ _ _
    ... ≤ ((coeffs y).support ∩ (Q.adjacent q).to_finset).sum (λ p, |coeffs y q| ) : finset.sum_le_sum (λ p _, H_max p)
    ... = (finset.card ((coeffs y).support ∩ (Q.adjacent q).to_finset): ℝ) * |coeffs y q| : by rw [← smul_eq_mul, ← finset.sum_const']
    ... ≤ (finset.card ((H ∩ Q.adjacent q).to_finset )) * |ε q y| :
     (mul_le_mul_right H_q_pos).mpr (by {
             norm_cast,
             exact finset.card_le_of_subset (by rw finset.to_finset_inter ; apply finset.inter_subset_inter_right coeffs_support) })
end