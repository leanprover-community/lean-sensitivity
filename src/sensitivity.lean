import data.real.basic
import linear_algebra.dual

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

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

/-- The hypercube. -/
def Q (n : ℕ) : Type := fin n → bool
instance {n : ℕ} : fintype (Q n) := by delta Q; apply_instance

/-- The adjacency relation on Q^n. -/
constant adjacent {n : ℕ} (p q : Q n) : Prop

/-- The basis of V_n, indexed on Q^n. -/
constant e {n : ℕ} : Q n → V n
axiom is_basis_e {n : ℕ} : is_basis ℝ (@e n)

def ε {n : ℕ} : Q n → (V n →ₗ[ℝ] ℝ) :=
is_basis_e.dual_basis

axiom f_matrix_adjacent {n : ℕ} (p q : Q n) (h : adjacent p q) : abs (ε q (f n (e p))) = 1
axiom f_matrix_nonadjacent {n : ℕ} (p q : Q n) (h : ¬ adjacent p q) : ε q (f n (e p)) = 0

/-- The linear operator g_n corresponding to Knuth's matrix B_n.
  We adopt the convention n = m+1. -/
def g (m : ℕ) : V m →ₗ[ℝ] V (m+1) :=
linear_map.pair (f m + real.sqrt (m+1) • linear_map.id) linear_map.id

lemma g_injective {m : ℕ} : function.injective (g m) :=
sorry

-- I don't understand why the type ascription is necessary here, when f_squared worked fine
lemma f_image_g {m : ℕ} (w : V (m + 1)) (hv : ∃ v, w = g m v) :
  (f (m + 1) : V (m + 1) → V (m + 1)) w = real.sqrt (m + 1) • w :=
sorry

variables {m : ℕ} (H : finset (Q (m + 1))) (hH : H.card ≥ 2^m + 1)
include hH

lemma exists_eigenvalue :
  ∃ y ∈ submodule.span ℝ (e '' H.to_set) ⊓ (g m).range, y ≠ (0 : _) :=
sorry                           -- Dimension argument

theorem degree_theorem :
  ∃ q, q ∈ H ∧ real.sqrt (m + 1) ≤ (H.filter (adjacent q)).card :=
sorry
