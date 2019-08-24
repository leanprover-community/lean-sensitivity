/-
  A reduction of Nisan and Szegedy's sensitivity conjecture to the degree theorem of Huang,
  following the introduction of Huang's "Induced subgraphs of hypercubes and a proof of the
  Sensitivity Conjecture" (arXiv:1907.00847v1)
-/

import sensitivity
import analysis.complex.exponential
import data.polynomial
import tactic.tidy

open function bool dual_pair finite_dimensional linear_map fintype

noncomputable theory
local attribute [instance, priority 1] classical.prop_decidable
local attribute [instance, priority 0] set.decidable_mem_of_fintype

section reduction

variable {n : ℕ}

def Q.flip (S : set (fin n)) : Q n → Q n :=
λ x, (λ i, if i ∈ S then (bool.cases_on (x i) tt ff) else x i)

def local_sensitivity (f : Q n → bool) (x : Q n) : ℕ :=
fintype.card {i // f x ≠ f (Q.flip ({i}) x)}

def sensitivity (f : Q n → bool) : ℕ :=
let ls := local_sensitivity f in ls (classical.some $ fintype.exists_max ls)

-- The local block sensitivity bs(f,x) is the maximum number of
-- disjoint blocks B₁, ⋯, B̨  of (fin n), such that for each i,  f (Q.flip Bᵢ x) ≠ f x.
def local_block_sensitivity (f : Q n → bool) (x : Q n) : ℕ := sorry

def block_sensitivity (f : Q n → bool) :=
let lbs := local_block_sensitivity f in lbs (classical.some $ fintype.exists_max lbs)

def deg : (Q n → bool) → ℕ := sorry

local notation `s` := sensitivity

local notation `bs` := block_sensitivity

def sensitivity_conjecture (n) : Prop := ∃ (p : polynomial ℝ), ∀ (f : Q n → bool), ↑(bs f) ≤ p.eval (s f)

-- Δ(H) is the supremum over q ∈ H of Card (H ∩ q.adjacent)
def Δ (H : set $ Q (n+1)) : ℕ := sorry

def Γ (H : set $ Q (n + 1)) : ℕ := max (Δ H) (Δ (- H))

theorem huang_degree_theorem' : ∀ (H : set (Q (n + 1))) (hH : Card H ≥ 2^n + 1), √n ≤ Δ H := sorry

theorem gotsman_linial_equivalence (h : ℕ → ℝ) (h_mono : monotone h) :
  (∀ (H : set (Q (n + 1))) (hH : Card H ≥ 2^n + 1), h n ≤ Γ H) ↔
  (∀ f : Q (n + 1) → bool, h (deg f) ≤ s f) := sorry

theorem nisan_szegedy_upper_bound (f : Q n → bool) : (↑(bs f) : ℝ) ≤ (2 * (deg f)^(2 : ℝ) : ℝ) := sorry

theorem huang_sensitivity_theorem (f : Q n → bool) : (↑(bs f) : ℝ) ≤ 2 * (s f : ℝ) ^ (4 : ℝ) :=
sorry

lemma two_times_x_to_4_is_polynomial : ∃ (p : polynomial ℝ), ∀ x, p.eval x = 2 * x ^ (4 : ℝ) :=
begin
  refine ⟨2 * (polynomial.X^4), _⟩, sorry
end

-- the Nisan-Szegedy sensitivity conjecture (DOI 10.1145/129712.129757):
-- bs is polynomially bounded by f
theorem sensitivity_conjecture_true : sensitivity_conjecture n :=
by {obtain ⟨p, Hp⟩ := two_times_x_to_4_is_polynomial, use p, simp [Hp, huang_sensitivity_theorem]}

end reduction
