import data.real.basic

def dense_in_R (A : set ℝ) := ∀ (x y : ℝ), x < y → ∃ a ∈ A, a ∈ set.Ioo x y
def embedded_rationals : set ℝ := { x | ∃ r : ℚ, x = ↑r }

theorem rat_dense_in_R : dense_in_R embedded_rationals := 
  intros x y le,

  have h : ∃ n : ℕ, 0 < n ∧ (1/n : ℝ) < (y - x), 
  apply archimedean_R, 
  linarith,

  cases h with n ar,

  have h : ∃ m : ℤ, ((m - 1) : ℝ) ≤ (n*x) ∧ (n*x : ℝ) < (m : ℝ), 
  apply has_ceiling (n*x), 

  cases h with m hc,

  have h : 0 < n → (1/n : ℝ) * (m : ℝ) = (m/n : ℝ),
  apply inv_prod_other m n, 

  use [m/n, m/n], 
  simp, 

  have g : x < (m/n : ℝ) ↔ (↑n*x) < (↑m),
  apply lt_div_iff' _, norm_num [h],
  simp * at *,

  split,
  rw g, apply hc.2, 