module

public import ArtinMatthews.MarkedSparseHeight
public import ArtinMatthews.MarkedSparseIntervals


set_option backward.privateInPublic true
@[expose] public section

/-! The unit-interval exceptional-frequency estimate with the actual
frequency height `4*x*(log x)^B`, not an assumed logarithmic height bound. -/

namespace ArtinMatthews

open Filter

theorem markedPrimePolynomial_sparse_unitIntervals_at_x (c C₁ A B : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, 1 < Y →
      c * (Real.log x)^(1/(10:ℝ)) ≤ Real.log Y →
      Real.log Y ≤ C₁ * (Real.log x)^(1/(5:ℝ)) →
      ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, (p : ℝ) ≤ 2*Y) →
      ∀ I : Finset ℤ,
      (∀ z ∈ I, ∃ t ∈ Set.Icc (z : ℝ) ((z : ℝ)+1),
        |t| ≤ 4*x*(Real.log x)^B ∧
        (Real.log x)^(-A) ≤ ‖markedPrimePolynomial P Y χ ξ t‖) →
      (I.card : ℝ) ≤ 3*Real.exp ((Real.log x)^(91/(100:ℝ))) := by
  have hcst := markedPrimePolynomial_sparse_unitIntervals c C₁ 2 A hc hC₁
    (by norm_num) hA
  filter_upwards [Real.tendsto_log_atTop.eventually hcst,
    marked_sparse_frequency_height B hB] with x hcount hheight
  intro Y hY hlo hhi k χ ξ P hP hcap I hwitness
  exact hcount Y (4*x*(Real.log x)^B) hY hlo hhi hheight.1 hheight.2
    k χ ξ P hP hcap I hwitness

end ArtinMatthews
