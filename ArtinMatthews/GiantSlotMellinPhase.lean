module

public import ArtinMatthews.GiantSlotDyadicGeometry
public import ArtinMatthews.PrimeExtractionSeparatedCoefficients
public import ArtinMatthews.MarkedTypeIIActualRectangle


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Mellin phases on the shortened original slot rectangle.
The selected slot acquires the literal modulation, and the cofactor
receives a phase of norm one. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators

theorem giant_centered_mellin_phase_eq (W t : ℝ) {m : ℕ} (hm : 0 < m) :
    markedMajorCenteredCoefficient W 0 m*primeExtractionMellinPhase t m =
      markedMajorCenteredCoefficient W (2*Real.pi*t) m := by
  rw [primeExtractionMellinPhase_eq_markedLogTwist,markedLogTwist_eq_cpow hm]
  unfold markedMajorCenteredCoefficient
  simp only [Complex.ofReal_zero,zero_mul,Complex.cpow_zero,one_mul]
  rw [mul_comm Complex.I ((2*Real.pi*t:ℝ):ℂ)]
  ring

theorem giant_slot_mellin_phase_eq_interval {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (x γ t : ℝ) (X k l : ℕ) (hz : 0 ≤ x^γ) (β : ℕ → ℂ) :
    let M := max (2^k) (⌊x^γ⌋₊+1)
    let N := min X (2*2^k-1)
    let U := 2^l
    let V := min X (2*2^l-1)
    let W := Real.exp ((Real.log x)^(6/25:ℝ))
    primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock X k)
      (primeExtractionDyadicBlock X l) (giantOrdinarySlotCore e χ G x γ β) t =
      ∑ m ∈ Icc M N,∑ n ∈ Icc U V,
        χ (m*n)*markedMajorCenteredCoefficient W (2*Real.pi*t) m *
          (β n*primeExtractionMellinPhase t n)*G x (m*n-1)*
          (literalMarkedArrayWeight e x (m*n-1):ℂ) := by
  dsimp only
  unfold primeExtractionBilinearPhaseSum
  rw [← giant_dyadic_block_threshold_eq_Icc X k hz,giant_dyadic_block_eq_Icc X l,sum_filter]
  apply sum_congr rfl
  intro m hm
  by_cases h : x^γ < (m:ℝ)
  · rw [ite_eq_left h]
    apply sum_congr rfl
    intro n _
    simp only [giantOrdinarySlotCore,giantCenteredSlotCoefficient,h,ite_true]
    rw [← giant_centered_mellin_phase_eq _ _ (mem_Ioc.mp (mem_filter.mp hm).1).1]
    ring
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro n _
    simp only [giantOrdinarySlotCore,giantCenteredSlotCoefficient,h,ite_false,mul_zero,zero_mul]

end
end ArtinMatthews
