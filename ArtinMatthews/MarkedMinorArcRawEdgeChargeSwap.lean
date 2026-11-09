module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargedAction


set_option backward.privateInPublic true
@[expose] public section

/-! The concrete correction from the original V^-1 promotion charge to
the transposed V^-1 storage charge, with a uniform finite-product bound. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgeChargeSwapModifier {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) : ℂ :=
  ∏ j, (if (c.promotions j).isSome then (V j : ℂ) else 1) *
    (if c.store j then (((V j)⁻¹ : ℝ) : ℂ) else 1)

theorem markedRawEdgeChoiceCharge_swap
    {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hV : ∀ j, V j ≠ 0)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCharge (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ s c *
      markedRawEdgeChoiceFreshMass ν hZ s c =
      (markedRawEdgeChoicePrimeMass ν V hZ s c : ℂ) *
        markedRawEdgeChargeSwapModifier V hZ s c := by
  unfold markedRawEdgeChoiceCharge markedRawEdgeChoiceFreshMass markedRawEdgeChargeSwapModifier
  simp only [markedRawEdgeChoicePrimeMass_eq_targetLast, Complex.ofReal_prod]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hv : (V j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hV j)
  by_cases hp : (c.promotions j).isSome <;>
    by_cases hs : c.store j <;> simp [hp,hs,hv,mul_comm]

/-- Uniform correction factor: promoting and storing in the same group
cancels exactly, so each group incurs at most one bound C. -/
theorem markedRawEdgeChargeSwapModifier_norm_le
    {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (V : J → ℝ) (hV : ∀ j, 0 < V j)
    {C : ℝ} (hC : 1 ≤ C) (hVC : ∀ j, V j ≤ C) (hiVC : ∀ j, (V j)⁻¹ ≤ C)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    ‖markedRawEdgeChargeSwapModifier V hZ s c‖ ≤ C ^ Fintype.card J := by
  unfold markedRawEdgeChargeSwapModifier
  rw [norm_prod]
  calc
    _ ≤ ∏ _j : J, C := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact norm_nonneg _
      · intro j _
        have hv : (V j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hV j).ne'
        by_cases hp : (c.promotions j).isSome
        · by_cases hs : c.store j
          · simpa [hp,hs,hv] using hC
          · simpa only [hp,hs,Bool.false_eq_true,ite_true,ite_false,mul_one,Complex.norm_real,
              Real.norm_of_nonneg (hV j).le] using hVC j
        · by_cases hs : c.store j
          · simpa only [hp,hs,Bool.false_eq_true,ite_true,ite_false,one_mul,Complex.norm_real,
              Real.norm_of_nonneg (inv_pos.mpr (hV j)).le] using hiVC j
          · simpa [hp,hs] using hC
    _ = _ := by simp

end
end ArtinMatthews
