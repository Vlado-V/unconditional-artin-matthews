module

public import ArtinMatthews.CubicThetaShiftedCorrelation
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Order.Interval.Finset.Box


set_option backward.privateInPublic true
@[expose] public section

/-! The integer-indexed paper sum agrees with the natural-indexed correlation,
because its source is supported on a strictly positive interval. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

def thetaShiftedIntegerTerm (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 : ℕ) (g : ℝ → ℂ) (n : ℤ) : ℂ :=
  idealThetaCoeff χ ((m1 : ℤ)*n+1).toNat * idealThetaCoeff χ ((m2 : ℤ)*n+1).toNat * g n

theorem thetaShiftedIntegerTerm_nat (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 : ℕ) (g : ℝ → ℂ) (n : ℕ) :
    thetaShiftedIntegerTerm χ m1 m2 g n =
      idealThetaCoeff χ (m1*n+1) * idealThetaCoeff χ (m2*n+1) * g n := by
  simp only [thetaShiftedIntegerTerm, ← Nat.cast_mul, ← Nat.cast_add_one,
    Int.toNat_natCast, Int.cast_natCast]

theorem thetaShiftedIntegerCorrelation_eq_nat (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 : ℕ) (T : ℝ) (hT : 0 < T) (g : ℝ → ℂ)
    (hg : Function.support g ⊆ Icc T (2*T)) :
    Summable (thetaShiftedIntegerTerm χ m1 m2 g) ∧
      (∑' n : ℤ, thetaShiftedIntegerTerm χ m1 m2 g n) = thetaShiftedCorrelation χ m1 m2 g := by
  have hpos : Summable (fun n : ℕ => thetaShiftedIntegerTerm χ m1 m2 g n) := by
    simpa only [thetaShiftedIntegerTerm_nat] using thetaShiftedCorrelation_summable χ m1 m2 T g hg
  have hzero (n : ℕ) : thetaShiftedIntegerTerm χ m1 m2 g (-(n+1)) = 0 := by
    have hz : g ((-(n+1) : ℤ) : ℝ) = 0 := by
      by_contra hn
      have hp := (hg hn).1
      push_cast at hp
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    simp only [thetaShiftedIntegerTerm, hz, mul_zero]
  have hneg : Summable (fun n : ℕ => thetaShiftedIntegerTerm χ m1 m2 g (-(n+1))) := by
    simp only [hzero, summable_zero]
  refine ⟨hpos.of_nat_of_neg_add_one hneg, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  simp only [hzero, tsum_zero, add_zero, thetaShiftedIntegerTerm_nat, thetaShiftedCorrelation]

end ArtinMatthews
