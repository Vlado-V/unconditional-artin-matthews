module

public import ArtinMatthews.GiantSignedGhostConvergence
public import ArtinMatthews.GiantSignedGhostAbsoluteRow
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Countable individual moves of the original ghost row. Indexed old
deletions and ordered births are both retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedGhostMoves {P : Finset ℕ} (m : GiantSignedGroupMemory P) :=
  Σ _S : Finset (Fin m.1), Σ b : ℕ, Fin b → P

def giantSignedGhostMoveTarget {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (r : GiantSignedGhostMoves m) : GiantSignedGroupMemory P :=
  giantSignedGhostTarget m r.1 r.2.2

def giantSignedGhostMoveCoefficient {P : Finset ℕ} (ν : P → ℝ)
    (A C D : ℂ) (m : GiantSignedGroupMemory P) (r : GiantSignedGhostMoves m) : ℂ := by
  classical
  exact if r.1 ⊆ giantSignedGhostZeroIndices m then
    D ^ r.1.card * A ^ ((giantSignedGhostZeroIndices m).card - r.1.card) *
      (C ^ r.2.1 / (Nat.factorial r.2.1 : ℂ)) * ∏ i, (ν (r.2.2 i) : ℂ)
  else 0

theorem giantSignedGhostMoveCoefficient_norm {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (m : GiantSignedGroupMemory P) (r : GiantSignedGhostMoves m) :
    (‖giantSignedGhostMoveCoefficient ν A C D m r‖ : ℂ) =
      giantSignedGhostMoveCoefficient ν (‖A‖ : ℂ) (‖C‖ : ℂ) (‖D‖ : ℂ) m r := by
  classical
  unfold giantSignedGhostMoveCoefficient
  split_ifs
  · simp only [norm_mul, norm_pow, norm_div, norm_prod, Complex.norm_natCast,
      Complex.norm_real]
    simp_rw [Real.norm_of_nonneg (hν _)]
    push_cast
    rfl
  · simp only [norm_zero, Complex.ofReal_zero]

theorem giantSignedGhostMoves_summable_norm {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ) (_hB : 0 ≤ B) (_hv : 0 ≤ v)
    (hf : ∀ m, ‖f m‖ ≤ B * v ^ m.1) (m : GiantSignedGroupMemory P) :
    Summable (fun r : GiantSignedGhostMoves m =>
      ‖giantSignedGhostMoveCoefficient ν A C D m r * f (giantSignedGhostMoveTarget m r)‖) := by
  classical
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro S
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simp only [tsum_fintype]
  by_cases hz : S ⊆ giantSignedGhostZeroIndices m
  · let c := ‖D‖ ^ S.card * ‖A‖ ^ ((giantSignedGhostZeroIndices m).card - S.card)
    have hc : 0 ≤ c := mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _)
    apply ((giantSignedGhost_birthSeries_hasSum ν ‖C‖ v).summable.mul_left
      (c * (B * v ^ (m.1 - S.card)))).of_nonneg_of_le
    · intro _
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · intro b
      calc
        _ ≤ ∑ β : Fin b → P, c * (‖C‖ ^ b / (Nat.factorial b : ℝ)) *
            (∏ i, ν (β i)) * (B * v ^ (giantSignedGhostTarget m S β).1) := by
          apply Finset.sum_le_sum
          intro β _
          simp only [giantSignedGhostMoveCoefficient, giantSignedGhostMoveTarget, hz, ite_true,
            norm_mul, norm_pow, norm_div, norm_prod, Complex.norm_natCast, Complex.norm_real]
          simp_rw [Real.norm_of_nonneg (hν _)]
          exact mul_le_mul_of_nonneg_left (hf _)
            (mul_nonneg (mul_nonneg hc (div_nonneg (pow_nonneg (norm_nonneg _) _)
              (Nat.cast_nonneg _))) (Finset.prod_nonneg fun _ _ => hν _))
        _ = _ := by
          simp only [giantSignedGhostTarget_degree, pow_add, Finset.mul_sum,
            Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro β _
          dsimp only [c]
          ring
  · simp only [giantSignedGhostMoveCoefficient, hz, ite_false, zero_mul, norm_zero,
      Finset.sum_const_zero]
    exact summable_zero

theorem giantSignedGhostMoves_tsum {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ) (hB : 0 ≤ B) (hv : 0 ≤ v)
    (hf : ∀ m, ‖f m‖ ≤ B * v ^ m.1) (m : GiantSignedGroupMemory P) :
    (∑' r : GiantSignedGhostMoves m,
      giantSignedGhostMoveCoefficient ν A C D m r * f (giantSignedGhostMoveTarget m r)) =
      giantSignedGhostGroupApply ν A C D f m := by
  classical
  have hs := (giantSignedGhostMoves_summable_norm ν hν A C D f B v hB hv hf m).of_norm
  rw [hs.tsum_sigma]
  simp only [tsum_fintype]
  have hi (S : Finset (Fin m.1)) :
      (∑' r : Σ b : ℕ, Fin b → P,
        giantSignedGhostMoveCoefficient ν A C D m ⟨S, r⟩ *
          f (giantSignedGhostMoveTarget m ⟨S, r⟩)) =
        if S ⊆ giantSignedGhostZeroIndices m then
          D ^ S.card * A ^ ((giantSignedGhostZeroIndices m).card - S.card) *
            ∑' b, giantSignedGhostBirthContribution ν C m S f b else 0 := by
    rw [(hs.sigma_factor S).tsum_sigma]
    by_cases hz : S ⊆ giantSignedGhostZeroIndices m
    · simp only [tsum_fintype, giantSignedGhostMoveCoefficient, hz, ite_true,
        giantSignedGhostMoveTarget, giantSignedGhostBirthContribution, ← tsum_mul_left]
      congr 1
      funext b
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      ring
    · simp only [giantSignedGhostMoveCoefficient, hz, ite_false, zero_mul, tsum_zero]
  simp_rw [hi]
  have he : (Finset.univ : Finset (Finset (Fin m.1))).filter
      (fun S => S ⊆ giantSignedGhostZeroIndices m) = (giantSignedGhostZeroIndices m).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
  rw [← Finset.sum_filter, he]
  rfl

end
end ArtinMatthews
