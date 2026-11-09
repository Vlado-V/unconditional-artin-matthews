module

public import ArtinMatthews.GiantSignedGhostMoves
public import ArtinMatthews.GiantSignedGhostPositiveApply


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted Cauchy for the actual unbounded ghost row. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedGhostMoves_norm_weight_summable {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (F : GiantSignedGroupMemory P → ℝ) (hF0 : ∀ m, 0 ≤ F m)
    (B u : ℝ) (hB : 0 ≤ B) (hu : 0 ≤ u)
    (hF : ∀ m, F m ≤ B * u ^ m.1) (m : GiantSignedGroupMemory P) :
    Summable (fun r : GiantSignedGhostMoves m =>
      ‖giantSignedGhostMoveCoefficient ν A C D m r‖ * F (giantSignedGhostMoveTarget m r)) := by
  apply Complex.summable_ofReal.mp
  have hs := (giantSignedGhostMoves_summable_norm ν hν
    (‖A‖ : ℂ) (‖C‖ : ℂ) (‖D‖ : ℂ) (fun t => (F t : ℂ)) B u hB hu
    (fun t => by simpa only [Complex.norm_real, Real.norm_of_nonneg (hF0 t)] using hF t) m).of_norm
  simpa only [Complex.ofReal_mul, giantSignedGhostMoveCoefficient_norm ν hν A C D m] using hs

theorem giantSignedGhostMoves_norm_weight_tsum {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (F : GiantSignedGroupMemory P → ℝ) (hF0 : ∀ m, 0 ≤ F m)
    (B u : ℝ) (hB : 0 ≤ B) (hu : 0 ≤ u)
    (hF : ∀ m, F m ≤ B * u ^ m.1) (m : GiantSignedGroupMemory P) :
    (∑' r : GiantSignedGhostMoves m,
      ‖giantSignedGhostMoveCoefficient ν A C D m r‖ * F (giantSignedGhostMoveTarget m r)) =
      giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ F m := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, giantSignedGhostPositiveApply_coe]
  simp_rw [Complex.ofReal_mul, giantSignedGhostMoveCoefficient_norm ν hν A C D m]
  exact giantSignedGhostMoves_tsum ν hν (‖A‖ : ℂ) (‖C‖ : ℂ) (‖D‖ : ℂ)
    (fun t => (F t : ℂ)) B u hB hu
    (fun t => by simpa only [Complex.norm_real, Real.norm_of_nonneg (hF0 t)] using hF t) m

theorem giantSignedGhostGroupApply_weighted_cauchy {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f : GiantSignedGroupMemory P → ℂ) (B u v : ℝ)
    (hB : 0 ≤ B) (hu : 0 ≤ u) (hv : 0 < v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (m : GiantSignedGroupMemory P) :
    ‖giantSignedGhostGroupApply ν A C D f m‖ ^ 2 ≤
      giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ (fun t => v ^ t.1) m *
        giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ (giantSignedGhostCauchyTest f v) m := by
  let c := giantSignedGhostMoveCoefficient ν A C D m
  let target := giantSignedGhostMoveTarget m
  have hc := (giantSignedGhostMoves_summable_norm ν hν A C D f B u hB hu hf m).of_norm
  have hw := giantSignedGhostMoves_norm_weight_summable ν hν A C D
    (fun t => v ^ t.1) (fun _ => pow_nonneg hv.le _) 1 v zero_le_one hv.le
    (fun _ => by simp only [one_mul]; exact le_rfl) m
  have hg := giantSignedGhostMoves_norm_weight_summable ν hν A C D
    (giantSignedGhostCauchyTest f v) (giantSignedGhostCauchyTest_nonneg f v hv.le)
    (B ^ 2) (u ^ 2 / v) (sq_nonneg _) (div_nonneg (sq_nonneg _) hv.le)
    (giantSignedGhostCauchyTest_bound f B u v hv hf) m
  have hcg : Summable (fun r : GiantSignedGhostMoves m =>
      ‖c r‖ * ‖f (target r)‖ ^ 2 / v ^ (target r).1) := by
    simpa only [giantSignedGhostCauchyTest, mul_div_assoc] using hg
  have h := countableWeightedCauchy c (fun r => f (target r))
    (fun r => v ^ (target r).1) (fun r => pow_pos hv _) hc hw hcg
  rw [giantSignedGhostMoves_tsum ν hν A C D f B u hB hu hf m] at h
  rw [giantSignedGhostMoves_norm_weight_tsum ν hν A C D
    (fun t => v ^ t.1) (fun _ => pow_nonneg hv.le _) 1 v zero_le_one hv.le
    (fun _ => by simp only [one_mul]; exact le_rfl) m] at h
  have he := giantSignedGhostMoves_norm_weight_tsum ν hν A C D
    (giantSignedGhostCauchyTest f v) (giantSignedGhostCauchyTest_nonneg f v hv.le)
    (B ^ 2) (u ^ 2 / v) (sq_nonneg _) (div_nonneg (sq_nonneg _) hv.le)
    (giantSignedGhostCauchyTest_bound f B u v hv hf) m
  have he' : (∑' r : GiantSignedGhostMoves m,
      ‖c r‖ * ‖f (target r)‖ ^ 2 / v ^ (target r).1) =
      giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ (giantSignedGhostCauchyTest f v) m := by
    simpa only [c, target, giantSignedGhostCauchyTest, mul_div_assoc] using he
  rw [he'] at h
  exact h

end
end ArtinMatthews
