module

public import ArtinMatthews.GiantSignedGhostColumn
public import ArtinMatthews.GiantSignedGhostRowCauchy


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted Schur on all memory degrees for the literal ghost row. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {P : Finset ℕ} [∀ p : P, NeZero p.val]

theorem giantSignedGhostGroupApply_schur_real
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (v : ℝ) (hv : 0 < v)
    (hrow : ‖A‖ + ‖D‖ / v ≤ 1) (hcol : ‖A‖ + ‖C‖ / v ≤ 1)
    (f : GiantSignedGroupMemory P → ℂ) (hfs : GiantSignedGroupSymmetric f)
    (B u : ℝ) (hB : 0 ≤ B) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) :
    (∑' m, giantSignedGroupMemoryMass ν m * ‖giantSignedGhostGroupApply ν A C D f m‖ ^ 2) ≤
      Real.exp ((‖C‖ + ‖D‖) * (∑ p : P, ν p) * v) *
        ∑' m, giantSignedGroupMemoryMass ν m * ‖f m‖ ^ 2 := by
  let w : GiantSignedGroupMemory P → ℝ := fun m => v ^ m.1
  let g := giantSignedGhostCauchyTest f v
  let T := giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ g
  let R := Real.exp (‖C‖ * (∑ p : P, ν p) * v)
  let C' := Real.exp (‖D‖ * (∑ p : P, ν p) * v)
  have hg0 : ∀ m, 0 ≤ g m := giantSignedGhostCauchyTest_nonneg f v hv.le
  have hgb : ∀ m, g m ≤ B ^ 2 * (u ^ 2 / v) ^ m.1 :=
    giantSignedGhostCauchyTest_bound f B u v hv hf
  have hgc : ∀ m, ‖(g m : ℂ)‖ ≤ B ^ 2 * (u ^ 2 / v) ^ m.1 := by
    intro m
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hg0 m)] using hgb m
  have hgu : 0 < u ^ 2 / v := div_pos (sq_pos_of_pos hu) hv
  have hT0 : ∀ m, 0 ≤ T m :=
    giantSignedGhostPositiveApply_nonneg ν hν ‖A‖ ‖C‖ ‖D‖
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) g hg0
  let bT := B ^ 2 * Real.exp (‖(‖C‖ : ℂ)‖ * (∑ p : P, ν p) * (u ^ 2 / v))
  let uT := (u ^ 2 / v) * max 1 (‖(‖A‖ : ℂ)‖ + ‖(‖D‖ : ℂ)‖ / (u ^ 2 / v))
  have hT : ∀ m, ‖(T m : ℂ)‖ ≤ bT * uT ^ m.1 := by
    intro m
    rw [giantSignedGhostPositiveApply_coe]
    exact giantSignedGhostGroupApply_exponential_bound ν hν
      (‖A‖ : ℂ) (‖C‖ : ℂ) (‖D‖ : ℂ) (fun t => (g t : ℂ))
      (B ^ 2) (u ^ 2 / v) (sq_nonneg _) hgu hgc m
  have hwc : ∀ m : GiantSignedGroupMemory P, ‖(w m : ℂ)‖ ≤ 1 * v ^ m.1 := by
    intro m
    simp only [w, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hv.le _), one_mul, le_refl]
  have hsT := giantSignedGroupRealPairing_summable ν hν w T 1 bT v uT
    zero_le_one (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) hv.le
    (mul_nonneg hgu.le (le_trans zero_le_one (le_max_left _ _))) hwc hT
  have hlocal : ∀ m, giantSignedGroupMemoryMass ν m *
      ‖giantSignedGhostGroupApply ν A C D f m‖ ^ 2 ≤
      R * (giantSignedGroupMemoryMass ν m * w m * T m) := by
    intro m
    have hcauchy := giantSignedGhostGroupApply_weighted_cauchy ν hν A C D f B u v hB hu.le hv hf m
    have hp := giantSignedGhostPositiveApply_weight ν hν ‖A‖ ‖C‖ ‖D‖ v
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hv hrow m
    calc
      _ ≤ giantSignedGroupMemoryMass ν m *
          (giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ w m * T m) :=
        mul_le_mul_of_nonneg_left hcauchy (giantSignedGroupMemoryMass_nonneg ν hν m)
      _ ≤ giantSignedGroupMemoryMass ν m * ((w m * R) * T m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (hT0 m))
          (giantSignedGroupMemoryMass_nonneg ν hν m)
      _ = _ := by ring
  have hsR := hsT.mul_left R
  have hsL := hsR.of_nonneg_of_le
    (fun m => mul_nonneg (giantSignedGroupMemoryMass_nonneg ν hν m) (sq_nonneg _)) hlocal
  have hc := giantSignedGhostPositive_column_weight ν hν ‖A‖ ‖C‖ ‖D‖ v
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hv hcol g hg0
    (giantSignedGhostCauchyTest_symmetric f v hfs) (B ^ 2) (u ^ 2 / v)
    (sq_nonneg _) hgu hgb
  have heg : (∑' m, giantSignedGroupMemoryMass ν m * w m * g m) =
      ∑' m, giantSignedGroupMemoryMass ν m * ‖f m‖ ^ 2 := by
    apply tsum_congr
    intro m
    dsimp only [w, g, giantSignedGhostCauchyTest]
    field_simp [pow_ne_zero _ hv.ne']
  calc
    _ ≤ ∑' m, R * (giantSignedGroupMemoryMass ν m * w m * T m) :=
      hsL.tsum_le_tsum hlocal hsR
    _ = R * ∑' m, giantSignedGroupMemoryMass ν m * w m * T m := tsum_mul_left
    _ ≤ R * (C' * ∑' m, giantSignedGroupMemoryMass ν m * w m * g m) :=
      mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ = (R * C') * ∑' m, giantSignedGroupMemoryMass ν m * ‖f m‖ ^ 2 := by rw [heg, mul_assoc]
    _ = _ := by
      dsimp only [R, C']
      rw [← Real.exp_add]
      congr 2
      ring

theorem giantSignedGhostGroupApply_energy
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (v : ℝ) (hv : 0 < v)
    (hrow : ‖A‖ + ‖D‖ / v ≤ 1) (hcol : ‖A‖ + ‖C‖ / v ≤ 1)
    (f : GiantSignedGroupMemory P → ℂ) (hfs : GiantSignedGroupSymmetric f)
    (B u : ℝ) (hB : 0 ≤ B) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) :
    giantSignedGroupEnergy ν (giantSignedGhostGroupApply ν A C D f) ≤
      ENNReal.ofReal (Real.exp ((‖C‖ + ‖D‖) * (∑ p : P, ν p) * v)) *
        giantSignedGroupEnergy ν f := by
  have hgf := giantSignedGhostGroupApply_exponential_bound ν hν A C D f B u hB hu hf
  have hsout := giantSignedFock_energy_summable ν hν (giantSignedGhostGroupApply ν A C D f)
    (B * Real.exp (‖C‖ * (∑ p : P, ν p) * u))
    (u * max 1 (‖A‖ + ‖D‖ / u)) (mul_nonneg hB (Real.exp_nonneg _))
    (mul_nonneg hu.le (le_trans zero_le_one (le_max_left _ _))) hgf
  have hsin := giantSignedFock_energy_summable ν hν f B u hB hu.le hf
  unfold giantSignedGroupEnergy
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (giantSignedGroupMemoryMass_nonneg ν hν m) (sq_nonneg _)) hsout,
    ← ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (giantSignedGroupMemoryMass_nonneg ν hν m) (sq_nonneg _)) hsin,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    (giantSignedGhostGroupApply_schur_real ν hν A C D v hv hrow hcol f hfs B u hB hu hf)

end
end ArtinMatthews
