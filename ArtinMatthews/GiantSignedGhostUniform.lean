module

public import ArtinMatthews.GiantSignedGhostSchur
public import ArtinMatthews.GiantSignedGhostWeight
public import ArtinMatthews.GiantSignedGhostSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! One memory weight controls the original ghost and doubled births.
The energy constant depends on the zero-residue mass, not on memory degree. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

theorem giantSignedGhost_uniform_energy
    (aMax cMax dMax massMax : ℝ) (ha : aMax < 1)
    (hc : 0 ≤ cMax) (hd : 0 ≤ dMax) :
    ∃ v : ℝ, 1 < v ∧ ∀ (P : Finset ℕ) (_ : ∀ p : P, NeZero p.val)
      (ν : P → ℝ), (∀ p, 0 ≤ ν p) → (∑ p : P, ν p) ≤ massMax →
      ∀ A C D z : ℂ, ‖A‖ ≤ aMax → ‖C‖ ≤ cMax → ‖D‖ ≤ dMax → ‖z‖ ≤ 2 →
      ∀ (f : GiantSignedGroupMemory P → ℂ), GiantSignedGroupSymmetric f →
      ∀ B u : ℝ, 0 ≤ B → 0 < u → (∀ m, ‖f m‖ ≤ B * u ^ m.1) →
        giantSignedGroupEnergy ν (giantSignedGhostGroupApply ν A (z * C) D f) ≤
          ENNReal.ofReal (Real.exp ((2 * cMax + dMax) * massMax * v)) *
            giantSignedGroupEnergy ν f := by
  obtain ⟨v, hv, hvbound⟩ := giantSignedGhostWeight_exists aMax cMax dMax ha
  refine ⟨v, hv, ?_⟩
  intro P inst ν hν hmass A C D z hA hC hD hz f hfs B u hB hu hf
  let _ := inst
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  have hw := hvbound ‖A‖ ‖C‖ ‖D‖ hA
    (by simpa only [abs_of_nonneg (norm_nonneg _)] using hC)
    (by simpa only [abs_of_nonneg (norm_nonneg _)] using hD)
  simp only [abs_of_nonneg (norm_nonneg _)] at hw
  have hzc : ‖z * C‖ ≤ 2 * ‖C‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hcolumn : ‖A‖ + ‖z * C‖ / v ≤ 1 := by
    have hzv := div_le_div_of_nonneg_right hzc hv0.le
    linarith [hw.2]
  have he := giantSignedGhostGroupApply_energy ν hν A (z * C) D v hv0 hw.1.le hcolumn
    f hfs B u hB hu hf
  have hsum : 0 ≤ ∑ p : P, ν p := Finset.sum_nonneg (fun p _ => hν p)
  have hec : (‖z * C‖ + ‖D‖) * (∑ p : P, ν p) * v ≤
      (2 * cMax + dMax) * massMax * v := by
    apply mul_le_mul_of_nonneg_right _ hv0.le
    exact mul_le_mul
      (add_le_add (hzc.trans (mul_le_mul_of_nonneg_left hC (by norm_num))) hD)
      hmass hsum (add_nonneg (mul_nonneg (by norm_num) hc) hd)
  exact he.trans (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hec)) le_rfl)

theorem giantSignedGhostGroup_energy
    {P : Finset ℕ} [∀ p : P, NeZero p.val]
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (V q ρ v : ℝ) (hv : 0 < v)
    (hrow : |q / ρ ^ 2| + |-(1-q) / ρ| / v ≤ 1)
    (hcol : |q / ρ ^ 2| + |-(1-q) * V / ρ| / v ≤ 1)
    (f : GiantSignedGroupMemory P → ℂ) (hfs : GiantSignedGroupSymmetric f)
    (B u : ℝ) (hB : 0 ≤ B) (hu : 0 < u) (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) :
    giantSignedGroupEnergy ν (giantSignedGhostGroup ν V q ρ f) ≤
      ENNReal.ofReal (Real.exp ((|-(1-q) * V / ρ| + |-(1-q) / ρ|) *
        (∑ p : P, ν p) * v)) * giantSignedGroupEnergy ν f := by
  have he := giantSignedGhostGroupApply_energy ν hν ((q / ρ ^ 2 : ℝ) : ℂ)
    ((-(1-q) * V / ρ : ℝ) : ℂ) ((-(1-q) / ρ : ℝ) : ℂ) v hv
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hrow)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hcol) f hfs B u hB hu hf
  simpa only [giantSignedGhostGroup, Complex.norm_real, Real.norm_eq_abs] using he

end
end ArtinMatthews
