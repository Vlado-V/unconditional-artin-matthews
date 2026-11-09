module

public import ArtinMatthews.ShiftedABLRhoCommonTransforms
public import ArtinMatthews.ShiftedABLRhoSourcePacket
public import ArtinMatthews.SpectralABLSameCuspWeightedSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Literal source scales and frequency bounds for the common packet. -/

noncomputable section
open Set OAI.CubicEisenstein
namespace ArtinMatthews

def shiftedABLRhoConductorBase (L n r : ℕ) (R : ℝ) : ℝ :=
  3*(L : ℝ)*R*(n : ℝ)*(r : ℝ)

theorem shiftedABLRhoSpectralParameters {F L n r : ℕ} {R Z : ℝ}
    (hF : 0 < F) (hL : 0 < L) (hn : 0 < n) (hr : 0 < r) (hR : 1 ≤ R) (hZ : 1 ≤ Z) :
    let X := ablTheorem24BesselScale (3*(L : ℝ)/(F : ℝ)) R n r F
    let P := ablTheorem24SpectralParameter (3*(L : ℝ)/(F : ℝ)) R Z n r F
    let P₀ := shiftedABLRhoConductorBase L n r R
    0 < X ∧ 1 ≤ P₀ ∧ P = P₀*Z ∧ Z ≤ P ∧ P⁻¹ ≤ X ∧ X⁻¹ ≤ P := by
  intro X P P₀
  have hF₀ : 0 < (F : ℝ) := Nat.cast_pos.mpr hF
  have hL₁ : 1 ≤ (L : ℝ) := by exact_mod_cast hL
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hr₁ : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hX : 0 < X := by dsimp only [X,ablTheorem24BesselScale]; positivity
  have hP₀ : 1 ≤ P₀ := by
    unfold P₀ shiftedABLRhoConductorBase
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hL₁) hR) hn₁) hr₁
  have hP : P = P₀*Z := by
    dsimp only [P,P₀,shiftedABLRhoConductorBase,ablTheorem24SpectralParameter]
    field_simp [hF₀.ne'] <;> ring
  have hZP : Z ≤ P := hP ▸ le_mul_of_one_le_left (zero_le_one.trans hZ) hP₀
  have hPpos : 0 < P := zero_lt_one.trans_le (hZ.trans hZP)
  have hInv : P⁻¹ ≤ X := shiftedABLDyadicRadialParameter_inv_le_scale hF hL hn hr hR hZ
  exact ⟨hX,hP₀,hP,hZP,hInv,(inv_le_comm₀ hX hPpos).mpr hInv⟩

theorem shiftedABLRho_source_frequency_bound {m3 m4 : ℕ} {d : ℕ × ℕ} {i : ℕ × Bool}
    (ρ : shiftedABLSourceRhoIndex m3 m4 d i) :
    |cuspFourierFrequency 1 ρ.val| ≤ 4*Real.pi*(2 : ℝ)^i.1 := by
  have h := spectralABL_diagonal_argument_scale ρ.val
  have hB := (shiftedABLRhoSignedBlock_band ρ.property).2.2
  have hm := mul_le_mul_of_nonneg_left hB (show 0 ≤ 4*Real.pi by positivity)
  linarith

theorem spectralABL_frequency_abs_natAbs (n : ℤ) :
    |cuspFourierFrequency 1 n| = 2*Real.pi*(n.natAbs : ℝ) := by
  linarith only [spectralABL_diagonal_argument_scale n]

end ArtinMatthews
