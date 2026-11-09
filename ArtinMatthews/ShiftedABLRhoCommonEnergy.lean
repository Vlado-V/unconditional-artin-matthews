module

public import ArtinMatthews.ShiftedABLRhoCommonTransforms
public import ArtinMatthews.ShiftedABLRhoCommonKBounds
public import ArtinMatthews.SpectralABLSourceTestBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine spectral symbols of the exact common spatial profile. -/

noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

theorem shiftedABLRhoCommonTest_tsupport_pos (a u : ℝ) (ha : 0 < a) :
    tsupport (shiftedABLRhoCommonTest a u) ⊆ Ioi (0 : ℝ) :=
  fun _ hx => (show 0 < a/3 by positivity).trans_le ((shiftedABLRhoCommonTest_tsupport a u ha) hx).1

def shiftedABLRhoCommonJEnergy (X u : ℝ) (hX : 0 < X) : SpectralEnergyTest :=
  let a := 4*Real.pi*X
  have ha : 0 < a := by dsimp only [a]; positivity
  spectralJClippedEnergyTest (shiftedABLRhoCommonTest a u)
    (shiftedABLRhoCommonTest_contDiff a u ha) (shiftedABLRhoCommonTest_compact a u ha)
    (shiftedABLRhoCommonTest_tsupport_pos a u ha)

def shiftedABLRhoCommonKEnergy (X u : ℝ) (hX : 0 < X) : SpectralEnergyTest :=
  let a := 4*Real.pi*X
  have ha : 0 < a := by dsimp only [a]; positivity
  spectralABLOppositeEnergyTest (shiftedABLRhoCommonTest a u)
    (shiftedABLRhoCommonTest_contDiff a u ha) (shiftedABLRhoCommonTest_compact a u ha)
    (shiftedABLRhoCommonTest_tsupport_pos a u ha)

theorem spectralABLPrincipalSymbolBound_mono {h : SpectralEnergyTest} {H K Z : ℝ}
    (hB : spectralABLPrincipalSymbolBound h H Z) (hK : H ≤ K) :
    spectralABLPrincipalSymbolBound h K Z := by
  intro t
  exact (hB t).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (spectralPrincipalDecayWeight_nonneg _ _)) (Real.cosh_pos _).le)

theorem spectralABLComplementarySymbolBound_mono {h : SpectralEnergyTest} {H K a : ℝ}
    (ha : 0 < a) (hB : spectralABLComplementarySymbolBound h H a) (hK : H ≤ K) :
    spectralABLComplementarySymbolBound h K a := by
  intro l hl hl₁
  have hcos : 0 ≤ Real.cos (Real.pi*Real.sqrt (1/4-(l : ℝ))) :=
    (show 0 ≤ Real.cos (Real.pi/4) by rw [Real.cos_pi_div_four]; positivity).trans
      (spectral_cosine_complementary_lower_of_gap hl)
  exact (hB l hl hl₁).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg ha.le _)) hcos)

theorem shiftedABLRhoCommonEnergy_bounds (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X u Z P : ℝ, ∀ hX : 0 < X, X ≤ B →
      1+|u| ≤ Z → 1 ≤ P → P⁻¹ ≤ X → Z ≤ P →
      let H := C*P^δ
      let hJ := shiftedABLRhoCommonJEnergy X u hX
      let hK := shiftedABLRhoCommonKEnergy X u hX
      (spectralABLPrincipalSymbolBound hJ H Z ∧ spectralABLComplementarySymbolBound hJ H (X/Z)) ∧
      (spectralABLPrincipalSymbolBound hK H Z ∧ spectralABLComplementarySymbolBound hK H (X/Z)) := by
  obtain ⟨C₁,hC₁,hJ⟩ := shiftedABLRhoCommonTest_conductor_estimates (4*Real.pi*B) δ (by positivity) hδ 4
  obtain ⟨C₂,hC₂,hK⟩ := shiftedABLRhoCommonTest_opposite_conductor_estimates B δ hB hδ 4
  let C := max (Real.pi*C₁) C₂
  refine ⟨C,hC₂.trans_le (le_max_right _ _),?_⟩
  intro X u Z P hX hXB hZ hP hPX hZP
  let a := 4*Real.pi*X
  let f := shiftedABLRhoCommonTest a u
  have ha : 0 < a := by dsimp only [a]; positivity
  have hZ₁ : 1 ≤ Z := le_trans (le_add_of_nonneg_right (abs_nonneg u)) hZ
  have haX : X ≤ a := by
    dsimp only [a]
    exact (one_mul X).symm.trans_le (mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hX.le)
  have hPδ : 0 ≤ P^δ := by positivity
  obtain ⟨hpJ,heJ⟩ := hJ a u Z P ha (by dsimp only [a]; gcongr) hZ hP (hPX.trans haX)
  obtain ⟨hpK,heK⟩ := hK X u Z P hX hXB hZ hP hPX hZP
  have h₁ := spectralJClippedEnergyTest_symbol_bounds f (shiftedABLRhoCommonTest_contDiff a u ha)
    (shiftedABLRhoCommonTest_compact a u ha) (shiftedABLRhoCommonTest_tsupport_pos a u ha)
    (H := C₁*P^δ) (Z := Z) (a := X/Z)
    (fun t => by simpa only [f,spectralPrincipalDecayWeight,mul_one_div] using hpJ t)
    (fun κ hκ hκ₁ => (heJ κ hκ hκ₁).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) ((div_le_self hX.le hZ₁).trans haX) (by linarith))
      (by positivity)))
  have h₂ := spectralABLOppositeEnergyTest_symbol_bounds f (shiftedABLRhoCommonTest_contDiff a u ha)
    (shiftedABLRhoCommonTest_compact a u ha) (shiftedABLRhoCommonTest_tsupport_pos a u ha)
    (H := C₂*P^δ) (Z := Z) (a := X/Z)
    (fun t => by simpa only [f,a,spectralPrincipalDecayWeight,mul_one_div] using hpK t) heK
  have hjC : Real.pi*(C₁*P^δ) ≤ C*P^δ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hPδ
  have hkC : C₂*P^δ ≤ C*P^δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hPδ
  exact ⟨⟨spectralABLPrincipalSymbolBound_mono h₁.1 hjC,
    spectralABLComplementarySymbolBound_mono (by positivity) h₁.2 hjC⟩,
    ⟨spectralABLPrincipalSymbolBound_mono h₂.1 hkC,
      spectralABLComplementarySymbolBound_mono (by positivity) h₂.2 hkC⟩⟩

end ArtinMatthews
