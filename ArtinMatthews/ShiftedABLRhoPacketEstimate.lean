module

public import ArtinMatthews.ShiftedABLRhoNativePacket
public import ArtinMatthews.ShiftedABLRhoCommonEnergy
public import ArtinMatthews.SpectralMixedPacketBound
public import ArtinMatthews.ShiftedABLRhoHolomorphicEstimate


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform spectral size of the literal separated signed circle block. -/

noncomputable section
open Set MeasureTheory OAI OAI.CubicEisenstein
open scoped MatrixGroups BigOperators ContDiff
namespace ArtinMatthews

def gamma0MixedPacketHolomorphicSize (N : ℕ) (B : ℝ) (n : ℤ) (S : ℝ) : ℝ :=
  Real.sqrt (S*(1+B/(N : ℝ)))*Real.sqrt (1+(n.natAbs : ℝ)/(N : ℝ))

theorem shiftedABLFullSeparatedSignedSum_spectral_size_bound (B₀ δ : ℝ)
    (hB₀ : 0 < B₀) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : SevenEighths.HeckeFamily.Character)
      (D m3 m4 F L : ℕ) [NeZero F], 0 < m3 → 0 < m4 → m3 ≠ m4 →
      (m3*m4).Coprime F → 0 < L →
      ∀ (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) (t Z : ℝ),
      let r := m3*m4
      let N := r*F
      let n := (m3 : ℤ)-(m4 : ℤ)
      let R := (2 : ℝ)^i.1
      let X := ablTheorem24BesselScale (3*(L : ℝ)/(F : ℝ)) R n.natAbs r F
      let P := ablTheorem24SpectralParameter (3*(L : ℝ)/(F : ℝ)) R Z n.natAbs r F
      let B := 4*Real.pi*R
      let S := ∑ ρ ∈ shiftedABLSourceRhoIndex m3 m4 d i,
        ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2
      X ≤ B₀ → X ≤ Z → 1+|t+shiftedABLRhoHeight z| ≤ Z →
      ‖shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t‖ ≤
        C*((F : ℝ)*Real.sqrt (r : ℝ))*P^δ*
          (gamma0MixedPacketPrincipalSize N B |cuspFourierFrequency 1 n| Z S+
            gamma0MixedPacketExceptionalSize N B n (X/Z) δ S+
            gamma0MixedPacketHolomorphicSize N B n S) := by
  obtain ⟨C₁,hC₁,hEnergy⟩ := shiftedABLRhoCommonEnergy_bounds B₀ δ hB₀ hδ
  obtain ⟨C₂,hC₂,hSpectral⟩ := gamma0MixedPacket_bound hδ
  obtain ⟨C₃,hC₃,hHolomorphic⟩ := shiftedABLRhoCommonTest_holomorphic_packet_bound B₀ hB₀
  let C := (4*Real.pi+4)*(C₂*C₁)+C₃
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro χ D m3 m4 F L inst hm3 hm4 hne hcop hL d i z t Z r N n R X P B S hXB hXZ hZ
  let u := t+shiftedABLRhoHeight z
  let a := X/Z
  let U := shiftedABLSourceRhoIndex m3 m4 d i
  let α := shiftedABLSourceRhoPacketCoefficient χ D m3 m4 d i z t
  let m (ρ : U) := ρ.val
  have hinj : Function.Injective m := Subtype.val_injective
  have hm (ρ : U) : m ρ ≠ 0 := shiftedABLSourceRhoIndex_ne_zero ρ
  have hn : n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hr : 0 < r := Nat.mul_pos hm3 hm4
  have hr₁ : 1 < r := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact lt_of_lt_of_le (by decide : 1 < 1*2) (Nat.mul_le_mul hm3 (by omega))
    · exact lt_of_lt_of_le (by decide : 1 < 2*1) (Nat.mul_le_mul (by omega) hm4)
  let _ : NeZero r := ⟨hr.ne'⟩
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hZ₁ : 1 ≤ Z := (le_add_of_nonneg_right (abs_nonneg _)).trans hZ
  obtain ⟨hX,hP₀,hPeq,hZP,hInv,_⟩ := shiftedABLRhoSpectralParameters (NeZero.pos F) hL
    (Int.natAbs_pos.mpr hn) hr hR hZ₁
  have hP : 1 ≤ P := hZ₁.trans hZP
  have hPδ : 1 ≤ P^δ := Real.one_le_rpow hP hδ.le
  have ha : 0 < a := div_pos hX (zero_lt_one.trans_le hZ₁)
  have ha₁ : a ≤ 1 := (div_le_one (zero_lt_one.trans_le hZ₁)).mpr hXZ
  have hB : 0 < B := by dsimp only [B]; positivity
  have hfreq (ρ : U) : |cuspFourierFrequency 1 (m ρ)| ≤ B :=
    shiftedABLRho_source_frequency_bound ρ
  have hp : 0 < |cuspFourierFrequency 1 n|/
      (gamma0CuspTrueWidth (r*F) (gamma0CuspOneOver F) : ℝ) :=
    div_pos (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn))
      (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos _ _))
  obtain ⟨Y,hY,hYL,hYR,hYE⟩ := gamma0MixedPacket_small_height_exists hB hp ha
  obtain ⟨a₀,b₀,hab⟩ := exists_atkin_bezout hcop
  let f := shiftedABLRhoCommonTest (4*Real.pi*X) u
  have hf : ContDiff ℝ ∞ f := shiftedABLRhoCommonTest_contDiff _ _ (by positivity)
  have hc : HasCompactSupport f := shiftedABLRhoCommonTest_compact _ _ (by positivity)
  have hp₀ : tsupport f ⊆ Ioi (0 : ℝ) := shiftedABLRhoCommonTest_tsupport_pos _ _ (by positivity)
  have hE := hEnergy X u Z P hX hXB hZ hP hInv hZP
  let Psize := gamma0MixedPacketPrincipalSize N B |cuspFourierFrequency 1 n| Z S
  let Esize := gamma0MixedPacketExceptionalSize N B n a δ S
  let Hsize := gamma0MixedPacketHolomorphicSize N B n S
  let T := (C₂*C₁)*P^δ*(Psize+Esize)
  let V := (F : ℝ)*Real.sqrt (r : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hPsize : 0 ≤ Psize := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hEsize : 0 ≤ Esize := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hHsize : 0 ≤ Hsize := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hC₄ : 4*(C₂*C₁) ≤ C := by
    dsimp only [C]
    nlinarith only [mul_nonneg Real.pi_pos.le (mul_nonneg hC₂.le hC₁.le),hC₃.le]
  have hCπ : (4*Real.pi)*(C₂*C₁) ≤ C := by
    dsimp only [C]
    nlinarith only [mul_nonneg hC₂.le hC₁.le,hC₃.le]
  have hC₃' : C₃ ≤ C := le_add_of_nonneg_left (by positivity)
  have hEq := shiftedABLFullSeparatedSignedSum_eq_nativePacket χ D m3 m4 F L hcop hL hm3 hm4 hne d i z t
  change _ = gamma0MixedSourcePacketSum f r F hcop n U.attach α m at hEq
  have hSα : (∑ ρ ∈ U.attach, ‖α ρ‖^2) = S :=
    shiftedABLSourceRhoPacketCoefficient_sq χ D m3 m4 d i z t
  have hPacket (h : SpectralEnergyTest) (hP : spectralABLPrincipalSymbolBound h (C₁*P^δ) Z)
      (hE : spectralABLComplementarySymbolBound h (C₁*P^δ) a) :
      ‖gamma0MixedPacketSpectralSide (r*F) h (gamma0CuspOneOver F) Y hY n hn U.attach α m hm‖ ≤ T := by
    have hPck := hSpectral r F hcop h U.attach α m hm hinj n hn hB hZ₁ ha ha₁
      (by positivity : 0 ≤ C₁*P^δ) hY hYL hYR hYE hfreq hP hE
    rw [hSα] at hPck
    exact hPck.trans_eq (by dsimp only [T,Psize,Esize]; ring)
  rw [hEq]
  by_cases hSign : i.2 = decide (n < 0)
  · have hPos (ρ : U) (_ : ρ ∈ U.attach) : 0 < m ρ*n :=
      shiftedABLSourceRhoIndex_sameSign ρ n hn hSign
    have hTrace := gamma0MixedSourcePacketSum_sameSign_trace f hf hc hp₀ r F hr₁ hcop hab Y hY
      n hn U.attach α m hm hPos
    let m₀ (ρ : U) := sourceJHolomorphicIndexMagnitude (m ρ) (hm ρ)
    let n₀ := sourceJHolomorphicIndexMagnitude n hn
    let Holo := sourceJHolomorphicMixedPacketSeries f r F hab (decide (n < 0)) U.attach α m₀ n₀
    have hInj : Function.Injective m₀ := shiftedABLSourceRhoIndex_magnitude_injective
    have hMag (ρ : U) (_ : ρ ∈ U.attach) : (m₀ ρ : ℝ) ≤ B := by
      change ((m ρ).natAbs : ℝ) ≤ B
      refine (shiftedABLRhoSignedBlock_band ρ.property).2.2.trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (zero_le_one.trans hR)
    have hHolo := (hHolomorphic X u hX hXB r F hcop hab (decide (n < 0))
      U.attach α m₀ n₀ B hB hInj.injOn hMag).2.2
    rw [hSα,mul_assoc C₃] at hHolo
    change ‖Holo‖ ≤ C₃*Hsize at hHolo
    let J := gamma0MixedPacketSpectralSide (r*F) (shiftedABLRhoCommonJEnergy X u hX)
      (gamma0CuspOneOver F) Y hY n hn U.attach α m hm
    have hJ : ‖J‖ ≤ T := hPacket _ hE.1.1 hE.1.2
    change gamma0MixedSourcePacketSum f r F hcop n U.attach α m =
      gamma0MixedSourceCompensation r F b₀ n*(4*J+Holo) at hTrace
    rw [hTrace,norm_mul,gamma0MixedSourceCompensation_norm]
    change V*‖4*J+Holo‖ ≤ C*V*P^δ*(Psize+Esize+Hsize)
    have hJ₄ : ‖(4 : ℂ)*J‖ ≤ C*P^δ*(Psize+Esize) := by
      rw [norm_mul,show ‖(4 : ℂ)‖ = 4 from Complex.norm_natCast 4]
      calc
        _ ≤ 4*T := mul_le_mul_of_nonneg_left hJ (by norm_num)
        _ = (4*(C₂*C₁))*P^δ*(Psize+Esize) := by dsimp only [T]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₄ (by positivity))
          (add_nonneg hPsize hEsize)
    have hHol : ‖Holo‖ ≤ C*P^δ*Hsize := hHolo.trans
      (mul_le_mul_of_nonneg_right (hC₃'.trans (le_mul_of_one_le_right hC.le hPδ)) hHsize)
    calc
      _ ≤ V*(C*P^δ*(Psize+Esize)+C*P^δ*Hsize) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hJ₄ hHol)) hV
      _ = _ := by ring
  · have hNeg (ρ : U) (_ : ρ ∈ U.attach) : m ρ*n < 0 :=
      shiftedABLSourceRhoIndex_oppositeSign ρ n hn hSign
    have hTrace := gamma0MixedSourcePacketSum_opposite_trace f hf hc hp₀ r F hr₁ hcop hab Y hY
      n hn U.attach α m hm hNeg
    let K := gamma0MixedPacketSpectralSide (r*F) (shiftedABLRhoCommonKEnergy X u hX)
      (gamma0CuspOneOver F) Y hY n hn U.attach α m hm
    have hK : ‖K‖ ≤ T := hPacket _ hE.2.1 hE.2.2
    change gamma0MixedSourcePacketSum f r F hcop n U.attach α m =
      (4*(Real.pi : ℂ))*gamma0MixedSourceCompensation r F b₀ n*K at hTrace
    rw [hTrace,norm_mul,norm_mul,norm_mul,gamma0MixedSourceCompensation_norm,
      show ‖(4 : ℂ)‖ = 4 from Complex.norm_natCast 4,Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    change (4*Real.pi)*V*‖K‖ ≤ C*V*P^δ*(Psize+Esize+Hsize)
    calc
      _ ≤ (4*Real.pi)*V*T := mul_le_mul_of_nonneg_left hK (by positivity)
      _ = ((4*Real.pi)*(C₂*C₁))*V*P^δ*(Psize+Esize) := by dsimp only [T]; ring
      _ ≤ C*V*P^δ*(Psize+Esize) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCπ hV) (by positivity)) (add_nonneg hPsize hEsize)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hHsize) (by positivity)

end ArtinMatthews
