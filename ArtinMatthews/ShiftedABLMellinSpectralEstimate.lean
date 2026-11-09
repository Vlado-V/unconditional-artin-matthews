module

public import ArtinMatthews.ShiftedABLRhoPacketEstimate
public import ArtinMatthews.ShiftedABLRhoFourierBound
public import ArtinMatthews.ShiftedABLSourceSpectralPower
public import ArtinMatthews.SpectralABLSourceSpectralJoin


set_option backward.privateInPublic true
@[expose] public section

/-! The original signed circle sum with its exact q-independent
coefficient packet and unrestricted Mellin heights. -/

noncomputable section
open Set MeasureTheory OAI OAI.CubicEisenstein
open scoped BigOperators
namespace ArtinMatthews

theorem shiftedABLMellinSignedSum_source_spectral_bound (B₀ ν : ℝ) (hB₀ : 0 < B₀) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : SevenEighths.HeckeFamily.Character)
      (D m3 m4 F L : ℕ) [NeZero F], 0 < m3 → 0 < m4 → m3 ≠ m4 →
      (m3*m4).Coprime F → 0 < L → (F : ℝ) ≤ 3*(L : ℝ) →
      ∀ (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ),
      let r := m3*m4
      let N := r*F
      let n := shiftedABLFirstIndex m3 m4
      let R := (2 : ℝ)^i.1
      let X := ablTheorem24BesselScale (3*(L : ℝ)/(F : ℝ)) R n r F
      let P₀ := shiftedABLRhoConductorBase L n r R
      let G := Real.sqrt ((n : ℝ)*(Nat.gcd N n : ℝ))
      let S := ∑ ρ ∈ shiftedABLSourceRhoIndex m3 m4 d i,
        ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2
      X ≤ B₀ → ∀ V : ℝ, 1 ≤ V → (n : ℝ)*X ≤ V*G →
      ‖shiftedABLMellinSignedSum χ D m3 m4 F r L d i z‖ ≤
        C*((F : ℝ)*Real.sqrt (r : ℝ))*P₀^ν*Real.sqrt V*(1+‖z.1‖+‖z.2‖)^4*
          Real.sqrt S*Real.sqrt (1+R/(N : ℝ))*Real.sqrt (1+G/(X*(N : ℝ))) := by
  let δ := min (ν/4) (1/4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδν : (5/2)*δ ≤ ν := by
    have h := min_le_left (ν/4) (1/4 : ℝ)
    dsimp only [δ]
    linarith
  have hδ₁ : (5/2)*δ ≤ 1 := by
    have h := min_le_right (ν/4) (1/4 : ℝ)
    dsimp only [δ]
    linarith
  obtain ⟨C₁,hC₁,hPacket⟩ := shiftedABLFullSeparatedSignedSum_spectral_size_bound B₀ δ hB₀ hδ
  let B₁ := max 1 B₀
  have hB₁ : 1 ≤ B₁ := le_max_left _ _
  let M := shiftedABLRhoFourierMoment 4
  have hM : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  have hJ : 0 < spectralABLSourceJoinConstant := by
    unfold spectralABLSourceJoinConstant
    positivity
  let K := 4*C₁*spectralABLSourceJoinConstant*B₁^4
  have hK : 0 < K := by dsimp only [K]; positivity
  let C := (16*M+1)*K
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro χ D m3 m4 F L inst hm3 hm4 hne hcop hL hQ d i z r N n R X P₀ G S hXB V hV hnX
  let nZ := (m3 : ℤ)-(m4 : ℤ)
  have hn : 0 < n := Int.natAbs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
  have hr : 0 < r := Nat.mul_pos hm3 hm4
  have hF : 0 < F := NeZero.pos F
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hN : 0 < (N : ℝ) := by dsimp only [N]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hA : 0 ≤ R/(N : ℝ) := by positivity
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  obtain ⟨hX,hP₀,_,_,_,_⟩ := shiftedABLRhoSpectralParameters (Z := 1) hF hL hn hr hR le_rfl
  have hB : 0 ≤ G/(X*(N : ℝ)) := by positivity
  let V₀ := ((F : ℝ)*Real.sqrt (r : ℝ))*P₀^ν*Real.sqrt V*Real.sqrt S*
    Real.sqrt (1+R/(N : ℝ))*Real.sqrt (1+G/(X*(N : ℝ)))
  have hV₀ : 0 ≤ V₀ := by dsimp only [V₀]; positivity
  have hPoint (t : ℝ) : ‖shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t‖ ≤
      (K*V₀)*(1+‖t+shiftedABLRhoHeight z‖)^4 := by
    let u := t+shiftedABLRhoHeight z
    let Z := B₁*(1+|u|)
    have hZ : 1+|u| ≤ Z := le_mul_of_one_le_left (by positivity) hB₁
    have hZ₁ : 1 ≤ Z := (le_add_of_nonneg_right (abs_nonneg _)).trans hZ
    have hXZ : X ≤ Z := (hXB.trans (le_max_right _ _)).trans
      (le_mul_of_one_le_right (zero_le_one.trans hB₁) (le_add_of_nonneg_right (abs_nonneg _)))
    let P := ablTheorem24SpectralParameter (3*(L : ℝ)/(F : ℝ)) R Z n r F
    obtain ⟨_,_,hPeq,_,_,hInv⟩ := shiftedABLRhoSpectralParameters hF hL hn hr hR hZ₁
    have hsz := (ablTheorem24_source_spectral_budget hF hn hr hQ hR hZ₁ hX hV hS hδ.le hInv hnX).2
    have hPkt := hPacket χ D m3 m4 F L hm3 hm4 hne hcop hL d i z t Z hXB hXZ hZ
    let Qsize := gamma0MixedPacketPrincipalSize N (4*Real.pi*R) |cuspFourierFrequency 1 nZ| Z S+
      gamma0MixedPacketExceptionalSize N (4*Real.pi*R) nZ (X/Z) δ S+
      gamma0MixedPacketHolomorphicSize N (4*Real.pi*R) nZ S
    change ‖shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t‖ ≤
      C₁*((F : ℝ)*Real.sqrt (r : ℝ))*P^δ*Qsize at hPkt
    have hsz' : Qsize ≤
        2*spectralABLSourceJoinConstant*(1+P^(3*δ/2))*Real.sqrt (Z*V)*
          Real.sqrt S*Real.sqrt (Z^2+R/(N : ℝ))*Real.sqrt (Z^2+G*Z/(X*(N : ℝ))) := by
      simpa only [Qsize,gamma0MixedPacketPrincipalSize,gamma0MixedPacketExceptionalSize,
        gamma0MixedPacketExceptionalWeight,gamma0MixedPacketHolomorphicSize,
        spectralABL_frequency_abs_natAbs,N,X,P,G,n,nZ,shiftedABLFirstIndex,← mul_div_assoc] using hsz
    have hPow := spectralABL_source_power_absorb hP₀ hZ₁ (zero_le_one.trans hV) hS hA hB
      hδ.le hδν hδ₁
    dsimp only at hPow
    rw [← hPeq,show G/(X*(N : ℝ))*Z = G*Z/(X*(N : ℝ)) by ring] at hPow
    have hP : 0 < P := by
      dsimp only [P]
      rw [hPeq]
      exact mul_pos (zero_lt_one.trans_le hP₀) (zero_lt_one.trans_le hZ₁)
    calc
      _ ≤ C₁*((F : ℝ)*Real.sqrt (r : ℝ))*P^δ*Qsize := hPkt
      _ ≤ C₁*((F : ℝ)*Real.sqrt (r : ℝ))*P^δ*
          (2*spectralABLSourceJoinConstant*(1+P^(3*δ/2))*Real.sqrt (Z*V)*
            Real.sqrt S*Real.sqrt (Z^2+R/(N : ℝ))*Real.sqrt (Z^2+G*Z/(X*(N : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsz' (by positivity)
      _ = (2*C₁*spectralABLSourceJoinConstant*((F : ℝ)*Real.sqrt (r : ℝ)))*
          (P^δ*(1+P^(3*δ/2))*Real.sqrt (Z*V)*Real.sqrt S*
            Real.sqrt (Z^2+R/(N : ℝ))*Real.sqrt (Z^2+G*Z/(X*(N : ℝ)))) := by ring
      _ ≤ (2*C₁*spectralABLSourceJoinConstant*((F : ℝ)*Real.sqrt (r : ℝ)))*
          (2*P₀^ν*Real.sqrt V*Real.sqrt S*Real.sqrt (1+R/(N : ℝ))*
            Real.sqrt (1+G/(X*(N : ℝ)))*Z^4) :=
        mul_le_mul_of_nonneg_left hPow (by positivity)
      _ = _ := by
        dsimp only [K,V₀,Z,u]
        rw [Real.norm_eq_abs,mul_pow]
        ring
  have h := shiftedABLMellinSignedSum_norm_le_of_full_separated χ D m3 m4 F r L hne hF hr hL
    hcop d i z 4 (mul_nonneg hK.le hV₀) hPoint
  have hConst : (2 : ℝ)^4*M*K ≤ C := by
    dsimp only [C]
    norm_num
    nlinarith only [hK.le]
  calc
    _ ≤ (2 : ℝ)^4*M*(K*V₀)*(1+‖z.1‖+‖z.2‖)^4 := h
    _ = ((2 : ℝ)^4*M*K)*V₀*(1+‖z.1‖+‖z.2‖)^4 := by ring
    _ ≤ C*V₀*(1+‖z.1‖+‖z.2‖)^4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hConst hV₀) (by positivity)
    _ = _ := by dsimp only [V₀]; ring

end ArtinMatthews
