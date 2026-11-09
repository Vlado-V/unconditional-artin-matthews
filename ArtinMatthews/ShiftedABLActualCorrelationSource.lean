module

public import ArtinMatthews.ShiftedABLCorrelationSourceJoin
public import ArtinMatthews.ShiftedABLMellinSpectralEstimate


set_option backward.privateInPublic true
@[expose] public section

/-! Specialization of the signed spectral theorem to the original
shifted correlation, retaining its physical theta coefficients. -/

noncomputable section
open OAI UpperHalfPlane
open scoped BigOperators MatrixGroups
namespace ArtinMatthews

theorem shiftedABL_signedSpectralInput : ShiftedABLSignedSpectralInput := by
  intro B ν hB hν
  obtain ⟨C,hC,hbound⟩ := shiftedABLMellinSignedSum_source_spectral_bound B ν hB hν
  refine ⟨4,C,hC,?_⟩
  intro χ D m3 m4 F L instF instD hm3 hm4 hne hcop hL hQ d i r n R Q X G P₀ hXB V hV hnX z
  have hF : (F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne F)
  have heX : ablTheorem24BesselScale (Q/(F : ℝ)) R n r F = X := by
    dsimp only [X,ablTheorem24BesselScale]
    congr 1
    field_simp [hF] <;> ring
  have hx : ablTheorem24BesselScale (Q/(F : ℝ)) R n r F ≤ B := heX.trans_le hXB
  have hnx : (n : ℝ)*ablTheorem24BesselScale (Q/(F : ℝ)) R n r F ≤ V*G := by
    rw [heX]
    exact hnX
  have h := hbound χ D m3 m4 F L hm3 hm4 hne hcop hL hQ d i z hx V hV hnx
  let S := ∑ ρ ∈ shiftedABLSourceRhoIndex m3 m4 d i,
    ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2
  change ‖shiftedABLMellinSignedSum χ D m3 m4 F r L d i z‖ ≤
    C*((F : ℝ)*Real.sqrt (r : ℝ))*P₀^ν*Real.sqrt V*(1+‖z.1‖+‖z.2‖)^4*
      Real.sqrt S*Real.sqrt (1+R/((r*F : ℕ) : ℝ))*
      Real.sqrt (1+G/(ablTheorem24BesselScale (Q/(F : ℝ)) R n r F*((r*F : ℕ) : ℝ))) at h
  rw [heX] at h
  simpa only [Real.norm_eq_abs,Nat.cast_mul,mul_assoc,S,shiftedABLSourceRhoIndex] using h

theorem shiftedABL_correlationSource
    (N : ℕ) [NeZero N] (hN : 3 ∣ N)
    (f : CuspForm (cubicThetaKernel N) 1) (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ k, (qExpansion 1 f).coeff k = idealThetaCoeff χ k) :
    ShiftedABLCorrelationSource N χ :=
  shiftedABL_correlationSource_of_signed_spectral shiftedABL_signedSpectralInput N hN f χ hcoeff

theorem cubicNumerator_shiftedABLCorrelationSource
    (a : ℤ) (ha : a ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3=(a : OAI.CubicFirstMoment.Eisenstein)) :
    ShiftedABLCorrelationSource (cubicNumeratorThetaLevel a)
      (cubicNumeratorHeckeCharacter a ha) :=
  cubicNumerator_shiftedABLCorrelationSource_of_signed_spectral shiftedABL_signedSpectralInput a ha hnoncube

end ArtinMatthews
