module

public import ArtinMatthews.SpectralJNativeAmplitudes
public import ArtinMatthews.SpectralABLWhittakerUniqueness
public import ArtinMatthews.SpectralPrimitiveFourierCritical


set_option backward.privateInPublic true
@[expose] public section

/-! The bare native spectral side is independent of the auxiliary positive height. -/
namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped MatrixGroups BigOperators
noncomputable section

theorem gamma0BareCuspidalTerm_height_eq (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (i : Gamma0AllHeightSpectralIndex N) :
    gamma0BareCuspidalTerm N h r s Y hY m n hm hn i =
      gamma0BareCuspidalTerm N h r s Z hZ m n hm hn i := by
  unfold gamma0BareCuspidalTerm gamma0BareCuspidalAmplitude
  rw [gamma0ABLSourceRho_height_eq N i r Y Z hY hZ m hm,
    gamma0ABLSourceRho_height_eq N i s Y Z hY hZ n hn]

theorem gamma0BareEisensteinSourceCoefficient_height_ae (N : ℕ) [NeZero N]
    (a : Gamma0EisensteinCuspClasses N) (r : SL(2, ℤ))
    (Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z) (n : ℤ) (hn : n ≠ 0) :
    (fun t => gamma0BareEisensteinSourceCoefficient N a r Y hY n hn t) =ᵐ[volume]
      fun t => gamma0BareEisensteinSourceCoefficient N a r Z hZ n hn t := by
  filter_upwards [gamma0PrimitiveFourierAmplitude_height_critical_ae N
    (gamma0EisensteinCuspClassRepresentative N a) r Y Z hY hZ n hn] with t ht
  rw [gamma0BareEisensteinSourceCoefficient_half_amplitude,
    gamma0BareEisensteinSourceCoefficient_half_amplitude, ht]

theorem gamma0BareContinuousRhoIntegrand_height_ae (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (r s : SL(2, ℤ))
    (Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn =ᵐ[volume]
      gamma0BareContinuousRhoIntegrand N h r s Z hZ m n hm hn := by
  have hA : ∀ᵐ t ∂volume, ∀ a : Gamma0EisensteinCuspClasses N,
      gamma0BareEisensteinSourceCoefficient N a r Y hY m hm t =
        gamma0BareEisensteinSourceCoefficient N a r Z hZ m hm t :=
    ae_all_iff.mpr (fun a => gamma0BareEisensteinSourceCoefficient_height_ae N a r Y Z hY hZ m hm)
  have hB : ∀ᵐ t ∂volume, ∀ a : Gamma0EisensteinCuspClasses N,
      gamma0BareEisensteinSourceCoefficient N a s Y hY n hn t =
        gamma0BareEisensteinSourceCoefficient N a s Z hZ n hn t :=
    ae_all_iff.mpr (fun a => gamma0BareEisensteinSourceCoefficient_height_ae N a s Y Z hY hZ n hn)
  filter_upwards [hA, hB] with t hA hB
  unfold gamma0BareContinuousRhoIntegrand
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [hA a, hB a]

theorem gamma0BareSourceSpectralSide_height_eq (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (r s : SL(2, ℤ))
    (Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    gamma0BareSourceSpectralSide N h r s Y hY m n hm hn =
      gamma0BareSourceSpectralSide N h r s Z hZ m n hm hn := by
  have hC : (∑' i, gamma0BareCuspidalTerm N h r s Y hY m n hm hn i) =
      ∑' i, gamma0BareCuspidalTerm N h r s Z hZ m n hm hn i :=
    tsum_congr (gamma0BareCuspidalTerm_height_eq N h r s Y Z hY hZ m n hm hn)
  have hI :
      (∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn t) =
        ∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoIntegrand N h r s Z hZ m n hm hn t :=
    integral_congr_ae (ae_restrict_of_ae
      (gamma0BareContinuousRhoIntegrand_height_ae N h r s Y Z hY hZ m n hm hn))
  unfold gamma0BareSourceSpectralSide
  rw [hC, hI]

end
end ArtinMatthews
