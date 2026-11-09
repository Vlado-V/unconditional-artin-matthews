module

public import ArtinMatthews.SpectralInfinityComplementaryCusp
public import ArtinMatthews.SpectralInfinityContinuousPacket
public import ArtinMatthews.SpectralInfinityResidualPacket
public import ArtinMatthews.SpectralJNativeAmplitudes


set_option backward.privateInPublic true
@[expose] public section

/-! Actual coefficients of a finite packet at infinity paired with
one frequency at the other chart. The terms use the source rho scale. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0MixedPacketCuspidalTerm {ι : Type*} (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (i : Gamma0AllHeightSpectralIndex N) : ℂ :=
  gamma0CuspidalTestSymbol N h i *
    (gamma0CuspUnitAmplitude N i b Y hY n hn *
      star (gamma0InfinityCuspPacketAmplitude N i v α m hm Y hY))/4

def gamma0MixedPacketContinuousIntegrand {ι : Type*} (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0) (t : ℝ) : ℂ :=
  (spectralContinuousTestSymbol h t *
    ∑ a : Gamma0EisensteinCuspClasses N, gamma0PrimitiveFourierAmplitude N
      (gamma0EisensteinCuspClassRepresentative N a) b Y hY n hn (eisensteinCriticalPoint t) *
        star (gamma0InfinityContinuousPacketFourier N v α m hm Y hY a t))/4

def gamma0MixedPacketResidualTerm {ι : Type*} (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (b : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) : ℂ :=
  h l*(((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j b n hn) *
    star (gamma0InfinityResidualPacketRho N l j v α m hm))

private theorem conj_packet {ι : Type*} (v : Finset ι) (α A : ι → ℂ) :
    star (∑ j ∈ v, star (α j)*A j) = ∑ j ∈ v, α j*star (A j) := by
  change (starRingEnd ℂ) (∑ j ∈ v, (starRingEnd ℂ) (α j)*A j) = _
  simp only [map_sum, map_mul, starRingEnd_apply, star_star]

theorem gamma0MixedPacketCuspidalTerm_eq_sum {ι : Type*} (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (i : Gamma0AllHeightSpectralIndex N) :
    gamma0MixedPacketCuspidalTerm N h b Y hY n hn v α m hm i =
      ∑ j ∈ v, α j*gamma0BareCuspidalTerm N h b 1 Y hY n (m j) hn (hm j) i := by
  unfold gamma0MixedPacketCuspidalTerm gamma0InfinityCuspPacketAmplitude gamma0BareCuspidalTerm
  simp_rw [gamma0BareCuspidalAmplitude_half_unit]
  rw [conj_packet,Finset.mul_sum,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [show gamma0CuspUnitAmplitude N i 1 Y hY (m j) (hm j) =
      gamma0CuspBesselAmplitude N i 1 Y hY ((gamma0CuspFrequencyStep N 1 : ℤ)*m j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hm j)) by
        simp [gamma0CuspUnitAmplitude,gamma0CuspTrueWidth_identity]]
  rw [star_mul,show star (1/2 : ℂ) = 1/2 by norm_num]
  ring

theorem gamma0MixedPacketContinuousIntegrand_eq_sum {ι : Type*} (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0) (t : ℝ) :
    gamma0MixedPacketContinuousIntegrand N h b Y hY n hn v α m hm t/((2*Real.pi : ℝ) : ℂ) =
      ∑ j ∈ v, α j*gamma0BareContinuousRhoIntegrand N h b 1 Y hY n (m j) hn (hm j) t := by
  unfold gamma0MixedPacketContinuousIntegrand gamma0InfinityContinuousPacketFourier
    gamma0BareContinuousRhoIntegrand
  simp_rw [gamma0BareEisensteinSourceCoefficient_half_amplitude,conj_packet,Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_div,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_div,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [star_mul,show star (1/2 : ℂ) = 1/2 by norm_num]
  ring

theorem gamma0MixedPacketResidualTerm_eq_sum {ι : Type*} (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (b : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (l : Ici (0 : ℝ)) (k : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
    gamma0MixedPacketResidualTerm N h b n hn v α m hm l k =
      ∑ j ∈ v, α j*gamma0BareResidualRhoTerm N h b 1 n (m j) hn (hm j) l k := by
  unfold gamma0MixedPacketResidualTerm gamma0InfinityResidualPacketRho gamma0BareResidualRhoTerm
  rw [conj_packet,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end ArtinMatthews
