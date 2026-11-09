module

public import ArtinMatthews.SpectralHeatSpectralPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The exact finite residual coefficient sum passes to the bare
window with its actual energies, amplitudes, and multiplicities. -/

noncomputable section
open Set Filter
open scoped MatrixGroups Topology
namespace ArtinMatthews

def gamma0BareResidualRhoTerm (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (l : Ici (0 : ℝ))
    (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) : ℂ :=
  h l*(((Real.sqrt |(m : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j r m hm)*
    star ((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j s n hn))

def gamma0HeatResidualRhoSum (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (R : ℝ) : ℂ :=
  ∑ l∈gamma0ResidualEnergyWindow N, ∑ j, gamma0BareResidualRhoTerm N h r s m n hm hn l j*
    spectralHeatEnergyWeight R l

def gamma0BareResidualRhoSum (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) : ℂ :=
  ∑ l∈gamma0ResidualEnergyWindow N, ∑ j, gamma0BareResidualRhoTerm N h r s m n hm hn l j

theorem gamma0HeatResidualRhoSum_norm_le (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) {R : ℝ} (hR : 1 ≤ R) :
    ‖gamma0HeatResidualRhoSum N h r s m n hm hn R‖ ≤ Real.exp (1/2 : ℝ)*
      ∑ l∈gamma0ResidualEnergyWindow N, ∑ j, ‖gamma0BareResidualRhoTerm N h r s m n hm hn l j‖ := by
  unfold gamma0HeatResidualRhoSum
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro l _
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro j _
  rw [norm_mul,mul_comm (Real.exp (1/2 : ℝ))]
  exact mul_le_mul_of_nonneg_left (spectralHeatEnergyWeight_norm_le hR l.property) (norm_nonneg _)

theorem gamma0HeatResidualRhoSum_tendsto_bare (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Tendsto (gamma0HeatResidualRhoSum N h r s m n hm hn) atTop
      (𝓝 (gamma0BareResidualRhoSum N h r s m n hm hn)) := by
  unfold gamma0HeatResidualRhoSum gamma0BareResidualRhoSum
  apply tendsto_finset_sum
  intro l _
  apply tendsto_finset_sum
  intro j _
  simpa only [mul_one] using tendsto_const_nhds.mul (spectralHeatEnergyWeight_tendsto l)

end ArtinMatthews
