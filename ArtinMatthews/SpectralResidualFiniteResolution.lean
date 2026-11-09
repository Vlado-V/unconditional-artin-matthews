module

public import ArtinMatthews.SpectralResidualFiniteEnergies
public import ArtinMatthews.SpectralStoneNativePairing


set_option backward.privateInPublic true
@[expose] public section

/-! The residual part of the actual compact spectral resolution is a
finite sum at fixed level, with every projection retained explicitly. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0ResidualEnergyWindow (N : ℕ) [NeZero N] : Finset (Ici (0:ℝ)) :=
  ((gamma0ResidualEnergyCandidates_finite N).preimage Subtype.val_injective.injOn).toFinset

theorem mem_gamma0ResidualEnergyWindow (N : ℕ) [NeZero N] (l : Ici (0:ℝ)) :
    l∈gamma0ResidualEnergyWindow N ↔ (l:ℝ)∈gamma0ResidualEnergyCandidates N :=
  Set.Finite.mem_toFinset _

theorem gamma0StoneResidualPair_eq_finite (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) :
    gamma0StoneResidualPair N u v=
      ∑ l∈gamma0ResidualEnergyWindow N,
        inner ℂ (gamma0AmbientResidualProjection N (l:ℝ) u) (gamma0AmbientResidualProjection N (l:ℝ) v) := by
  unfold gamma0StoneResidualPair
  apply tsum_eq_sum
  intro l hl
  have hn : (l:ℝ)∉gamma0ResidualEnergyCandidates N := mt (mem_gamma0ResidualEnergyWindow N l).mpr hl
  rw [gamma0AmbientResidualProjection_zero_off_finite N (l:ℝ) l.property hn u,inner_zero_left]

theorem gamma0CompactStoneNativePairing_finiteResidual (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0SmoothSeedMass N ξ)=
      (∑' i : Gamma0AllHeightSpectralIndex N,
        inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0FullCuspidalSpectralBasis N i).val*
          inner ℂ (gamma0FullCuspidalSpectralBasis N i).val (gamma0SmoothSeedMass N ξ))+
      (gamma0StoneEisensteinPair N ψ ξ+
        ∑ l∈gamma0ResidualEnergyWindow N,
          inner ℂ (gamma0AmbientResidualProjection N (l:ℝ) (gamma0SmoothSeedMass N ψ))
            (gamma0AmbientResidualProjection N (l:ℝ) (gamma0SmoothSeedMass N ξ))) := by
  rw [gamma0CompactStoneNativePairing N ψ ξ,gamma0StoneResidualPair_eq_finite]

end ArtinMatthews
