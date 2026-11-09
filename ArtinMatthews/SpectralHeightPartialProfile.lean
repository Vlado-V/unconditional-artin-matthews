module

public import ArtinMatthews.SpectralWeylCutoffCompact
public import ArtinMatthews.SpectralDecayingSeedCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite seed approximants have one literal compact height
profile, the same cutoff used on the physical KL side. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology MatrixGroups
namespace ArtinMatthews

def spectralHeightProfilePartial (K : ℕ) (ρ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K+1),
    (spectralHeightProfileBlock ((2 : ℝ)^k) ρ y+
      spectralHeightProfileBlock (((2 : ℝ)^(k+1))⁻¹) ρ y)

theorem spectralHeightProfilePartial_apply (K : ℕ) (ρ : ℝ → ℝ) (y : ℝ) :
    spectralHeightProfilePartial K ρ y = spectralHeightAnnularPartial K y*ρ y :=
  spectralHeightProfileBlock_partial ρ K y

theorem spectralHeightProfilePartial_contDiff (K : ℕ) (ρ : ℝ → ℝ)
    (hρ : ContDiffOn ℝ ∞ ρ (Ioi (0 : ℝ))) : ContDiff ℝ ∞ (spectralHeightProfilePartial K ρ) := by
  apply ContDiff.sum
  intro k _
  exact (spectralHeightProfileBlock_contDiff (by positivity) ρ hρ).add
    (spectralHeightProfileBlock_contDiff (by positivity) ρ hρ)

theorem spectralHeightProfilePartial_tsupport (K : ℕ) (ρ : ℝ → ℝ) :
    tsupport (spectralHeightProfilePartial K ρ) ⊆
      Icc (((2 : ℝ)^(K+1))⁻¹) (2*(2 : ℝ)^(K+1)) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  constructor
  · by_contra! h
    apply hy
    rw [spectralHeightProfilePartial_apply,spectralHeightAnnularPartial_zero_low K h.le,zero_mul]
  · by_contra! h
    apply hy
    rw [spectralHeightProfilePartial_apply,spectralHeightAnnularPartial_zero_high K h.le,zero_mul]

theorem spectralHeightProfilePartial_compact (K : ℕ) (ρ : ℝ → ℝ) :
    HasCompactSupport (spectralHeightProfilePartial K ρ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (spectralHeightProfilePartial_tsupport K ρ)

theorem spectralHeightProfilePartial_positive (K : ℕ) (ρ : ℝ → ℝ) :
    tsupport (spectralHeightProfilePartial K ρ) ⊆ Ioi (0 : ℝ) :=
  fun _ hy => (by positivity : 0 < ((2 : ℝ)^(K+1))⁻¹).trans_le
    ((spectralHeightProfilePartial_tsupport K ρ hy).1)

theorem gamma0PrimitiveDecayingCutoffSeed_eq_partial (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (P : SpectralDecayingHeightProfile) (K : ℕ) :
    gamma0PrimitiveDecayingCutoffSeed N a n P K =
      gamma0PrimitiveFourierPoincareSeed N a n (spectralHeightProfilePartial K P.value)
        (spectralHeightProfilePartial_contDiff K P.value P.smooth)
        (spectralHeightProfilePartial_compact K P.value)
        (spectralHeightProfilePartial_positive K P.value) := by
  apply Subtype.ext
  ext z
  rw [gamma0PrimitiveDecayingCutoffSeed_apply]
  change _ = gamma0PrimitiveFourierScale N a •
    (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      ((gamma0CuspFrequencyStep N a : ℤ)*n) (spectralHeightProfilePartial K P.value)
      (spectralHeightProfilePartial_contDiff K P.value P.smooth)
      (spectralHeightProfilePartial_compact K P.value)
      (spectralHeightProfilePartial_positive K P.value)).val (a • z)
  rw [cuspFourierTestSeed_apply,smul_eq_mul,gamma0PrimitiveDecayingSeedValue,
    spectralHeightProfilePartial_apply]
  push_cast
  ring

end ArtinMatthews
