module

public import ArtinMatthews.SpectralDecayingPoincare


set_option backward.privateInPublic true
@[expose] public section

/-! The compact seed approximants are literal height cutoffs of the
original Fourier seed, in the stated integral cusp chart. -/

noncomputable section
open Set Filter
open scoped MatrixGroups ContDiff Topology
namespace ArtinMatthews

def gamma0PrimitiveDecayingSeedValue (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) (z : UpperHalfPlane) : ℂ :=
  gamma0PrimitiveFourierScale N a*
    ((spectralHorizontalPartition (N : ℝ) (a • z).re*P.value (a • z).im : ℝ) : ℂ)*
    star (cuspFourierPhase (N : ℝ) ((gamma0CuspFrequencyStep N a : ℤ)*n) (a • z).re)

theorem gamma0PrimitiveHeightBlockSeed_apply (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (P : SpectralDecayingHeightProfile)
    (A : ℝ) (hA : 0 < A) (z : UpperHalfPlane) :
    (gamma0PrimitiveHeightBlockSeed N a n P A hA).val z =
      (spectralHeightAnnularBlock A (a • z).im : ℂ)*gamma0PrimitiveDecayingSeedValue N a n P z := by
  change gamma0PrimitiveFourierScale N a •
    (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      ((gamma0CuspFrequencyStep N a : ℤ)*n) (spectralHeightProfileBlock A P.value)
      (spectralHeightProfileBlock_contDiff hA P.value P.smooth)
      (spectralHeightProfileBlock_compact hA P.value)
      (spectralHeightProfileBlock_positive hA P.value)).val (a • z) = _
  rw [cuspFourierTestSeed_apply,smul_eq_mul,gamma0PrimitiveDecayingSeedValue,spectralHeightProfileBlock]
  push_cast
  ring

theorem gamma0PrimitiveDecayingCutoffSeed_apply (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (P : SpectralDecayingHeightProfile)
    (K : ℕ) (z : UpperHalfPlane) :
    (gamma0PrimitiveDecayingCutoffSeed N a n P K).val z =
      (spectralHeightAnnularPartial K (a • z).im : ℂ)*gamma0PrimitiveDecayingSeedValue N a n P z := by
  simp only [gamma0PrimitiveDecayingCutoffSeed,Submodule.coe_sum,Submodule.coe_add,
    CompactlySupportedContinuousMap.sum_apply,CompactlySupportedContinuousMap.add_apply,
    gamma0PrimitiveHeightBlockSeed_apply,← add_mul,← Complex.ofReal_add]
  rw [← Finset.sum_mul,← Complex.ofReal_sum]
  rfl

theorem gamma0PrimitiveDecayingCutoffSeed_eventually (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (P : SpectralDecayingHeightProfile) (z : UpperHalfPlane) :
    ∀ᶠ K : ℕ in atTop,
      (gamma0PrimitiveDecayingCutoffSeed N a n P K).val z =
        gamma0PrimitiveDecayingSeedValue N a n P z := by
  filter_upwards [spectralHeightAnnularPartial_eventually_one (a • z).im_pos] with K hK
  rw [gamma0PrimitiveDecayingCutoffSeed_apply,hK,Complex.ofReal_one,one_mul]

end ArtinMatthews
