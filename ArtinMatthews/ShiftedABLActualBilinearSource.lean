module

public import ArtinMatthews.ShiftedABLActualCorrelationSource
public import ArtinMatthews.ShiftedBilinearSource


set_option backward.privateInPublic true
@[expose] public section

/-! The native cubic numerator satisfies the original full shifted
bilinear bound, with the level-prime reduction supplied by the receiver. -/

namespace ArtinMatthews

open Set
open scoped ContDiff

theorem cubicNumerator_shiftedBilinearBound
    (a : ℤ) (ha : a ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3=(a : OAI.CubicFirstMoment.Eisenstein))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∀ ν : ℝ, 0 < ν → ∃ Cν : ℝ, 0 < Cν ∧ ∀ x : ℝ, 1 ≤ x →
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter a ha) Φ x ν Cν :=
  cubicNumerator_shiftedBilinearBound_of_correlation a ha
    (cubicNumerator_shiftedABLCorrelationSource a ha hnoncube) Φ hΦ hsupp

end ArtinMatthews
