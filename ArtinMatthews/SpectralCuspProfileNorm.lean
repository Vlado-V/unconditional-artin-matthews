module

public import ArtinMatthews.SpectralPrimitiveFourierPoincare
public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
public import ArtinMatthews.SpectralCuspPoincareOverlap
public import ArtinMatthews.SpectralCuspPoincareMassBound
public import ArtinMatthews.SpectralInfinityFourierSeedMassBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Height-explicit norm bounds for genuine compact Fourier profiles at
every cusp. The level and primitive-width factors remain explicit. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff CompactlySupported InnerProductSpace
namespace ArtinMatthews

theorem h2_modularTranslate_norm_sq_integral (a : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds) :
    (∫ z : UpperHalfPlane, ‖(modularTranslateSmoothSeed a ψ).val z‖^2)=
      ∫ z : UpperHalfPlane, ‖ψ.val z‖^2 := by
  have hme : MeasurableEmbedding (fun z : UpperHalfPlane => a • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ a • z)
    exact measurableEmbedding_const_smul _
  exact (h2_integer_measurePreserving a).integral_comp hme (fun z => ‖ψ.val z‖^2)

theorem cuspFourierTestSeed_invariant_mass_bound (N : ℕ) [NeZero N] (n : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    (∫ z : UpperHalfPlane, ‖(cuspFourierTestSeed (N : ℝ)
      (Nat.cast_pos.mpr (NeZero.pos N)) n ρ hρ hcρ hpρ).val z‖^2) ≤
      (N : ℝ)*cuspFourierHeightPairing ρ ρ := by
  have h := gamma0InfinityFourierSeedPacket_mass_le N ({()} : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => n) (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ => ρ) (fun _ => hρ) (fun _ => hcρ) (fun _ => hpρ)
  simpa only [gamma0InfinityFourierSeedPacket,Finset.sum_singleton,one_smul,norm_one,
    one_pow,one_mul] using h

theorem cuspFourierTestSeed_support_closed (N : ℕ) [NeZero N] (n : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) {A : ℝ}
    (hLo : ∀ y ∈ tsupport ρ, A ≤ y) (z : UpperHalfPlane)
    (hz : (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n ρ hρ hcρ hpρ).val z ≠ 0) :
    z.re ∈ Icc 0 (2*(N : ℝ)) ∧ A ≤ z.im := by
  rw [cuspFourierTestSeed_apply] at hz
  have hn := Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hz).1
  exact ⟨spectralHorizontalPartition_tsupport (Nat.cast_pos.mpr (NeZero.pos N))
    (subset_tsupport _ (mul_ne_zero_iff.mp hn).1),
    hLo _ (subset_tsupport _ (mul_ne_zero_iff.mp hn).2)⟩

theorem gamma0FourierPoincareTest_orbit_normsq_le (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) {A : ℝ} (hA : 0 < A)
    (hLo : ∀ y ∈ tsupport ρ, A ≤ y) :
    ‖gamma0FourierPoincareTest N a n ρ hρ hcρ hpρ‖^2 ≤
      2*gamma0CuspOrbitOverlap N a A*(N : ℝ)*cuspFourierHeightPairing ρ ρ := by
  let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n ρ hρ hcρ hpρ
  have hs (z : UpperHalfPlane) (hz : (modularTranslateSmoothSeed a ψ).val z ≠ 0) :
      (a • z).re ∈ Icc 0 (2*(N : ℝ)) ∧ A ≤ (a • z).im :=
    cuspFourierTestSeed_support_closed N n ρ hρ hcρ hpρ hLo (a • z) hz
  have h := gamma0Cusp_compact_seed_orbit_mass_bound N a (modularTranslateSmoothSeed a ψ) hA hs
  rw [h2_modularTranslate_norm_sq_integral] at h
  calc
    _ ≤ 2*gamma0CuspOrbitOverlap N a A*(∫ z : UpperHalfPlane, ‖ψ.val z‖^2) := h
    _ ≤ 2*gamma0CuspOrbitOverlap N a A*((N : ℝ)*cuspFourierHeightPairing ρ ρ) :=
      mul_le_mul_of_nonneg_left (cuspFourierTestSeed_invariant_mass_bound N n ρ hρ hcρ hpρ)
        (by unfold gamma0CuspOrbitOverlap; positivity)
    _ = _ := by ring

def gamma0PrimitiveProfileNormConstant (N : ℕ) [NeZero N] (a : SL(2, ℤ)) : ℝ :=
  ‖gamma0PrimitiveFourierScale N a‖^2*(8*(2*(gamma0CuspFrequencyStep N a : ℝ)+1)*(N : ℝ))

theorem gamma0PrimitiveFourierPoincareTest_orbit_normsq_le (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    {A : ℝ} (hA : 0 < A) (hLo : ∀ y ∈ tsupport ρ, A ≤ y) :
    ‖gamma0PrimitiveFourierPoincareTest N a n ρ hρ hcρ hpρ‖^2 ≤
      gamma0PrimitiveProfileNormConstant N a*(1+2/A)*cuspFourierHeightPairing ρ ρ := by
  rw [gamma0PrimitiveFourierPoincareTest_eq,norm_smul,mul_pow]
  refine (mul_le_mul_of_nonneg_left
    (gamma0FourierPoincareTest_orbit_normsq_le N a _ ρ hρ hcρ hpρ hA hLo) (sq_nonneg _)).trans_eq ?_
  unfold gamma0PrimitiveProfileNormConstant gamma0CuspOrbitOverlap
  ring

end ArtinMatthews
