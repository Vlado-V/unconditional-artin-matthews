module

public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
public import ArtinMatthews.SpectralCuspTrueWidth
public import ArtinMatthews.SpectralGamma0PoincareSpectral
public import ArtinMatthews.SpectralInfinityOrbitalWeil
public import ArtinMatthews.SpectralSameCuspPoincareGram
public import ArtinMatthews.SpectralTrueWidthBesselHeightCutoff
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The high support infinity Gram identity for a family of different
compact profiles. Each actual diagonal carries its own invariant mass. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff MatrixGroups InnerProductSpace BigOperators

namespace ArtinMatthews

theorem spectral_finset_orthogonal_sum_normsq {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (t : Finset ι) (v : ι → H)
    (hv : Pairwise (fun j k => inner ℂ (v j) (v k) = 0)) :
    ‖∑ j ∈ t, v j‖^2 = ∑ j ∈ t, ‖v j‖^2 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
    have horth : inner ℂ (v j) (∑ k ∈ t, v k) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro k hk
      exact hv (fun e => hj (e.symm ▸ hk))
    have hp : ‖v j + ∑ k ∈ t, v k‖^2 = ‖v j‖^2+‖∑ k ∈ t, v k‖^2 := by
      simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    rw [Finset.sum_insert hj,Finset.sum_insert hj,hp,ih]

theorem gamma0FourierPoincareTest_identity_high_pairing (N : ℕ) [NeZero N]
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hηlo : ∀ z ∈ tsupport η, B ≤ z)
    (hcut : 1 < (N : ℝ)^2*A*B) :
    let d := gamma0CuspFrequencyStep N 1
    inner ℂ (gamma0FourierPoincareTest N 1 ((d : ℤ)*m) ρ hρ hcρ hpρ)
      (gamma0FourierPoincareTest N 1 ((d : ℤ)*n) η hη hcη hpη) =
      if m = n then ((4*(N : ℝ)^2*cuspFourierHeightPairing ρ η : ℝ) : ℂ) else 0 := by
  dsimp only
  have h := gamma0FourierPoincareTest_sameCusp_gram N 1 m n ρ η hρ hη hcρ hcη hpρ hpη
  dsimp only at h
  have hz := gamma0PositiveGeometricSum_identity_zero_of_high_support N m n hm hn
    ρ η hρ hη hcρ hcη hpρ hpη hA hB hρlo hηlo hcut
  rw [hz,mul_zero,add_zero] at h
  simpa only [gamma0CuspFrequencyStep_identity,pow_two,mul_assoc] using h

theorem gamma0FourierPoincarePacket_identity_high_profile_normsq {ι : Type*}
    (N : ℕ) [NeZero N] (t : Finset ι) (α : ι → ℂ) (ν : ι → ℤ)
    (hν : Function.Injective ν) (hν0 : ∀ j, ν j ≠ 0)
    (ρ : ι → ℝ → ℝ) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j))
    (hcρ : ∀ j, HasCompactSupport (ρ j)) (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ))
    {A : ℝ} (hA : 0 < A) (hρlo : ∀ j, ∀ y ∈ tsupport (ρ j), A ≤ y)
    (hcut : 1 < (N : ℝ)^2*A*A) :
    let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*ν j
    let P := gamma0FourierPoincarePacket N t α (fun _ => 1) nN ρ hρ hcρ hpρ
    ‖P‖^2 = 4*(N : ℝ)^2*(∑ j ∈ t, ‖α j‖^2*cuspFourierHeightPairing (ρ j) (ρ j)) := by
  dsimp only
  let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*ν j
  let V j := gamma0FourierPoincareTest N 1 (nN j) (ρ j) (hρ j) (hcρ j) (hpρ j)
  have hPair (j k : ι) : inner ℂ (V j) (V k) =
      if ν j = ν k then ((4*(N : ℝ)^2*cuspFourierHeightPairing (ρ j) (ρ k) : ℝ) : ℂ) else 0 :=
    gamma0FourierPoincareTest_identity_high_pairing N (ν j) (ν k) (hν0 j) (hν0 k)
      (ρ j) (ρ k) (hρ j) (hρ k) (hcρ j) (hcρ k) (hpρ j) (hpρ k)
      hA hA (hρlo j) (hρlo k) hcut
  have hV (j : ι) : ‖V j‖^2 = 4*(N : ℝ)^2*cuspFourierHeightPairing (ρ j) (ρ j) := by
    calc
      _ = (inner ℂ (V j) (V j)).re := (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = _ := by rw [hPair j j,ite_eq_left rfl,Complex.ofReal_re]
  have horth : Pairwise (fun j k => inner ℂ (α j • V j) (α k • V k) = 0) := by
    intro j k hjk
    rw [inner_smul_left,inner_smul_right,hPair,ite_eq_right (fun h => hjk (hν h)),mul_zero,mul_zero]
  change ‖∑ j ∈ t, α j • V j‖^2 = _
  rw [spectral_finset_orthogonal_sum_normsq t _ horth,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_smul,mul_pow,hV]
  ring

end ArtinMatthews
