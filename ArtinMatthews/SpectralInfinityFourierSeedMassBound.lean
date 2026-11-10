module

public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
public import ArtinMatthews.SpectralInfinityFourierSeedPacket
public import ArtinMatthews.SpectralInfinityFourierSeedPairing
public import ArtinMatthews.SpectralInfinityPoincareOrbitBound
public import ArtinMatthews.SpectralInfinityPoincareOrbitMass
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact horizontal orthogonality bounds the invariant seed mass,
and the actual overlap bound passes it to the completed packet. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff CompactlySupported InnerProductSpace BigOperators

namespace ArtinMatthews

theorem gamma0InfinityFourierSeedPacket_mass_le {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n) (ρ : ι → ℝ → ℝ)
    (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)) (hcρ : ∀ j, HasCompactSupport (ρ j))
    (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) :
    let Ψ := gamma0InfinityFourierSeedPacket N t α n ρ hρ hcρ hpρ
    (∫ z : UpperHalfPlane, ‖Ψ.val z‖^2) ≤
      (N : ℝ)*(∑ j ∈ t, ‖α j‖^2*cuspFourierHeightPairing (ρ j) (ρ j)) := by
  dsimp only
  let Ψ := gamma0InfinityFourierSeedPacket N t α n ρ hρ hcρ hpρ
  let W (z : UpperHalfPlane) := ∑ j ∈ t, α j • cuspFourierWave N (n j) (ρ j) z
  let F := spectralCompactSeedNormSq Ψ.val
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hW : Continuous W := continuous_finsetSum t (fun j _ =>
    (cuspFourierWave_continuous N (n j) (ρ j) (hρ j).continuous).const_smul (α j))
  have hI : Integrable (fun z => inner ℂ (Ψ.val z) (W z)) :=
    spectralCompactSeed_inner_integrable Ψ.val W hW
  have hI₀ : Integrable (fun z : UpperHalfPlane => ‖Ψ.val z‖^2) := by
    apply (F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport).re.congr
    filter_upwards with z
    change (F z).re = _
    rw [spectralCompactSeedNormSq_apply,Complex.ofReal_re]
  have hPoint (z : UpperHalfPlane) :
      ‖Ψ.val z‖^2 ≤ (inner ℂ (Ψ.val z) (W z)).re := by
    let p := spectralHorizontalPartition (N : ℝ) z.re
    have hp : 0 ≤ p ∧ p ≤ 1 := spectralHorizontalPartition_bounds hN z.re
    have hΨ : Ψ.val z = (p : ℂ)*W z := gamma0InfinityFourierSeedPacket_apply N t α n ρ hρ hcρ hpρ z
    have hInner : (inner ℂ (Ψ.val z) (W z)).re = p*‖W z‖^2 := by
      rw [hΨ,RCLike.inner_apply,mul_comm (W z)]
      change ((starRingEnd ℂ) ((p : ℂ)*W z)*W z).re = _
      rw [map_mul,Complex.conj_ofReal,mul_assoc,← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq,← Complex.ofReal_mul,Complex.ofReal_re]
    rw [hInner,hΨ,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp.1,mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [sq] using mul_le_of_le_one_right hp.1 hp.2) (sq_nonneg _)
  change (∫ z : UpperHalfPlane, ‖Ψ.val z‖^2) ≤ _
  calc
    _ ≤ ∫ z : UpperHalfPlane, (inner ℂ (Ψ.val z) (W z)).re :=
      integral_mono hI₀ hI.re hPoint
    _ = _ := by
      change (∫ z : UpperHalfPlane, RCLike.re (inner ℂ (Ψ.val z) (W z))) = _
      rw [integral_re hI]
      have h := gamma0InfinityFourierSeedPacket_inner_wave N t α n hn ρ hρ hcρ hpρ
      change (∫ z : UpperHalfPlane, inner ℂ (Ψ.val z) (W z)) = _ at h
      rw [h]
      rfl

theorem gamma0InfinityFourierPoincarePacket_orbit_normsq_le {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n) (ρ : ι → ℝ → ℝ)
    (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)) (hcρ : ∀ j, HasCompactSupport (ρ j))
    (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) {A : ℝ} (hA : 0 < A)
    (hLo : ∀ j ∈ t, ∀ y ∈ tsupport (ρ j), A ≤ y) :
    ‖gamma0FourierPoincarePacket N t α (fun _ => 1) n ρ hρ hcρ hpρ‖^2 ≤
      2*((2*(N : ℝ)+1)*(4*(1+2/((N : ℝ)*A))))*(N : ℝ)*
        (∑ j ∈ t, ‖α j‖^2*cuspFourierHeightPairing (ρ j) (ρ j)) := by
  let Ψ := gamma0InfinityFourierSeedPacket N t α n ρ hρ hcρ hpρ
  let C := (2*(N : ℝ)+1)*(4*(1+2/((N : ℝ)*A)))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  rw [← gamma0InfinityFourierSeedPacket_mass_image N t α n ρ hρ hcρ hpρ]
  change ‖gamma0SmoothSeedMass N Ψ‖^2 ≤ 2*C*(N : ℝ)*_
  calc
    _ ≤ 2*C*(∫ z : UpperHalfPlane, ‖Ψ.val z‖^2) :=
      gamma0Infinity_compact_seed_orbit_mass_bound N Ψ hA
        (gamma0InfinityFourierSeedPacket_support N t α n ρ hρ hcρ hpρ hLo)
    _ ≤ 2*C*((N : ℝ)*(∑ j ∈ t, ‖α j‖^2*cuspFourierHeightPairing (ρ j) (ρ j))) :=
      mul_le_mul_of_nonneg_left (gamma0InfinityFourierSeedPacket_mass_le N t α n hn ρ hρ hcρ hpρ)
        (by positivity)
    _ = _ := by ring

end ArtinMatthews
