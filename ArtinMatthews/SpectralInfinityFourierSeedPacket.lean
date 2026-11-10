module

public import ArtinMatthews.SpectralFourierParabolicUnfolding
public import ArtinMatthews.SpectralGamma0PoincareSpectral
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The actual finite infinity packet has one compact seed, whose
horizontal partition factors out of the full Fourier sum. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff CompactlySupported InnerProductSpace BigOperators

namespace ArtinMatthews

def gamma0InfinityFourierSeedPacket {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (ρ : ι → ℝ → ℝ)
    (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)) (hcρ : ∀ j, HasCompactSupport (ρ j))
    (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) : h2SmoothCompactSeeds :=
  ∑ j ∈ t, α j • cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    (n j) (ρ j) (hρ j) (hcρ j) (hpρ j)

theorem gamma0InfinityFourierSeedPacket_mass_image {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (ρ : ι → ℝ → ℝ)
    (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)) (hcρ : ∀ j, HasCompactSupport (ρ j))
    (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) :
    gamma0SmoothSeedMass N (gamma0InfinityFourierSeedPacket N t α n ρ hρ hcρ hpρ) =
      gamma0FourierPoincarePacket N t α (fun _ => 1) n ρ hρ hcρ hpρ := by
  have hmod (ψ : h2SmoothCompactSeeds) : modularTranslateSmoothSeed 1 ψ = ψ := by
    apply Subtype.ext
    ext z
    rw [modularTranslateSmoothSeed_apply,one_smul]
  simp only [gamma0InfinityFourierSeedPacket,gamma0FourierPoincarePacket,
    gamma0FourierPoincareTest,map_sum,map_smul,hmod]

theorem gamma0InfinityFourierSeedPacket_apply {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (ρ : ι → ℝ → ℝ)
    (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)) (hcρ : ∀ j, HasCompactSupport (ρ j))
    (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    (gamma0InfinityFourierSeedPacket N t α n ρ hρ hcρ hpρ).val z =
      (spectralHorizontalPartition (N : ℝ) z.re : ℂ)*
        (∑ j ∈ t, α j • cuspFourierWave N (n j) (ρ j) z) := by
  simp only [gamma0InfinityFourierSeedPacket,Submodule.coe_sum,Submodule.coe_smul_of_tower,
    CompactlySupportedContinuousMap.sum_apply,CompactlySupportedContinuousMap.smul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [cuspFourierTestSeed_apply,cuspFourierWave,smul_eq_mul,smul_eq_mul,Complex.ofReal_mul]
  ring

theorem gamma0InfinityFourierSeedPacket_support {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (ρ : ι → ℝ → ℝ)
    (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)) (hcρ : ∀ j, HasCompactSupport (ρ j))
    (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ)) {A : ℝ}
    (hLo : ∀ j ∈ t, ∀ y ∈ tsupport (ρ j), A ≤ y) (z : UpperHalfPlane)
    (hz : (gamma0InfinityFourierSeedPacket N t α n ρ hρ hcρ hpρ).val z ≠ 0) :
    z.re ∈ Icc 0 (2*(N : ℝ)) ∧ A ≤ z.im := by
  rw [gamma0InfinityFourierSeedPacket_apply] at hz
  refine ⟨spectralHorizontalPartition_tsupport (Nat.cast_pos.mpr (NeZero.pos N)) (subset_tsupport _ ?_),?_⟩
  · intro hp
    exact hz (by rw [hp,Complex.ofReal_zero,zero_mul])
  · by_contra! hbad
    apply hz
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j hj
    have hzero : ρ j z.im = 0 := image_eq_zero_of_notMem_tsupport (fun h => (not_le_of_gt hbad) (hLo j hj _ h))
    simp only [cuspFourierWave,hzero,Complex.ofReal_zero,zero_mul,smul_zero]

theorem cuspFourierWave_continuous (N : ℕ) (n : ℤ) (ρ : ℝ → ℝ) (hρ : Continuous ρ) :
    Continuous (cuspFourierWave N n ρ) := by
  unfold cuspFourierWave
  exact (Complex.continuous_ofReal.comp (hρ.comp UpperHalfPlane.continuous_im)).mul
    (Complex.continuous_conj.comp ((cuspFourierPhase_contDiff (N : ℝ) n).continuous.comp
      UpperHalfPlane.continuous_re))

theorem spectralCompactSeed_inner_integrable (ψ : C_c(UpperHalfPlane, ℂ))
    (W : UpperHalfPlane → ℂ) (hW : Continuous W) :
    Integrable (fun z => inner ℂ (ψ z) (W z)) := by
  apply (ψ.continuous.inner (𝕜 := ℂ) hW).integrable_of_hasCompactSupport
  apply ψ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  apply subset_tsupport
  intro hzero
  exact hz (by simp [hzero])

end ArtinMatthews
