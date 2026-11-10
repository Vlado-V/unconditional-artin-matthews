module

public import ArtinMatthews.SpectralGamma0PoincareBessel
public import ArtinMatthews.SpectralCuspFourierFaithful
public import ArtinMatthews.SpectralInfinityFourierWidth
public import ArtinMatthews.SpectralInfinityMassFaithful
public import ArtinMatthews.SpectralNativeBesselAmplitudeHeights
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual normalized cusp eigenvector has a nonzero native
infinity Fourier amplitude at a nonzero true-width frequency. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

local instance infinityNative_inner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) _

theorem gamma0InfinityNativeBesselAmplitude_exists_ne_zero (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (Y₀ : ℝ) (hY₀ : 0 < Y₀) :
    ∃ (n : ℤ) (hn : n ≠ 0),
      gamma0CuspBesselAmplitude N i 1 Y₀ hY₀ ((N : ℤ)*n)
        (mul_ne_zero (by exact_mod_cast NeZero.ne N) hn) ≠ 0 := by
  by_contra! hz
  let f := (gamma0FullCuspidalSpectralBasis N i).val
  have hmass : f = 0 := by
    apply gamma0Mass_eq_zero_of_infinity_restrictions_eq_zero N
    intro Y hY
    apply gamma0CuspMassRestriction_eq_zero_of_fourier_eq_zero N 1 Y hY f
    intro m
    by_cases hm : m = 0
    · subst m
      rw [gamma0CuspFourierCoefficient_zero_eq_constantTerm]
      exact ((mem_gamma0AllHeightCuspidalMassSpace_iff_constantTerm N f).mp
        (gamma0FullCuspidalSpectralBasis N i).property) 1 Y hY
    · by_cases hd : (N : ℤ) ∣ m
      · obtain ⟨n, rfl⟩ := hd
        have hn : n ≠ 0 := by
          intro he
          exact hm (by simp only [he, mul_zero])
        have ha : gamma0CuspBesselAmplitude N i 1 Y hY ((N : ℤ)*n) hm = 0 := by
          rw [gamma0CuspBesselAmplitude_height_eq N i 1 Y Y₀ hY hY₀ _ hm]
          exact hz n hn
        have hb := gamma0CuspBesselAmplitude_fourier_ae N i 1 Y hY ((N : ℤ)*n) hm
        rw [ha] at hb
        simp only [zero_mul] at hb
        apply Lp.ext
        have he : (gamma0CuspFourierCoefficient N 1 Y hY ((N : ℤ)*n) f : ℝ → ℂ)
            =ᵐ[(cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure Y] (0 : ℝ → ℂ) :=
          (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mpr hb
        exact he.trans (Lp.coeFn_zero ℂ 2 _).symm
      · exact gamma0InfinityFourierCoefficient_eq_zero_of_not_dvd N Y hY m hd f
  have hb : gamma0FullCuspidalSpectralBasis N i = 0 := Subtype.ext hmass
  have hn := (gamma0FullCuspidalSpectralBasis N).orthonormal.norm_eq_one i
  rw [hb, norm_zero] at hn
  exact zero_ne_one hn

end ArtinMatthews
