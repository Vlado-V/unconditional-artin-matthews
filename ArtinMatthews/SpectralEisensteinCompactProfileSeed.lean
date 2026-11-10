module

public import ArtinMatthews.SpectralEisensteinParabolicEnumeration
public import ArtinMatthews.SpectralSeparableTestSeed
public import ArtinMatthews.SpectralModularDensitySeeds
public import ArtinMatthews.SpectralCuspEisensteinSeries
public import ArtinMatthews.SpectralHorizontalPeriodPartition
public import ArtinMatthews.SpectralHorizontalLatticePartition
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Actual compact smooth seeds for complex-valued normalized cusp-height
profiles, with the genuine source width retained. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff CompactlySupported
namespace ArtinMatthews

theorem cuspHeightProfile_scaled_compact (w : ℝ) (hw : 0 < w) (ρ : ℝ → ℂ)
    (hcρ : HasCompactSupport ρ) : HasCompactSupport (fun y => ρ (y/w)) := by
  have h := hcρ.comp_homeomorph (Homeomorph.mulLeft₀ w⁻¹ (inv_ne_zero hw.ne'))
  simpa only [Function.comp_def,Homeomorph.coe_mulLeft₀,div_eq_mul_inv,mul_comm] using h

theorem cuspHeightProfile_scaled_support (w : ℝ) (hw : 0 < w) (ρ : ℝ → ℂ)
    (hpos : tsupport ρ ⊆ Ioi (0:ℝ)) :
    tsupport (fun y => ρ (y/w)) ⊆ Ioi (0:ℝ) := by
  intro y hy
  change 0 < y
  have hpre : y/w ∈ tsupport ρ :=
    tsupport_comp_subset_preimage (f := fun y : ℝ => y/w) ρ (by fun_prop) hy
  have h := (lt_div_iff₀ hw).mp (hpos hpre)
  simpa only [zero_mul] using h

def cuspHeightProfileBaseSeed (w : ℝ) (hw : 0 < w) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi (0:ℝ)) :
    h2SmoothCompactSeeds :=
  h2SeparableSmoothSeed (fun x => (spectralHorizontalPartition w x:ℂ)) (fun y => ρ (y/w))
    (Complex.ofRealCLM.contDiff.comp (spectralHorizontalPartition_contDiff w))
    (hρ.comp (contDiff_id.div_const w))
    ((spectralHorizontalPartition_hasCompactSupport hw).comp_left Complex.ofReal_zero)
    (cuspHeightProfile_scaled_compact w hw ρ hcρ) (cuspHeightProfile_scaled_support w hw ρ hpos)

def cuspHeightProfileSeed (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi (0:ℝ)) :
    h2SmoothCompactSeeds :=
  modularTranslateSmoothSeed a (cuspHeightProfileBaseSeed (gamma0CuspTrueWidth N a:ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N a) ρ hρ hcρ hpos)

theorem cuspHeightProfileSeed_apply (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi (0:ℝ))
    (z : UpperHalfPlane) :
    (cuspHeightProfileSeed N a ρ hρ hcρ hpos).val z=
      (spectralHorizontalPartition (gamma0CuspTrueWidth N a:ℝ) (a • z).re:ℂ)*
        ρ ((a • z).im/(gamma0CuspTrueWidth N a:ℝ)) := rfl

theorem cuspHeightProfileSeed_parabolic (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi (0:ℝ))
    (v : Gamma0CuspEisensteinRows N 1 a) (z : UpperHalfPlane) :
    (∑ᶠ k : ℤ, (cuspHeightProfileSeed N a ρ hρ hcρ hpos).val
      ((cuspEisensteinParabolicEnumerate N a (v,k)).val • z))=
      ρ (cuspEisensteinRowHeight N 1 a v z/(gamma0CuspTrueWidth N a:ℝ)) := by
  simp_rw [cuspHeightProfileSeed_apply,← mul_smul,cuspEisensteinParabolicEnumerate_matrix,
    mul_smul,integerTranslation_eq_T_zpow,ModularGroup.re_T_zpow_smul,ModularGroup.im_T_zpow_smul]
  simp only [Int.cast_mul,Int.cast_natCast]
  have he (k : ℤ) :
      (spectralHorizontalPartition (gamma0CuspTrueWidth N a:ℝ)
        (((gamma0CuspEisensteinRowRepresentative N 1 a v).val • z).re+
          (gamma0CuspTrueWidth N a:ℝ)*k):ℂ)*
        ρ (((gamma0CuspEisensteinRowRepresentative N 1 a v).val • z).im/
          (gamma0CuspTrueWidth N a:ℝ))=
      spectralHorizontalPartition (gamma0CuspTrueWidth N a:ℝ)
        (((gamma0CuspEisensteinRowRepresentative N 1 a v).val • z).re+
          (gamma0CuspTrueWidth N a:ℝ)*k) •
        ρ (((gamma0CuspEisensteinRowRepresentative N 1 a v).val • z).im/
          (gamma0CuspTrueWidth N a:ℝ)) := by rw [Complex.real_smul]
  simp_rw [he]
  rw [← finsum_smul,spectralHorizontalPartition_lattice_finsum
    (show (0:ℝ) < gamma0CuspTrueWidth N a by exact_mod_cast gamma0CuspTrueWidth_pos N a),one_smul]
  rfl

end ArtinMatthews
