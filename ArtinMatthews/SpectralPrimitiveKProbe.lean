module

public import ArtinMatthews.SpectralPrimitiveKTransform
public import ArtinMatthews.SpectralCuspBesselNonzeroProbe
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

/-! Genuine nonzero primitive-width K probes exist throughout Re(s)>0,
including every critical parameter. Width and height scaling are literal. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0PrimitiveKTransform_exists_nonzero_probe (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ Ioi Y ∧
      gamma0PrimitiveKTransform N r Y n ρ s ≠ 0 := by
  let w : ℝ := gamma0CuspTrueWidth N r
  let q : ℝ := 2*Real.pi*|(n : ℝ)|
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hq : 0 < q := mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (abs_pos.mpr (by exact_mod_cast hn))
  have hν : -1/2 < (s-1/2).re := by
    have hh : (1/2 : ℂ).re = (1/2 : ℝ) := by norm_num
    rw [Complex.sub_re,hh]
    linarith
  obtain ⟨β,hβ,hcβ,hsβ,hne⟩ := cuspBesselTransform_exists_nonzero_probe
    (s-1/2) hν q (Y/w) hq (div_pos hY hw)
  let ρ (y : ℝ) := β (y/w)
  have hρ : ContDiff ℝ ∞ ρ := hβ.comp (contDiff_id.div_const w)
  have hcρ : HasCompactSupport ρ := by
    simpa only [ρ,Function.comp_def,Homeomorph.coe_mulRight₀,div_eq_mul_inv] using
      hcβ.comp_homeomorph (Homeomorph.mulRight₀ w⁻¹ (inv_ne_zero hw.ne'))
  have hsρ : tsupport ρ ⊆ Ioi Y := by
    intro y hy
    have hm : y/w ∈ tsupport β :=
      tsupport_comp_subset_preimage β (continuous_id.div_const w) hy
    have hh : Y/w < y/w := hsβ hm
    exact (div_lt_div_iff_of_pos_right hw).mp hh
  refine ⟨ρ,hρ,hcρ,hsρ,?_⟩
  have he : (fun u => ρ (w*u)) = β := by
    funext u
    dsimp only [ρ]
    rw [mul_div_cancel_left₀ u hw.ne']
  change cuspBesselTransform (s-1/2) q (Y/w) (fun u => ρ (w*u)) ≠ 0
  rw [he]
  exact hne

end ArtinMatthews
