module

public import ArtinMatthews.SpectralEisensteinHeightCutoff
public import ArtinMatthews.SpectralEisensteinPowerCalculus
public import ArtinMatthews.SpectralGamma0EisensteinPlaneTerms
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The noncompact height cutoff is genuinely smooth: its actual row series
is locally finite, and each term is differentiated as an actual plane function. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem cuspEisensteinRow_coefficients_ne_zero (N : ℕ) (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) : (v.val 0:ℝ) ≠ 0 ∨ (v.val 1:ℝ) ≠ 0 := by
  by_cases hc : (v.val 0:ℝ)=0
  · right
    intro hd
    apply gamma0CuspEisensteinRows_ne_zero N r a v
    funext i
    fin_cases i
    · exact_mod_cast hc
    · exact_mod_cast hd
  · exact Or.inl hc

def cuspEisensteinRowPlaneTerm (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (p : ℝ×ℝ) : ℂ :=
  eisensteinRowPower s (v.val 0) (v.val 1) p

theorem cuspEisensteinRowPlaneTerm_eq (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (p : ℝ×ℝ) (hp : 0 < p.2) :
    cuspEisensteinRowPlaneTerm N r a s v p=
      cuspEisensteinRowTerm N r a s v ⟨Complex.mk p.1 p.2,hp⟩ := by
  have hq : eisensteinRowQuadratic (v.val 0) (v.val 1) p=
      ‖(v.val 0:ℂ)*Complex.mk p.1 p.2+v.val 1‖^2 := by
    simpa only [Complex.ofReal_intCast] using eisensteinRowQuadratic_norm_sq (v.val 0) (v.val 1) p
  rw [cuspEisensteinRowPlaneTerm,eisensteinRowPower_eq_height s _ _
    (cuspEisensteinRow_coefficients_ne_zero N r a v) p hp,
    cuspEisensteinRowTerm,cuspEisensteinRowHeight_row,hq]
  rfl

def cuspEisensteinNormalizedHeightPlane (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (p : ℝ×ℝ) : ℝ :=
  p.2/((gamma0CuspTrueWidth N a:ℝ)*eisensteinRowQuadratic (v.val 0) (v.val 1) p)

theorem cuspEisensteinNormalizedHeightPlane_eq (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (p : ℝ×ℝ) (hp : 0 < p.2) :
    cuspEisensteinNormalizedHeightPlane N r a v p=
      cuspEisensteinNormalizedHeight N r a v ⟨Complex.mk p.1 p.2,hp⟩ := by
  have hq : eisensteinRowQuadratic (v.val 0) (v.val 1) p=
      ‖(v.val 0:ℂ)*Complex.mk p.1 p.2+v.val 1‖^2 := by
    simpa only [Complex.ofReal_intCast] using eisensteinRowQuadratic_norm_sq (v.val 0) (v.val 1) p
  rw [cuspEisensteinNormalizedHeight,cuspEisensteinRowHeight_row,
    cuspEisensteinNormalizedHeightPlane,hq]
  simp only [UpperHalfPlane.im,div_div,mul_comm]

theorem cuspEisensteinNormalizedHeightPlane_smooth (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) :
    ContDiffOn ℝ ∞ (cuspEisensteinNormalizedHeightPlane N r a v) {p : ℝ×ℝ | 0 < p.2} := by
  have hq : ContDiff ℝ ∞ (eisensteinRowQuadratic (v.val 0) (v.val 1)) := by
    unfold eisensteinRowQuadratic
    fun_prop
  unfold cuspEisensteinNormalizedHeightPlane
  apply contDiffOn_snd.div (contDiffOn_const.mul hq.contDiffOn)
  intro p hp
  exact mul_ne_zero (by exact_mod_cast (gamma0CuspTrueWidth_pos N a).ne')
    (eisensteinRowQuadratic_pos _ _ (cuspEisensteinRow_coefficients_ne_zero N r a v) p hp).ne'

def cuspEisensteinCutoffPlaneTerm (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (p : ℝ×ℝ) : ℂ :=
  (eisensteinHeightCutoff (cuspEisensteinNormalizedHeightPlane N r a v p):ℂ)*
    (gamma0CuspTrueWidth N a:ℂ)^(-s)*cuspEisensteinRowPlaneTerm N r a s v p

theorem cuspEisensteinCutoffPlaneTerm_smooth (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) :
    ContDiffOn ℝ ∞ (cuspEisensteinCutoffPlaneTerm N r a s v) {p : ℝ×ℝ | 0 < p.2} := by
  have hh := eisensteinHeightCutoff_contDiff.comp_contDiffOn
    (cuspEisensteinNormalizedHeightPlane_smooth N r a v)
  have hc := Complex.ofRealCLM.contDiff.comp_contDiffOn hh
  exact (hc.mul contDiffOn_const).mul
    (eisensteinRowPower_contDiffOn s _ _ (cuspEisensteinRow_coefficients_ne_zero N r a v))

theorem cuspEisensteinCutoffPlaneTerm_eq (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (p : ℝ×ℝ) (hp : 0 < p.2) :
    cuspEisensteinCutoffPlaneTerm N r a s v p=
      cuspEisensteinCutoffTerm N r a s v ⟨Complex.mk p.1 p.2,hp⟩ := by
  rw [cuspEisensteinCutoffPlaneTerm,cuspEisensteinNormalizedHeightPlane_eq N r a v p hp,
    cuspEisensteinRowPlaneTerm_eq N r a s v p hp,cuspEisensteinCutoffTerm,
    cuspEisensteinNormalizedHeight_power]
  ring

end ArtinMatthews
