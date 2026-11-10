module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Singular
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Homogeneity and smoothness of the actual Newtonian Hessian entries. -/

noncomputable section
open scoped RealInnerProductSpace Topology
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def newtonianEntry (m : ℕ) (v w x : E) : ℝ := newtonianSecond m x v w

theorem contDiffAt_newtonianEntry (m : ℕ) (v w : E) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ⊤ (newtonianEntry m v w) x := by
  have h : ContDiffAt ℝ ⊤ (newtonianKernel m : E → ℝ) x :=
    contDiffAt_radialPower _ hx
  have h1 : ContDiffAt ℝ ⊤ (fderiv ℝ (newtonianKernel m : E → ℝ)) x :=
    h.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ ⊤ (fderiv ℝ (fderiv ℝ (newtonianKernel m : E → ℝ))) x :=
    h1.fderiv_right (by norm_num)
  exact (h2.clm_apply contDiffAt_const).clm_apply contDiffAt_const

theorem newtonianEntry_formula (m : ℕ) (v w : E) {x : E} (hx : x ≠ 0) :
    newtonianEntry m v w x =
      (2 - (m : ℝ)) * ‖x‖ ^ (-(m : ℝ)) * ⟪v, w⟫ +
      (m : ℝ) * ((m : ℝ) - 2) * ‖x‖ ^ (-(m : ℝ) - 2) * ⟪x, v⟫ * ⟪x, w⟫ := by
  change (fderiv ℝ (fderiv ℝ (radialPower (1 - (m : ℝ) / 2))) x) v w = _
  rw [second_fderiv_radialPower _ hx, radialPowerHessian_apply]
  have hc1 : 2 * (1 - (m : ℝ) / 2) = 2 - (m : ℝ) := by ring
  have hc2 : 4 * (1 - (m : ℝ) / 2) * (1 - (m : ℝ) / 2 - 1) =
      (m : ℝ) * ((m : ℝ) - 2) := by ring
  have hp1 : (‖x‖ ^ 2) ^ (1 - (m : ℝ) / 2 - 1) = ‖x‖ ^ (-(m : ℝ)) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg x)]
    congr 1
    push_cast
    ring
  have hp2 : (‖x‖ ^ 2) ^ (1 - (m : ℝ) / 2 - 2) = ‖x‖ ^ (-(m : ℝ) - 2) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg x)]
    congr 1
    push_cast
    ring
  rw [hc1, hc2, hp1, hp2]

theorem newtonianEntry_smul (m : ℕ) (v w : E) {x : E} (hx : x ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    newtonianEntry m v w (c • x) = c ^ (-(m : ℝ)) * newtonianEntry m v w x := by
  have hcx : c • x ≠ 0 := smul_ne_zero hc.ne' hx
  rw [newtonianEntry_formula m v w hcx, newtonianEntry_formula m v w hx,
    norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  simp only [Real.mul_rpow hc.le (norm_nonneg x), real_inner_smul_left]
  have hp : c ^ (-(m : ℝ) - 2) * c ^ 2 = c ^ (-(m : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hc]
    congr 1
    ring
  calc
    _ = c ^ (-(m : ℝ)) * ((2 - (m : ℝ)) * ‖x‖ ^ (-(m : ℝ)) * ⟪v, w⟫) +
        (c ^ (-(m : ℝ) - 2) * c ^ 2) *
          ((m : ℝ) * ((m : ℝ) - 2) * ‖x‖ ^ (-(m : ℝ) - 2) * ⟪x, v⟫ * ⟪x, w⟫) := by ring
    _ = _ := by rw [hp]; ring

end OAI.Analysis.PDE.Schauder
