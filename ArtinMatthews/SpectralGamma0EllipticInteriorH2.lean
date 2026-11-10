module

public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Weak.Elliptic.InteriorH2


set_option backward.privateInPublic true
@[expose] public section

/-! The actual L²-forcing interior H² theorem, specialized to the Euclidean
Laplacian.  The positive hyperbolic coefficient is handled by the separately
constructed inverse-height forcing; no smoothness of that forcing is used. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational

namespace ArtinMatthews

theorem spectralElliptic_laplacian_interior_H2
    (p : H1Pair 1) (hp : p ∈ H1Zero (univ : Set (Fin 2 → ℝ)))
    (f : Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))) {Ω : Set (Fin 2 → ℝ)}
    (hΩ : IsOpen Ω) (hweak : WeakDivergenceEquation Ω p.2 f)
    (η : (Fin 2 → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {K L : ℝ} (hK : 0 ≤ K) (hηM : ∀ x, |η x| ≤ 1)
    (hηK : ∀ x, ‖cellGradient η x‖ ≤ K) (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L)
    (hsη : tsupport η ⊆ Ω) (j : Fin 2) :
    ∃ g : Lp (CellVectors 1) 2 (volume : Measure (Fin 2 → ℝ)),
      ‖g‖ ≤ Real.sqrt ((‖f‖+2*(K*‖p.2‖))^2 + 4*‖f‖*(K*‖p.2‖)) + L*‖p.2‖ ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1) (cutoffL2 η hη.continuous hηM p.2) g := by
  let A : (Fin 2 → ℝ) → CellVectors 1 →L[ℝ] CellVectors 1 :=
    fun _ => ContinuousLinearMap.id ℝ (CellVectors 1)
  have hA : ContDiff ℝ 1 A := contDiff_const
  have hAM : ∀ x, ‖A x‖ ≤ 1 := fun _ => ContinuousLinearMap.norm_id_le
  have hDA : ∀ x, ‖fderiv ℝ A x‖ ≤ 0 := by
    intro x
    rw [show fderiv ℝ A x = 0 from fderiv_const_apply _]
    exact ContinuousLinearMap.opNorm_zero.le
  have hell : ∀ x z, (1 : ℝ)*‖z‖^2 ≤ inner ℝ (A x z) z := by
    intro x z
    simp [A]
  have hmul : fieldMultiplierCLM A hA.continuous.aestronglyMeasurable
      (Eventually.of_forall hAM) p.2 = p.2 := by
    apply Lp.ext
    filter_upwards [fieldMultiplierCLM_ae A hA.continuous.aestronglyMeasurable
      (Eventually.of_forall hAM) p.2] with x hx
    exact hx
  have hw : WeakDivergenceEquation Ω
      (fieldMultiplierCLM A hA.continuous.aestronglyMeasurable (Eventually.of_forall hAM) p.2) f := by
    rw [hmul]
    exact hweak
  simpa only [zero_mul,add_zero,zero_add,one_mul,mul_one,div_one] using
    interior_weak_gradient_derivative A hA (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0) hK hAM hDA hell
      p hp f hΩ hw η hη hcη hηM hηK hηL hsη j

end ArtinMatthews
