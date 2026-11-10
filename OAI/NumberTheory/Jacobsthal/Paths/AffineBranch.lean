module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
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
public import Mathlib.Order.CompletePartialOrder
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


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

namespace ErdosDivisibleInflection

theorem affine_of_second_derivative_zero (f : ℝ → ℝ) (a b x : ℝ)
    (hx : x ∈ Set.Ioo a b) (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (h2 : ∀ t ∈ Set.Ioo a b, deriv (deriv f) t = 0) :
    ∃ A B : ℝ, ∀ t ∈ Set.Ioo a b, f t = A*t+B := by
  have hdf : ContDiffOn ℝ 1 (deriv f) (Set.Ioo a b) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdconst : Set.EqOn (deriv f) (fun _ => deriv f x) (Set.Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (g := fun _ : ℝ => deriv f x) isPreconnected_Ioo
      (hdf.differentiableOn (by norm_num)) (differentiableOn_const (deriv f x)) _ hx rfl
    intro t ht
    simpa only [deriv_const] using h2 t ht
  let A := deriv f x
  let B := f x-A*x
  have hAffine (t : ℝ) : HasDerivAt (fun t => A*t+B) A t := by
    simpa using ((hasDerivAt_id t).const_mul A).add_const B
  have he : Set.EqOn f (fun t => A*t+B) (Set.Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (g := fun t => A*t+B) isPreconnected_Ioo
      (hf.differentiableOn (by norm_num)) (fun t _ => (hAffine t).differentiableAt.differentiableWithinAt)
      _ hx _
    · intro t ht
      rw [(hAffine t).deriv]
      exact hdconst ht
    · dsimp [A,B]
      ring
  exact ⟨A,B,fun t ht => he ht⟩

end ErdosDivisibleInflection

end

end Erdos970

end OAI
