module

public import ArtinMatthews.SpectralEisensteinRegularMatching
public import ArtinMatthews.SpectralEisensteinRegularGerms
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

/-! Parametrization of the critical line and access to its regular points. -/
noncomputable section
open Set Filter Topology
namespace ArtinMatthews

def eisensteinCriticalPoint (t : ℝ) : ℂ :=
  ((1/2:ℝ):ℂ)+(t:ℂ)*Complex.I

theorem eisensteinCriticalPoint_re (t : ℝ) : (eisensteinCriticalPoint t).re=1/2 := by
  simp [eisensteinCriticalPoint,Complex.mul_re]

theorem eisensteinCriticalPoint_im (t : ℝ) : (eisensteinCriticalPoint t).im=t := by
  simp [eisensteinCriticalPoint,Complex.mul_im]

theorem eisensteinCriticalPoint_im_eq {s : ℂ} (hs : s.re=1/2) : eisensteinCriticalPoint s.im=s :=
  Complex.ext (by rw [eisensteinCriticalPoint_re,hs]) (eisensteinCriticalPoint_im _)

theorem eisensteinCriticalPoint_injective : Function.Injective eisensteinCriticalPoint :=
  fun a b h => (eisensteinCriticalPoint_im a).symm.trans
    ((congrArg Complex.im h).trans (eisensteinCriticalPoint_im b))

theorem eisensteinCriticalPoint_continuous : Continuous eisensteinCriticalPoint := by
  unfold eisensteinCriticalPoint
  fun_prop

theorem eisensteinCriticalPoint_tendsto_punctured (t : ℝ) :
    Tendsto eisensteinCriticalPoint (𝓝[≠] t) (𝓝[≠] eisensteinCriticalPoint t) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨eisensteinCriticalPoint_continuous.continuousAt.mono_left
    nhdsWithin_le_nhds,?_⟩
  filter_upwards [(self_mem_nhdsWithin : ({t}:Set ℝ)ᶜ∈𝓝[≠] t)] with u hu
  intro h
  exact hu (mem_singleton_iff.mpr (eisensteinCriticalPoint_injective (mem_singleton_iff.mp h)))

theorem eisensteinCritical_frequency_eventually_ne_zero (t : ℝ) :
    ∀ᶠ u in 𝓝[≠] t,u≠0 := by
  by_cases ht : t=0
  · subst t
    exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
      (show t∈({0}:Set ℝ)ᶜ from ht))

theorem gamma0EisensteinMatchingRegular_critical_eventually (N : ℕ) [NeZero N] (t : ℝ) :
    ∀ᶠ u in 𝓝[≠] t,gamma0EisensteinMatchingRegular N (eisensteinCriticalPoint u) ∧ u≠0 :=
  ((eisensteinCriticalPoint_tendsto_punctured t).eventually
    (gamma0EisensteinMatchingRegular_eventually N (eisensteinCriticalPoint t))).and
    (eisensteinCritical_frequency_eventually_ne_zero t)

end ArtinMatthews
