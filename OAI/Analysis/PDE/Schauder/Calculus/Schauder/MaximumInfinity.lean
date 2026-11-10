module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Dirichlet.Maximum
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Maximum principles and uniqueness for solutions decaying at infinity. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet

theorem maximum_principle_at_infinity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {ι : Type*} [Fintype ι] (a : E → ι → ℝ) (v : E → ι → E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (ha : ∀ x i, 0 ≤ a x i)
    (htrace : ∀ x, 0 < ∑ i, a x i * ‖v x i‖ ^ 2)
    (hL : ∀ x, 0 ≤ OAI.Analysis.PDE.Dirichlet.ellipticValue a v f x)
    (hinfty : Tendsto f (cocompact E) (𝓝 0)) (x : E) : f x ≤ 0 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  obtain ⟨K, hK, htail⟩ := Filter.mem_cocompact.mp (hinfty.eventually (Iio_mem_nhds hε))
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt (‖x‖ + 1) (0 : E)
  have hx : x ∈ closedBall 0 R := by
    simp only [mem_closedBall, dist_zero_right]
    linarith
  apply OAI.Analysis.PDE.Dirichlet.maximum_principle (isCompact_closedBall 0 R) hf
    (fun y _ i => ha y i) (fun y _ => htrace y) (fun y _ => hL y) ?_ x hx
  intro y _hy hyi
  have hnot : y ∉ K := fun hyK => hyi (ball_subset_interior_closedBall (hKR hyK))
  exact (htail hnot).le

theorem uniqueness_at_infinity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {ι : Type*} [Fintype ι] (a : E → ι → ℝ) (v : E → ι → E)
    (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (ha : ∀ x i, 0 ≤ a x i)
    (htrace : ∀ x, 0 < ∑ i, a x i * ‖v x i‖ ^ 2)
    (hL : ∀ x, OAI.Analysis.PDE.Dirichlet.ellipticValue a v f x = OAI.Analysis.PDE.Dirichlet.ellipticValue a v g x)
    (hf0 : Tendsto f (cocompact E) (𝓝 0))
    (hg0 : Tendsto g (cocompact E) (𝓝 0)) : f = g := by
  have hle (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
      (hL : ∀ x, OAI.Analysis.PDE.Dirichlet.ellipticValue a v f x = OAI.Analysis.PDE.Dirichlet.ellipticValue a v g x)
      (hf0 : Tendsto f (cocompact E) (𝓝 0))
      (hg0 : Tendsto g (cocompact E) (𝓝 0)) (x : E) : f x ≤ g x := by
    have h := maximum_principle_at_infinity a v (fun y => f y + (-1 : ℝ) • g y)
      (hf.add (hg.const_smul (-1 : ℝ))) ha htrace (fun y => ?_) ?_ x
    · simpa using h
    · rw [OAI.Analysis.PDE.Dirichlet.ellipticValue_add_smul a v hf hg, hL y]
      simp
    · simpa using hf0.add (hg0.const_smul (-1 : ℝ))
  funext x
  exact le_antisymm (hle f g hf hg hL hf0 hg0 x)
    (hle g f hg hf (fun x => (hL x).symm) hg0 hf0 x)

end OAI.Analysis.PDE.Schauder
