module

public import OAI.Analysis.PDE.Weak.Elliptic.H1
public import OAI.Analysis.PDE.Weak.Elliptic.Multiplier
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport
public import ArtinMatthews.SpectralGamma0EllipticPotentialRegularity
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
public import OAI.Analysis.Normed.Function.Sobolev.PiEmbedding
public import OAI.Analysis.PDE.Weak.Elliptic.Classical.Glue
public import OAI.Analysis.PDE.Weak.Elliptic.LocalFamily


set_option backward.privateInPublic true
@[expose] public section

/-! Fourier Sobolev embedding and unique gluing of the actual potential
bootstrap.  The output is a genuine smooth representative of the L² class. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

variable (B : (Fin 2 → ℝ) → ℝ →L[ℝ] ℝ) (hB : SmoothBounded B)
  {M : ℝ} (hBM : ∀ x, ‖B x‖ ≤ M)
  (p : H1Pair 1) (hp : p ∈ H1Zero (univ : Set (Fin 2 → ℝ)))
  {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
  (he : WeakDivergenceEquation Ω p.2
    (fieldMultiplierCLM B hB.1.continuous.aestronglyMeasurable (Eventually.of_forall hBM) p.1))

include hB hBM hp hΩ he

theorem spectralElliptic_potential_contDiff_local_representative (q : ℕ)
    {x : Fin 2 → ℝ} (hx : x ∈ Ω) :
    ∃ (V : Set (Fin 2 → ℝ)) (u : (Fin 2 → ℝ) → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ContDiff ℝ q u ∧
      (∀ᵐ y ∂volume, y ∈ V → p.1 y = u y) := by
  obtain ⟨W,hW,hxW,hWΩ,hreg⟩ :=
    spectralElliptic_potential_regular_near_point B hB hBM p hp hΩ he (q+3) hx
  obtain ⟨V,K,U,hV,hxV,hVW,hK,_,hU,hUs,hUd⟩ :=
    weakRegularity_local_family hW hxW hreg.value
  obtain ⟨u,hu,hueq⟩ :=
    OAI.Analysis.Normed.Function.Sobolev.exists_contDiff_pi_representative_of_compact_L2_derivatives
      (by norm_num : 0 < 2) (by omega : 2+q < q+3) U hK hUs hUd
  refine ⟨V,u,hV,hxV,hVW.trans hWΩ,hu,?_⟩
  filter_upwards [hU,hueq] with y hy hz
  exact fun hyV => (hy hyV).symm.trans hz

theorem spectralElliptic_potential_smooth_representative :
    ∃ u : (Fin 2 → ℝ) → ℝ, ContDiffOn ℝ ∞ u Ω ∧
      (∀ᵐ y ∂volume, y ∈ Ω → u y = p.1 y) :=
  exists_smoothOn_representative hΩ p.1
    (fun q _x hx => spectralElliptic_potential_contDiff_local_representative B hB hBM p hp hΩ he q hx)

end ArtinMatthews
