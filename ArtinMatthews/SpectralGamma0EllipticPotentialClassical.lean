module

public import ArtinMatthews.SpectralGamma0EllipticTests
public import OAI.Analysis.PDE.Weak.Elliptic.H1
public import OAI.Analysis.PDE.Weak.Elliptic.Multiplier
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport
public import ArtinMatthews.SpectralGamma0EllipticPotentialSmooth
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
public import OAI.Analysis.PDE.Variational.LocalizedEquation
public import OAI.Analysis.PDE.Weak.Elliptic.Classical.Equation
public import OAI.Analysis.PDE.Weak.Elliptic.Classical.Glue


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine smooth representative of a weak potential solution also
satisfies its classical equation. No smooth representative is an input. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem spectralEllipticPositiveLaplacian_germ {u v : (Fin 2 → ℝ) → ℝ}
    {x : Fin 2 → ℝ} (h : u =ᶠ[𝓝 x] v) :
    spectralEllipticPositiveLaplacian u x = spectralEllipticPositiveLaplacian v x := by
  unfold spectralEllipticPositiveLaplacian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hd : (fun y => fderiv ℝ u y (Pi.single i 1)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ v y (Pi.single i 1)) :=
    h.fderiv.mono (fun y hy => congrArg (fun A : (Fin 2 → ℝ) →L[ℝ] ℝ =>
      A (Pi.single i 1)) hy)
  exact congrArg (fun A : (Fin 2 → ℝ) →L[ℝ] ℝ => A (Pi.single i 1)) hd.fderiv_eq

variable (B : (Fin 2 → ℝ) → ℝ →L[ℝ] ℝ) (hB : SmoothBounded B)
  {M : ℝ} (hBM : ∀ x, ‖B x‖ ≤ M)
  (p : H1Pair 1) (hp : p ∈ H1Zero (univ : Set (Fin 2 → ℝ)))
  {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
  (he : WeakDivergenceEquation Ω p.2
    (fieldMultiplierCLM B hB.1.continuous.aestronglyMeasurable (Eventually.of_forall hBM) p.1))

include hB hBM hp hΩ he

theorem spectralElliptic_potential_smooth_classical_representative :
    ∃ u : (Fin 2 → ℝ) → ℝ, ContDiffOn ℝ ∞ u Ω ∧
      (∀ᵐ y ∂volume, y ∈ Ω → u y = p.1 y) ∧
      ∀ x ∈ Ω, spectralEllipticPositiveLaplacian u x = B x (u x) := by
  obtain ⟨u,hu,hup⟩ := spectralElliptic_potential_smooth_representative B hB hBM p hp hΩ he
  refine ⟨u,hu,hup,?_⟩
  intro x hx
  obtain ⟨V,v,hV,hxV,hVΩ,hv,hpv⟩ :=
    spectralElliptic_potential_contDiff_local_representative B hB hBM p hp hΩ he 2 hx
  have huv : EqOn u v V := by
    apply continuous_eqOn_of_local_ae hV (hu.continuousOn.mono hVΩ) hv.continuous.continuousOn
    filter_upwards [hup,hpv] with y hy hz
    exact fun hyV => (hy (hVΩ hyV)).trans (hz hyV)
  have heV : WeakDivergenceEquation V (fun y => (ContinuousLinearMap.id ℝ (CellVectors 1)) (p.2 y))
      (fieldMultiplierCLM B hB.1.continuous.aestronglyMeasurable (Eventually.of_forall hBM) p.1) :=
    weakEquation_congr_on he hVΩ (Eventually.of_forall fun _ _ => rfl)
      (Eventually.of_forall fun _ _ => rfl)
  have hfv : ∀ᵐ y ∂volume, y ∈ V →
      fieldMultiplierCLM B hB.1.continuous.aestronglyMeasurable
        (Eventually.of_forall hBM) p.1 y = B y (v y) := by
    filter_upwards [fieldMultiplierCLM_ae B hB.1.continuous.aestronglyMeasurable
      (Eventually.of_forall hBM) p.1,hpv] with y hy hz
    exact fun hyV => hy.trans (congrArg (B y) (hz hyV))
  have hclass := classical_equation_of_H1_representative hV
    (fun _ => ContinuousLinearMap.id ℝ (CellVectors 1)) contDiff_const p hp _
    (fun y => B y (v y)) (hB.1.continuous.clm_apply hv.continuous) hfv heV v hv hpv
  have hvx : spectralEllipticPositiveLaplacian v x = B x (v x) := hclass.2 x hxV
  have hlocal : u =ᶠ[𝓝 x] v := Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) huv
  rw [spectralEllipticPositiveLaplacian_germ hlocal,huv hxV]
  exact hvx

end ArtinMatthews
