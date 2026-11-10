module

public import ArtinMatthews.SourceKPCoupledWindowContinuation
public import ArtinMatthews.SourceAdelicIntertwinerEuler
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! The checked nonzero continuation of the literal finite window
is the remainder in the actual global trace intertwiner at the wild test. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourceArchJacquet
open scoped NumberField AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCoupledTraceIntertwiner_eq_window :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      sixthWildPrimes K ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ s : ℂ, ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        sourceKPAdelicTraceIntertwiner K hζ s (sourceKPCoupledWildWeyl K hζ) =
          (((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K)) *
            (sourceKPExteriorScattering S s * sourceKPCoupledWindowContinuation K S s) := by
  obtain ⟨S, hS, hHilbert, hTrace, h⟩ := sourceKPAdelicTraceIntertwiner_eq_euler K hζ
    (sourceKPCoupledWildWeyl K hζ) (sixthWildPrimes K)
  refine ⟨S, hS, hHilbert, hTrace, fun s hs => ?_⟩
  have he := h s hs
  rw [sourceKPCoupledWildWeyl_arch K hζ, sourceKPCoupledWindowContinuation_agrees K hζ S hs] at he
  simpa only [sourceArchSphericalProduct, map_one, sourceArchSphericalSection_one,
    Finset.prod_const_one, mul_one] using he

end
end ArtinMatthews
