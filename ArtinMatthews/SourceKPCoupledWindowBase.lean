module

public import ArtinMatthews.SourceFiniteWindowEuler
public import ArtinMatthews.SourceKPCoupledCylinderHaar
public import ArtinMatthews.SourceKPCoupledLocalProduct
public import ArtinMatthews.SourceKPCoupledCompactKernel
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

/-! The actual compact-window integral equals the positive mass of
the simultaneous wild cylinder, in the global standard Haar measure. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance coupledBaseFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance coupledBaseFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩

local notation "Oᶠ" => IntegralAdeles.Construction.finiteIntegralRing K
local notation "C₀" => sourceKPCoupledDeepCylinder K (sixthWildPrimes K)
local notation "μ₀" => sourceKPFiniteStandardHaar K
local notation "g₀" => sourceKPCoupledWildWeyl K hζ

theorem sourceKPCoupledWindow_empty :
    sourceKPFiniteWindow K ∅ = (Oᶠ : Set 𝔸ᶠ[K]) := by
  ext x
  change (∀ P, P ∉ (∅ : Finset _) → x P ∈ P.adicCompletionIntegers K) ↔
    ∀ P, x P ∈ P.adicCompletionIntegers K
  simp

theorem sourceKPCoupledWindowIntegral_empty (s : ℂ) :
    sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s (g₀).2) ∅ =
      ((μ₀).real C₀ : ℂ) := by
  have hC := sourceKPCoupledDeepCylinder_measurable K (sixthWildPrimes K)
  have hO := (IntegralAdeles.Construction.isOpen_finiteIntegralRing K).measurableSet
  have hCO : C₀ ⊆ (Oᶠ : Set 𝔸ᶠ[K]) := fun _ hx => hx.1
  unfold sourceKPFiniteWindowIntegral
  rw [sourceKPCoupledWindow_empty K]
  calc
    _ = ∫ x in (Oᶠ : Set 𝔸ᶠ[K]), (C₀).indicator (fun _ => (1 : ℂ)) x ∂μ₀ :=
      setIntegral_congr_fun hO (sourceKPCoupledCompactKernel_indicator K hζ s)
    _ = _ := by
      rw [integral_indicator hC, integral_const, Measure.real, Measure.restrict_apply_univ,
        Measure.restrict_apply hC, Set.inter_eq_left.mpr hCO]
      simp [Complex.real_smul, Measure.real]

end
end ArtinMatthews
