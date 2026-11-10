module

public import ArtinMatthews.AnalyticWeilSquareClasses
public import ArtinMatthews.AdicConductorBridge
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
public import ArtinMatthews.AdicAnalyticWeil
public import ArtinMatthews.QuadraticHilbertNormSign
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

/-! Actual tame adic analytic Weil cocycle with a transported genuine
Hilbert pairing. The character is arbitrary conductor zero; its residue
Gauss comparison and the pairing sign are both derived. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance adicCocycleCharZero : CharZero (v.adicCompletion F) :=
  charZero_of_injective_ringHom (algebraMap F (v.adicCompletion F)).injective
local instance adicCocycleMeasurable : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance adicCocycleBorel : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem adicAnalyticWeil_cocycle (ψ : AddChar (v.adicCompletion F) ℂ)
    (hψ : adicConductorZero F v ψ) (hu : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
    (htwo : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1)
    (B : HilbertPairing (v.adicCompletion F) 2) (hB : B.IsLocalHilbertPairing)
    (a b : (v.adicCompletion F)ˣ) :
    analyticNormalizedWeil ψ a * analyticNormalizedWeil ψ b =
      rootSign (v.adicCompletion F)
        (B (powerClass (v.adicCompletion F) 2 a) (powerClass (v.adicCompletion F) 2 b)) *
      analyticNormalizedWeil ψ (a * b) := by
  let C := v.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : ValuativeRel C := adicRelation F v
  let : IsNonarchimedeanLocalField C := adicLocalField F v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  have h2 : ValuativeRel.valuation C (2 : C) = 1 := by
    have hrel : (2 : C) =ᵥ (1 : C) := (Valuation.veq_iff_eq ν).mpr (by simpa only [map_one] using htwo)
    simpa only [map_one] using (Valuation.veq_iff_eq (ValuativeRel.valuation C)).mp hrel
  let μ := tamePrimitiveRoots C h2
  let χ := conductorResidueChar C ψ hψ
  have hcmp (x : Cˣ) : analyticNormalizedWeil ψ x = localTameGaussSection C χ x :=
    adic_normalizedAnalyticWeil_eq_tame F v ψ hψ hu hc htwo x
  calc
    _ = localTameGaussSection C χ a * localTameGaussSection C χ b :=
      congrArg₂ (· * ·) (hcmp a) (hcmp b)
    _ = localQuadraticHilbert C h2 μ a b * localTameGaussSection C χ (a * b) :=
      localTameGaussSection_cocycle C h2 μ χ (conductorResidueChar_nontrivial C ψ hψ) a b
    _ = _ := congrArg₂ (· * ·) (localQuadraticHilbert_eq_pairingSign C h2 μ B hB a b) (hcmp (a * b)).symm

end

end ArtinMatthews.QuadraticWeil
