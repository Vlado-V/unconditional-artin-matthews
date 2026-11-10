module

public import ArtinMatthews.SLocalAnalyticWeil
public import ArtinMatthews.StandardTameFiniteWeil
public import ArtinMatthews.SLocalPowerModule
public import ArtinMatthews.StandardWeilSProduct
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual analytic Weil S-product is a quadratic character on every
actual isotropic subgroup. Its multiplication and sign values are derived
from the proved cocycle and square-class exponent, not supplied as premises. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open ArtinMatthews.QuadraticGauss
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
  (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : standardWeilBadPlaces F ⊆ S)
  (B : Subgroup (SLocalPowerClasses F 2 S))
  (hB : ∀ x ∈ B, ∀ y ∈ B,
    sLocalHilbertForm F 2 (numberFieldQuadraticRoots F) S x y = 1)

include hS hB

def sLocalAnalyticWeilCharacter : B →* ℂˣ where
  toFun b := Units.mk0 (sLocalAnalyticWeil F S b) (sLocalAnalyticWeil_ne_zero F S b)
  map_one' := Units.ext (sLocalAnalyticWeil_one F S)
  map_mul' a b := by
    apply Units.ext
    have h := sLocalAnalyticWeil_cocycle F S hS (a : SLocalPowerClasses F 2 S) b
    let z : rootsOfUnity 2 F := sLocalHilbertForm F 2 (numberFieldQuadraticRoots F) S
      (a : SLocalPowerClasses F 2 S) b
    have hz : z = 1 := hB a a.property b b.property
    have hsign : rootSign F z = 1 := by rw [hz, map_one]
    change sLocalAnalyticWeil F S (a : SLocalPowerClasses F 2 S) * sLocalAnalyticWeil F S b =
      rootSign F z * sLocalAnalyticWeil F S ((a : SLocalPowerClasses F 2 S) * b) at h
    rw [hsign, one_mul] at h
    exact h.symm

theorem sLocalAnalyticWeilCharacter_apply (b : B) :
    (sLocalAnalyticWeilCharacter F S hS B hB b : ℂ) = sLocalAnalyticWeil F S b := rfl

theorem sLocalAnalyticWeilCharacter_sq (b : B) :
    sLocalAnalyticWeilCharacter F S hS B hB b ^ 2 = 1 := by
  have hb : b ^ 2 = 1 := Subtype.ext (sLocalPowerClasses_pow_eq_one F 2 S (b : SLocalPowerClasses F 2 S))
  rw [← map_pow, hb, map_one]

theorem sLocalAnalyticWeilCharacter_values (b : B) :
    sLocalAnalyticWeil F S b = 1 ∨ sLocalAnalyticWeil F S b = -1 := by
  apply sq_eq_one_iff.mp
  exact congrArg Units.val (sLocalAnalyticWeilCharacter_sq F S hS B hB b)

theorem sLocalAnalyticWeilCharacter_source_value (b : B) :
    (sLocalAnalyticWeil F S ((b : SLocalPowerClasses F 2 S)⁻¹))⁻¹ =
      (sLocalAnalyticWeilCharacter F S hS B hB b : ℂ) := by
  change ((sLocalAnalyticWeilCharacter F S hS B hB b⁻¹ : ℂ))⁻¹ = _
  rw [map_inv, Units.val_inv_eq_inv_val, inv_inv]

theorem sLocalAnalyticWeilCharacter_norm (b : B) : ‖sLocalAnalyticWeil F S b‖ = 1 := by
  rcases sLocalAnalyticWeilCharacter_values F S hS B hB b with h | h <;> simp [h]

def sLocalAnalyticWeilRootCharacter : B →* rootsOfUnity 2 ℂ where
  toFun b := ⟨sLocalAnalyticWeilCharacter F S hS B hB b,
    sLocalAnalyticWeilCharacter_sq F S hS B hB b⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem sLocalAnalyticWeilRootCharacter_apply (b : B) :
    ((sLocalAnalyticWeilRootCharacter F S hS B hB b : ℂˣ) : ℂ) =
      sLocalAnalyticWeil F S b := rfl

end

end ArtinMatthews.QuadraticWeil
