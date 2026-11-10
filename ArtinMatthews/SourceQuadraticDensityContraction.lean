module

public import ArtinMatthews.QuadraticHeckeFiniteEnergy
public import ArtinMatthews.QuadraticHeckeMainTermEuler
public import ArtinMatthews.SourceQuadraticConductor
public import ArtinMatthews.SourceQuadraticLocalClasses
public import ArtinMatthews.QuadraticHeckeDensityContraction
public import ArtinMatthews.QuadraticHeckeSmallResidue
public import ArtinMatthews.SourceQuadraticBlockIdeals
public import ArtinMatthews.SourceQuadraticPairConductor
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
public import Mathlib.NumberTheory.Height.NumberField
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "ρ" => quadraticHeckeCoprimeDensity F

theorem sourceQuadraticPairConductor_density (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    ρ (sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))) =
      ρ (I (b - g)) * ρ (I (c - g)) := by
  rw [sourceQuadraticPairConductor_eq_product F S₀ hζ b c g hb hc hg hclass]
  exact quadraticHeckeCoprimeDensity_mul F
    (sourcePrimeExponentIdeal_ne_bot F S₀ (b - g))
    (sourcePrimeExponentIdeal_ne_bot F S₀ (c - g))
    ((sourceQuadraticBlock_ideal_coprime_iff F S₀ _ _).mpr
      (sourceQuadraticPair_residual_data F S₀ b c g hb hc hg).2.2.1)

def sourceQuadraticDensityTwistedCoeff (g : E) (u : E → ℂ) (b : E) : ℂ :=
  ρ (I (b - g)) * u b

theorem sourceQuadraticDensityTwistedCoeff_mass (cols : Finset E) (g : E) (u : E → ℂ) :
    coeffMass cols (sourceQuadraticDensityTwistedCoeff F S₀ g u) ≤ coeffMass cols u := by
  exact quadraticHeckeCoprimeDensity_mass_le F cols (fun b => I (b - g)) u

theorem sourceQuadraticPair_density_twist (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (u : E → ℂ) :
    star (u b) * u c * ρ (sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))) =
      star (sourceQuadraticDensityTwistedCoeff F S₀ g u b) *
        sourceQuadraticDensityTwistedCoeff F S₀ g u c := by
  rw [sourceQuadraticPairConductor_density F S₀ hζ b c g hb hc hg hclass]
  simp only [sourceQuadraticDensityTwistedCoeff, star_mul,
    quadraticHeckeCoprimeDensity_star]
  ring

end
end ArtinMatthews.SourceEulerAssembly
