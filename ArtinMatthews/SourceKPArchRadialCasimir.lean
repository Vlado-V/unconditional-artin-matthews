module

public import ArtinMatthews.SourceKPArchRadialDerivative
public import ArtinMatthews.SourceArchDiagonalDerivative
public import ArtinMatthews.SourceArchUpperDerivative
public import ArtinMatthews.SourceArchCasimirLogIdentities
public import ArtinMatthews.SourceArchDiagonalCompact
public import ArtinMatthews.SourceArchSphericalRightCasimir
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

/-! The actual spherical Casimir applied to a radial height cutoff. -/

namespace ArtinMatthews.SourceArchJacquet
open scoped ContDiff MatrixGroups
noncomputable section

def sourceKPRadialUpperSection (φ : ℝ → ℝ) (A : ℝ) (s : ℂ)
    (g : GL (Fin 2) ℂ) (z : ℂ) : ℝ → ℂ :=
  sourceKPRadialPath φ (sourceKPRadialUpperHeight A g z) (sourceArchUpperSection s g z)

def sourceKPRadialDiagonalSection (φ : ℝ → ℝ) (A : ℝ) (s : ℂ)
    (g : GL (Fin 2) ℂ) : ℝ → ℂ :=
  sourceKPRadialPath φ (sourceKPRadialDiagonalHeight A g) (sourceArchDiagonalSection s g)

def sourceKPRadialSphericalSection (φ : ℝ → ℝ) (A : ℝ) (s : ℂ)
    (g : GL (Fin 2) ℂ) : ℂ :=
  (φ (A*(sourceArchHeight g)^2) : ℂ) * sourceArchSphericalGL s g

theorem sourceKPRadialUpperSection_hasDerivAt (φ : ℝ → ℝ) (A : ℝ) (s : ℂ)
    (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ) :
    HasDerivAt (sourceKPRadialUpperSection φ A s g z)
      (sourceKPRadialPathOne φ (sourceKPRadialUpperHeight A g z)
        (sourceArchUpperLogOne g z) (2*s+1) (sourceArchUpperSection s g z) t) t :=
  sourceKPRadialPath_hasDerivAt _ _ _ _ _ _
    ((hφ.differentiable (by norm_num)).differentiableAt)
    (sourceKPRadialUpperHeight_hasDerivAt A g z t)
    (sourceArchUpperSection_hasDerivAt s g z t)

theorem sourceKPRadialUpperSection_deriv_two (φ : ℝ → ℝ) (A : ℝ) (s : ℂ)
    (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ) :
    deriv (deriv (sourceKPRadialUpperSection φ A s g z)) t =
      sourceKPRadialPathTwo φ (sourceKPRadialUpperHeight A g z)
        (sourceArchUpperLogOne g z) (sourceArchUpperLogTwo g z) (2*s+1)
        (sourceArchUpperSection s g z) t :=
  sourceKPRadialPath_deriv_two _ _ _ _ _ _ _ hφ
    (sourceKPRadialUpperHeight_hasDerivAt A g z)
    (sourceArchUpperLogOne_hasDerivAt g z) (sourceArchUpperSection_hasDerivAt s g z)

theorem sourceKPRadialDiagonalSection_hasDerivAt (φ : ℝ → ℝ) (A : ℝ) (s : ℂ)
    (g : GL (Fin 2) ℂ) (t : ℝ) (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ) :
    HasDerivAt (sourceKPRadialDiagonalSection φ A s g)
      (sourceKPRadialPathOne φ (sourceKPRadialDiagonalHeight A g)
        (sourceArchDiagonalLogOne g) (2*s+1) (sourceArchDiagonalSection s g) t) t :=
  sourceKPRadialPath_hasDerivAt _ _ _ _ _ _
    ((hφ.differentiable (by norm_num)).differentiableAt)
    (sourceKPRadialDiagonalHeight_hasDerivAt A g t)
    (sourceArchDiagonalSection_hasDerivAt s g t)

theorem sourceKPRadialDiagonalSection_deriv_two (φ : ℝ → ℝ) (A : ℝ) (s : ℂ)
    (g : GL (Fin 2) ℂ) (t : ℝ) (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ) :
    deriv (deriv (sourceKPRadialDiagonalSection φ A s g)) t =
      sourceKPRadialPathTwo φ (sourceKPRadialDiagonalHeight A g)
        (sourceArchDiagonalLogOne g) (sourceArchDiagonalLogTwo g) (2*s+1)
        (sourceArchDiagonalSection s g) t :=
  sourceKPRadialPath_deriv_two _ _ _ _ _ _ _ hφ
    (sourceKPRadialDiagonalHeight_hasDerivAt A g)
    (sourceArchDiagonalLogOne_hasDerivAt g) (sourceArchDiagonalSection_hasDerivAt s g)

def sourceKPRadialSphericalCasimir (φ : ℝ → ℝ) (A : ℝ) (s : ℂ)
    (g : GL (Fin 2) ℂ) : ℂ :=
  -(deriv (deriv (sourceKPRadialUpperSection φ A s g 1)) 0 +
    deriv (deriv (sourceKPRadialUpperSection φ A s g Complex.I)) 0 +
    deriv (deriv (sourceKPRadialDiagonalSection φ A s g)) 0 -
    2*deriv (sourceKPRadialDiagonalSection φ A s g) 0)

theorem sourceKPRadialSphericalCasimir_eq (φ : ℝ → ℝ) (A : ℝ) (s : ℂ)
    (g : GL (Fin 2) ℂ) (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ) :
    sourceKPRadialSphericalCasimir φ A s g =
      (1-4*s^2)*sourceKPRadialSphericalSection φ A s g +
        (-(4*(A*(sourceArchHeight g)^2)^2*deriv (deriv φ) (A*(sourceArchHeight g)^2) : ℝ) -
          (8*s+4)*(A*(sourceArchHeight g)^2 : ℝ)*((deriv φ (A*(sourceArchHeight g)^2) : ℝ) : ℂ)) *
            sourceArchSphericalGL s g := by
  let h := A*(sourceArchHeight g)^2
  have hs : (sourceArchUpperLogOne g 1 0 : ℂ)^2 +
      (sourceArchUpperLogOne g Complex.I 0 : ℂ)^2 +
      (sourceArchDiagonalLogOne g 0 : ℂ)^2 = 1 := by
    exact_mod_cast (sourceArchCasimir_log_identities g).1
  have hl : (sourceArchUpperLogTwo g 1 0 : ℂ) +
      (sourceArchUpperLogTwo g Complex.I 0 : ℂ) +
      (sourceArchDiagonalLogTwo g 0 : ℂ) - 2*(sourceArchDiagonalLogOne g 0 : ℂ) = -2 := by
    exact_mod_cast (sourceArchCasimir_log_identities g).2
  have hU (z : ℂ) : sourceKPRadialUpperHeight A g z 0 = h := by
    simp only [sourceKPRadialUpperHeight,Complex.ofReal_zero,zero_mul,sourceKPUpperMatrix_zero,mul_one,h]
  have hA : sourceKPRadialDiagonalHeight A g 0 = h := by
    simp only [sourceKPRadialDiagonalHeight,sourceArchPositiveDiagonal_zero,mul_one,h]
  have he : sourceKPRadialSphericalCasimir φ A s g =
      -(((4*h^2*deriv (deriv φ) h : ℝ) + 4*(2*s+2)*(h : ℂ)*((deriv φ h : ℝ) : ℂ) +
            (2*s+1)^2*(φ h : ℂ)) *
          ((sourceArchUpperLogOne g 1 0 : ℂ)^2 +
            (sourceArchUpperLogOne g Complex.I 0 : ℂ)^2 + (sourceArchDiagonalLogOne g 0 : ℂ)^2) +
        ((2*h*deriv φ h : ℝ) + (2*s+1)*(φ h : ℂ)) *
          ((sourceArchUpperLogTwo g 1 0 : ℂ) + (sourceArchUpperLogTwo g Complex.I 0 : ℂ) +
            (sourceArchDiagonalLogTwo g 0 : ℂ) - 2*(sourceArchDiagonalLogOne g 0 : ℂ))) *
              sourceArchSphericalGL s g := by
    rw [sourceKPRadialSphericalCasimir,sourceKPRadialUpperSection_deriv_two _ _ _ _ _ _ hφ,
      sourceKPRadialUpperSection_deriv_two _ _ _ _ _ _ hφ,
      sourceKPRadialDiagonalSection_deriv_two _ _ _ _ _ hφ,
      (sourceKPRadialDiagonalSection_hasDerivAt φ A s g 0 hφ).deriv]
    simp only [sourceKPRadialPathTwo,sourceKPRadialPathOne,hU,hA,
      sourceArchUpperSection_zero,sourceArchDiagonalSection_zero]
    ring
  rw [he,hs,hl,sourceKPRadialSphericalSection]
  dsimp only [h]
  push_cast
  ring

end
end ArtinMatthews.SourceArchJacquet
