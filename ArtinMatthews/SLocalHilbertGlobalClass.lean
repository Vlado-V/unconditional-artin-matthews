module

public import ArtinMatthews.StandardWeilHilbertProducts
public import ArtinMatthews.SLocalWeakApproximation
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

/-! The actual finite S-Hilbert product on diagonal global classes is the
literal product of the globally normalized finite Hilbert signs. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open ArtinMatthews.QuadraticGauss
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem sLocalHilbertSign_globalClass (S : Finset (HeightOneSpectrum (𝓞 F))) (a b : Fˣ) :
    rootSign F (sLocalHilbertForm F 2 (numberFieldQuadraticRoots F) S
      (sLocalGlobalClassMap F 2 S a) (sLocalGlobalClassMap F 2 S b)) =
      ∏ v : S, finiteQuadraticHilbertSign F a b v.1 := by
  let H : S → rootsOfUnity 2 F := fun v =>
    GlobalHilbertPairingFamily.finiteFactor F
      (finitePlaceAdicHilbertPairingFamily F 2 (numberFieldQuadraticRoots F))
      (numberFieldQuadraticRoots F) v.1 a b
  change rootSign F (∏ v : S, H v) = ∏ v : S, rootSign F (H v)
  exact map_prod _ _ _

end

end ArtinMatthews.QuadraticWeil
