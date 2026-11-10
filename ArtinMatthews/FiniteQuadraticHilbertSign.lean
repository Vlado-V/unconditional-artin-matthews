module

public import ArtinMatthews.StandardWeilHilbertProducts
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

/-! The canonical complex sign of the actual transported local pairing is
the same sign as its global finite-place factor. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open ArtinMatthews.QuadraticGauss
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem finiteQuadraticHilbertSign_eq_local (a b : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    finiteQuadraticHilbertSign F a b v = rootSign (v.adicCompletion F)
      (finitePlaceAdicHilbertPairingFamily F 2 (numberFieldQuadraticRoots F) v
        (powerClass (v.adicCompletion F) 2 (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a))
        (powerClass (v.adicCompletion F) 2 (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b))) := by
  let C := v.adicCompletion F
  let e : rootsOfUnity 2 F ≃* rootsOfUnity 2 C :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F C).injective (numberFieldQuadraticRoots F)
  let z : rootsOfUnity 2 C := finitePlaceAdicHilbertPairingFamily F 2 (numberFieldQuadraticRoots F) v
    (powerClass C 2 (Units.map (algebraMap F C).toMonoidHom a))
    (powerClass C 2 (Units.map (algebraMap F C).toMonoidHom b))
  change rootSign F (e.symm z) = rootSign C z
  exact rootSign_eq_of_one_iff _ _ e.symm.map_eq_one_iff

end

end ArtinMatthews.QuadraticWeil
