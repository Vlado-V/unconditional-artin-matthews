module

public import ArtinMatthews.SourceFiniteKPHilbert
public import ArtinMatthews.SourceKubotaCoordinates
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

/-! Cubic Hilbert-symbol identities for the actual deep unit subgroup.
These retain the concrete local power subgroup used by Hensel lifting. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

def sourceKPUnitCubes (F : Type*) [Field F] : Subgroup Fˣ :=
  (powMonoidHom (3 : ℕ)).range

theorem sourceKPUnitCubes_minusOne (F : Type*) [Field F] :
    sourceMinusOneUnit F ∈ sourceKPUnitCubes F := by
  refine ⟨sourceMinusOneUnit F, ?_⟩
  apply Units.ext
  simp [sourceMinusOneUnit, pow_succ]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceFiniteKPHilbert_of_cube_left (a b : (P.adicCompletion K)ˣ)
    (ha : a ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceFiniteKPHilbert K hζ P a b = 1 := by
  obtain ⟨u,hu⟩ := ha
  change u^3 = a at hu
  rw [← hu, sourceFiniteKPHilbert_cube_left]

theorem sourceFiniteKPHilbert_of_cube_right (a b : (P.adicCompletion K)ˣ)
    (hb : b ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceFiniteKPHilbert K hζ P a b = 1 := by
  obtain ⟨u,hu⟩ := hb
  change u^3 = b at hu
  rw [← hu, sourceFiniteKPHilbert_cube_right]

theorem sourceFiniteKPHilbert_div_cubes (x y a b : (P.adicCompletion K)ˣ)
    (ha : a ∈ sourceKPUnitCubes (P.adicCompletion K))
    (hb : b ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceFiniteKPHilbert K hζ P (x/a) (y/b) = sourceFiniteKPHilbert K hζ P x y := by
  rw [map_div (sourceFiniteKPHilbert K hζ P) x a, MonoidHom.div_apply,
    sourceFiniteKPHilbert_of_cube_left K hζ P a (y/b) ha,
    div_one, map_div, sourceFiniteKPHilbert_of_cube_right K hζ P x b hb, div_one]

theorem sourceFiniteKPHilbert_mul_cubes (x y a b : (P.adicCompletion K)ˣ)
    (ha : a ∈ sourceKPUnitCubes (P.adicCompletion K))
    (hb : b ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceFiniteKPHilbert K hζ P (x*a) (y*b) = sourceFiniteKPHilbert K hζ P x y := by
  rw [map_mul (sourceFiniteKPHilbert K hζ P) x a, MonoidHom.mul_apply,
    sourceFiniteKPHilbert_of_cube_left K hζ P a (y*b) ha,
    mul_one, map_mul, sourceFiniteKPHilbert_of_cube_right K hζ P x b hb, mul_one]

theorem sourceFiniteKPHilbert_of_cube_ratio (a b : (P.adicCompletion K)ˣ)
    (hab : a/b ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceFiniteKPHilbert K hζ P a b = 1 := by
  have he : a = (a/b)*b := (div_mul_cancel a b).symm
  conv_lhs => rw [he, map_mul, MonoidHom.mul_apply]
  rw [sourceFiniteKPHilbert_of_cube_left K hζ P (a/b) b hab,
    sourceFiniteKPHilbert_diag, one_mul]

end
end ArtinMatthews
