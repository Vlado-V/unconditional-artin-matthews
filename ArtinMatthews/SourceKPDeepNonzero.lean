module

public import ArtinMatthews.SourceKPDeepCubes
public import ArtinMatthews.SourceFiniteKPMultipliers
public import ArtinMatthews.SourceKPHilbertSum
public import ArtinMatthews.SourceKubotaBottomRows
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

/-! The nonzero lower-row branch of the actual deep compact multiplier.
Cube diagonal entries reduce it to the additive Steinberg identity. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceFiniteKP2Multiplier_deep_nonzero
    (g h : GL (Fin 2) (P.adicCompletion K))
    (hg : g 1 0 ≠ 0) (hh : h 1 0 ≠ 0) (hgh : (g*h) 1 0 ≠ 0)
    (a d : (P.adicCompletion K)ˣ)
    (ha : h 0 0 = ((a^3 : (P.adicCompletion K)ˣ) : P.adicCompletion K))
    (hd : g 1 1 = ((d^3 : (P.adicCompletion K)ˣ) : P.adicCompletion K))
    (hdet : GeneralLinearGroup.det g ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceFiniteKP2Multiplier K hζ P g h = 1 := by
  let B := sourceFiniteKPHilbert K hζ P
  let x := sourceKubotaX g
  let y := sourceKubotaX h
  let z := sourceKubotaX (g*h)
  have hs : (z : P.adicCompletion K) =
      ((x*a^3 : (P.adicCompletion K)ˣ) : P.adicCompletion K) +
        ((d^3*y : (P.adicCompletion K)ˣ) : P.adicCompletion K) := by
    dsimp only [x,y,z]
    rw [Units.val_mul, Units.val_mul, sourceKubotaX_val_left _ hgh,
      sourceKubotaX_val_left _ hg, sourceKubotaX_val_left _ hh,
      sourceGL2_bottom_left_mul, ha, hd]
  have haC : a^3 ∈ sourceKPUnitCubes (P.adicCompletion K) := ⟨a,rfl⟩
  have hdC : d^3 ∈ sourceKPUnitCubes (P.adicCompletion K) := ⟨d,rfl⟩
  have hsymbol : B (z/x) (z/y) = 1 := by
    have hsum := sourceFiniteKPHilbert_sum K hζ P z (x*a^3) (d^3*y) hs
    rw [mul_comm (d^3) y, div_mul_eq_div_div, div_mul_eq_div_div,
      sourceFiniteKPHilbert_div_cubes K hζ P (z/x) (z/y) (a^3) (d^3) haC hdC] at hsum
    exact hsum
  have hstrip : B (z/x) (z/(y*GeneralLinearGroup.det g)) = B (z/x) (z/y) := by
    rw [div_mul_eq_div_div, map_div,
      sourceFiniteKPHilbert_of_cube_right K hζ P (z/x) (GeneralLinearGroup.det g) hdet, div_one]
  change B (z/x) (z/(y*GeneralLinearGroup.det g)) *
    B (GeneralLinearGroup.det g) (GeneralLinearGroup.det h)^2 = 1
  rw [hstrip, hsymbol,
    sourceFiniteKPHilbert_of_cube_left K hζ P (GeneralLinearGroup.det g) (GeneralLinearGroup.det h) hdet,
    one_pow, one_mul]

end
end ArtinMatthews
