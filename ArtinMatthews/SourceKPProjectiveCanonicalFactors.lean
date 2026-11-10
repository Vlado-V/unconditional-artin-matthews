module

public import ArtinMatthews.SourceKPProjectiveIwasawa
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceKubotaCocycle
public import ArtinMatthews.SourceKubotaGL2Generation
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

/-! Canonical root and torus products in the actual projective cover.
The Iwasawa factorization retains the central phase as a separate
factor ahead of the upper-root and torus sections. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceFiniteKP2ProjectiveLift_upper_add (x y : P.adicCompletion K) :
    sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x) *
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper y) =
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper (x + y)) := by
  rw [sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _
    (sourceKP2Multiplier_left_upper (sourceFiniteKPHilbert K hζ P) x (sourceGL2Upper y)), sourceGL2Upper_mul]

theorem sourceFiniteKP2ProjectiveLift_diagonal_mul (x y : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal x) *
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal y) =
        sourceFiniteKP2ProjectiveCenter K hζ P (sourceFiniteKPHilbert K hζ P x y ^ 2) *
          sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal (x * y)) := by
  rw [sourceFiniteKP2ProjectiveLift_mul, sourceFiniteKP2Multiplier_rankOne]
  exact congrArg (fun g => sourceFiniteKP2ProjectiveCenter K hζ P (sourceFiniteKPHilbert K hζ P x y ^ 2) *
    sourceFiniteKP2ProjectiveLift K hζ P g) ((sourceGL2DiagonalHom (P.adicCompletion K)).map_mul x y).symm

theorem sourceFiniteKP2Projective_Iwasawa_canonical (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (g : SourceFiniteKP2Projective K hζ P) :
    ∃ (z : rootsOfUnity 3 (P.adicCompletion K)) (x : P.adicCompletion K)
        (y : (P.adicCompletion K)ˣ) (k : SourceFiniteKP2Integral K P),
      g = sourceFiniteKP2ProjectiveCenter K hζ P z *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x) *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal y) *
        sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k := by
  obtain ⟨b, k, hg⟩ := sourceFiniteKP2Projective_Iwasawa K hζ P h6 g
  let E := sourceFiniteKPProjectiveBorelEquiv K hζ P
  let a := E.symm b
  let x := a.val.base 0 1
  let y := GeneralLinearGroup.det a.val.base
  have ha : E a = b := E.apply_symm_apply b
  have hbase : a.val.base = sourceGL2Upper x * sourceGL2Diagonal y :=
    sourceGL2NormalizedBorel_factor (P.adicCompletion K) a.val.base a.property
  have hcenter : a.val = sourceFiniteKP2Center K hζ P a.val.central * sourceFiniteKP2Lift K hζ P a.val.base := by
    apply SourceFiniteKP2Cover.ext
    · change a.val.central = a.val.central * 1 * sourceFiniteKP2Multiplier K hζ P 1 a.val.base
      rw [sourceFiniteKP2Multiplier_one_left, mul_one, mul_one]
    · change a.val.base = 1 * a.val.base
      rw [one_mul]
  have hb : b.val = sourceFiniteKP2ProjectiveMk K hζ P a.val := by
    rw [← ha]
    exact sourceFiniteKPProjectiveBorelEquiv_val K hζ P a
  have hm := congrArg (sourceFiniteKP2ProjectiveMk K hζ P) hcenter
  rw [map_mul] at hm
  refine ⟨a.val.central, x, y, k, ?_⟩
  rw [hg, hb, hm]
  change sourceFiniteKP2ProjectiveCenter K hζ P a.val.central *
      sourceFiniteKP2ProjectiveLift K hζ P a.val.base *
        sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k = _
  rw [hbase, ← sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _
    (sourceFiniteKP2Multiplier_root_diagonal K hζ P x y).1, ← mul_assoc]

end
end ArtinMatthews
