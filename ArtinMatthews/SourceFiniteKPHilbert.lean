module

public import ArtinMatthews.SLocalSourceComplements
public import ArtinMatthews.SourceCubicKPTorus
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

/-! Actual cubic Hilbert symbols in every finite completion, in the
Artin-first orientation required before the paper's transposed sextic
normalization. All the symbol laws used by the Kubota computations are
derived from CFT, including the actual Steinberg law. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory GlobalClassFieldTheory.Reciprocity
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (v : HeightOneSpectrum (𝓞 K))

def sourceFiniteKPHilbert : (v.adicCompletion K)ˣ →*
    ((v.adicCompletion K)ˣ →* rootsOfUnity 3 (v.adicCompletion K)) :=
  let p := powerClass (v.adicCompletion K) 3
  let H := finitePlaceAdicHilbertPairingFamily K 3
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) v
  (MonoidHom.compHom' p).comp (H.comp p)

theorem sourceFiniteKPHilbert_apply (a b : (v.adicCompletion K)ˣ) :
    sourceFiniteKPHilbert K hζ v a b =
      (finitePlaceAdicHilbertPairingFamily K 3
        (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) v).symbol a b := rfl

theorem sourceFiniteKPHilbert_skew (a b : (v.adicCompletion K)ˣ) :
    sourceFiniteKPHilbert K hζ v a b = (sourceFiniteKPHilbert K hζ v b a)⁻¹ := by
  exact (finitePlaceAdicHilbertPairingFamily_isLocallyHilbert K 3
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) v).2.1 _ _

theorem sourceFiniteKPHilbert_diag (a : (v.adicCompletion K)ˣ) :
    sourceFiniteKPHilbert K hζ v a a = 1 := by
  let z := sourceFiniteKPHilbert K hζ v a a
  have h : z = z⁻¹ := sourceFiniteKPHilbert_skew K hζ v a a
  have h₂ : z * z = 1 := (congrArg (z * ·) h).trans (mul_inv_cancel z)
  have h₃ := sourceCubicRoot_cube (v.adicCompletion K) z
  change z ^ (2 + 1 : ℕ) = 1 at h₃
  rw [pow_succ, pow_two, h₂, one_mul] at h₃
  exact h₃

theorem sourceFiniteKPHilbert_steinberg (a : (v.adicCompletion K)ˣ)
    (ha : 1 - (a : v.adicCompletion K) ≠ 0) :
    sourceFiniteKPHilbert K hζ v a (Units.mk0 _ ha) = 1 :=
  (finitePlaceAdicHilbertPairingFamily_isLocallyHilbert K 3
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) v).1 a ha

theorem sourceFiniteKPHilbert_cube_left (a b : (v.adicCompletion K)ˣ) :
    sourceFiniteKPHilbert K hζ v (a ^ 3) b = 1 := by
  rw [map_pow, MonoidHom.pow_apply, sourceCubicRoot_cube]

theorem sourceFiniteKPHilbert_cube_right (a b : (v.adicCompletion K)ˣ) :
    sourceFiniteKPHilbert K hζ v a (b ^ 3) = 1 := by
  rw [map_pow, sourceCubicRoot_cube]

end
end ArtinMatthews
