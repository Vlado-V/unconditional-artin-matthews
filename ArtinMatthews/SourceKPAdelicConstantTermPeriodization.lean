module

public import ArtinMatthews.SourceKPAdelicEisensteinHolomorphic
public import ArtinMatthews.SourceKPAdelicEisensteinConvergence
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

/-! The actual upper-unipotent restriction of the Eisenstein series is
the rational periodization of its global intertwining kernel. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicPrincipalSeriesScalar_upper (s : ℂ)
    (f : SourceKPAdelicPrincipalSeries K hζ s) (y : 𝔸[K]) (g : SourceKPAdelicProjective K hζ) :
    (sourceKPAdelicPrincipalSeriesScalar K hζ s f).val (sourceKPAdelicUpperLift K hζ y*g) =
      (sourceKPAdelicPrincipalSeriesScalar K hζ s f).val g := by
  let b := sourceKPAdelicBorelCoordinatesEquiv K hζ (y,1)
  have hb : b.val = sourceKPAdelicUpperLift K hζ y := by
    rw [sourceKPAdelicBorelCoordinatesEquiv_val]
    exact mul_one _
  have hp : sourceKPAdelicBorelTorusProjection K hζ b = 1 :=
    sourceKPAdelicBorelTorusProjection_coordinates K hζ y 1
  have hm : sourceKPAdelicBorelModularHalf K hζ b = 1 := by
    change (sourceKPIdeleComplexNorm K (1/2 : ℂ)
      (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b)) : ℂ) = 1
    rw [hp, map_one, map_one, Units.val_one]
  change (f.val (sourceKPAdelicUpperLift K hζ y*g)).val 1 = (f.val g).val 1
  rw [← hb, sourceAlgebraicInducedSpace_covariant]
  change (sourceKPAdelicBorelModularHalf K hζ b •
    sourceKPAdelicTorusInducedRepresentation K hζ s (sourceKPAdelicBorelTorusProjection K hζ b)
      (f.val g)).val 1 = _
  rw [hm,hp,map_one,one_smul]
  rfl

def sourceKPAdelicIntertwiningKernel (s : ℂ) (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) : ℂ :=
  sourceKPAdelicCompactScalar K hζ s
    (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ y * g)

theorem sourceKPAdelicIntertwiningKernel_entire (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    Differentiable ℂ (fun s => sourceKPAdelicIntertwiningKernel K hζ s g y) :=
  sourceKPAdelicCompactScalar_entire K hζ _

theorem sourceKPAdelicIntertwiningKernel_shift (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) (x : K) :
    sourceKPAdelicIntertwiningKernel K hζ s g (algebraMap K 𝔸[K] x+y) =
      sourceKPAdelicCompactScalar K hζ s
        (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) *
          (sourceKPAdelicUpperLift K hζ y*g)) := by
  unfold sourceKPAdelicIntertwiningKernel
  rw [sourceKPAdelicUpperLift_add]
  simp only [mul_assoc]

theorem sourceKPAdelicIntertwiningKernel_periodization_summable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    Summable (fun x : K => sourceKPAdelicIntertwiningKernel K hζ s g (algebraMap K 𝔸[K] x+y)) := by
  simp_rw [sourceKPAdelicIntertwiningKernel_shift]
  exact sourceKPAdelicCompact_openCell_summable K hζ hs _

theorem sourceKPAdelicCompactEisenstein_upper_periodization {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g) =
      sourceKPAdelicCompactScalar K hζ s g +
        ∑' x : K, sourceKPAdelicIntertwiningKernel K hζ s g (algebraMap K 𝔸[K] x+y) := by
  rw [sourceKPAdelicCompactEisenstein, sourceKPAdelicEisensteinSum_bruhat K hζ s _ _
    (sourceKPAdelicCompactEisenstein_converges K hζ hs _)]
  have hu := sourceKPAdelicPrincipalSeriesScalar_upper K hζ s (sourceKPAdelicCompactSection K hζ s) y g
  change sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicUpperLift K hζ y*g) =
    sourceKPAdelicCompactScalar K hζ s g at hu
  change sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicUpperLift K hζ y*g) +
    (∑' x : K, sourceKPAdelicCompactScalar K hζ s
      (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) *
        (sourceKPAdelicUpperLift K hζ y*g))) = _
  rw [hu]
  simp_rw [sourceKPAdelicIntertwiningKernel_shift]

theorem sourceKPAdelicCompactEisenstein_upper_rational {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) (a : K) :
    sourceKPAdelicCompactEisenstein K hζ s
      (sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] a+y)*g) =
        sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g) := by
  rw [sourceKPAdelicUpperLift_add, mul_assoc, sourceKPAdelicUpperLift_rational]
  exact sourceKPAdelicEisensteinSum_rational K hζ s (sourceKPAdelicCompactSection K hζ s) _
    (sourceKPAdelicCompactEisenstein_converges K hζ hs _) (sourcePGL2Upper a)

end
end ArtinMatthews
