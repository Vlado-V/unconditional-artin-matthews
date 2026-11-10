module

public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceAdelicScalarHaar
public import ArtinMatthews.SourceKPIntertwinerRationalKernel
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

/-! Rational-Borel invariance in the group variable of the actual
trace-Haar intertwining integral. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped NumberField MatrixGroups AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPTraceRationalMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPTraceRationalBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicTraceIntertwiner_rational_diagonal (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (a : Kˣ) :
    sourceKPAdelicTraceIntertwiner K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) * g) =
        sourceKPAdelicTraceIntertwiner K hζ s g := by
  unfold sourceKPAdelicTraceIntertwiner sourceKPAdelicIntertwiner
  simp_rw [sourceKPAdelicIntertwiningKernel_rational_diagonal]
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  have he : MeasurableEmbedding (fun y : 𝔸[K] =>
      algebraMap K 𝔸[K] (↑(a⁻¹) : K) * y) :=
    sourceKPAdelicPrincipalMul_measurableEmbedding K a⁻¹
  exact (sourceKPAdelicStandardHaar_principal_mul K a⁻¹).integral_comp he
    (sourceKPAdelicIntertwiningKernel K hζ s g)

theorem sourceKPAdelicTraceIntertwiner_rationalBorel (s : ℂ) (b : PGL(2, K))
    (hb : b ∈ sourceKPRationalBorel K) (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicTraceIntertwiner K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ b * g) =
        sourceKPAdelicTraceIntertwiner K hζ s g := by
  have hb' : b ∈ sourceKPRingBorel K := by
    rw [sourceKPRingBorel_field]
    exact hb
  obtain ⟨x, a, hba⟩ := (sourceKPRingBorel_mem_iff K b).mp hb'
  have hu : sourceKPAdelicProjectiveRationalLift K hζ
      (ProjGenLinGroup.mk (sourceKPUpperMatrix K x)) =
        sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) := by
    rw [sourceKPUpperMatrix_field]
    exact (sourceKPAdelicUpperLift_rational K hζ x).symm
  rw [hba, map_mul, mul_assoc, hu, sourceKPAdelicTraceIntertwiner_left_upper,
    sourceKPAdelicTraceIntertwiner_rational_diagonal]

def sourceKPAdelicTraceIntertwiner_asRationalBorelFunction (s : ℂ) :
    SourceKPRationalBorelFunction K hζ :=
  ⟨sourceKPAdelicTraceIntertwiner K hζ s,
    sourceKPAdelicTraceIntertwiner_rationalBorel K hζ s⟩

theorem sourceKPAdelicTraceIntertwiner_asRationalBorelFunction_apply
    (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    (sourceKPAdelicTraceIntertwiner_asRationalBorelFunction K hζ s).val g =
      sourceKPAdelicTraceIntertwiner K hζ s g := rfl

end
end ArtinMatthews
