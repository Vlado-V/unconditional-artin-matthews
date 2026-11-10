module

public import ArtinMatthews.SourceKPDeepHensel
public import ArtinMatthews.SourceKPDeepMultiplier
public import ArtinMatthews.SourceFiniteKP2Cover
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

/-! The actual deep principal congruence subgroup of the completed
integer matrix group and its phase-one cubic covering section. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain IsLocalRing Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local notation "O" => P.adicCompletionIntegers K
local notation "L" => P.adicCompletion K

def sourceKPDeepIntegralGroup : Subgroup (GL (Fin 2) O) :=
  (GeneralLinearGroup.map (Ideal.Quotient.mk (sourceKPDeepIdeal K P))).ker

theorem sourceKPDeepIntegral_diagonal (g : sourceKPDeepIntegralGroup K P) (i : Fin 2) :
    g.val i i - 1 ∈ sourceKPDeepIdeal K P := by
  have hg : GeneralLinearGroup.map (Ideal.Quotient.mk (sourceKPDeepIdeal K P)) g.val = 1 := g.property
  have he : Ideal.Quotient.mk (sourceKPDeepIdeal K P) (g.val i i) = 1 := by
    simpa using congrArg (fun a : GL (Fin 2) (O ⧸ sourceKPDeepIdeal K P) => a i i) hg
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_one, he, sub_self]

theorem sourceKPDeepIntegral_det (g : sourceKPDeepIntegralGroup K P) :
    (GeneralLinearGroup.det g.val : O) - 1 ∈ sourceKPDeepIdeal K P := by
  have hg : GeneralLinearGroup.map (Ideal.Quotient.mk (sourceKPDeepIdeal K P)) g.val = 1 := g.property
  have hd := congrArg GeneralLinearGroup.det hg
  rw [GeneralLinearGroup.map_det, map_one] at hd
  have he := congrArg Units.val hd
  change Ideal.Quotient.mk (sourceKPDeepIdeal K P) (GeneralLinearGroup.det g.val : O) = 1 at he
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_one, he, sub_self]

def sourceKPDeepLocalBase : sourceKPDeepIntegralGroup K P →* GL (Fin 2) L :=
  (GeneralLinearGroup.map (algebraMap O L)).comp (sourceKPDeepIntegralGroup K P).subtype

theorem sourceKPDeepLocalBase_cubeData (g : sourceKPDeepIntegralGroup K P) :
    SourceKPMatrixCubeData (sourceKPDeepLocalBase K P g) := by
  refine ⟨?_, ?_, ?_⟩
  · change ∃ a : Lˣ, algebraMap O L (g.val 0 0) = ((a^3 : Lˣ) : L)
    exact sourceKPDeepEntry_cube K P _ (sourceKPDeepIntegral_diagonal K P g 0)
  · change ∃ d : Lˣ, algebraMap O L (g.val 1 1) = ((d^3 : Lˣ) : L)
    exact sourceKPDeepEntry_cube K P _ (sourceKPDeepIntegral_diagonal K P g 1)
  · obtain ⟨a,ha⟩ := sourceKPDeepEntry_cube K P (GeneralLinearGroup.det g.val : O)
      (sourceKPDeepIntegral_det K P g)
    refine ⟨a, ?_⟩
    apply Units.ext
    change ((a^3 : Lˣ) : L) = (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap O L) g.val) : L)
    rw [GeneralLinearGroup.map_det]
    exact ha.symm

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPDeepLocalBase_multiplier (g h : sourceKPDeepIntegralGroup K P) :
    sourceFiniteKP2Multiplier K hζ P (sourceKPDeepLocalBase K P g) (sourceKPDeepLocalBase K P h) = 1 := by
  apply sourceFiniteKP2Multiplier_deep_cubes K hζ P
  · exact sourceKPDeepLocalBase_cubeData K P g
  · exact sourceKPDeepLocalBase_cubeData K P h
  · rw [← map_mul]
    exact sourceKPDeepLocalBase_cubeData K P (g*h)

def sourceKPDeepLocalSection : sourceKPDeepIntegralGroup K P →* SourceFiniteKP2Cover K hζ P where
  toFun g := ⟨1, sourceKPDeepLocalBase K P g⟩
  map_one' := by
    apply SourceFiniteKP2Cover.ext
    · rfl
    · exact map_one (sourceKPDeepLocalBase K P)
  map_mul' g h := by
    apply SourceFiniteKP2Cover.ext
    · change 1 = 1 * 1 * sourceFiniteKP2Multiplier K hζ P
        (sourceKPDeepLocalBase K P g) (sourceKPDeepLocalBase K P h)
      rw [sourceKPDeepLocalBase_multiplier, mul_one, mul_one]
    · exact map_mul (sourceKPDeepLocalBase K P) g h

theorem sourceKPDeepLocalSection_projection (g : sourceKPDeepIntegralGroup K P) :
    sourceFiniteKP2Projection K hζ P (sourceKPDeepLocalSection K P hζ g) =
      sourceKPDeepLocalBase K P g := rfl

end
end ArtinMatthews
