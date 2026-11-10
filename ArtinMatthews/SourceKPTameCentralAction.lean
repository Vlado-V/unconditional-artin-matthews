module

public import ArtinMatthews.SourceKPTameSpherical
public import ArtinMatthews.SourceKPTameTorusValues
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! The actual algebraic normalized induction is genuine. Its center
acts through the same inverse angular embedding as the torus action. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceFiniteKPProjectiveBorelCenter (z : rootsOfUnity 3 (P.adicCompletion K)) :
    SourceFiniteKPProjectiveBorel K hζ P :=
  sourceFiniteKPProjectiveBorelEquiv K hζ P
    ⟨sourceFiniteKP2Center K hζ P z, (sourceGL2NormalizedBorel (P.adicCompletion K)).one_mem⟩

theorem sourceFiniteKPProjectiveBorelCenter_val (z : rootsOfUnity 3 (P.adicCompletion K)) :
    (sourceFiniteKPProjectiveBorelCenter K hζ P z).val = sourceFiniteKP2ProjectiveCenter K hζ P z := rfl

variable (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))

theorem sourceKPTameBorelRepresentation_center (z : rootsOfUnity 3 (P.adicCompletion K)) (f : ZMod 3 → ℂ) :
    sourceKPTameBorelRepresentation K hζ P h6 π hπ (sourceFiniteKPProjectiveBorelCenter K hζ P z) f =
      (sourceKPCentralComplex K hζ P z : ℂ) • f := by
  rw [sourceFiniteKPProjectiveBorelCenter, sourceKPTameBorelRepresentation_of_normalized]
  let b : SourceFiniteKPNormalizedBorel K hζ P :=
    ⟨sourceFiniteKP2Center K hζ P z, (sourceGL2NormalizedBorel (P.adicCompletion K)).one_mem⟩
  have hb : sourceFiniteKPNormalizedBorelBase K hζ P b = 1 := by
    change GeneralLinearGroup.det (1 : GL (Fin 2) (P.adicCompletion K)) = 1
    exact map_one _
  have hu : sourceKPFiniteVal K P (sourceFiniteKPNormalizedBorelBase K hζ P b : P.adicCompletion K) = 1 := by
    rw [hb, Units.val_one, map_one]
  have ht : sourceFiniteKPNormalizedBorelToTorus K hζ P b = sourceFiniteKPRankOneCenter K hζ P z := by
    apply Subtype.ext
    apply SourceFiniteKP2Cover.ext
    · rfl
    · change sourceGL2Diagonal (sourceFiniteKPNormalizedBorelBase K hζ P b) = 1
      rw [hb]
      exact (sourceGL2DiagonalHom (P.adicCompletion K)).map_one
  change sourceKPTameBorelHalf K hζ P b • (sourceKPTameTorusRepresentation K hζ P h6 π hπ
    (sourceFiniteKPNormalizedBorelToTorus K hζ P b) f) = _
  rw [sourceKPTameBorelHalf_of_unit K hζ P b hu, ht, one_smul, sourceKPTameTorusRepresentation_center]

theorem sourceKPTameInducedRepresentation_center (z : rootsOfUnity 3 (P.adicCompletion K))
    (f : sourceKPTameInducedSpace K hζ P h6 π hπ) :
    sourceKPTameInducedRepresentation K hζ P h6 π hπ (sourceFiniteKP2ProjectiveCenter K hζ P z) f =
      (sourceKPCentralComplex K hζ P z : ℂ) • f := by
  apply Subtype.ext
  funext g
  change f.val (g * sourceFiniteKP2ProjectiveCenter K hζ P z) =
    (sourceKPCentralComplex K hζ P z : ℂ) • f.val g
  rw [(sourceFiniteKP2ProjectiveCenter_commute K hζ P z g).eq.symm, ← sourceFiniteKPProjectiveBorelCenter_val,
    f.property, sourceKPTameBorelRepresentation_center]

end
end ArtinMatthews
