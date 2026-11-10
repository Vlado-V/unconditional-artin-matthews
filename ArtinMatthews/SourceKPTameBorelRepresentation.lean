module

public import ArtinMatthews.SourceFiniteKPProjectiveBorel
public import ArtinMatthews.SourceKPTameTorusRepresentation
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

/-! The actual normalized Borel action for the tame model. The modular
half factor is the explicit Q^(-ord/2). The compact upper triangular
lifts fix the distinguished basis vector. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups ValuativeRel
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceKPTameBorelHalf : SourceFiniteKPNormalizedBorel K hζ P →* ℂ where
  toFun g := sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ)
    (-(sourceKPValuationOrder (sourceKPFiniteVal K P) (sourceFiniteKPNormalizedBorelBase K hζ P g) : ℝ) / 2)
  map_one' := by
    rw [map_one, sourceKPValuationOrder_one]
    simp [sourceJacquetScale]
  map_mul' g h := by
    let ν := sourceKPFiniteVal K P
    let b := sourceFiniteKPNormalizedBorelBase K hζ P
    let Q : ℝ := Ideal.absNorm P.asIdeal
    have hQ : 0 < Q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))
    change sourceJacquetScale Q (-(sourceKPValuationOrder ν (b (g * h)) : ℝ) / 2) =
      sourceJacquetScale Q (-(sourceKPValuationOrder ν (b g) : ℝ) / 2) *
        sourceJacquetScale Q (-(sourceKPValuationOrder ν (b h) : ℝ) / 2)
    rw [map_mul b, sourceKPValuationOrder_mul, Int.cast_add, ← sourceJacquetScale_add hQ]
    congr 1
    ring

theorem sourceKPTameBorelHalf_of_unit (g : SourceFiniteKPNormalizedBorel K hζ P)
    (hg : sourceKPFiniteVal K P (sourceFiniteKPNormalizedBorelBase K hζ P g : P.adicCompletion K) = 1) :
    sourceKPTameBorelHalf K hζ P g = 1 := by
  change sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ)
    (-(sourceKPValuationOrder (sourceKPFiniteVal K P) (sourceFiniteKPNormalizedBorelBase K hζ P g) : ℝ) / 2) = 1
  rw [sourceKPValuationOrder_of_unit _ _ hg]
  simp [sourceJacquetScale]

variable (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))

def sourceKPTameNormalizedBorelRepresentation :
    Representation ℂ (SourceFiniteKPNormalizedBorel K hζ P) (ZMod 3 → ℂ) where
  toFun g := sourceKPTameBorelHalf K hζ P g •
    sourceKPTameTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPNormalizedBorelToTorus K hζ P g)
  map_one' := by rw [map_one, map_one, map_one, one_smul]
  map_mul' g h := by
    rw [map_mul (sourceKPTameBorelHalf K hζ P),
      map_mul (sourceFiniteKPNormalizedBorelToTorus K hζ P),
      map_mul (sourceKPTameTorusRepresentation K hζ P h6 π hπ)]
    exact (smul_mul_smul_comm _ _ _ _).symm

def sourceKPTameBorelRepresentation :
    Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) (ZMod 3 → ℂ) :=
  (sourceKPTameNormalizedBorelRepresentation K hζ P h6 π hπ).comp
    (sourceFiniteKPProjectiveBorelEquiv K hζ P).symm.toMonoidHom

theorem sourceKPTameBorelRepresentation_of_normalized (g : SourceFiniteKPNormalizedBorel K hζ P) :
    sourceKPTameBorelRepresentation K hζ P h6 π hπ (sourceFiniteKPProjectiveBorelEquiv K hζ P g) =
      sourceKPTameNormalizedBorelRepresentation K hζ P h6 π hπ g := by
  let E := sourceFiniteKPProjectiveBorelEquiv K hζ P
  change sourceKPTameNormalizedBorelRepresentation K hζ P h6 π hπ (E.symm (E g)) = _
  rw [MulEquiv.symm_apply_apply]

theorem sourceKPTameNormalizedBorelRepresentation_lift_unit
    (g : GL (Fin 2) (P.adicCompletion K)) (hg : g ∈ sourceGL2NormalizedBorel (P.adicCompletion K))
    (hd : sourceKPFiniteVal K P (GeneralLinearGroup.det g : P.adicCompletion K) = 1) :
    sourceKPTameNormalizedBorelRepresentation K hζ P h6 π hπ (sourceFiniteKPNormalizedBorelLift K hζ P g hg)
        (sourceJacquetBasis 0) = sourceJacquetBasis 0 := by
  let b := sourceFiniteKPNormalizedBorelLift K hζ P g hg
  change sourceKPTameBorelHalf K hζ P b •
    (sourceKPTameTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPNormalizedBorelToTorus K hζ P b)
      (sourceJacquetBasis 0)) = _
  have h := sourceKPTameBorelHalf_of_unit K hζ P b hd
  have hb := sourceFiniteKPNormalizedBorelToTorus_lift K hζ P g hg
  rw [h, hb, one_smul, sourceKPTameTorusRepresentation_unit_fixed K hζ P h6 π hπ _ hd]

end
end ArtinMatthews
