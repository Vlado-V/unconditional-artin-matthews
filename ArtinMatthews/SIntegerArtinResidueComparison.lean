module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
public import ArtinMatthews.AdicIntegerResidueEquiv
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

/-! Actual comparison of the norm-completion integer ring used by CFT
and the adic integer ring used by the standard additive character.
No definitional equality of the two local field models is assumed. -/
namespace ArtinMatthews.SIntegerAdicResidue

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open ArtinMatthews.QuadraticWeil
open scoped NumberField ValuativeRel Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local instance comparisonAdicRelation : ValuativeRel (P.adicCompletion K) := adicRelation K P
local instance comparisonAdicLocalField : IsNonarchimedeanLocalField (P.adicCompletion K) := adicLocalField K P

def artinAdicIntegerEquiv :
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) P] ≃+* 𝒪[P.adicCompletion K] :=
  (finitePlaceCompletionIntegerRingEquiv P).trans
    (RingEquiv.subringCongr (adic_integer_eq K P).symm)

theorem artinAdicIntegerEquiv_global (x : 𝓞 K) :
    artinAdicIntegerEquiv K P (finitePlaceIntegerToCompletion P x) = adicIntegralOfInteger K P x := by
  apply Subtype.ext
  change finitePlaceCompletionRingEquiv P
    (algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) P) (x : K)) =
      algebraMap (𝓞 K) (P.adicCompletion K) x
  rw [finitePlaceCompletionRingEquiv_toCompletion]
  change algebraMap K (P.adicCompletion K) (algebraMap (𝓞 K) K x) = _
  exact (IsScalarTower.algebraMap_apply (𝓞 K) K (P.adicCompletion K) x).symm

def artinAdicResidueEquiv :
    𝓀[ChosenFinitePlaceBaseCompletion (K := K) P] ≃+* 𝓀[P.adicCompletion K] :=
  IsLocalRing.ResidueField.mapEquiv (artinAdicIntegerEquiv K P)

theorem artinAdicResidueEquiv_global (x : 𝓞 K) :
    artinAdicResidueEquiv K P
      (IsLocalRing.residue 𝒪[ChosenFinitePlaceBaseCompletion (K := K) P]
        (finitePlaceIntegerToCompletion P x)) = adicResidueOfInteger K P x := by
  change IsLocalRing.residue 𝒪[P.adicCompletion K]
    (artinAdicIntegerEquiv K P (finitePlaceIntegerToCompletion P x)) = _
  rw [artinAdicIntegerEquiv_global]
  rfl

theorem artinAdicResidueEquiv_idealResidue :
    (finitePlaceIdealResidueEquivCompletion P).trans (artinAdicResidueEquiv K P) =
      adicIntegerResidueEquiv K P := by
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingEquiv.trans_apply, finitePlaceIdealResidueEquivCompletion_apply_mk,
    adicIntegerResidueEquiv_mk]
  exact artinAdicResidueEquiv_global K P x

end
end ArtinMatthews.SIntegerAdicResidue
