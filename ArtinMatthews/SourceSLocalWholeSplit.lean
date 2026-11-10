module

public import ArtinMatthews.SourceSLocalSheetNorm
public import ArtinMatthews.SourceSLocalSheetTopology
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

/-! Extract the chosen infinite unit from the whole product. All
remaining infinite units and finite S units keep their original coordinates. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped NumberField
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

def sourceSWholeToSheet (x : SWholeUnits K S) : v.Completionˣ × SNormOneOtherUnits S v :=
  (x.1 v, sourceSheetOther S v x)

def sourceSWholeSheetSplit : SWholeUnits K S ≃ₜ* v.Completionˣ × SNormOneOtherUnits S v where
  toFun := sourceSWholeToSheet S v
  invFun y := sourceSheetFill S v y.1 y.2
  left_inv := sourceSheetFill_reconstruct S v
  right_inv y := Prod.ext (sourceSheetFill_chosen S v y.1 y.2) (sourceSheetOther_fill S v y.1 y.2)
  map_mul' x y := Prod.ext rfl (sourceSheetOther_mul S v x y)
  continuous_toFun := ((continuous_apply v).comp continuous_fst).prodMk (continuous_sourceSheetOther S v)
  continuous_invFun := continuous_sourceSheetFill S v continuous_fst continuous_snd

@[simp] theorem sourceSWholeSheetSplit_apply (x : SWholeUnits K S) :
    sourceSWholeSheetSplit S v x = (x.1 v, sourceSheetOther S v x) := rfl

@[simp] theorem sourceSWholeSheetSplit_symm_apply (y : v.Completionˣ × SNormOneOtherUnits S v) :
    (sourceSWholeSheetSplit S v).symm y = sourceSheetFill S v y.1 y.2 := rfl

end
end ArtinMatthews.SourcePhysical
