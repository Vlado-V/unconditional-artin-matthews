module

public import OAI.RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles
public import ArtinMatthews.SourceAdelicRowBody
public import ArtinMatthews.SourceAdelicSL2Haar
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! A nonzero rational row with integral finite coordinates and a uniform
archimedean bound after multiplication by an actual determinant-one adele matrix. -/
namespace ArtinMatthews
open NumberField MeasureTheory Set
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local instance sourceAdelicShortRow_measurableSpace : MeasurableSpace 𝔸[F] := borel 𝔸[F]
local instance sourceAdelicShortRow_borelSpace : BorelSpace 𝔸[F] := ⟨rfl⟩

def sourceRationalAdelicRow (g : SL(2, 𝔸[F])) (q : F × F) : 𝔸[F] × 𝔸[F] :=
  (algebraMap F 𝔸[F] q.1 * g 0 0 + algebraMap F 𝔸[F] q.2 * g 1 0,
    algebraMap F 𝔸[F] q.1 * g 0 1 + algebraMap F 𝔸[F] q.2 * g 1 1)

theorem sourceSL2Adelic_uniform_short_row :
    ∃ R : ℝ, 0 < R ∧ ∀ g : SL(2, 𝔸[F]), ∃ q : F × F, q ≠ 0 ∧
      (sourceRationalAdelicRow F g q).1.2 ∈ IntegralAdeles.Construction.finiteIntegralRing F ∧
      (sourceRationalAdelicRow F g q).2.2 ∈ IntegralAdeles.Construction.finiteIntegralRing F ∧
      ∀ v : InfinitePlace F, ‖(sourceRationalAdelicRow F g q).1.1 v‖ ≤ R ∧
        ‖(sourceRationalAdelicRow F g q).2.1 v‖ ≤ R := by
  obtain ⟨R, hR, hbound⟩ := sourceKPAdelicBlichfeldtBody_diff_arch_bound F
  refine ⟨R, hR, fun g => ?_⟩
  let T := sourceSL2AdelicRowAction F g
  have hT : MeasurePreserving T (sourceKPAdelicRowHaar F) (sourceKPAdelicRowHaar F) :=
    sourceSL2Adelic_row_measurePreserving F g
  have hmeas : MeasurableSet (T ⁻¹' sourceKPAdelicBlichfeldtBody F) :=
    (sourceKPAdelicBlichfeldtBody_measurable F).preimage hT.measurable
  have hvol : 1 < sourceKPAdelicRowHaar F (T ⁻¹' sourceKPAdelicBlichfeldtBody F) := by
    rw [hT.measure_preimage (sourceKPAdelicBlichfeldtBody_measurable F).nullMeasurableSet,
      sourceKPAdelicBlichfeldtBody_mass]
    norm_num
  obtain ⟨q, hq, x, hx, y, hy, hxy⟩ := sourceKPAdelicRow_blichfeldt F
    (T ⁻¹' sourceKPAdelicBlichfeldtBody F) hmeas.nullMeasurableSet hvol
  have hrow : sourceRationalAdelicRow F g q = T y - T x := by
    calc
      _ = T (algebraMap F 𝔸[F] q.1, algebraMap F 𝔸[F] q.2) :=
        (sourceSL2AdelicRowAction_rational F g q).symm
      _ = _ := by
        rw [hxy]
        exact sourceSL2AdelicRowAction_sub F g y x
  have hfin := sourceKPAdelicBlichfeldtBody_diff_integral F (x := T x) (y := T y) hx hy
  have harch := hbound (T x) hx (T y) hy
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · simpa only [hrow, Prod.fst_sub] using hfin.1
  · simpa only [hrow, Prod.snd_sub] using hfin.2
  · intro v
    simpa only [hrow, Prod.fst_sub, Prod.snd_sub] using harch v

end
end ArtinMatthews
