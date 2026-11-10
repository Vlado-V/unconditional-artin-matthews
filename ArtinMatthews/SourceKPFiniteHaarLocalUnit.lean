module

public import ArtinMatthews.SourceAdelicStandardHaar
public import ArtinMatthews.SourceFinitePlaceSplit
public import ArtinMatthews.SourceFinitePlaceHaar
public import ArtinMatthews.SourceLocalHaarGeneralDilation
public import ArtinMatthews.StandardLocalBall
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

/-! A finite idele supported at one place dilates only that factor
of the actual normalized finite additive Haar measure. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical
open scoped NumberField AdeleRing ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "A" => 𝔸ᶠ[K]
local notation "R" => sourceKPFinitePlaceRemainder K P
local notation "e" => ContinuousAddEquiv.symm (sourceKPFinitePlaceSplit K P)
local notation "j" => sourceKPAdeleLocalUnit K P

local instance sourceKPFiniteHaarLocalUnitMeasurable : MeasurableSpace A := borel A
local instance sourceKPFiniteHaarLocalUnitBorel : BorelSpace A := ⟨rfl⟩
local instance sourceKPFiniteHaarLocalUnitCompletionMeasurable : MeasurableSpace L := borel L
local instance sourceKPFiniteHaarLocalUnitCompletionBorel : BorelSpace L := ⟨rfl⟩

theorem sourceKPFiniteHaarLocalUnit_merge (t : Lˣ) (x : L) (r : R) :
    (j t : A) * e (x,r) = e ((t : L)*x,r) := by
  rw [sourceKPFinitePlaceSplit_symm_apply,sourceKPFinitePlaceSplit_symm_apply]
  apply Subtype.ext
  funext Q
  change (j t : A) Q * (sourceKPFiniteAdditiveSingle K P x Q + r.val Q) =
    sourceKPFiniteAdditiveSingle K P ((t : L)*x) Q + r.val Q
  by_cases hQ : Q = P
  · subst Q
    have ht : (j t : A) P = (t : L) :=
      congrArg (fun u : Lˣ => (u : L)) (sourceKPAdeleLocalUnit_same K P t)
    have hr : r.val P = 0 := r.property
    rw [ht,sourceKPFiniteAdditiveSingle_same,sourceKPFiniteAdditiveSingle_same,hr,add_zero,add_zero]
  · have ht : (j t : A) Q = (1 : Q.adicCompletion K) :=
      congrArg (fun u : (Q.adicCompletion K)ˣ => (u : Q.adicCompletion K))
        (sourceKPAdeleLocalUnit_other K P t Q hQ)
    rw [ht,one_mul,sourceKPFiniteAdditiveSingle_other K P x Q hQ,
      sourceKPFiniteAdditiveSingle_other K P ((t : L)*x) Q hQ]

theorem sourceKPFiniteHaarLocalUnit_inv (t : Lˣ) : (j t)⁻¹ = j t⁻¹ := by
  rw [sourceKPAdeleLocalUnit,sourceKPAdeleLocalUnit,map_inv,map_inv]

theorem sourceKPFiniteHaarLocalUnit_map (t : Lˣ) :
    (sourceKPFiniteStandardHaar K).map (fun x : A => (j t : A)*x) =
      (‖((t⁻¹ : Lˣ) : L)‖₊ : ℝ≥0∞) • sourceKPFiniteStandardHaar K := by
  let μ := sourceJacquetHaar K P
  let ν := sourceKPFinitePlaceRemainderStandardHaar K P
  let f : L → L := fun x => (t : L)*x
  let m : A → A := fun x => (j t : A)*x
  have hm : Measurable m := (continuous_const.mul continuous_id).measurable
  have hf : Measurable f := (continuous_const.mul continuous_id).measurable
  have he : Measurable (e : L × R → A) := (e).continuous.measurable
  have hc : m ∘ e = e ∘ Prod.map f id := by
    funext p
    exact sourceKPFiniteHaarLocalUnit_merge K P t p.1 p.2
  let : μ.IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  calc
    _ = (μ.prod ν).map (m ∘ e) := by
      rw [sourceKPFiniteStandardHaar_place_split K P,Measure.map_map hm he]
    _ = ((μ.map f).prod ν).map e := by
      rw [hc,← Measure.map_map he (hf.prodMap measurable_id),
        ← Measure.map_prod_map μ ν hf measurable_id,Measure.map_id]
    _ = _ := by
      have hμ : μ.map f = (‖((t⁻¹ : Lˣ) : L)‖₊ : ℝ≥0∞) • μ :=
        sourceLocalAddHaar_map_mul K P μ t
      rw [hμ,Measure.prod_smul_left,Measure.map_smul _ he.aemeasurable]
      rw [sourceKPFiniteStandardHaar_place_split K P]

end
end ArtinMatthews
