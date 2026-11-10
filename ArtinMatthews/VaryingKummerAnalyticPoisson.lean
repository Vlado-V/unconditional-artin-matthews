module

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Analysis.Matrix.Normed


set_option backward.privateInPublic true
@[expose] public section

/-! Exact generic proof extraction from OpenAI math-main, XiBoundary.lean
lines 455–655. Only namespace/import routing changes.
See varying-kummer-theta-stage/generic-extraction-manifest.json. -/

namespace ArtinMatthews.ReusedTheta
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
variable {d : Type*} [Fintype d]

def integerVector (z : d → ℤ) : d → ℝ := fun i => z i

def torusProjection (x : d → ℝ) : UnitAddTorus d := fun i => x i

omit [Fintype d] in
lemma torusProjection_openQuotient : IsOpenQuotientMap (torusProjection (d := d)) := by
  exact IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

omit [Fintype d] in
lemma torusProjection_eq_iff (x y : d → ℝ) :
    torusProjection x = torusProjection y ↔ ∃ z : d → ℤ, y = x + integerVector z := by
  constructor
  · intro h
    have H (i : d) : ∃ z : ℤ, (z:ℝ) = -(x i) + y i := by
      have hi := QuotientAddGroup.eq.mp (congrFun h i)
      simpa only [AddSubgroup.mem_zmultiples_iff,zsmul_eq_mul,mul_one] using hi
    choose z hz using H
    exact ⟨z,funext (fun i => by dsimp [integerVector]; linarith [hz i])⟩
  · rintro ⟨z,rfl⟩
    funext i
    apply QuotientAddGroup.eq.mpr
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨z i,?_⟩
    simp [integerVector,zsmul_eq_mul]

def translate (f : C(d → ℝ,ℂ)) (z : d → ℤ) : C(d → ℝ,ℂ) :=
  f.comp (ContinuousMap.addRight (integerVector z))

def LocallyNormal (f : C(d → ℝ,ℂ)) : Prop :=
  ∀ K : TopologicalSpace.Compacts (d → ℝ),
    Summable (fun z : d → ℤ => ‖(translate f z).restrict K‖)

def periodizedReal (f : C(d → ℝ,ℂ)) : C(d → ℝ,ℂ) := ∑' z : d → ℤ, translate f z

lemma periodizedReal_apply (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) (x : d → ℝ) :
    periodizedReal f x = ∑' z : d → ℤ, f (x + integerVector z) := by
  exact (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm hf) x).symm

lemma periodizedReal_per (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f)
    (x : d → ℝ) (z : d → ℤ) :
    periodizedReal f (x + integerVector z) = periodizedReal f x := by
  rw [periodizedReal_apply f hf,periodizedReal_apply f hf]
  convert (Equiv.addLeft z).tsum_eq (fun n : d → ℤ => f (x + integerVector n)) using 1
  apply tsum_congr
  intro n
  congr 1
  ext i
  simp [integerVector,add_assoc]

def torusRepresentative (y : UnitAddTorus d) : d → ℝ :=
  (UnitAddTorus.measurableEquivPiIoc (fun _ : d => 0) y).val

omit [Fintype d] in
lemma torusProjection_representative (y : UnitAddTorus d) :
    torusProjection (torusRepresentative y) = y := by
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : d => 0)).symm_apply_apply y

lemma periodizedReal_representative (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) (x : d → ℝ) :
    periodizedReal f (torusRepresentative (torusProjection x)) = periodizedReal f x := by
  obtain ⟨z,hz⟩ := (torusProjection_eq_iff x (torusRepresentative (torusProjection x))).mp
    (torusProjection_representative _).symm
  rw [hz]
  exact periodizedReal_per f hf x z

def periodizedTorus (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) : C(UnitAddTorus d,ℂ) where
  toFun y := periodizedReal f (torusRepresentative y)
  continuous_toFun := by
    apply torusProjection_openQuotient.isQuotientMap.continuous_iff.mpr
    have he : (fun y => periodizedReal f (torusRepresentative y)) ∘ torusProjection =
        periodizedReal f := funext (periodizedReal_representative f hf)
    rw [he]
    exact (periodizedReal f).continuous

lemma periodizedTorus_apply (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) (x : d → ℝ) :
    periodizedTorus f hf (torusProjection x) = ∑' z : d → ℤ, f (x + integerVector z) := by
  rw [periodizedTorus]
  change periodizedReal f (torusRepresentative (torusProjection x)) = _
  rw [periodizedReal_representative f hf,periodizedReal_apply f hf]

instance integerTranslationAction : AddAction (d → ℤ) (d → ℝ) where
  vadd z x := integerVector z + x
  zero_vadd x := by
    change integerVector 0 + x = x
    ext i
    simp [integerVector]
  add_vadd z w x := by
    change integerVector (z+w) + x = integerVector z + (integerVector w + x)
    ext i
    simp [integerVector,add_assoc]

instance integerTranslationMeasurable : MeasurableConstVAdd (d → ℤ) (d → ℝ) :=
  ⟨fun _ => measurable_const.add measurable_id⟩

instance integerTranslationPreservesVolume :
    VAddInvariantMeasure (d → ℤ) (d → ℝ) volume where
  measure_preimage_vadd z S hS := by
    exact (measurePreserving_add_left volume (integerVector z)).measure_preimage hS.nullMeasurableSet

def unitCube : Set (d → ℝ) := {x | ∀ i, x i ∈ Ioc (0:ℝ) 1}

lemma unitCube_fundamental : IsAddFundamentalDomain (d → ℤ) (unitCube (d := d)) volume := by
  apply IsAddFundamentalDomain.mk' (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)).nullMeasurableSet
  intro x
  refine ⟨fun i => 1 - Int.ceil (x i),?_,?_⟩
  · intro i
    change 0 < ((1-Int.ceil (x i):ℤ):ℝ) + x i ∧
      ((1-Int.ceil (x i):ℤ):ℝ) + x i ≤ 1
    push_cast
    constructor <;> linarith [Int.ceil_lt_add_one (x i),Int.le_ceil (x i)]
  · intro z hz
    ext i
    have H := hz i
    change 0 < (z i:ℝ) + x i ∧ (z i:ℝ) + x i ≤ 1 at H
    have hc : Int.ceil (x i) = 1-z i := Int.ceil_eq_iff.mpr (by push_cast; constructor <;> linarith)
    omega

lemma integral_periodization (f : C(d → ℝ,ℂ)) (hf : Integrable f) :
    (∫ x in unitCube, ∑' z : d → ℤ, f (x + integerVector z)) = ∫ x, f x := by
  have hfd := unitCube_fundamental (d := d)
  have hn : (∑' z : d → ℤ, ∫⁻ x in unitCube, ‖f (z +ᵥ x)‖ₑ) ≠ ⊤ := by
    rw [←hfd.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  have H := integral_tsum
    (fun z : d → ℤ => ((f.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable.restrict)) hn
  calc
    _ = ∫ x in unitCube, ∑' z : d → ℤ, f (z +ᵥ x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply tsum_congr
      intro z
      change f (x + integerVector z) = f (integerVector z + x)
      rw [add_comm]
    _ = _ := H.trans (hfd.integral_eq_tsum'' f hf).symm

omit [Fintype d] in
lemma torusProjection_add_integer (x : d → ℝ) (z : d → ℤ) :
    torusProjection (x + integerVector z) = torusProjection x :=
  ((torusProjection_eq_iff x (x + integerVector z)).mpr ⟨z,rfl⟩).symm

def fourierCharacter (m : d → ℤ) : C(d → ℝ,ℂ) :=
  (UnitAddTorus.mFourier (-m)).comp ⟨torusProjection,torusProjection_openQuotient.continuous⟩

lemma fourierCharacter_norm (m : d → ℤ) (x : d → ℝ) : ‖fourierCharacter m x‖ = 1 := by
  simp only [fourierCharacter,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
    UnitAddTorus.mFourier,norm_prod]
  simp only [fourier_apply,Circle.norm_coe,Finset.prod_const_one]

lemma fourierCharacter_periodic (m z : d → ℤ) (x : d → ℝ) :
    fourierCharacter m (x + integerVector z) = fourierCharacter m x := by
  change UnitAddTorus.mFourier (-m) (torusProjection (x + integerVector z)) = _
  rw [torusProjection_add_integer]
  rfl

lemma integrable_character_mul (m : d → ℤ) (f : C(d → ℝ,ℂ))
    (hf : Integrable f) : Integrable (fourierCharacter m * f) := by
  apply hf.norm.mono' (fourierCharacter m * f).continuous.aestronglyMeasurable
  filter_upwards [] with x
  simp only [ContinuousMap.mul_apply,norm_mul,fourierCharacter_norm,one_mul]
  exact le_rfl

lemma fourierCoeff_periodizedTorus (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f)
    (hfInt : Integrable f) (m : d → ℤ) :
    UnitAddTorus.mFourierCoeff (periodizedTorus f hf) m = ∫ x, fourierCharacter m x * f x := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (fun _ => 0)]
  simp only [smul_eq_mul,zero_add]
  change (∫ x in unitCube, fourierCharacter m x * periodizedTorus f hf (torusProjection x)) = _
  calc
    _ = ∫ x in unitCube, ∑' z : d → ℤ, (fourierCharacter m * f) (x + integerVector z) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [periodizedTorus_apply,←tsum_mul_left]
      apply tsum_congr
      intro z
      rw [ContinuousMap.mul_apply,fourierCharacter_periodic]
    _ = _ := integral_periodization _ (integrable_character_mul m f hfInt)

 

theorem multivariate_poisson (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f)
    (hfInt : Integrable f)
    (hFourier : Summable (fun m : d → ℤ => ∫ x, fourierCharacter m x * f x))
    (x : d → ℝ) :
    (∑' z : d → ℤ, f (x + integerVector z)) =
      ∑' m : d → ℤ, (∫ y, fourierCharacter m y * f y) *
        UnitAddTorus.mFourier m (torusProjection x) := by
  have hs : Summable (UnitAddTorus.mFourierCoeff (periodizedTorus f hf)) := by
    exact hFourier.congr (fun m => (fourierCoeff_periodizedTorus f hf hfInt m).symm)
  have H := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (torusProjection x)
  simpa only [fourierCoeff_periodizedTorus f hf hfInt,smul_eq_mul,periodizedTorus_apply] using H.tsum_eq.symm


end
end ArtinMatthews.ReusedTheta
