module

public import ArtinMatthews.SourceAdelicStandardHaar
public import ArtinMatthews.SourceKPAdeleLocalCover
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import ArtinMatthews.SourceAdelicTraceHaar
public import ArtinMatthews.SourceKPFiniteHaarLocalUnit
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
public import Mathlib.Tactic.ENatToNat
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

/-! The finite-idele dilation character is the actual finite absolute
norm. Single-place factors account for its finite valuation support;
the remaining integral unit preserves the integral open subgroup. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure Set
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing ENNReal NNReal Pointwise Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local notation "A" => 𝔸ᶠ[K]
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "U" => IntegralAdeles.Construction.finiteIntegralRing K
local notation "M₀" => sourceKPFiniteStandardHaar K
local notation "Δ" => (distribHaarChar A : Aˣ →* ℝ≥0)
local notation "j" => sourceKPAdeleLocalUnit K

local instance sourceKPFiniteHaarDilationMeasurable : MeasurableSpace A := borel A
local instance sourceKPFiniteHaarDilationBorel : BorelSpace A := ⟨rfl⟩

def sourceKPFiniteHaarUnitAt (P : Pr) : Aˣ →* (P.adicCompletion K)ˣ :=
  Units.map (sourceKPAdeleEval K P).toMonoidHom

local notation "φ" => sourceKPFiniteHaarUnitAt K

theorem sourceKPFiniteHaar_map_char (a : Aˣ) :
    (M₀).map (fun x : A => (a : A)*x) = (Δ a⁻¹ : ℝ≥0∞) • M₀ := by
  ext1 s hs
  have hm : Measurable (fun x : A => (a : A)*x) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs,Measure.smul_apply,smul_eq_mul]
  have he : (fun x : A => (a : A)*x) ⁻¹' s = a⁻¹ • s := by
    change (fun x : A => a • x) ⁻¹' s = _
    simpa only [inv_inv] using preimage_smul_inv a⁻¹ s
  rw [he,← distribHaarChar_mul M₀]

theorem sourceKPFiniteHaarChar_localUnit (P : Pr) (t : (P.adicCompletion K)ˣ) :
    Δ (j P t) = ‖(t : P.adicCompletion K)‖₊ := by
  let L := P.adicCompletion K
  have h₁ := sourceKPFiniteHaar_map_char K (j P t)⁻¹
  rw [inv_inv] at h₁
  have h₂ := sourceKPFiniteHaarLocalUnit_map K P t⁻¹
  rw [inv_inv,← sourceKPFiniteHaarLocalUnit_inv K P t] at h₂
  have h := congrArg (fun ν : Measure A => (ν U).toReal) (h₁.symm.trans h₂)
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.coe_toReal] at h
  have hpos : 0 < (M₀ U).toReal := by
    rw [sourceKPFiniteStandardHaar_integral]
    exact ENNReal.toReal_pos
      (ENNReal.inv_ne_zero.mpr (sourceKPDiscriminantRoot_ne_top K))
      (ENNReal.inv_ne_top.mpr (sourceKPDiscriminantRoot_ne_zero K))
  exact NNReal.coe_injective (mul_right_cancel₀ hpos.ne' h)

theorem sourceKPFiniteHaarChar_integral_unit (a : Aˣ)
    (ha : ∀ P : Pr, ‖(a : A) P‖ = 1) : Δ a = 1 := by
  have h₁ : (a : A) ∈ U := by
    intro P
    exact Valued.toNormedField.norm_le_one_iff.mp (ha P).le
  have h₂ : ((a⁻¹ : Aˣ) : A) ∈ U := by
    intro P
    have hnorm : ‖((φ P a⁻¹ : (P.adicCompletion K)ˣ) : P.adicCompletion K)‖ ≤ 1 := by
      rw [map_inv (φ P),Units.val_inv_eq_inv_val,norm_inv,
        show ‖((φ P a : (P.adicCompletion K)ˣ) : P.adicCompletion K)‖ = 1 from ha P,inv_one]
    exact Valued.toNormedField.norm_le_one_iff.mp hnorm
  have hU : a • (U : Set A) = U := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem]
    constructor
    · intro hx
      change x ∈ U
      have hm := (U).mul_mem h₁ hx
      change (a : A)*(((a⁻¹ : Aˣ) : A)*x) ∈ U at hm
      simpa only [← mul_assoc,← Units.val_mul,mul_inv_cancel,Units.val_one,one_mul] using hm
    · intro hx
      change ((a⁻¹ : Aˣ) : A)*x ∈ U
      exact (U).mul_mem h₂ hx
  let ν := sourceKPFiniteIntegralHaar K
  have hν : ν U = 1 := sourceKPFiniteIntegralHaar_integral K
  refine distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := ν) (s := (U : Set A)) (by rw [hν]; simp) (by rw [hν]; simp) ?_
  rw [hU,ENNReal.coe_one,one_mul]

theorem sourceKPFiniteHaarUnitAt_product (a : Aˣ) (T : Finset Pr) (P : Pr) :
    φ P (∏ Q ∈ T, j Q (φ Q a)) = if P ∈ T then φ P a else 1 := by
  rw [map_prod (φ P)]
  by_cases hP : P ∈ T
  · rw [ite_eq_left hP,Finset.prod_eq_single_of_mem P hP]
    · exact sourceKPAdeleLocalUnit_same K P (φ P a)
    · intro Q _ hQ
      exact sourceKPAdeleLocalUnit_other K Q (φ Q a) P hQ.symm
  · rw [ite_eq_right hP]
    apply Finset.prod_eq_one
    intro Q hQ
    exact sourceKPAdeleLocalUnit_other K Q (φ Q a) P (fun h => hP (h.symm ▸ hQ))

theorem sourceKPFiniteHaarChar_eq_norm (a : Aˣ) :
    (Δ a : ℝ) = ‖(a : A)‖ := by
  have hfin := FiniteAdeleRing.hasFiniteMulSupport_norm a
  let T := hfin.toFinset
  let v := ∏ Q ∈ T, j Q (φ Q a)
  let r := v⁻¹*a
  have hr (P : Pr) : ‖(r : A) P‖ = 1 := by
    change ‖((φ P (v⁻¹*a) : (P.adicCompletion K)ˣ) : P.adicCompletion K)‖ = 1
    rw [map_mul (φ P),map_inv (φ P)]
    have hP := sourceKPFiniteHaarUnitAt_product K a T P
    change φ P v = _ at hP
    rw [hP]
    by_cases hp : P ∈ T
    · rw [ite_eq_left hp,inv_mul_cancel,Units.val_one,norm_one]
    · rw [ite_eq_right hp,inv_one,one_mul]
      by_contra h
      exact hp (hfin.mem_toFinset.mpr h)
  have he : Δ a = ∏ P ∈ T, ‖((φ P a : (P.adicCompletion K)ˣ) : P.adicCompletion K)‖₊ := by
    calc
      _ = Δ (v*r) := congrArg Δ (mul_inv_cancel_left v a).symm
      _ = Δ v := by rw [map_mul Δ,sourceKPFiniteHaarChar_integral_unit K r hr,mul_one]
      _ = _ := by
        dsimp only [v]
        rw [map_prod Δ]
        exact Finset.prod_congr rfl (fun P _ => sourceKPFiniteHaarChar_localUnit K P (φ P a))
  rw [he,NNReal.coe_prod,FiniteAdeleRing.norm_eq_finprod_of_unit,finprod_eq_prod _ hfin]
  rfl

theorem sourceKPFiniteHaar_map_mul (a : Aˣ) :
    (M₀).map (fun x : A => (a : A)*x) = ENNReal.ofReal ‖((a⁻¹ : Aˣ) : A)‖ • M₀ := by
  rw [sourceKPFiniteHaar_map_char K a,← sourceKPFiniteHaarChar_eq_norm K a⁻¹,
    ENNReal.ofReal_coe_nnreal]

end
end ArtinMatthews
