module

public import ArtinMatthews.IdealProductModes
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Reconstruction by the concrete product modes identifies the
literal independent coordinate average with its spectral mask. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealLabelMass_pos {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (a : MarkedPhysicalMarking P M) : 0 < idealLabelMass P M a :=
  prod_pos fun j _ => prod_pos fun i _ => hw j (a j i)

theorem idealProductMode_expansion {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (f : MarkedPhysicalMarking P M → ℂ) (a : MarkedPhysicalMarking P M) :
    (∑ t,idealHoeffdingTransform P b f t*idealProductMode b t a)=f a := by
  have he := congrArg (fun v : EuclideanSpace ℂ (MarkedPhysicalMarking P M) => v.ofLp a)
    ((idealProductBasis b).sum_repr (idealWeightedVector P f))
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,idealProductBasis_apply] at he
  change (∑ t,idealHoeffdingTransform P b f t*idealProductBasisVector b t a)=
    (Real.sqrt (idealLabelMass P M a):ℂ)*f a at he
  simp_rw [idealProductMode_eq P hV,← mul_div_assoc]
  rw [← sum_div,he,mul_div_cancel_left₀]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (idealLabelMass_pos P hw a)).ne'

theorem idealWeightedVector_modeSum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (c : MarkedPhysicalMarking P M → ℂ) :
    idealWeightedVector P (fun a => ∑ t,c t*idealProductMode b t a)=
      ∑ t,c t • idealProductBasis b t := by
  apply WithLp.ofLp_injective
  funext a
  simp only [idealWeightedVector,WithLp.ofLp_toLp,WithLp.ofLp_sum,WithLp.ofLp_smul,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,idealProductBasis_apply,mul_sum]
  apply sum_congr rfl
  intro t _
  rw [idealProductMode_eq P hV]
  have hs : (Real.sqrt (idealLabelMass P M a):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (idealLabelMass_pos P hw a)).ne'
  field_simp

theorem idealHoeffdingTransform_modeSum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (c : MarkedPhysicalMarking P M → ℂ) :
    idealHoeffdingTransform P b (fun a => ∑ t,c t*idealProductMode b t a)=c := by
  funext t
  unfold idealHoeffdingTransform
  rw [idealWeightedVector_modeSum P hV hw]
  have hsum := (idealProductBasis b).sum_repr_symm (WithLp.toLp 2 c)
  rw [hsum,LinearIsometryEquiv.apply_symm_apply]

theorem idealAverageSet_modeSum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (S : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ)
    (a : MarkedPhysicalMarking P M) :
    idealAverageSet P S f a=∑ t,(if IdealAverageSurvives a₀ S t then
      idealHoeffdingTransform P b f t else 0)*idealProductMode b t a := by
  have hf : f=(fun a => ∑ t,idealHoeffdingTransform P b f t*idealProductMode b t a) :=
    funext fun a => (idealProductMode_expansion P hV hw b f a).symm
  conv_lhs => rw [hf]
  unfold idealAverageSet idealLabelExpectation
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  have hs : (∑ z,algebraMap ℝ ℂ (idealLabelMass P M z)*
      (idealHoeffdingTransform P b f t*idealProductMode b t (idealMix S a z)))=
      idealHoeffdingTransform P b f t*idealAverageSet P S (idealProductMode b t) a := by
    unfold idealAverageSet idealLabelExpectation
    rw [mul_sum]
    apply sum_congr rfl
    intro z _
    ring
  rw [hs,idealProductMode_average P hV hw b a₀ hb]
  split_ifs <;> simp

theorem idealHoeffdingTransform_average {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (S : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealHoeffdingTransform P b (idealAverageSet P S f)=fun t =>
      if IdealAverageSurvives a₀ S t then idealHoeffdingTransform P b f t else 0 := by
  rw [show idealAverageSet P S f=fun a => ∑ t,
    (if IdealAverageSurvives a₀ S t then idealHoeffdingTransform P b f t else 0)*idealProductMode b t a
    from funext (idealAverageSet_modeSum P hV hw b a₀ hb S f)]
  exact idealHoeffdingTransform_modeSum P hV hw b _

end
end ArtinMatthews
