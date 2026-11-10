module

public import ArtinMatthews.MarkedPhysicalScalarAbsScales
public import ArtinMatthews.MarkedPhysicalCoprimeScalarDetector
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedPhysicalScalarAbsBudget
public import ArtinMatthews.MarkedTypeIICommonQuotientActual
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Uniform absolute mass for the actual scalar detector branches.
All label, representation and coefficient losses are explicit logarithmic
powers with no loss in the exponent from the number of marking bands. -/
namespace ArtinMatthews
noncomputable section
open Filter

theorem markedPhysicalScalarAbsMass_actual_log_bound {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (δ K Cα Cβ Qexp R W : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (hQexp : 0 ≤ Qexp) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W)
    (hηs : Function.support η ⊆ Set.Icc 1 4) (hψs : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,∀ Y : ℝ,0 < Y →
      ∀ (S T : Finset ℕ) (Z : ℕ),x^δ ≤ (Z:ℝ) → (Z:ℝ) ≤ K*x →
      (∀ v ∈ S.product T,v.1*v.2 ∈ Finset.Icc 1 Z) →
      ∀ α β : ℕ → ℂ,(∀ m∈S,‖α m‖ ≤ (Real.log x)^Cα) → (∀ n∈T,‖β n‖ ≤ (Real.log x)^Cβ) →
      let P := fun j => markedLogPowerBand (e j) x
      let E := markedPhysicalScalarAbsLogExponent Cα Cβ Qexp
      let Q := (Real.log x)^Qexp
      markedPhysicalCoprimeScalarDetectorAbsMass P S T η Y (markedRawEdgeDeltaDetector ψ Y) α β
        ≤ C*(Y*(Z:ℝ))*(Real.log x)^E ∧
      markedPhysicalCoprimeScalarDetectorAbsMass P S T η Y (markedRawEdgeMajorDetector ψ Q Y) α β
        ≤ C*(Y*(Z:ℝ))*(Real.log x)^E := by
  let Vmax := ((Real.log 2/2)⁻¹)^(Fintype.card J)
  let Cδ := 128*Vmax^2*W*(K+1)^3
  let Cm := 64*Vmax^2*W*(2*R+1)*(K+1)^3
  have hCδ : 0 ≤ Cδ := by dsimp only [Cδ]; positivity
  have hCm : 0 ≤ Cm := by dsimp only [Cm]; positivity
  refine ⟨Cδ+Cm,add_nonneg hCδ hCm,?_⟩
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    ((by norm_num : (0:ℝ)<1/10).trans_le (he j)))
  filter_upwards [hbands,markedTypeII_actual_label_fourth_le_eventually e he heUpper δ hδ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop (1:ℝ)]
    with x hmass hlabel hlog hx
  intro Y hY S T Z hZl hZu hRZ α β hα hβ
  dsimp only
  let L := Real.log x
  let P := fun j => markedLogPowerBand (e j) x
  let Q := L^Qexp
  let E := markedPhysicalScalarAbsLogExponent Cα Cβ Qexp
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hQ : 1 ≤ Q := Real.one_le_rpow hlog hQexp
  have hZ : 1 ≤ Z := by exact_mod_cast (Real.one_le_rpow hx hδ.le).trans hZl
  have hV := markedPhysicalScalar_labelMass_bound P (by positivity : 0 < Real.log 2/2)
    (fun j => (hmass j).1.le)
  have hh := markedPhysicalScalar_harmonic_log_le (zero_lt_one.trans_le hx) hlog hK hZ hZu
  have hpow := markedPhysicalScalarAbs_log_powers hL Cα Cβ Qexp
  have hH : 0 ≤ 1+Real.log (Z:ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hZ))
  have hYZE : 0 ≤ Y*(Z:ℝ)*L^E := by positivity
  have hM : 0 ≤ markedMajorLabelMass P := hV.1
  have hM' : markedMajorLabelMass P ≤ Vmax := hV.2
  have hE : (L^Cα*L^Cβ)^2*Q^3*L^3=L^E := hpow
  constructor
  · calc
      _ ≤ 128*(markedMajorLabelMass P)^2*(L^Cα*L^Cβ)^2*W*Y*(Z:ℝ)*(1+Real.log (Z:ℝ))^3 :=
        markedPhysicalCoprimeDelta_abs_le P S T Z hZ hRZ η ψ hY hW hη hψ hηs
          (fun a ha => hlabel Z hZl a (Finset.mem_filter.mp ha).1) α β hα hβ
      _ ≤ 128*Vmax^2*(L^Cα*L^Cβ)^2*W*Y*(Z:ℝ)*((K+1)*L)^3 := by
        gcongr
        exact hh.1
      _ = Y*(Z:ℝ)*Cδ*((L^Cα*L^Cβ)^2*L^3) := by dsimp only [Cδ]; ring
      _ ≤ Y*(Z:ℝ)*Cδ*((L^Cα*L^Cβ)^2*Q^3*L^3) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hQ)) (by positivity)
      _ = Cδ*(Y*(Z:ℝ))*L^E := by rw [hE]; ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCm) hYZE
  · calc
      _ ≤ 64*(markedMajorLabelMass P)^2*(L^Cα*L^Cβ)^2*W*(2*R+1)*Q^3*Y*(Z:ℝ)*
          (∑ d ∈ Finset.Icc 1 Z,1/(d:ℝ))^3 :=
        markedPhysicalCoprimeMajor_abs_le P S T Z hRZ η ψ
          (zero_le_one.trans hQ) hY hR hW (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hL.le _)
          hη hψ hηs hψs α β hα hβ
      _ ≤ 64*Vmax^2*(L^Cα*L^Cβ)^2*W*(2*R+1)*Q^3*Y*(Z:ℝ)*((K+1)*L)^3 := by
        gcongr
        exact hh.2
      _ = Y*(Z:ℝ)*Cm*((L^Cα*L^Cβ)^2*Q^3*L^3) := by dsimp only [Cm]; ring
      _ = Cm*(Y*(Z:ℝ))*L^E := by rw [hE]; ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCδ) hYZE

end
end ArtinMatthews
