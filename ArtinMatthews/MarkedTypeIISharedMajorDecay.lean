module

public import ArtinMatthews.MarkedTypeIISharedMajorFinite
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedTypeIICollisionDecay
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
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Logarithmic saving of the actual shared-label major contribution.
The only losses in the exponent come from the scalar coefficients,
the major-arc measure and the third harmonic power. -/
namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped Topology
attribute [local instance] Classical.propDecidable

private theorem markedTypeIIMajor_harmonic_cutoff
    {x K : ℝ} (hK : 0 < K) (hx : 0 < x) (hL : 1 ≤ Real.log x) (Z : ℕ)
    (hZ : (Z:ℝ) ≤ K*x) :
    (∑ d ∈ Icc 1 Z,1/(d:ℝ)) ≤ (K+1)*Real.log x := by
  by_cases hZ₀ : Z=0
  · subst Z
    simp only [Icc_eq_empty_of_lt (show 0 < 1 by decide),sum_empty]
    positivity
  have hz : 0 < (Z:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hZ₀
  have hH : (∑ d ∈ Icc 1 Z,1/(d:ℝ)) ≤ 1+Real.log (Z:ℝ) := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
      using harmonic_le_one_add_log Z
  have hlog := Real.log_le_log hz hZ
  rw [Real.log_mul hK.ne' hx.ne'] at hlog
  have hklog := Real.log_le_sub_one_of_pos hK
  nlinarith [mul_nonneg hK.le (show 0 ≤ Real.log x-1 by linarith)]

theorem markedTypeIIScalarMajor_shared_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (R W Cα Cβ Qexp K D : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) (hK : 0 < K)
    (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, 0 < Y → ∀ (S T N : Finset ℕ) (Z : ℕ),
      (Z:ℝ) ≤ K*x →
      (∀ v ∈ S×ˢN,v.1*v.2 ∈ Icc 1 Z) →
      (∀ v ∈ T×ˢN,v.1*v.2 ∈ Icc 1 Z) →
      ∀ (α β : ℕ → ℂ),
      (∀ m ∈ S,‖α m‖ ≤ (Real.log x)^Cα) →
      (∀ m ∈ T,‖α m‖ ≤ (Real.log x)^Cα) →
      (∀ n ∈ N,‖β n‖ ≤ (Real.log x)^Cβ) →
      ∀ (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ), (∀ z v w,‖G z v w‖ ≤ 1) →
      let P := fun j => markedLogPowerBand (e j) x
      ‖markedTypeIIScalarMajorOn P
        ((markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter fun z => ¬ z.1.Coprime z.2)
        S T N η ψ ((Real.log x)^Qexp) Y α β G‖ ≤ Y*(Z:ℝ)*(Real.log x)^(-D) := by
  let Vmax := ((Real.log 2/2)⁻¹)^(Fintype.card J)
  let E := 2*(Cα+Cβ)+3*Qexp+3
  let C := 64*Vmax^2*W*(2*R+1)*(K+1)^3
  have hV₀ : 0 < Real.log 2/2 := by positivity
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    ((by norm_num : (0:ℝ)<1/10).trans_le (he j)))
  have hdecay := (marked_bands_reciprocal_square_log_saving Finset.univ e
    (fun j _ => he j) (D+E)).const_mul C
  simp only [mul_zero] at hdecay
  have hsmall := ((tendsto_order.1 hdecay).2 1 zero_lt_one).mono (fun _ hx => hx.le)
  filter_upwards [hbands,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),hsmall,
    eventually_gt_atTop (0:ℝ)] with x hxV hx hs hxpos
  intro Y hY S T N Z hZ hS hT α β hαS hαT hβ G hG
  dsimp only
  let L := Real.log x
  let P := fun j => markedLogPowerBand (e j) x
  let m := ∑ p ∈ Finset.univ.biUnion P,1/(p:ℝ)^2
  have hL : 0 < L := zero_lt_one.trans_le hx
  have hm : 0 ≤ m := sum_nonneg (fun _ _ => by positivity)
  have hVp (j : J) : 0 < bandReciprocalMass (P j) := hV₀.trans (hxV j).1
  have hm₀ : 0 ≤ markedMajorLabelMass P := (markedMajorLabelMass_pos P hVp).le
  have hmV : markedMajorLabelMass P ≤ Vmax := by
    unfold markedMajorLabelMass
    have hprod := prod_le_prod₀
      (s := (Finset.univ : Finset J)) (f := fun j => (bandReciprocalMass (P j))⁻¹)
      (g := fun _ => (Real.log 2/2)⁻¹)
      (fun j _ => inv_nonneg.mpr (hVp j).le)
      (fun j _ => inv_anti₀ hV₀ (hxV j).1.le)
    simpa only [prod_const,card_univ,Vmax] using hprod
  have hhar := markedTypeIIMajor_harmonic_cutoff hK hxpos hx Z hZ
  have hpow : (L^Cα*L^Cβ)^2*(L^Qexp)^3*L^3=L^E := by
    rw [← Real.rpow_add hL,← Real.rpow_mul_natCast hL.le,← Real.rpow_mul_natCast hL.le,
      ← Real.rpow_natCast L 3,← Real.rpow_add hL,← Real.rpow_add hL]
    congr 1
    dsimp only [E]
    push_cast
    ring
  have hsave : C*L^E*m ≤ L^(-D) := by
    change C*(L^(D+E)*m) ≤ 1 at hs
    rw [Real.rpow_neg hL.le,← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hL D)).mpr
    calc
      _ = C*(L^(D+E)*m) := by rw [Real.rpow_add hL D E]; ring
      _ ≤ 1 := hs
  calc
    _ ≤ 64*(markedMajorLabelMass P)^2*(L^Cα*L^Cβ)^2*W*(2*R+1)*(L^Qexp)^3*Y*(Z:ℝ)*
          (∑ d ∈ Icc 1 Z,1/(d:ℝ))^3*m :=
      markedTypeIIScalarMajor_shared_norm_le P (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        S T N Z hS hT η ψ (Real.rpow_nonneg hL.le _) hY hR hW
        (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hL.le _)
        hη hψ hsupp α β hαS hαT hβ G hG
    _ ≤ 64*Vmax^2*(L^Cα*L^Cβ)^2*W*(2*R+1)*(L^Qexp)^3*Y*(Z:ℝ)*((K+1)*L)^3*m := by
      gcongr
    _ = Y*(Z:ℝ)*(C*((L^Cα*L^Cβ)^2*(L^Qexp)^3*L^3)*m) := by
      dsimp only [C]
      ring
    _ = Y*(Z:ℝ)*(C*L^E*m) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end
end ArtinMatthews
