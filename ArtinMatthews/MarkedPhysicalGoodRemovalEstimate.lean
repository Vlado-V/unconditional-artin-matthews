module

public import ArtinMatthews.MarkedPhysicalCanonicalRoots
public import ArtinMatthews.MarkedPhysicalGoodPairingReverse
public import ArtinMatthews.MarkedPhysicalSourceBad
public import ArtinMatthews.MarkedPhysicalActualGoodRemoval
public import ArtinMatthews.MarkedPhysicalBadPairing
public import ArtinMatthews.MarkedPhysicalEndpointNormActual
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

/-! The original physical cutoff error, with the full root and label
distribution discharged. The explicit bound is then available for the
final logarithmic parameter choice. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedPhysical_source_bad_absolute_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (β H R T : ℝ) (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β)
    (hβhi : β+(1/100 : ℝ) < 49/50) (hH : 0 ≤ H) (hR : 0 ≤ R)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (_hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
        (d₀ Y U V A B C D Q W Hη F G : ℝ)
        (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
        (w : Z → ℤ × ℤ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → U ≤ A → A ≤ B → B ≤ 16*U →
        V ≤ C → C ≤ D → D ≤ 2*V → Z ⊆ markedPhysicalPrimitiveBox A B C D →
        (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
        1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
        0 ≤ W → 0 ≤ Hη → 0 ≤ F → 0 ≤ G →
        (∀ v, ‖ψ v‖ ≤ W) → (∀ v, ψ v ≠ 0 → |v| ≤ R) → (∀ v, ‖η v‖ ≤ Hη) →
        ∀ (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ),
        (∀ s, ‖f s‖ ≤ F) → (∀ s, ‖g s‖ ≤ G) →
        markedPhysicalEdgeAbsolutePairing (fun j => markedLogPowerBand (e j) x)
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η d₀ Y Q 1
          (markedPhysicalBadVector (MarkedPhysicalActualGood e x d₀ Y w) f) g / (U*V) ≤
          (Hη^2*F*G) * ((16/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) +
            (5*E*W)*x^(-δ/4000)) := by
  obtain ⟨E,hE,hroot⟩ := markedPhysicalActualUnionMajorantSum_bound e he hinj β H R T
    hβ heβ hβhi hH hR hδ
  refine ⟨E,hE,?_⟩
  filter_upwards [hroot, markedPhysical_source_bad_absolute_le_majorant e he,
    eventually_gt_atTop (1 : ℝ)] with x hx hpair hx1
  intro hdis d₀ Y U V A B C D Q W Hη F G Z hZ w ψ η hU hV hUA hAB hB hVC hCD hD
    hbox hw hQ hQhi hY hYhi hYlo hW hHη hF hG hψ hsupp hη f g hf hg
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hA1 : 1 < A := ((Real.one_lt_rpow hx1 hδ).trans_le hU).trans_le hUA
  have hC1 : 1 < C := ((Real.one_lt_rpow hx1 hδ).trans_le hV).trans_le hVC
  have hp := hpair d₀ Y Q hdis Z hZ w hw ψ η Hη F G R hHη hF hG hη
    (zero_lt_one.trans_le hY) hsupp f g hf hg A B C D U hA1 hC1 hUp hUA hB hbox
  have hr := hx hdis d₀ Y U V A B C D Q W ψ hU hV hUA hAB hB hVC hCD hD
    hQ hQhi hY hYhi hYlo hW hψ hsupp
  calc
    _ ≤ ((Hη^2*F*G) * markedPhysicalActualUnionMajorantSum e x hdis d₀ Y A B C D R Q ψ)/(U*V) :=
      div_le_div_of_nonneg_right hp (mul_pos hUp hVp).le
    _ = (Hη^2*F*G) * (markedPhysicalActualUnionMajorantSum e x hdis d₀ Y A B C D R Q ψ/(U*V)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)

theorem markedPhysical_good_removal_explicit_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (β H R T : ℝ) (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β)
    (hβhi : β+(1/100 : ℝ) < 49/50) (hH : 0 ≤ H) (hR : 0 ≤ R)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (_hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
        (d₀ Y U V A B C D Q W Hη Cα Cβ q : ℝ)
        (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
        (w : Z → ℤ × ℤ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (α βf : ℕ → ℂ),
        x^δ ≤ U → x^δ ≤ V → U ≤ A → A ≤ B → B ≤ 16*U →
        V ≤ C → C ≤ D → D ≤ 2*V → Z ⊆ markedPhysicalPrimitiveBox A B C D →
        (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
        1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
        0 ≤ W → 0 ≤ Hη → 0 ≤ Cα → 0 ≤ Cβ →
        (∀ v, ‖ψ v‖ ≤ W) → (∀ v, ψ v ≠ 0 → |v| ≤ R) → (∀ v, ‖η v‖ ≤ Hη) →
        (∀ n, ‖α n‖ ≤ Cα) → (∀ n, ‖βf n‖ ≤ Cβ) →
        let P := fun j => markedLogPowerBand (e j) x
        let hP := fun j p (hp : p ∈ P j) => (mem_markedLogPowerBand.mp hp).1
        let ν := fun j => bandReciprocalMass (P j)
        let n := ⌊(Real.log x)^(1/100 : ℝ)⌋₊
        let f := fun s : MarkedPhysicalState P (markedPadSlots x) Z =>
          markedPhysicalEndpointVector P (markedPadSlots x) α βf s.1.1.1
        let G := MarkedPhysicalActualGood e x d₀ Y w
        ‖markedPhysicalEdgePairing P hP ν n Z hZ ψ η d₀ Y Q q f f -
          markedPhysicalEdgePairing P hP ν n Z hZ ψ η d₀ Y Q q
            (markedPhysicalGoodVector G f) (markedPhysicalGoodVector G f)‖/(U*V) ≤
          (2*Hη^2*(Cα*Cβ)^2) *
            ((16/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) +
              (5*E*W)*x^(-δ/4000)) := by
  obtain ⟨E,hE,hsource⟩ := markedPhysical_source_bad_absolute_bound e he hinj β H R T
    hβ heβ hβhi hH hR hδ
  refine ⟨E,hE,?_⟩
  filter_upwards [hsource, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro hdis d₀ Y U V A B C D Q W Hη Cα Cβ q Z hZ w ψ η α βf hU hV hUA hAB hB hVC hCD hD
    hbox hw hQ hQhi hY hYhi hYlo hW hHη hCα hCβ hψ hsupp hη hα hβf
  dsimp only
  let P := fun j => markedLogPowerBand (e j) x
  let f := fun s : MarkedPhysicalState P (markedPadSlots x) Z =>
    markedPhysicalEndpointVector P (markedPadSlots x) α βf s.1.1.1
  have hf : ∀ s, ‖f s‖ ≤ Cα*Cβ := fun s =>
    markedPhysicalEndpointVector_norm_le_global P (markedPadSlots x) α βf hCα hCβ hα hβf s.1.1.1
  have hF : 0 ≤ Cα*Cβ := mul_nonneg hCα hCβ
  have hfirst := hx hdis d₀ Y U V A B C D Q W Hη (Cα*Cβ) (Cα*Cβ) Z hZ w ψ η
    hU hV hUA hAB hB hVC hCD hD hbox hw hQ hQhi hY hYhi hYlo hW hHη hF hF hψ hsupp hη f f hf hf
  obtain ⟨hψr,hsuppr⟩ := markedRawEdgeReflectedCutoff_bounds ψ hψ hsupp
  have hsecond := hx hdis d₀ Y U V A B C D Q W Hη (Cα*Cβ) (Cα*Cβ) Z hZ w
    (markedRawEdgeReflectedCutoff ψ) η hU hV hUA hAB hB hVC hCD hD hbox hw hQ hQhi hY hYhi hYlo
    hW hHη hF hF hψr hsuppr hη f f hf hf
  have hremove := markedPhysicalActualGoodRemoval_bound e x hdis Z hZ ψ η d₀ Y Q q α βf w
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hnorm := div_le_div_of_nonneg_right hremove (mul_pos hUp hVp).le
  rw [add_div] at hnorm
  apply (hnorm.trans (add_le_add hfirst hsecond)).trans_eq
  ring

end ArtinMatthews
