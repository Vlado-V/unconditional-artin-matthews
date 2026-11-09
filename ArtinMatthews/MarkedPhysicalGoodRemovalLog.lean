module

public import ArtinMatthews.MarkedPhysicalGoodRemovalEstimate
public import ArtinMatthews.MarkedPhysicalLogAbsorption


set_option backward.privateInPublic true
@[expose] public section

/-! Removing the actual first/second-good projection from the original
physical endpoint pairing costs every prescribed inverse logarithm.
The estimate uses the true canonical-root distribution and physical
endpoint vectors, not a small projection norm on arbitrary states. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedPhysical_good_removal_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (β H R A₀ Eα Eβ G Hη W : ℝ)
    (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β) (hβhi : β+(1/100 : ℝ) < 49/50)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hHη : 0 ≤ Hη) (hW : 0 ≤ W)
    {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hψ : ∀ v, ‖ψ v‖ ≤ W) (hsupp : ∀ v, ψ v ≠ 0 → |v| ≤ R)
    (hη : ∀ v, ‖η v‖ ≤ Hη) :
    ∀ᶠ x : ℝ in atTop, ∀ (d₀ Y U V A B C D Q q : ℝ)
      (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
      (w : Z → ℤ × ℤ) (α βf : ℕ → ℂ),
      x^δ ≤ U → x^δ ≤ V → U ≤ A → A ≤ B → B ≤ 16*U →
      V ≤ C → C ≤ D → D ≤ 2*V → Z ⊆ markedPhysicalPrimitiveBox A B C D →
      (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) → Q ≤ (Real.log x)^A₀ →
      1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
      Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      (∀ n, ‖α n‖ ≤ (Real.log x)^Eα) → (∀ n, ‖βf n‖ ≤ (Real.log x)^Eβ) →
      let P := fun j => markedLogPowerBand (e j) x
      let hP := fun j p (hp : p ∈ P j) => (mem_markedLogPowerBand.mp hp).1
      let ν := fun j => bandReciprocalMass (P j)
      let n := ⌊(Real.log x)^(1/100 : ℝ)⌋₊
      let f := fun s : MarkedPhysicalState P (markedPadSlots x) Z =>
        markedPhysicalEndpointVector P (markedPadSlots x) α βf s.1.1.1
      let good := MarkedPhysicalActualGood e x d₀ Y w
      ‖markedPhysicalEdgePairing P hP ν n Z hZ ψ η d₀ Y Q q f f -
        markedPhysicalEdgePairing P hP ν n Z hZ ψ η d₀ Y Q q
          (markedPhysicalGoodVector good f) (markedPhysicalGoodVector good f)‖/(U*V) ≤
        (Real.log x)^(-G) := by
  let S := Eα+Eβ
  let T := G+2*S+3*A₀+1
  obtain ⟨E,hE,hbound⟩ := markedPhysical_good_removal_explicit_bound e he hinj β H R T
    hβ heβ hβhi hH hR hδ
  let K := 2*Hη^2
  let C₀ := (16/(riemannZeta 2).re)*(33*W*(8*R+5))
  let E₀ := 5*E*W
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC₀ : 0 ≤ C₀ := by
    have hz := markedPhysicalRoot_zeta_two_pos
    dsimp only [C₀]
    positivity
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  have hbudget := markedPhysicalGoodRemoval_budget K C₀ E₀ G S A₀ (δ/4000)
    hK hC₀ hE₀ (by positivity)
  filter_upwards [hbound, hbudget, marked_array_disjoint_eventually e hinj,
    eventually_gt_atTop (1 : ℝ)] with x hx hb hdis hx1
  intro d₀ Y U V A B C D Q q Z hZ w α βf hU hV hUA hAB hB hVC hCD hD hbox hw
    hQ hQhi hQlog hY hYhi hYlo hα hβf
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hα₀ : 0 ≤ (Real.log x)^Eα := Real.rpow_nonneg hlog.le _
  have hβ₀ : 0 ≤ (Real.log x)^Eβ := Real.rpow_nonneg hlog.le _
  have hh := hx hdis d₀ Y U V A B C D Q W Hη ((Real.log x)^Eα) ((Real.log x)^Eβ) q
    Z hZ w ψ η α βf hU hV hUA hAB hB hVC hCD hD hbox hw
    hQ hQhi hY hYhi hYlo hW hHη hα₀ hβ₀ hψ hsupp hη hα hβf
  have hprod : (Real.log x)^Eα*(Real.log x)^Eβ = (Real.log x)^S := by
    dsimp only [S]
    exact (Real.rpow_add hlog _ _).symm
  rw [hprod] at hh
  apply hh.trans
  have hq3 : Q^3 ≤ ((Real.log x)^A₀)^3 := pow_le_pow_left₀ (zero_le_one.trans hQ) hQlog 3
  have hl : 0 ≤ (Real.log x)^(-T) := Real.rpow_nonneg hlog.le _
  have hneg : -δ/4000 = -(δ/4000) := by ring
  calc
    _ = K*((Real.log x)^S)^2 * (C₀*Q^3*(Real.log x)^(-T) + E₀*x^(-(δ/4000))) := by
      dsimp only [K, C₀, E₀]
      rw [hneg]
      ring
    _ ≤ K*((Real.log x)^S)^2 *
        (C₀*((Real.log x)^A₀)^3*(Real.log x)^(-T) + E₀*x^(-(δ/4000))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq3 hC₀) hl) le_rfl)
        (mul_nonneg hK (sq_nonneg _))
    _ ≤ _ := hb

end ArtinMatthews
