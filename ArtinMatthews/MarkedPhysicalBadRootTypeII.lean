module

public import ArtinMatthews.MarkedPhysicalBadRootEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Conditional bad-root energy for the original supported Type-II
coefficients, with beta's exact finite square sum retained. -/
namespace ArtinMatthews
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRootBadVector_typeII_energy
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (δ A : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop,∀ (d₀ Y : ℝ) (Z : Finset (ℤ × ℤ)) (U V : ℝ),
      Real.exp (L^(1/10:ℝ)) ≤ Y → 0 < U → 0 < V →
      (∀ z ∈ Z,U ≤ (z.1:ℝ) ∧ (z.1:ℝ) ≤ 16*U ∧ V ≤ (z.2:ℝ) ∧ (z.2:ℝ) ≤ 2*V) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n ∈ Sα,Real.exp (δ*L) ≤ (n:ℝ)) →
      (∫ θ : AddCircle (1:ℝ),
        ∑ s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) (Real.exp L))
          (markedPadSlots (Real.exp L)) Z,
          markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) (Real.exp L)))
            (markedPadSlots (Real.exp L)) *
          ‖markedPhysicalRootBadVector e (Real.exp L) d₀ Y
            (markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation Sα)
            (markedPhysicalRestrictedBeta Sβ β) θ s‖^2) ≤
        (16*U)*L^(4-A)*∑ s ∈ (Finset.Ioc 0 ⌊2*V⌋₊) ∩ Sβ,‖β s‖^2 := by
  filter_upwards [(Real.tendsto_exp_atTop.eventually (markedPhysicalRootBadVector_actual_energy e he hinj A)),
    markedPhysicalEndpointEnergy_actual_typeII e (fun j => by linarith [he j]) hinj δ hδ,
    eventually_gt_atTop (0:ℝ)] with L hb hephy hL
  intro d₀ Y Z U V hY hU hV hbox Sα Sβ modulation β hSα
  have hbad := hb d₀ Y Z
    (markedMajorRestrictedCoefficient (Real.exp (L^(6/25:ℝ))) modulation Sα)
    (markedPhysicalRestrictedBeta Sβ β) (by simpa only [Real.log_exp] using hY)
  simp only [Real.log_exp] at hbad
  have henergy := hephy (markedPadSlots (Real.exp L)) Z U V hU hV hbox Sα Sβ modulation β hSα
  apply hbad.trans
  calc
    _ ≤ L^(-A)*((16*U)*L^4*∑ s ∈ (Finset.Ioc 0 ⌊2*V⌋₊) ∩ Sβ,‖β s‖^2) :=
      mul_le_mul_of_nonneg_left henergy (Real.rpow_nonneg hL.le _)
    _ = _ := by rw [show L^(4-A)=L^(-A)*L^(4:ℝ) by rw [← Real.rpow_add hL]; congr 1; ring]; norm_num; ring

end
end ArtinMatthews
