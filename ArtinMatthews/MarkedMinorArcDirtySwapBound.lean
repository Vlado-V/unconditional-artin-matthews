module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargeSwap
public import ArtinMatthews.MarkedMinorArcDirtyMajorActualTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! The true original/reversed charge correction is uniformly bounded
on the actual logarithmic prime bands, independently of pending cutoff. -/
namespace ArtinMatthews
noncomputable section
open Filter

theorem markedRawEdgeChargeSwapModifier_actual_bound_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ),0 ≤ q → q ≤ 1 →
      ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
        (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z)
        (c : MarkedRawEdgeChoice hZ s),
        ‖markedRawEdgeChargeSwapModifier (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ s c‖ ≤
          (2/Real.log 2)^(Fintype.card J) := by
  have hband := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [hband,markedDirty_actual_band_transfer_eventually e he] with x hb ht
  intro q hq₀ hq₁ pads B Z hZ s c
  have h := ht q hq₀ hq₁
  exact markedRawEdgeChargeSwapModifier_norm_le _ (fun j => (h.2.1 j).1)
    markedDirty_transfer_constant_one_le
    (fun j => (hb j).2.le.trans markedDirty_transfer_constant_one_le)
    (fun j => (h.2.1 j).2) hZ s c

end
end ArtinMatthews
