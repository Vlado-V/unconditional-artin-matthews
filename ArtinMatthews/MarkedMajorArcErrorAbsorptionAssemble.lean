module

public import ArtinMatthews.MarkedMajorArcErrorAbsorptionRates


set_option backward.privateInPublic true
@[expose] public section

/-! Exact assembly of the four actual Riesz errors and the boundary error. -/
namespace ArtinMatthews

theorem marked_major_interval_error_le_six {K C L H ε u v r s : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hr : 0 ≤ r)
    (h₁ : markedMajorRieszError K C L H ((1+ε)*v) ≤ r)
    (h₂ : markedMajorRieszError K C L H ((1+ε)*u) ≤ r)
    (h₃ : markedMajorRieszError K C L H v ≤ r)
    (h₄ : markedMajorRieszError K C L H u ≤ r)
    (hb : (ε*(u+v)+2)*(Real.log ((1+ε)*v)/u) ≤ s) :
    markedMajorIntervalError K C L H ε u v ≤ 6*r/ε+s := by
  unfold markedMajorIntervalError
  calc
    _ ≤ ((1+ε)*(r+r)+r+r)/ε+s := by gcongr
    _ ≤ _ := by
      gcongr
      nlinarith

theorem marked_major_interval_error_power_of_four {K C L A D B c u v : ℝ}
    (hL : 1 ≤ L) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (h₁ : markedMajorRieszError K C L (L^B) ((1+L^(-D))*v) ≤
      (c/12)*L^(-(A+D)))
    (h₂ : markedMajorRieszError K C L (L^B) ((1+L^(-D))*u) ≤
      (c/12)*L^(-(A+D)))
    (h₃ : markedMajorRieszError K C L (L^B) v ≤ (c/12)*L^(-(A+D)))
    (h₄ : markedMajorRieszError K C L (L^B) u ≤ (c/12)*L^(-(A+D)))
    (hb : (L^(-D)*(u+v)+2)*(Real.log ((1+L^(-D))*v)/u) ≤
      (c/2)*L^(-A)) :
    markedMajorIntervalError K C L (L^B) (L^(-D)) u v ≤ c*L^(-A) := by
  have hLp : 0 < L := by linarith
  have hεp : 0 < L^(-D) := Real.rpow_pos_of_pos hLp _
  have hε : L^(-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.mpr hD)
  have hh := marked_major_interval_error_le_six hεp hε
    (show 0 ≤ (c/12)*L^(-(A+D)) by positivity) h₁ h₂ h₃ h₄ hb
  have hid : L^(-(A+D))/L^(-D) = L^(-A) := by
    rw [← Real.rpow_sub hLp]
    congr 1
    ring
  calc
    _ ≤ 6*((c/12)*L^(-(A+D)))/L^(-D)+(c/2)*L^(-A) := hh
    _ = (c/2)*(L^(-(A+D))/L^(-D))+(c/2)*L^(-A) := by ring
    _ = _ := by rw [hid]; ring

end ArtinMatthews
