module

public import ArtinMatthews.SourceKPAdelicCuspCutoff
public import ArtinMatthews.SourceKPAdelicCuspOverlap


set_option backward.privateInPublic true
@[expose] public section

/-! The concrete cusp cutoff has at most one contributing rational
coset above height one and agrees with its inducing section high in a cusp. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicRationalHeight_high_subsingleton
    (q : SourceKPAdelicProjective K hζ) :
    Set.Subsingleton {c : SourceKPRationalBorelCoset K |
      1 < sourceKPAdelicRationalHeight K hζ q c} := by
  intro c hc d hd
  induction c using Quotient.inductionOn with
  | _ α =>
    induction d using Quotient.inductionOn with
    | _ β =>
      change 1 < sourceKPAdelicCoverHeight K hζ
        (sourceKPAdelicProjectiveRationalLift K hζ α*q) at hc
      change 1 < sourceKPAdelicCoverHeight K hζ
        (sourceKPAdelicProjectiveRationalLift K hζ β*q) at hd
      apply (sourceKPRationalBorelCosetMk_eq_iff K α β).mpr
      apply sourceKPAdelicCoverHeight_high_overlap K hζ
        (sourceKPAdelicProjectiveRationalLift K hζ α*q) (β*α⁻¹) hc
      simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using hd

theorem sourceKPAdelicCutoffEisenstein_eq_of_high {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : 2*T ≤ sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAdelicCutoffEisenstein K hζ T s q = sourceKPAdelicCompactScalar K hζ s q := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let c₀ := sourceKPRationalBorelCosetMk K (1 : PGL(2,K))
  have h₀ : sourceKPAdelicRationalHeight K hζ q c₀ = sourceKPAdelicCoverHeight K hζ q := by
    change sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ 1*q) = _
    rw [map_one, one_mul]
  have hhigh : 1 < sourceKPAdelicRationalHeight K hζ q c₀ := by
    rw [h₀]
    linarith
  have hz (c : SourceKPRationalBorelCoset K) (hc : c ≠ c₀) :
      sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c = 0 := by
    apply sourceKPAdelicCutoffSummand_zero K hζ hTpos s q c
    apply le_trans (le_of_not_gt ?_) hT
    intro hh
    exact hc (sourceKPAdelicRationalHeight_high_subsingleton K hζ q hh hhigh)
  change (∑' c, sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c) = _
  rw [tsum_eq_single c₀ hz, sourceKPAdelicCutoffSummand_eq, h₀,
    sourceKPAdelicHeightCutoff_one hTpos hq]
  change (1 : ℂ) * sourceKPAdelicCompactScalar K hζ s
    (sourceKPAdelicProjectiveRationalLift K hζ 1*q) = _
  rw [map_one, one_mul, one_mul]

theorem sourceKPAdelicCutoffEisenstein_zero_of_orbit_le {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : sourceKPAdelicOrbitHeight K hζ q ≤ T) :
    sourceKPAdelicCutoffEisenstein K hζ T s q = 0 := by
  calc
    _ = ∑' _c : SourceKPRationalBorelCoset K, (0 : ℂ) := by
      apply tsum_congr
      intro c
      apply sourceKPAdelicCutoffSummand_zero K hζ hT s q c
      induction c using Quotient.inductionOn with
      | _ γ =>
        exact (le_csSup (sourceKPAdelicOrbitHeight_range_bddAbove K hζ q)
          (Set.mem_range_self γ)).trans hq
    _ = 0 := tsum_zero

end
end ArtinMatthews
