module

public import ArtinMatthews.SourceKPDeepIdealHaar
public import ArtinMatthews.SourceKPLocalCompactFlatBorel


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine small valuation balls lie in the all-place Hensel cube
neighborhood. The resulting unit cubes act trivially on the actual
normalized Borel value space. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField AdeleRing SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K
local notation "ν₀" => sourceLocalValuation K P
local notation "B" => sourceLocalBall K P

theorem sourceKPJacquet_scaled_integer_contains_ball (c : L) (hc : c ≠ 0) :
    ∃ M : ℕ, 1 ≤ M ∧ B (-(M : ℤ)) ⊆ (fun x : L => c * x) '' (O : Set L) := by
  let d := WithZero.log (ν₀ c)
  have hd : WithZero.exp d = ν₀ c := WithZero.exp_log ((Valuation.ne_zero_iff ν₀).mpr hc)
  let M := max 1 (-d).toNat
  refine ⟨M, le_max_left _ _, ?_⟩
  intro x hx
  have hM : -(M : ℤ) ≤ d := by
    have h := le_max_right 1 (-d).toNat
    dsimp [M]
    omega
  have hv : ν₀ x ≤ ν₀ c := (show ν₀ x ≤ WithZero.exp (-(M : ℤ)) from hx).trans
    ((WithZero.exp_le_exp.mpr hM).trans_eq hd)
  refine ⟨x / c, ?_, ?_⟩
  · apply (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mpr
    change ν₀ (x / c) ≤ 1
    rw [map_div₀]
    exact (div_le_one₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff ν₀).mpr hc))).mpr hv
  · field_simp [hc]

theorem sourceKPJacquet_deep_ball_subset :
    ∃ M : ℕ, 1 ≤ M ∧ B (-(M : ℤ)) ⊆ sourceKPDeepIdealImage K P := by
  obtain ⟨c, hc, he⟩ := sourceKPDeepIdealImage_eq_scaled_integer K P
  rw [he]
  exact sourceKPJacquet_scaled_integer_contains_ball K P c hc

theorem sourceKPJacquet_tiny_unit_cube :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ z : Lˣ, ((z : L) - 1) ∈ B (-(M : ℤ)) →
      ∃ w : Lˣ, z = w ^ 3 ∧ ν₀ (z : L) = 1 := by
  obtain ⟨M, hM, hdeep⟩ := sourceKPJacquet_deep_ball_subset K P
  refine ⟨M, hM, ?_⟩
  intro z hz
  obtain ⟨r, hr, hrv⟩ := hdeep hz
  change r ∈ sourceKPDeepIdeal K P at hr
  let x : O := 1 + r
  have hx : x - 1 ∈ sourceKPDeepIdeal K P := by simpa only [x, add_sub_cancel_left] using hr
  obtain ⟨w, hw⟩ := sourceKPDeepEntry_cube K P x hx
  refine ⟨w, Units.ext ?_, ?_⟩
  · calc
      (z : L) = 1 + algebraMap O L r := by rw [hrv]; ring
      _ = algebraMap O L x := by dsimp only [x]; rw [map_add, map_one]
      _ = ((w ^ 3 : Lˣ) : L) := hw
  have hsmall : ν₀ ((z : L) - 1) < 1 :=
    (show ν₀ ((z : L) - 1) ≤ WithZero.exp (-(M : ℤ)) from hz).trans_lt (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega)
  calc
    _ = ν₀ (1 + ((z : L) - 1)) := congrArg ν₀ (by ring)
    _ = ν₀ 1 := (ν₀).map_add_eq_of_lt_left (by simpa only [map_one] using hsmall)
    _ = 1 := map_one _

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPJacquet_actual_unit_cube_fixed (s : ℂ) (y : Lˣ)
    (hy : ν₀ ((y ^ 3 : Lˣ) : L) = 1) (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicLocalBorelRepresentation K hζ P s
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P (y ^ 3)) v = v := by
  have hn : sourceKPIdeleAbsoluteNorm K ((IdeleGroup.ofAdicCompletion (𝓞 K) K P y)^3) = 1 := by
    rw [← map_pow, sourceKPIdeleAbsoluteNorm_ofAdicCompletion]
    exact Valued.toNormedField.norm_eq_one_iff.mpr hy
  rw [sourceKPAdelicLocalBorelRepresentation_cube,
    sourceKPIdeleComplexNorm_of_norm_one K (s+1/2) _ hn, Units.val_one, one_smul]

end
end ArtinMatthews
