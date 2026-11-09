module

public import ArtinMatthews.SourcePoissonQuotientMajorant


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical ENNReal BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SourcePoissonPhysicalOrbitIndex :=
  SourceFrequencyRepresentativeIndex F S₀ × SourceExponentCoordinates F S₀

private theorem sourcePoissonPhysicalOrbitIndex_countable :
    Countable (SourcePoissonPhysicalOrbitIndex F S₀) := by
  let : Countable (Ideal (𝓞 F)) := by
    apply Set.countable_univ_iff.mp
    apply (Set.countable_iUnion (fun n : ℕ =>
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).countable)).mono
    intro I _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  let : Countable (HeightOneSpectrum (𝓞 F)) := HeightOneSpectrum.asIdeal_injective.countable
  let : Countable (SourceFrequencyRepresentativeIndex F S₀) :=
    sourcePoissonActualFrequency_countable F S₀
  unfold SourcePoissonPhysicalOrbitIndex SourceExponentCoordinates SourceEuler.SourceCoordinates
  infer_instance

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (v : InfinitePlace F)

local notation "S" => sourceHilbertSet F S₀
local notation "I" => SourcePoissonPhysicalOrbitIndex F S₀
local notation "Γ" => sNormOneSixthSubgroup F S
local notation "D" => sNormOneFundamentalSet F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v
local notation "μ" => sourceSLocalProbeQuotientMeasure F hζ S v
local notation "Q" => SNormOneSixthQuotient F S
local notation "U" => sourceFrequencyRepresentative F hζ S₀
local notation "qu" => sourcePoissonFrequencyNorm F S₀
local notation "amp" => sourcePoissonOrbitAmplitude F S₀ hζ hS η

/-- The physical orbit family on the normalized quotient, before unfolding the sheets. -/
def sourcePoissonActualQuotientSeries (X Y Z : ℝ) (u : I → SWholeUnits F S) (t : Q) : ℂ :=
  sourceSLocalProbeOrbitSeries F hζ S v (fun p : I => amp X Y Z (U p.1) p.2) u t

/-- The absolute sheet masses themselves are summable at the actual initial scale. -/
theorem sourcePoissonActualQuotient_mass_lt_top {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : I → SWholeUnits F S)
    (hN : ∀ p, sLocalNorm F S (u p) = sourcePoissonOrbitScale F S₀ X (U p.1) p.2) :
    (∑' p : I, sourceSLocalProbeAbsoluteMass F hζ S v (amp X Y Z (U p.1) p.2) (u p)) < ⊤ := by
  obtain ⟨C, hC, hSheet⟩ := sourceSLocalProbeAbsoluteMass_le F hζ S v 2 (by norm_num)
  obtain ⟨B, hB, hAmp⟩ := sourcePoissonOrbitAmplitude_scale_bound F S₀ hζ hS η hX hY hZ
  let A := sourceCoordinateMajorant F S₀ 3 10 3 12
  let V (j : SourceFrequencyRepresentativeIndex F S₀) := (qu (U j)) ^ (-(2 : ℝ))
  have hA : Summable A :=
    sourceCoordinateMajorant_summable F S₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hV : Summable V := sourcePoissonActualFrequencyNorm_summable F S₀ hζ
  have hV₀ : 0 ≤ V := fun j => Real.rpow_nonneg (sourcePoissonFrequencyNorm_pos F S₀ (U j)).le _
  have hA₀ : 0 ≤ A := by
    intro a
    dsimp [A, sourceCoordinateMajorant]
    positivity
  have hSum : Summable (fun p : I => C * (B * (V p.1 * A p.2))) :=
    ((hV.mul_of_nonneg hA hV₀ hA₀).mul_left B).mul_left C
  refine (ENNReal.tsum_le_tsum fun p => ?_).trans_lt
    (lt_top_iff_ne_top.mpr hSum.tsum_ofReal_ne_top)
  apply (hSheet _ (u p)).trans
  apply ENNReal.ofReal_le_ofReal
  rw [hN p]
  calc
    _ = C * (‖amp X Y Z (U p.1) p.2‖ *
        (sourcePoissonOrbitScale F S₀ X (U p.1) p.2) ^ (-(2 : ℝ))) := by ac_rfl
    _ ≤ C * (B * V p.1 * A p.2) := mul_le_mul_of_nonneg_left (hAmp (U p.1) p.2) hC
    _ = _ := by ac_rfl

/-- Joint absolute convergence of the actual translated terms on the fundamental set. -/
theorem sourcePoissonActualQuotient_ae_summable {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : I → SWholeUnits F S)
    (hN : ∀ p, sLocalNorm F S (u p) = sourcePoissonOrbitScale F S₀ X (U p.1) p.2) :
    ∀ᵐ x ∂(ν).restrict D, Summable (fun p : I × Γ => ‖amp X Y Z (U p.1.1) p.1.2 *
      sourceSLocalProbeOrbitTranslate F hζ S v (u p.1) p.2 x‖) := by
  let : Countable I := sourcePoissonPhysicalOrbitIndex_countable F S₀
  exact sourceSLocalProbeOrbitSeries_ae_summable F hζ S v
    (fun p : I => amp X Y Z (U p.1) p.2) u
    (sourcePoissonActualQuotient_mass_lt_top F S₀ hζ hS η v hX hY hZ u hN)

theorem sourcePoissonActualQuotient_ae_mk {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : I → SWholeUnits F S)
    (hN : ∀ p, sLocalNorm F S (u p) = sourcePoissonOrbitScale F S₀ X (U p.1) p.2) :
    ∀ᵐ x ∂(ν).restrict D,
      sourcePoissonActualQuotientSeries F S₀ hζ hS η v X Y Z u (sNormOneSixthQuotientMap F S x) =
      ∑' p : I × Γ, amp X Y Z (U p.1.1) p.1.2 *
        sourceSLocalProbeOrbitTranslate F hζ S v (u p.1) p.2 x := by
  filter_upwards [sourcePoissonActualQuotient_ae_summable F S₀ hζ hS η v hX hY hZ u hN] with x hx
  exact sourceSLocalProbeOrbitSeries_mk_of_summable F hζ S v
    (fun p : I => amp X Y Z (U p.1) p.2) u x hx

/-- The normalized quotient integral is the already constructed actual orbit series. -/
theorem sourcePoissonActualQuotient_unfold {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : I → SWholeUnits F S)
    (hN : ∀ p, sLocalNorm F S (u p) = sourcePoissonOrbitScale F S₀ X (U p.1) p.2) :
    Integrable (sourcePoissonActualQuotientSeries F S₀ hζ hS η v X Y Z u) μ ∧
      (∫ t, sourcePoissonActualQuotientSeries F S₀ hζ hS η v X Y Z u t ∂μ) =
        sourcePoissonActualOrbitSeries F S₀ hζ hS η v X Y Z := by
  let : Countable I := sourcePoissonPhysicalOrbitIndex_countable F S₀
  let c (p : I) := amp X Y Z (U p.1) p.2
  have hMass := sourcePoissonActualQuotient_mass_lt_top F S₀ hζ hS η v hX hY hZ u hN
  have h := sourceSLocalProbeOrbitSeries_unfold F hζ S v c u hMass
  have hs : Summable (fun p : I =>
      ‖c p * sourceSLocalProbeSheet F hζ S v (sLocalNorm F S (u p))‖) := by
    apply tsum_enorm_ne_top_iff_summable_norm.mp
    refine ((ENNReal.tsum_le_tsum fun p => ?_).trans_lt hMass).ne
    rw [← ofReal_norm, sourceSLocalProbeAbsoluteMass_eq_real]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, ← sourceSLocalProbeScaled_integral_eq_sheet]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
  refine ⟨h.1, h.2.trans ?_⟩
  rw [hs.of_norm.tsum_prod]
  unfold sourcePoissonActualOrbitSeries
  apply tsum_congr
  intro j
  apply tsum_congr
  intro a
  rw [hN (j,a)]
  exact sourcePoissonOrbitAmplitude_mul_sheet_eq_term F S₀ hζ hS η v X Y Z (U j) a

/-- The same equality for the representative integral and the jointly indexed translates. -/
theorem sourcePoissonActualQuotient_fundamentalIntegral {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : I → SWholeUnits F S)
    (hN : ∀ p, sLocalNorm F S (u p) = sourcePoissonOrbitScale F S₀ X (U p.1) p.2) :
    let G := fun x : SNormOne F S => ∑' p : I × Γ, amp X Y Z (U p.1.1) p.1.2 *
      sourceSLocalProbeOrbitTranslate F hζ S v (u p.1) p.2 x
    Integrable G ((ν).restrict D) ∧
      (∫ x in D, G x ∂ν) = sourcePoissonActualOrbitSeries F S₀ hζ hS η v X Y Z := by
  let P := sourcePoissonActualQuotientSeries F S₀ hζ hS η v X Y Z u
  have h := sourcePoissonActualQuotient_unfold F S₀ hζ hS η v hX hY hZ u hN
  have hm : Integrable P (((ν).restrict D).map (sNormOneSixthQuotientMap F S)) := h.1
  have hq : Measurable (sNormOneSixthQuotientMap F S) := measurable_quotient_mk''
  have hI := (integrable_map_measure hm.aestronglyMeasurable hq.aemeasurable).mp hm
  have hEq := sourcePoissonActualQuotient_ae_mk F S₀ hζ hS η v hX hY hZ u hN
  dsimp only
  refine ⟨hI.congr hEq, ?_⟩
  exact (integral_congr_ae (hEq.mono fun _ hx => hx.symm)).trans
    ((sNormOneQuotient_integral F S ν P h.1).symm.trans h.2)

end
end ArtinMatthews.SourceEulerAssembly
