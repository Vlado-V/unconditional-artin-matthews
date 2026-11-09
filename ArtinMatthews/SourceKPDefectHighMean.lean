module

public import ArtinMatthews.SourceKPDefectHighFormula
public import ArtinMatthews.SourceKPAutomorphicDefectGenuine
public import ArtinMatthews.SourceKPCuspBandUnfolding


set_option backward.privateInPublic true
@[expose] public section

/-! The actual defect pairs only with the unipotent mean on the high cusp.
The normalized trace measure and compact automorphic measure are the same
ones used in the genuine closed form. -/

namespace ArtinMatthews
open NumberField MeasureTheory Set Filter
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "π" => sourceKPAutomorphicCompactMk K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local instance sourceKPDefectHighMeanAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _

/-- The literal normalized unipotent average of a compact automorphic
representative on the high-cusp section. -/
def sourceKPCompactHighUnipotentMean (A : ℝ) (W : Y → ℂ)
    (x : SourceKPHighCuspFinite K hζ A) : ℂ :=
  ∫ y in sourceKPAdelicFundamentalDomain K,
    W (π (sourceKPHighCuspProjection K hζ A (Multiplicative.ofAdd y • x)).val)
      ∂sourceKPAdelicTraceProduct K

private theorem compactDefect_highProjection_upper {T : ℝ} (hT : 2 < T) (s : ℂ)
    (x : SourceKPHighCuspFinite K hζ (T / 2)) (y : 𝔸[K]) :
    sourceKPAutomorphicCompactCutoffDefect K hζ (by linarith : 0 < T) s
      (π (sourceKPHighCuspProjection K hζ (T / 2) (Multiplicative.ofAdd y • x)).val) =
    sourceKPAutomorphicCompactCutoffDefect K hζ (by linarith : 0 < T) s
      (π (sourceKPHighCuspProjection K hζ (T / 2) x).val) := by
  obtain ⟨q, hq⟩ := sourceKPFiniteLevelMk_surjective K hζ x.val
  have hqhigh : T / 2 < sourceKPAdelicCoverHeight K hζ q := by
    have hx := x.property
    change T / 2 < sourceKPFiniteLevelHeight K hζ x.val at hx
    rwa [← hq, sourceKPFiniteLevelHeight_mk] at hx
  have hproj : (sourceKPHighCuspProjection K hζ (T / 2) x).val =
      sourceKPAutomorphicLevelMk K hζ q :=
    congrArg (Quotient.mk _) hq.symm
  rw [sourceKPCuspHighUpper_projection_mk K hζ (T / 2) y x q hq, hproj,
    sourceKPAutomorphicCompactCutoffDefect_adelic, sourceKPAutomorphicCompactCutoffDefect_adelic]
  exact sourceKPAdelicCutoffCasimirDefect_high_upper K hζ hT s q hqhigh y

theorem sourceKPCompactDefect_pairing_eq_zero_of_highMean_zero {T : ℝ} (hT : 2 < T) (s : ℂ)
    (W : Y → ℂ) (hW : MemLp W 2 μY)
    (hmean : ∀ᵐ x ∂(sourceKPHighRepresentativeHaar K hζ (T / 2)).restrict
        (sourceKPCuspBandHighSection K hζ (T / 2)),
      sourceKPCompactHighUnipotentMean K hζ (T / 2) W x = 0) :
    sourceKPGenuineAutomorphicL2Pairing K hζ W hW
      (sourceKPAutomorphicGenuineDefectL2 K hζ (by linarith : 1 ≤ T) s) = 0 := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  let A := T / 2
  let F := sourceKPCuspBandHighSection K hζ A
  let p := sourceKPHighCuspProjection K hζ A
  let D := sourceKPAutomorphicCompactCutoffDefect K hζ hT0 s
  let d := sourceKPAutomorphicGenuineDefectL2 K hζ hT1 s
  have hd : (d.val : Y → ℂ) =ᵐ[μY] D := by
    have he : d.val = sourceKPAutomorphicDefectL2 K hζ hT1 s :=
      sourceKPAutomorphicGenuineDefectL2_coe K hζ hT1 s
    rw [he]
    exact sourceKPAutomorphicDefectL2_ae K hζ hT1 s
  let G : Y → ℂ := fun x => star (W x) * D x
  let f : SourceKPHighCuspAutomorphic K hζ A → ℂ := fun x => G (π x.val)
  have hG : Integrable G μY := sourceKPGenuineAutomorphicL2Pairing_integrable K hζ hW d hd
  have hf : Integrable f (sourceKPHighCuspMeasure K hζ A) :=
    sourceKPAutomorphicBandIntegral_integrable_high K hζ G hG A
  have hzero (x : Y) (hx : sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ A) : G x = 0 := by
    have hD : D x = 0 := sourceKPAutomorphicCompactCutoffDefect_zero_of_orbit_le K hζ hT0 s x hx
    change star (W x) * D x = 0
    rw [hD, mul_zero]
  obtain ⟨hm, hi, hc⟩ := sourceKPCuspBandHighSection_spec K hζ A
  have hA : 1 < A := by dsimp only [A]; linarith
  have havg := (sourceKPCuspHighSection_average_integral K hζ A hA F hm hi hc f hf).2
  calc
    _ = ∫ x : Y, G x ∂μY := sourceKPGenuineAutomorphicL2Pairing_apply K hζ hW d hd
    _ = ∫ x, f x ∂sourceKPHighCuspMeasure K hζ A :=
      sourceKPAutomorphicBandIntegral_eq_high K hζ G hG A hzero
    _ = ∫ x in F, (∫ y in sourceKPAdelicFundamentalDomain K,
        f (p (Multiplicative.ofAdd y • x)) ∂sourceKPAdelicTraceProduct K)
        ∂sourceKPHighRepresentativeHaar K hζ A := havg
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hmean] with x hx
      have hconst (y : 𝔸[K]) :
          D (π (p (Multiplicative.ofAdd y • x)).val) = D (π (p x).val) :=
        compactDefect_highProjection_upper K hζ hT s x y
      change (∫ y in sourceKPAdelicFundamentalDomain K,
        star (W (π (p (Multiplicative.ofAdd y • x)).val)) *
          D (π (p (Multiplicative.ofAdd y • x)).val) ∂sourceKPAdelicTraceProduct K) = 0
      simp_rw [hconst]
      rw [integral_mul_const]
      simp only [Complex.star_def, integral_conj]
      change star (sourceKPCompactHighUnipotentMean K hζ A W x) * D (π (p x).val) = 0
      rw [hx, star_zero, zero_mul]

theorem sourceKPGenuineDefect_inner_eq_zero_of_highMean_zero {T : ℝ} (hT : 2 < T) (s : ℂ)
    (u : SourceKPGenuineAutomorphicL2 K hζ)
    (hmean : ∀ᵐ x ∂(sourceKPHighRepresentativeHaar K hζ (T / 2)).restrict
        (sourceKPCuspBandHighSection K hζ (T / 2)),
      sourceKPCompactHighUnipotentMean K hζ (T / 2) (u.val : Y → ℂ) x = 0) :
    inner ℂ u (sourceKPAutomorphicGenuineDefectL2 K hζ (by linarith : 1 ≤ T) s) = 0 := by
  have hW : MemLp (u.val : Y → ℂ) 2 μY :=
    Lp.memLp (show Lp ℂ 2 μY from u.val)
  have h := sourceKPCompactDefect_pairing_eq_zero_of_highMean_zero K hζ hT s _ hW hmean
  change inner ℂ (hW.toLp (u.val : Y → ℂ))
    (sourceKPAutomorphicGenuineDefectL2 K hζ (by linarith : 1 ≤ T) s).val = 0 at h
  rw [Lp.toLp_coeFn] at h
  exact h

end
end ArtinMatthews
