module

public import ArtinMatthews.SourceKPAutomorphicSpectralContinuation
public import ArtinMatthews.SourceKPSelectedCuspPairing
public import ArtinMatthews.SourceKPBandResidueTransfer
public import ArtinMatthews.SourceKPCoupledScatteringResidue


set_option backward.privateInPublic true
@[expose] public section

/-! Nonvanishing from an exact full-dimensional outgoing band pairing. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic MeasureTheory Filter
open scoped NumberField AdeleRing MatrixGroups Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "L₂" => SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)
local notation "qf" => Prod.snd (sourceKPCoupledWildWeyl K hζ)
local notation "b" => Prod.snd (sourceKPFiniteLevelMk K hζ (1,qf))
local notation "h₀" => sourceKPAdelicCoverHeight K hζ (1,qf)

theorem sourceKPAutomorphicExceptionalResidue_band_of_initial {T A B : ℝ}
    (hT : 1 ≤ T) (hTA : 2*T ≤ A) (hA : 1 ≤ A) (hAB : A < B)
    (hinit : ∀ s : ℂ, ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1 →
      ((sourceKPAutomorphicTruncatedContinuation K hζ hT s : L₂) : Y → ℂ) =ᵐ[μY]
        sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      sixthWildPrimes K ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      sourceKPSelectedCuspBandPairing K hζ b (B := B) hA
          (sourceKPAutomorphicExceptionalResidue K hζ hT) =
        sourceKPCoupledScatteringResidue K S * sourceKPSelectedCuspMoment K hζ b A B h₀ (1/6) ∧
      sourceKPSelectedCuspBandPairing K hζ b (B := B) hA
          (sourceKPAutomorphicExceptionalResidue K hζ hT) ≠ 0 := by
  obtain ⟨S,hW,hH,hB,hM⟩ := sourceKPCoupledScatteringContinuation_initial K hζ
  let L := sourceKPSelectedCuspBandPairing K hζ b (B := B) hA
  let J := sourceKPSelectedCuspMoment K hζ b A B h₀
  have hh : 0 < h₀ := sourceKPAdelicCoverHeight_pos K hζ _
  let deg : ℝ := ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ)
  let a : ℂ := (deg : ℂ)
  have hdeg : 0 < deg := by dsimp only [deg]; positivity
  have ha : 0 < a.re := by simpa only [a,Complex.ofReal_re] using hdeg
  have he : (fun s => L (sourceKPAutomorphicTruncatedContinuation K hζ hT s)) =ᶠ[𝓝 a]
      fun s => sourceKPCoupledScatteringContinuation K S s*J s := by
    have ha' : deg/2 < a.re := by simp only [a,Complex.ofReal_re]; linarith
    filter_upwards [(Complex.continuous_re.tendsto a).eventually (Ioi_mem_nhds ha')] with s hs
    have hss : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1 := by
      change deg ≤ 2*s.re+1
      linarith
    have h := sourceKPSelectedCuspBandPairing_eq_intertwiner K hζ qf (B := B) hT hTA hA hss _
      (hinit s hss)
    rw [hM s hss] at h
    exact h
  have hU : IsPreconnected {s : ℂ | 0 < s.re} :=
    ((convex_Ioi (𝕜 := ℝ) (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hp := sourceKPBandResidue_pairing L hU
    (sourceKPAutomorphicTruncatedContinuation_meromorphic K hζ hT)
    (sourceKPCoupledScatteringContinuation_meromorphic K S)
    (sourceKPSelectedCuspMoment_analyticAt K hζ b (A := A) (B := B) (h := h₀) hA hh)
    ha (by norm_num : 0 < (1/6 : ℂ).re) he
    (sourceKPAutomorphicExceptionalResidue_tendsto K hζ hT)
    (sourceKPCoupledScatteringResidue_tendsto K S)
  have hJ : J (1/6) ≠ 0 := by
    have h := sourceKPSelectedCuspMoment_oneSixth_re_pos K hζ b hA hAB hh
    change 0 < (J (1/6)).re at h
    intro hz
    rw [hz,Complex.zero_re] at h
    exact (lt_irrefl _ h)
  refine ⟨S,hW,hH,hB,hp,?_⟩
  change L (sourceKPAutomorphicExceptionalResidue K hζ hT) ≠ 0
  rw [hp]
  exact mul_ne_zero (sourceKPCoupledScatteringResidue_ne_zero K S) hJ

theorem sourceKPAutomorphicTruncatedContinuation_order_of_residue_ne_zero {T : ℝ} (hT : 1 ≤ T)
    (hres : sourceKPAutomorphicExceptionalResidue K hζ hT ≠ 0) :
    meromorphicOrderAt (sourceKPAutomorphicTruncatedContinuation K hζ hT) (1/6) = -1 := by
  have hm : MeromorphicAt (sourceKPAutomorphicTruncatedContinuation K hζ hT) (1/6) :=
    sourceKPAutomorphicTruncatedContinuation_meromorphic K hζ hT _ (by norm_num)
  apply (meromorphicOrderAt_eq_int_iff hm (n := -1)).mpr
  refine ⟨sourceKPAutomorphicExceptionalRegularized K hζ hT,
    sourceKPAutomorphicExceptionalRegularized_analyticAt K hζ hT,?_ ,?_⟩
  · rwa [sourceKPAutomorphicExceptionalRegularized_value]
  · filter_upwards [sourceKPAutomorphicExceptionalRegularized_eventually_eq K hζ hT,
      self_mem_nhdsWithin] with s h hs
    have hne : s - (1/6 : ℂ) ≠ 0 := sub_ne_zero.mpr hs
    change sourceKPAutomorphicTruncatedContinuation K hζ hT s =
      (s-1/6)^(-1 : ℤ) • sourceKPAutomorphicExceptionalRegularized K hζ hT s
    rw [h,zpow_neg_one,smul_smul,inv_mul_cancel₀ hne,one_smul]

end
end ArtinMatthews
