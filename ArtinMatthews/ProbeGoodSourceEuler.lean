module

public import ArtinMatthews.ProbeGoodBadSourceBridge


set_option backward.privateInPublic true
@[expose] public section

/-! The j=0 case of the exact source term shared with the bad-prime proof. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeGoodSourceSeries_eq_raw (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ ξ w z : ℂ) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    Summable (probePrimeRawTerm K p hp χ η θ ((Q : ℂ) ^ (-ξ)) ((Q : ℂ) ^ (-w))
      (ArtinMatthews.probeLocalV Q z)) →
    probeBadPrimeSourceSeries K p hp χ 0 (probePrimeGaussGamma K p hp χ 2)
      (probePrimeGaussLocalVartheta K p hp χ η) θ ξ w z =
      probePrimeRawLocalSeries K p hp χ η θ ((Q : ℂ) ^ (-ξ)) ((Q : ℂ) ^ (-w))
        (ArtinMatthews.probeLocalV Q z) := by
  dsimp only
  intro hs
  simp only [Complex.ofReal_natCast] at hs ⊢
  let f := probePrimeRawTerm K p hp χ η θ
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-ξ))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (ArtinMatthews.probeLocalV (Ideal.absNorm (Ideal.span {p})) z)
  let g : (Fin 2 × ℕ × ℕ × ℕ) → ℂ := fun i =>
    probeBadPrimeSourceTerm K p hp χ 0 (probePrimeGaussGamma K p hp χ 2)
      (probePrimeGaussLocalVartheta K p hp χ η) θ ξ w z i.1 i.2.2.1 i.2.1 i.2.2.2
  have hg (i : Fin 2 × ℕ × ℕ × ℕ) : g i = f (probeSourceIndexEquiv i) := by
    rcases i with ⟨e, k, l, m⟩
    have he := probePrimeRawTerm_eq_source K p hp χ η θ ξ w z
      (probeBoolFinTwo.symm e) l k m
    simpa only [probeSourceIndexEquiv, Equiv.coe_fn_mk, Equiv.apply_symm_apply,
      Complex.ofReal_natCast, g, f] using he.symm
  have hgfun : g = f ∘ probeSourceIndexEquiv := funext hg
  have hgs : Summable g := by
    rw [hgfun]
    exact hs.comp_injective probeSourceIndexEquiv.injective
  have hsum : (∑' i, g i) = ∑' i, f i := by
    rw [hgfun]
    exact probeSourceIndexEquiv.tsum_eq f
  unfold probeBadPrimeSourceSeries probePrimeRawLocalSeries
  rw [← tsum_fintype (L := SummationFilter.unconditional (Fin 2))]
  exact hgs.tsum_prod.symm.trans hsum

theorem probeGoodSourceSeries_eq_factor (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ ξ w z : ℂ) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let v := probePrimeGaussLocalVartheta K p hp.ne_zero χ η
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q (v ^ 6) ξ z‖ < 1 →
    probeBadPrimeSourceSeries K p hp.ne_zero χ 0 (probePrimeGaussGamma K p hp.ne_zero χ 2)
      v θ ξ w z =
      ArtinMatthews.probeGoodLocalFactor (Q : ℂ)
        (ArtinMatthews.probeLocalV Q z) (ArtinMatthews.probeLocalW Q θ w)
        (ArtinMatthews.probeLocalD Q (η * θ⁻¹) ξ)
        (ArtinMatthews.probeLocalE Q (v ^ 6) ξ z) := by
  dsimp only
  intro hV hW hE
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  have he : (probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 *
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-ξ)) ^ 6 *
      ArtinMatthews.probeLocalV (Ideal.absNorm (Ideal.span {p})) z =
      ArtinMatthews.probeLocalE (Ideal.absNorm (Ideal.span {p}))
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6) ξ z := by
    simp only [ArtinMatthews.probeLocalV, ArtinMatthews.probeLocalE, Complex.ofReal_natCast]
    rw [mul_assoc, mul_assoc]
    congr 1
    simpa only [mul_assoc] using probe_cpow_local_geometric _ hq ξ z
  have hs := (probePrimeRawLocal_hasSum K p hp χ hχ hminus hchar η θ
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-ξ))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (ArtinMatthews.probeLocalV (Ideal.absNorm (Ideal.span {p})) z) hθ hV hW (he.symm ▸ hE)).summable
  rw [probeGoodSourceSeries_eq_raw K p hp.ne_zero χ η θ ξ w z hs]
  exact probePrimeRawLocal_analytic_factor K p hp χ hχ hminus hchar η θ ξ w z hθ hV hW hE

theorem probeGoodSourceSeries_correction (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ ξ w z : ℂ) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let v := probePrimeGaussLocalVartheta K p hp.ne_zero χ η
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q (v ^ 6) ξ z‖ < 1 →
    (1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q θ w) /
      (1 - ArtinMatthews.probeLocalD Q (η * θ⁻¹) ξ) *
      probeBadPrimeSourceSeries K p hp.ne_zero χ 0 (probePrimeGaussGamma K p hp.ne_zero χ 2)
        v θ ξ w z =
      ArtinMatthews.probeGoodPrimeCorrection Q θ (η * θ⁻¹) (v ^ 6) ξ w z := by
  dsimp only
  intro hV hW hE
  rw [probeGoodSourceSeries_eq_factor K p hp χ hχ hminus hchar η θ ξ w z hθ hV hW hE]
  rfl

end

end ArtinMatthews.VaryingKummerAnalytic
