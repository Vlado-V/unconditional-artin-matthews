module

public import ArtinMatthews.MarkedMajorTypeIIData
public import ArtinMatthews.MarkedMajorBandReindex


set_option backward.privateInPublic true
@[expose] public section

/-! The actual PD03 bands and scalar coefficient class instantiate every
arithmetic field of the proved determinant-major bound. -/
namespace ArtinMatthews
open Filter Finset
open scoped ContDiff

 theorem markedMajor_typeII_option_actual {J : Type} [Fintype J] [DecidableEq J]
    (e : Option J → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ))
    (δ C A Kx P : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y,‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo < 4*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ L : ℝ in atTop, ∀ H U u v Y modulation : ℝ, ∀ l r : ℕ, ∀ β : ℕ → ℂ,
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ Kx*Real.exp L →
      H ≤ u → u ≤ v → v ≤ 2*H → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      0 < Y → |modulation| ≤ L^C → (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      (∀ n ∈ Icc l r,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖markedMajorDeterminantPaperSum (fun i => markedLogPowerBand (e i) (Real.exp L))
        cutoff ψ (L^A) Y (Real.exp (L^(6/25:ℝ))) modulation u v l r β‖ ≤ (Y*(H*U))*L^(-P) := by
  let cfg := markedMajorTypeIIConfig δ C A hδ hC hA
  filter_upwards [markedMajor_determinant_major_all_log cfg 2 Kx (by norm_num) cutoff hcutoff hnorm
    hlo hhi hinterval hsupp ψ hψ P hP,markedMajorTypeII_band_data e hinj he A,
    markedMajorTypeII_scale_budget δ Kx hδ,eventually_ge_atTop (1:ℝ)] with L hs hb hrange hL
  intro H U u v Y modulation l r β hH hU hX hHu huv hvH hl hr hY hmod hβ hrough
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hUp : 0 < U := (Real.exp_pos _).trans_le hU
  have hscale := hrange H U v hH hU hX hvH
  have hrecH : Real.exp ((δ/2)*L) ≤ H := hscale.2.2.2.1.trans (half_le_self hHp.le)
  let z := markedMajorTypeIIData δ C A hδ hC hA e L H U u v Y modulation l r β hL
    hb.1 hb.2.1 hb.2.2.1 hY hrecH hscale.2.2.2.2.1 hHu huv hvH hscale.2.2.1 hl hr hβ hmod
  have heq : z.allBands=(fun i => markedLogPowerBand (e i) (Real.exp L)) :=
    markedMajorTypeIIData_allBands ..
  have hband : ∀ i p,p ∈ z.allBands i → L^A < (p:ℝ) := by
    simpa only [heq] using hb.2.2.2
  have hsave := hs (H*U) hscale.1 hscale.2.1 hX z (L^A)
    (Real.rpow_nonneg (zero_le_one.trans hL) _) le_rfl le_rfl hband hrough
  change ‖markedMajorDeterminantPaperSum z.allBands cutoff ψ (L^A) Y
    (Real.exp (L^(6/25:ℝ))) modulation u v l r β‖ ≤ (Y*(H*U))*L^(-P) at hsave
  rwa [heq] at hsave

end ArtinMatthews
