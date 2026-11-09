module

public import ArtinMatthews.MarkedTypeIISharedMajorDecay
public import ArtinMatthews.MarkedTypeIISharedMajorSource
public import ArtinMatthews.MarkedMajorTypeIICoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! The shared-label correction in the original scalar Type II rectangles.
The centered coefficient, closed endpoint interval, fixed character and
dyadic cutoff occur exactly as in the unrestricted major sum. -/
namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

private theorem markedTypeIIRectangle_product_mem
    (H U : ℝ) (hH : 0 < H) (hU : 0 < U) (S : Finset ℕ) (l r : ℕ)
    (hS : ∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U) :
    ∀ v ∈ S×ˢIcc l r, v.1*v.2 ∈ Icc 1 ⌊4*(H*U)⌋₊ := by
  intro v hv
  obtain ⟨hm,hn⟩ := mem_product.mp hv
  obtain ⟨hml,hmr⟩ := hS _ hm
  obtain ⟨hnl,hnr⟩ := mem_Icc.mp hn
  have hnlo := hl.trans (Nat.cast_le.mpr hnl)
  have hnhi := (Nat.cast_le.mpr hnr).trans hr
  have hm₀ := Nat.cast_pos.mp (hH.trans_le hml)
  have hn₀ := Nat.cast_pos.mp (hU.trans_le hnlo)
  refine mem_Icc.mpr ⟨Nat.mul_pos hm₀ hn₀,(Nat.le_floor_iff (by positivity)).mpr ?_⟩
  rw [Nat.cast_mul]
  nlinarith [mul_le_mul hmr hnhi (Nat.cast_nonneg v.2) (show 0 ≤ 2*H by positivity)]

theorem markedTypeIIActualSharedMajor_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (R W δ C Qexp K D : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) (hδ : 0 < δ) (hK : 0 < K)
    (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ L : ℝ in atTop, ∀ H U Y modulation : ℝ, ∀ (S T : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ),
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ K*Real.exp L →
      (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      (∀ m ∈ T,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → 0 < Y →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      ∀ (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ), (∀ z v w,‖G z v w‖ ≤ 1) →
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      ‖markedTypeIIScalarMajorOn P
        ((markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter fun z => ¬ z.1.Coprime z.2)
        S T (Icc l r) η ψ (L^Qexp) Y
        (markedMajorCenteredCoefficient (Real.exp (L^(6/25:ℝ))) modulation) β G‖ ≤
          (Y*(H*U))*L^(-D) := by
  have hmain := Real.tendsto_exp_atTop.eventually
    (markedTypeIIScalarMajor_shared_log_saving e he η ψ R W 2 C Qexp (4*K) (D+1)
      hR hW (by positivity) hη hψ hsupp)
  filter_upwards [hmain,markedMajorTypeII_alpha_bound δ hδ,eventually_ge_atTop (4:ℝ)]
    with L hmain hα hL
  simp only [Real.log_exp] at hmain
  intro H U Y modulation S T l r β hH hU hX hS hT hl hr hY hβ G hG
  dsimp only
  let Z := ⌊4*(H*U)⌋₊
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hUp : 0 < U := (Real.exp_pos _).trans_le hU
  have hLp : 0 < L := by linarith
  have hZle : (Z:ℝ) ≤ 4*(H*U) := Nat.floor_le (by positivity)
  have hZ : (Z:ℝ) ≤ (4*K)*Real.exp L := by linarith
  let α := markedMajorCenteredCoefficient (Real.exp (L^(6/25:ℝ))) modulation
  have ha (m : ℕ) (hm : H ≤ (m:ℝ)) : ‖α m‖ ≤ L^(2:ℝ) := by
    simpa only [Real.rpow_ofNat] using hα m modulation (hH.trans hm)
  have h := hmain Y hY S T (Icc l r) Z hZ
    (markedTypeIIRectangle_product_mem H U hHp hUp S l r hS hl hr)
    (markedTypeIIRectangle_product_mem H U hHp hUp T l r hT hl hr)
    α β (fun m hm => ha m (hS m hm).1) (fun m hm => ha m (hT m hm).1) hβ G hG
  have hsave : 4*L^(-(D+1)) ≤ L^(-D) := by
    calc
      _ ≤ L*L^(-(D+1)) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLp.le _)
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one L]
        rw [← Real.rpow_add hLp]
        congr 1
        ring
  apply h.trans
  calc
    _ ≤ Y*(4*(H*U))*L^(-(D+1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZle hY.le) (Real.rpow_nonneg hLp.le _)
    _ = (Y*(H*U))*(4*L^(-(D+1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

theorem markedMajorFixedIntervalPairSum_coprime_error_log_saving
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (R W δ C Qexp K D : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) (hδ : 0 < δ) (hK : 0 < K)
    (hη : ∀ u,‖η u‖ ≤ 1) (hηsupp : Function.support η ⊆ Set.Icc 1 4)
    (hψ : ∀ u,‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ L : ℝ in atTop, ∀ H U Y modulation : ℝ, ∀ (S T : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ),
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ K*Real.exp L →
      (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      (∀ m ∈ T,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → 0 < Y →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      let Wrough := Real.exp (L^(6/25:ℝ))
      ‖markedMajorFixedIntervalPairSum P ξ η ψ (L^Qexp) Y Wrough modulation S T l r β -
        markedMajorFixedDyadPairSum P η ψ (L^Qexp) Y Wrough modulation S T l r β ξ
          (fun z => z.1.Coprime z.2)‖ ≤ (Y*(H*U))*L^(-D) := by
  filter_upwards [markedTypeIIActualSharedMajor_log_saving e he η ψ R W δ C Qexp K D
    hR hW hδ hK hη hψ hsupp] with L h
  intro H U Y modulation S T l r β hH hU hX hS hT hl hr hY hβ
  dsimp only
  rw [markedMajorFixedIntervalPairSum_sub_coprime _ _ _ _ _ _ _ _ _ _ _ _ ξ hY hηsupp]
  let G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ :=
    fun _ v w => ξ (v.1*v.2:ℕ)*conj (ξ (w.1*w.2:ℕ))
  have hG (z v w : ℕ×ℕ) : ‖G z v w‖ ≤ 1 := by
    dsimp only [G]
    rw [norm_mul,Complex.norm_conj]
    simpa only [one_mul] using mul_le_mul (ξ.norm_le_one (v.1*v.2:ℕ))
      (ξ.norm_le_one (w.1*w.2:ℕ)) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have ht := h H U Y modulation S T l r β hH hU hX hS hT hl hr hY hβ G hG
  apply (le_of_eq ?_).trans ht
  unfold markedMajorFixedDyadPairSum
  apply congrArg (fun t : ℂ => ‖t‖)
  apply congrArg (fun pairs : Finset (ℕ×ℕ) => markedTypeIIScalarMajorOn
    (fun j => markedLogPowerBand (e j) (Real.exp L)) pairs S T (Icc l r) η ψ (L^Qexp) Y
    (markedMajorCenteredCoefficient (Real.exp (L^(6/25:ℝ))) modulation) β G)
  ext z
  simp only [mem_filter]

theorem markedMajorIntervalPairSum_coprime_error_log_saving
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (R W δ C Qexp K D : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) (hδ : 0 < δ) (hK : 0 < K)
    (hη : ∀ u,‖η u‖ ≤ 1) (hηsupp : Function.support η ⊆ Set.Icc 1 4)
    (hψ : ∀ u,‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ L : ℝ in atTop, ∀ H U Y modulation : ℝ, ∀ (S T : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ),
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ K*Real.exp L →
      (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      (∀ m ∈ T,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → 0 < Y →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      let Wrough := Real.exp (L^(6/25:ℝ))
      ‖markedMajorIntervalPairSum P η ψ (L^Qexp) Y Wrough modulation S T l r β -
        markedMajorDyadPairSum P η ψ (L^Qexp) Y Wrough modulation S T l r β
          (fun z => z.1.Coprime z.2)‖ ≤ (Y*(H*U))*L^(-D) := by
  filter_upwards [markedTypeIIActualSharedMajor_log_saving e he η ψ R W δ C Qexp K D
    hR hW hδ hK hη hψ hsupp] with L h
  intro H U Y modulation S T l r β hH hU hX hS hT hl hr hY hβ
  dsimp only
  rw [markedMajorIntervalPairSum_sub_coprime _ _ _ _ _ _ _ _ _ _ _ _ hY hηsupp]
  let G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ := fun _ _ _ => 1
  have ht := h H U Y modulation S T l r β hH hU hX hS hT hl hr hY hβ
    G (fun _ _ _ => by simp [G])
  apply (le_of_eq ?_).trans ht
  unfold markedMajorDyadPairSum
  apply congrArg (fun t : ℂ => ‖t‖)
  apply congrArg (fun pairs : Finset (ℕ×ℕ) => markedTypeIIScalarMajorOn
    (fun j => markedLogPowerBand (e j) (Real.exp L)) pairs S T (Icc l r) η ψ (L^Qexp) Y
    (markedMajorCenteredCoefficient (Real.exp (L^(6/25:ℝ))) modulation) β G)
  ext z
  simp only [mem_filter]

end
end ArtinMatthews
