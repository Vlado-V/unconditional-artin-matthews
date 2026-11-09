module

public import ArtinMatthews.MarkedTypeIICommonQuotientActual
public import ArtinMatthews.MarkedTypeIIDyadCauchy


set_option backward.privateInPublic true
@[expose] public section

/-! The proved common-quotient error on the occupied dyad of the actual
Cauchy inequality. The same factor sets, quotient range, and damping
remain in the original selected-label sum. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators Topology ComplexConjugate

variable {J : Type*} [Fintype J]

theorem markedTypeII_occupied_collision_eq_dyad (P : J → Finset ℕ) (Y : ℝ)
    (M N H : Finset ℕ) (α β : ℕ → ℂ) :
    markedTypeIICollisionSum (markedTypeIIOccupiedLabelEndpoints P Y M N) H
        (markedTypeIILabelEndpointCoefficient P Y α β) =
      markedTypeIICollisionSum (giantMarkedEndpoints P M N) H
        (markedTypeIIDyadCoefficient P markedTypeIILabelCutoff Y α β) := by
  classical
  let c := markedTypeIIDyadCoefficient P markedTypeIILabelCutoff Y α β
  let E := giantMarkedEndpoints P M N
  let good (a : MarkedTypeIIEndpoint) := markedTypeIILabelCutoff ((a.label:ℝ)/Y) ≠ 0
  have hz (a : MarkedTypeIIEndpoint) (ha : ¬ good a) : c a = 0 := by
    have h : markedTypeIILabelCutoff ((a.label:ℝ)/Y) = 0 := not_not.mp ha
    simp only [c,markedTypeIIDyadCoefficient,markedTypeIIEndpointCoeff,h,mul_zero,zero_mul]
  change markedTypeIICollisionSum (E.filter good) H c = markedTypeIICollisionSum E H c
  unfold markedTypeIICollisionSum
  rw [sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : good a
  · rw [ite_eq_left ha,sum_filter]
    apply sum_congr rfl
    intro b _
    by_cases hb : good b
    · exact ite_eq_left hb
    · rw [ite_eq_right hb,hz b hb]
      split_ifs <;> simp
  · rw [ite_eq_right ha]
    symm
    apply sum_eq_zero
    intro b _
    rw [hz a ha]
    split_ifs <;> simp

theorem markedTypeII_occupied_dyad_collision_log_saving
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (δ Cbox Cα Cβ G : ℝ) (hδ : 0 < δ) (hbox : 0 < Cbox) :
    ∀ᶠ x : ℝ in atTop, ∀ Hm Hn Y : ℝ, x^δ ≤ Hm → x^δ ≤ Hn → Hm*Hn ≤ Cbox*x → 0 < Y →
      ∀ M N H : Finset ℕ, (∀ m ∈ M, 0 < m ∧ (m:ℝ) ≤ 2*Hm) →
      (∀ n ∈ N, 0 < n ∧ (n:ℝ) ≤ 2*Hn) →
      ∀ α β : ℕ → ℂ, (∀ m ∈ M, ‖α m‖ ≤ (Real.log x)^Cα) →
      (∀ n ∈ N, ‖β n‖ ≤ (Real.log x)^Cβ) →
      let P := fun j => markedLogPowerBand (e j) x
      ‖markedTypeIICollisionSum (markedTypeIIOccupiedLabelEndpoints P Y M N) H
        (markedTypeIILabelEndpointCoefficient P Y α β)‖ ≤ Y*(Hm*Hn)*(Real.log x)^(-G) := by
  filter_upwards [markedTypeII_dyad_collision_log_saving e he heUpper δ (4*Cbox) Cα Cβ (G+1)
    hδ (by positivity) markedTypeIILabelCutoff markedTypeIILabelCutoff_norm_le_one
    markedTypeIILabelCutoff_support, eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))] with x hcollision hx hlog
  intro Hm Hn Y hHm hHn hprod hY M N H hM hN α β hα hβ
  dsimp only
  let X := Hm*Hn
  let Z := ⌊4*X⌋₊
  let L := Real.log x
  let P := fun j => markedLogPowerBand (e j) x
  have hL : 0 < L := (by norm_num : (0:ℝ) < 4).trans_le hlog
  have hxδ : 1 ≤ x^δ := Real.one_le_rpow hx hδ.le
  have hHm₀ : 0 ≤ Hm := zero_le_one.trans (hxδ.trans hHm)
  have hXlo : x^δ ≤ X := by
    calc
      _ ≤ Hm := hHm
      _ = Hm*1 := (mul_one _).symm
      _ ≤ X := mul_le_mul_of_nonneg_left (hxδ.trans hHn) hHm₀
  have hX : 0 ≤ X := zero_le_one.trans (hxδ.trans hXlo)
  have hZfloor : 4*X-1 < (Z:ℝ) := Nat.sub_one_lt_floor _
  have hZlo : x^δ ≤ (Z:ℝ) := by linarith
  have hZhi : (Z:ℝ) ≤ 4*X := Nat.floor_le (by positivity)
  have hZx : (Z:ℝ) ≤ (4*Cbox)*x := by
    calc
      _ ≤ 4*X := hZhi
      _ ≤ 4*(Cbox*x) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = _ := by ring
  have hMN : ∀ v ∈ M×ˢN,v.1*v.2 ≤ Z := by
    intro v hv
    obtain ⟨hm,hn⟩ := mem_product.mp hv
    apply (Nat.le_floor_iff (by positivity : 0 ≤ 4*X)).mpr
    rw [Nat.cast_mul]
    calc
      _ ≤ (2*Hm)*(2*Hn) := mul_le_mul (hM _ hm).2 (hN _ hn).2 (Nat.cast_nonneg _) (by positivity)
      _ = _ := by dsimp only [X]; ring
  have hpow : L^(-(G+1)) = L^(-G)*L⁻¹ := by
    rw [show -(G+1) = -G+(-1) by ring,Real.rpow_add hL,Real.rpow_neg_one]
  have hfour : 4*L⁻¹ ≤ 1 := by
    simpa only [div_eq_mul_inv] using (div_le_one hL).mpr hlog
  rw [markedTypeII_occupied_collision_eq_dyad P Y M N H α β]
  calc
    _ ≤ Y*(Z:ℝ)*L^(-(G+1)) := hcollision Y hY M N H Z hZlo hZx hMN α β hα hβ
    _ ≤ Y*(4*X)*L^(-(G+1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZhi hY.le) (Real.rpow_nonneg hL.le _)
    _ = Y*X*(4*L⁻¹)*L^(-G) := by rw [hpow]; ring
    _ ≤ Y*X*1*L^(-G) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfour (mul_nonneg hY.le hX)) (Real.rpow_nonneg hL.le _)
    _ = _ := by rw [mul_one]

theorem markedTypeIISelectedLabelDyadSum_le_of_determinant_collision
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (M N : Finset ℕ)
    (Hm Hn Y L G : ℝ) (hHm : 0 ≤ Hm) (hY : 0 < Y) (hXY : Y ≤ Hm*Hn) (hL : 10 ≤ L)
    (hM : ∀ m ∈ M, 0 < m ∧ (m:ℝ) ≤ 2*Hm) (hN : ∀ n ∈ N, 0 < n ∧ (n:ℝ) ≤ 2*Hn)
    (α β F : ℕ → ℂ) (hF : ∀ h, ‖F h‖ ≤ 1) :
    let E := markedTypeIIOccupiedLabelEndpoints P Y M N
    let B := markedTypeIIDyadQuotientRange Hm Hn Y
    let c := markedTypeIILabelEndpointCoefficient P Y α β
    ‖markedTypeIIDeterminantSum E c‖ ≤ Y*(Hm*Hn)*L^(-(2*G+1)) →
    ‖markedTypeIICollisionSum E (range B) c‖ ≤ Y*(Hm*Hn)*L^(-(2*G+1)) →
    ‖markedTypeIISelectedLabelDyadSum P Y M N α β F‖ ≤ (Hm*Hn)*L^(-G) := by
  let E := markedTypeIIOccupiedLabelEndpoints P Y M N
  let B := markedTypeIIDyadQuotientRange Hm Hn Y
  let c := markedTypeIILabelEndpointCoefficient P Y α β
  let X := Hm*Hn
  let D := markedTypeIIDeterminantSum E c
  let C := markedTypeIICollisionSum E (range B) c
  let W := Y*X*L^(-(2*G+1))
  change ‖D‖ ≤ W → ‖C‖ ≤ W → _
  intro hD hC
  have hX : 0 ≤ X := hY.le.trans hXY
  have hLp : 0 < L := (by norm_num : (0:ℝ) < 10).trans_le hL
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg hY.le hX) (Real.rpow_nonneg hLp.le _)
  have hR : (D+C).re ≤ 2*W := by
    rw [Complex.add_re]
    linarith [Complex.re_le_norm D,Complex.re_le_norm C]
  have hpow : L^(-(2*G+1)) = (L^(-G))^2*L⁻¹ := by
    rw [show -(2*G+1) = (-G)*((2:ℕ):ℝ)+(-1) by push_cast; ring,
      Real.rpow_add hLp,Real.rpow_mul_natCast hLp.le,Real.rpow_neg_one]
  have hten : 10*L⁻¹ ≤ 1 := by
    simpa only [div_eq_mul_inv] using (div_le_one hLp).mpr hL
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hX (Real.rpow_nonneg hLp.le _))).mp
  calc
    _ ≤ (B:ℝ)*(D+C).re :=
      markedTypeIISelectedLabelDyadSum_cauchy P hP M N Hm Hn Y hHm hY hM hN α β F hF
    _ ≤ (B:ℝ)*(2*W) := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
    _ ≤ (5*X/Y)*(2*W) := mul_le_mul_of_nonneg_right
      (markedTypeIIDyadQuotientRange_le hY hXY) (mul_nonneg (by norm_num) hW)
    _ = (10*L⁻¹)*(X*L^(-G))^2 := by
      dsimp only [W]
      rw [hpow]
      field_simp [hY.ne']
      ring
    _ ≤ 1*(X*L^(-G))^2 := mul_le_mul_of_nonneg_right hten (sq_nonneg _)
    _ = _ := one_mul _

theorem markedTypeIISelectedLabelDyadSum_log_saving_of_determinant
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (δ Cbox Cα Cβ G : ℝ) (hδ : 0 < δ) (hbox : 0 < Cbox) :
    ∀ᶠ x : ℝ in atTop, ∀ Hm Hn Y : ℝ, x^δ ≤ Hm → x^δ ≤ Hn → Hm*Hn ≤ Cbox*x →
      0 < Y → Y ≤ Hm*Hn →
      ∀ M N : Finset ℕ, (∀ m ∈ M, 0 < m ∧ (m:ℝ) ≤ 2*Hm) →
      (∀ n ∈ N, 0 < n ∧ (n:ℝ) ≤ 2*Hn) →
      ∀ α β F : ℕ → ℂ, (∀ m ∈ M, ‖α m‖ ≤ (Real.log x)^Cα) →
      (∀ n ∈ N, ‖β n‖ ≤ (Real.log x)^Cβ) → (∀ h, ‖F h‖ ≤ 1) →
      let P := fun j => markedLogPowerBand (e j) x
      let E := markedTypeIIOccupiedLabelEndpoints P Y M N
      let c := markedTypeIILabelEndpointCoefficient P Y α β
      ‖markedTypeIIDeterminantSum E c‖ ≤ Y*(Hm*Hn)*(Real.log x)^(-(2*G+1)) →
      ‖markedTypeIISelectedLabelDyadSum P Y M N α β F‖ ≤ (Hm*Hn)*(Real.log x)^(-G) := by
  filter_upwards [markedTypeII_occupied_dyad_collision_log_saving e he heUpper δ Cbox Cα Cβ
    (2*G+1) hδ hbox, eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10:ℝ))] with x hcollision hx hlog
  intro Hm Hn Y hHm hHn hX hY hXY M N hM hN α β F hα hβ hF
  dsimp only
  let P := fun j => markedLogPowerBand (e j) x
  let H := range (markedTypeIIDyadQuotientRange Hm Hn Y)
  intro hD
  have hHm₀ : 0 ≤ Hm := (Real.rpow_nonneg (zero_le_one.trans hx) δ).trans hHm
  exact markedTypeIISelectedLabelDyadSum_le_of_determinant_collision P
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    M N Hm Hn Y (Real.log x) G hHm₀ hY hXY hlog hM hN α β F hF hD
    (hcollision Hm Hn Y hHm hHn hX hY M N H hM hN α β hα hβ)

end
end ArtinMatthews
