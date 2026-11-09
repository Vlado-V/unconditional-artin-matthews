module

public import ArtinMatthews.MarkedPhysicalScalarMinorBounded
public import ArtinMatthews.MarkedTypeIIActualDeterminant


set_option backward.privateInPublic true
@[expose] public section

/-! The exact occupied determinant and the original full scalar major form
for arbitrary bounded rough coefficients. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J]

/-- The full major form has independent selected labels, including common selected primes. -/
def markedTypeIIScalarFullMajor (P : J → Finset ℕ) (S T : Finset ℕ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ) (α β : ℕ → ℂ) : ℂ :=
  markedTypeIIScalarMajorOn P ((markedMajorLabelSet P).product (markedMajorLabelSet P))
    S S T η ψ Q Y α β (fun _ _ _ => 1)

/-- The exact major contribution of the shared selected labels on the occupied dyad. -/
def markedTypeIIScalarSharedMajor (P : J → Finset ℕ) (S T : Finset ℕ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ) (α β : ℕ → ℂ) : ℂ :=
  markedTypeIIScalarMajorOn P
    (((markedTypeIIDyadLabels P Y).product (markedTypeIIDyadLabels P Y)).filter fun z => ¬ z.1.Coprime z.2)
    S S T η ψ Q Y α β (fun _ _ _ => 1)

theorem markedTypeIIScalarFullMajor_eq_coprime_add_shared
    (P : J → Finset ℕ) (S T : Finset ℕ) (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y : ℝ) (α β : ℕ → ℂ) (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4) :
    markedTypeIIScalarFullMajor P S T η ψ Q Y α β =
      markedPhysicalCoprimeScalarDetectorSum P S T η Y (markedRawEdgeMajorDetector ψ Q Y) α β +
        markedTypeIIScalarSharedMajor P S T η ψ Q Y α β := by
  unfold markedTypeIIScalarFullMajor markedTypeIIScalarSharedMajor
  rw [markedTypeIIScalarMajorOn_split P _ (fun z => z.1.Coprime z.2),
    markedPhysicalCoprimeScalarDetectorSum_major_on]
  have hcp : markedPhysicalCoprimeLabelPairs P =
      ((markedMajorLabelSet P).product (markedMajorLabelSet P)).filter (fun z => z.1.Coprime z.2) := rfl
  rw [hcp]
  congr 1
  · apply congrArg (fun L : Finset (ℕ×ℕ) =>
      markedTypeIIScalarMajorOn P L S S T η ψ Q Y α β (fun _ _ _ => 1))
    ext z
    simp only [mem_filter]
  · have h := markedTypeIIScalarMajorOn_filtered_dyad P (fun z => ¬ z.1.Coprime z.2)
      S S T η ψ Q Y α β (fun _ _ _ => 1) hY hη
    refine Eq.trans ?_ (Eq.trans h ?_)
    all_goals
      apply congrArg (fun L : Finset (ℕ×ℕ) =>
        markedTypeIIScalarMajorOn P L S S T η ψ Q Y α β (fun _ _ _ => 1))
      ext z
      simp only [Finset.product_eq_sprod, mem_filter, mem_product]

theorem markedTypeII_occupied_scalar_determinant_sub_major
    (P : J → Finset ℕ) (S T : Finset ℕ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y : ℝ) (α β : ℕ → ℂ) (hY : 0 < Y)
    (hψone : ∀ t ∈ Set.Icc (-4:ℝ) 4,ψ t=1) :
    markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y S T)
        (markedTypeIILabelEndpointCoefficient P Y α β) -
      markedTypeIIScalarFullMajor P S T markedTypeIILabelCutoff ψ Q Y α β =
        markedPhysicalCoprimeScalarDetectorSum P S T markedTypeIILabelCutoff Y
          (markedBanEdgeKernel ψ Q Y) α β -
        markedTypeIIScalarSharedMajor P S T markedTypeIILabelCutoff ψ Q Y α β := by
  rw [markedTypeII_occupied_determinant_eq_coprime_delta P Y ψ S T α β hψone,
    markedTypeIIScalarFullMajor_eq_coprime_add_shared P S T _ ψ Q Y α β hY markedTypeIILabelCutoff_support,
    markedPhysicalCoprimeScalarDetectorSum_minor_split]
  ring

/-- The original determinant is approximated by its original full major form
at the actual occupied-dyad scale, uniformly over both rough coefficient functions. -/
theorem markedTypeII_actual_scalar_determinant_comparison
    [DecidableEq J] [Nonempty J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (δ B Cα Cβ D Kbox : ℝ)
    (hδ : 0 < δ) (hB : 8 ≤ B) (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hD : 0 ≤ D) (hKbox : 0 < Kbox)
    (hdepth : 100*(5*(D+2*(Cα+Cβ)+8)+36)<(Fintype.card J:ℝ)) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn : ℝ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn → Hm*Hn ≤ Kbox*x →
      ∀ (S T : Finset ℕ) (α β : ℕ → ℂ),
      (∀ m∈S,Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm) → (∀ n∈T,Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn) →
      (∀ m∈S,‖α m‖ ≤ (Real.log x)^Cα) → (∀ n∈T,‖β n‖ ≤ (Real.log x)^Cβ) →
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      (∀ m∈S,α m ≠ 0 → MarkedPhysicalRoughAt W m) →
      (∀ n∈T,β n ≠ 0 → MarkedPhysicalRoughAt W n) →
      let P := fun j => markedLogPowerBand (e j) x
      let Q := (Real.log x)^(D+2*(Cα+Cβ)+17)
      ‖markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y S T)
          (markedTypeIILabelEndpointCoefficient P Y α β) -
        markedTypeIIScalarFullMajor P S T markedTypeIILabelCutoff markedTypeIIDeterminantCutoff Q Y α β‖ ≤
        (Y*(Hm*Hn))*(Real.log x)^(-D) := by
  let A := D+1
  let Qexp := A+2*(Cα+Cβ)+16
  have hdepth' : 100*(5*(A+2*(Cα+Cβ)+7)+36)<(Fintype.card J:ℝ) := by
    dsimp only [A]
    linarith
  have hQexp : Qexp=D+2*(Cα+Cβ)+17 := by dsimp only [Qexp,A]; ring
  filter_upwards [markedPhysicalTypeIICoprimeMinor_bounded_log_saving e he heUpper hinj hδ
      markedTypeIIDeterminantCutoff markedTypeIILabelCutoff 5 B 1 Cα Cβ A Kbox
      (by norm_num) hB (by norm_num) hCα hCβ (by dsimp only [A]; positivity) hKbox hdepth'
      markedTypeIILabelCutoff_support markedTypeIILabelCutoff_norm_le_one
      markedTypeIIDeterminantCutoff_norm_le_one markedTypeIIDeterminantCutoff_support,
    markedTypeIIScalarMajor_shared_log_saving e he markedTypeIILabelCutoff markedTypeIIDeterminantCutoff
      5 1 Cα Cβ Qexp (4*Kbox) (A+1) (by norm_num) (by norm_num) (by positivity)
      markedTypeIILabelCutoff_norm_le_one markedTypeIIDeterminantCutoff_norm_le_one
      markedTypeIIDeterminantCutoff_support,
    eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))]
    with x hminor hshared hx hL4
  intro Y Hm Hn hYlo hYhi hHm hHn hX S T α β hS hT hα hβ
  dsimp only
  intro hrα hrβ
  rw [← hQexp]
  let L := Real.log x
  let P := fun j => markedLogPowerBand (e j) x
  let Q := L^Qexp
  let X := Y*(Hm*Hn)
  have hY := (Real.exp_pos _).trans_le hYlo
  have hxδ := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) δ).le
  have hX₀ : 0 ≤ X := mul_nonneg hY.le (mul_nonneg (hxδ.trans hHm) (hxδ.trans hHn))
  have hL : 1 ≤ L := (by norm_num : (1:ℝ)≤4).trans hL4
  rw [markedTypeII_occupied_scalar_determinant_sub_major P S T markedTypeIIDeterminantCutoff Q Y α β hY
    markedTypeIIDeterminantCutoff_one]
  have hm := hminor Y Hm Hn hYlo hYhi hHm hHn hX S T α β hS hT hα hβ hrα hrβ
  have hz := markedPhysicalPadCofactor_height hx hδ.le hHm hHn hX S T hS hT
  let Z := ⌊4*(Hm*Hn)⌋₊
  have hb := hshared Y hY S S T Z hz.2.1 hz.2.2.2 hz.2.2.2 α β hα hα hβ
    (fun _ _ _ => 1) (fun _ _ _ => by rw [norm_one])
  have hsh : ‖markedTypeIIScalarSharedMajor P S T markedTypeIILabelCutoff markedTypeIIDeterminantCutoff
      Q Y α β‖ ≤ X*L^(-A) := by
    have hpow : 4*L^(-(A+1)) ≤ L^(-A) := by
      simpa only [Nat.cast_one,mul_one] using
        (markedPhysicalSourceErrorScale (N:=1) (G:=A) hL hL4 (by norm_num))
    apply hb.trans
    calc
      _ ≤ Y*(4*(Hm*Hn))*L^(-(A+1)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hz.2.2.1 hY.le) (Real.rpow_nonneg (zero_le_one.trans hL) _)
      _ = X*(4*L^(-(A+1))) := by dsimp only [X]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hX₀
  have hroom : 2*L^(-A) ≤ L^(-D) := by
    simpa only [Nat.cast_one,mul_one,A] using
      (markedPhysicalSourceErrorScale (N:=1) (G:=D) hL ((by norm_num : (2:ℝ)≤4).trans hL4) (by norm_num))
  calc
    _ ≤ _ + _ := norm_sub_le _ _
    _ ≤ X*L^(-A)+X*L^(-A) := add_le_add hm hsh
    _ = X*(2*L^(-A)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hroom hX₀

end
end ArtinMatthews
