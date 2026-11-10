module

public import ArtinMatthews.SourceAdelicStandardHaar
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Algebra.RestrictedProduct.Units
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Tactic.Monotonicity.Lemmas


set_option backward.privateInPublic true
@[expose] public section

/-! A unit pivot for a determinant-one adelic matrix, using integral
zero-or-one shear parameters at every finite place. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Filter
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

theorem sourceNonarchShearPivot_norm {k : Type*} [NormedField k] [IsUltrametricDist k]
    (a c : k) :
    ‖a + (if ‖a‖ < ‖c‖ then (1 : k) else 0) * c‖ = max ‖a‖ ‖c‖ := by
  by_cases h : ‖a‖ < ‖c‖
  · simpa only [ite_eq_left h, one_mul] using
      (IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne)
  · simp only [ite_eq_right h, zero_mul, add_zero, max_eq_left (le_of_not_gt h)]

theorem sourceNonarchColumn_max_one {k : Type*} [NormedField k] [IsUltrametricDist k]
    (a b c d : k) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (hdet : a * d - b * c = 1) : max ‖a‖ ‖c‖ = 1 := by
  apply le_antisymm (max_le ha hc)
  calc
    1 = ‖a * d - b * c‖ := by rw [hdet, norm_one]
    _ ≤ max ‖a * d‖ ‖b * c‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        (IsUltrametricDist.norm_add_le_max (a * d) (-(b * c)))
    _ ≤ max ‖a‖ ‖c‖ := by
      rw [norm_mul, norm_mul]
      exact max_le_max (mul_le_of_le_one_right (norm_nonneg a) hd)
        (mul_le_of_le_one_left (norm_nonneg c) hb)

variable (F : Type) [Field F] [NumberField F]

def sourceAdelicPivotShear (g : SL(2, 𝔸[F])) : 𝔸[F] :=
  (fun v => if (g 0 0).1 v = 0 then 1 else 0,
    ⟨fun P => if ‖(g 0 0).2 P‖ < ‖(g 1 0).2 P‖ then 1 else 0,
      Filter.Eventually.of_forall (fun P => by
        change (if ‖(g 0 0).2 P‖ < ‖(g 1 0).2 P‖ then (1 : P.adicCompletion F) else 0) ∈
          P.adicCompletionIntegers F
        split_ifs <;> simp)⟩)

theorem sourceAdelicPivotShear_isUnit (g : SL(2, 𝔸[F])) :
    IsUnit (g 0 0 + sourceAdelicPivotShear F g * g 1 0) := by
  let u := g 0 0 + sourceAdelicPivotShear F g * g 1 0
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have harch (v : InfinitePlace F) : u.1 v ≠ 0 := by
    have hd := congrArg (fun x : 𝔸[F] => x.1 v) hdet
    change (g 0 0).1 v * (g 1 1).1 v - (g 0 1).1 v * (g 1 0).1 v = 1 at hd
    change (g 0 0).1 v + (if (g 0 0).1 v = 0 then 1 else 0) * (g 1 0).1 v ≠ 0
    by_cases ha : (g 0 0).1 v = 0
    · have hc : (g 1 0).1 v ≠ 0 := by
        intro hc
        simp only [ha, hc, zero_mul, mul_zero, sub_self] at hd
        exact zero_ne_one hd
      simpa only [ha, ite_true, one_mul, zero_add] using hc
    · simpa only [ite_eq_right ha, zero_mul, add_zero] using ha
  have harchUnit : IsUnit u.1 := by
    refine ⟨⟨u.1, fun v => (u.1 v)⁻¹, ?_, ?_⟩, rfl⟩
    · funext v
      exact mul_inv_cancel₀ (harch v)
    · funext v
      exact inv_mul_cancel₀ (harch v)
  have hfinite (P : HeightOneSpectrum (𝓞 F)) : IsUnit (u.2 P) := by
    have hd := congrArg (fun x : 𝔸[F] => x.2 P) hdet
    change (g 0 0).2 P * (g 1 1).2 P - (g 0 1).2 P * (g 1 0).2 P = 1 at hd
    have hmax : 0 < max ‖(g 0 0).2 P‖ ‖(g 1 0).2 P‖ := by
      by_cases ha : (g 0 0).2 P = 0
      · have hc : (g 1 0).2 P ≠ 0 := by
          intro hc
          simp only [ha, hc, zero_mul, mul_zero, sub_self] at hd
          exact zero_ne_one hd
        exact lt_max_of_lt_right (norm_pos_iff.mpr hc)
      · exact lt_max_of_lt_left (norm_pos_iff.mpr ha)
    apply isUnit_iff_ne_zero.mpr
    apply norm_pos_iff.mp
    change 0 < ‖(g 0 0).2 P +
      (if ‖(g 0 0).2 P‖ < ‖(g 1 0).2 P‖ then (1 : P.adicCompletion F) else 0) * (g 1 0).2 P‖
    rwa [sourceNonarchShearPivot_norm]
  have heventual : ∀ᶠ P in Filter.cofinite,
      ∃ h : u.2 P ∈ P.adicCompletionIntegers F,
        IsUnit (⟨u.2 P, h⟩ : P.adicCompletionIntegers F) := by
    filter_upwards [(g 0 0).2.property, (g 0 1).2.property,
      (g 1 0).2.property, (g 1 1).2.property] with P ha hb hc hd
    have hdetP := congrArg (fun x : 𝔸[F] => x.2 P) hdet
    change (g 0 0).2 P * (g 1 1).2 P - (g 0 1).2 P * (g 1 0).2 P = 1 at hdetP
    have hn : ‖u.2 P‖ = 1 := by
      change ‖(g 0 0).2 P +
        (if ‖(g 0 0).2 P‖ < ‖(g 1 0).2 P‖ then (1 : P.adicCompletion F) else 0) * (g 1 0).2 P‖ = 1
      rw [sourceNonarchShearPivot_norm]
      exact sourceNonarchColumn_max_one _ _ _ _
        (Valued.toNormedField.norm_le_one_iff.mpr ha)
        (Valued.toNormedField.norm_le_one_iff.mpr hb)
        (Valued.toNormedField.norm_le_one_iff.mpr hc)
        (Valued.toNormedField.norm_le_one_iff.mpr hd) hdetP
    have hu : u.2 P ∈ P.adicCompletionIntegers F :=
      Valued.toNormedField.norm_le_one_iff.mp hn.le
    have hi : (u.2 P)⁻¹ ∈ P.adicCompletionIntegers F := by
      change Valued.v ((u.2 P)⁻¹) ≤ 1
      apply Valued.toNormedField.norm_le_one_iff.mp
      simp only [norm_inv, hn, inv_one, le_refl]
    have hne : u.2 P ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
    refine ⟨hu, ⟨⟨⟨u.2 P, hu⟩, ⟨(u.2 P)⁻¹, hi⟩, ?_, ?_⟩, rfl⟩⟩
    · apply Subtype.ext
      exact mul_inv_cancel₀ hne
    · apply Subtype.ext
      exact inv_mul_cancel₀ hne
  have hfiniteUnit : IsUnit u.2 := RestrictedProduct.isUnit_of_eventually_isUnit hfinite heventual
  obtain ⟨a, ha⟩ := harchUnit
  obtain ⟨b, hb⟩ := hfiniteUnit
  let w : (𝔸[F])ˣ := ⟨((a : InfiniteAdeleRing F), (b : 𝔸ᶠ[F])),
    ((a⁻¹ : (InfiniteAdeleRing F)ˣ), (b⁻¹ : (𝔸ᶠ[F])ˣ)),
    by
      apply Prod.ext
      · exact a.val_inv
      · exact b.val_inv,
    by
      apply Prod.ext
      · exact a.inv_val
      · exact b.inv_val⟩
  exact ⟨w, Prod.ext ha hb⟩

end
end ArtinMatthews
