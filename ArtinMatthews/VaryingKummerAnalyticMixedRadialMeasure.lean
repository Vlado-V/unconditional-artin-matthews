module

public import ArtinMatthews.VaryingKummerAnalyticMixedLogCoordinates
public import ArtinMatthews.VaryingKummerAnalyticGammaIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Measure normalization for the actual mixed-signature radial coordinates. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedPlaceInsert (u : logSpace K) (v : ℝ) (w : InfinitePlace K) : ℝ :=
  if h : w = w₀ then v else u ⟨w, h⟩

theorem mixedPlaceInsert_measurable :
    Measurable (fun p : logSpace K × ℝ => mixedPlaceInsert K p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro w
  unfold mixedPlaceInsert
  split_ifs <;> fun_prop

theorem lintegral_mixedPlaceInsert (f : (InfinitePlace K → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ u : logSpace K, ∫⁻ v : ℝ, f (mixedPlaceInsert K u v)) = ∫⁻ x, f x := by
  let p : InfinitePlace K → Prop := fun w => w ≠ w₀
  let : Unique {w : InfinitePlace K // ¬p w} :=
    ⟨⟨w₀, by simp [p]⟩, fun w => Subtype.ext (by simpa [p] using w.2)⟩
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) p
  have he (u : logSpace K) (v : {w : InfinitePlace K // ¬p w} → ℝ) :
      e.symm (u,v) = mixedPlaceInsert K u (v default) := by
    ext w
    by_cases hw : w = w₀
    · subst w
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd,
        mixedPlaceInsert, p]
      exact congrArg v (Subsingleton.elim _ _)
    · simp [e, MeasurableEquiv.piEquivPiSubtypeProd, mixedPlaceInsert, p, hw]
  have h := (volume_preserving_piEquivPiSubtypeProd
    (fun _ : InfinitePlace K => ℝ) p).symm.lintegral_comp (f := f) hf
  change (∫⁻ x : (logSpace K) × ({w : InfinitePlace K // ¬p w} → ℝ),
    f (e.symm x)) = _ at h
  rw [Measure.volume_eq_prod] at h
  rw [lintegral_prod (fun x : (logSpace K) × ({w : InfinitePlace K // ¬p w} → ℝ) =>
    f (e.symm x)) (by fun_prop)] at h
  simp_rw [he] at h
  rw [← h]
  apply lintegral_congr
  intro u
  symm
  exact (volume_preserving_piUnique (fun _ : {w : InfinitePlace K // ¬p w} => ℝ)).lintegral_comp
    (f := fun v => f (mixedPlaceInsert K u v))
    (hf.comp (mixedPlaceInsert_measurable K |>.comp (measurable_const.prodMk measurable_id)))

end
end ArtinMatthews.VaryingKummerAnalytic
