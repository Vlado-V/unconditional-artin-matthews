module

public import OAI.NumberTheory.Ostmann.ZeroDensity.RectangleGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! Removing finitely many principal parts and the resulting exact rectangle
identity. The finite patching and rectangle calculation follow OpenAI's
SmoothFiniteRegularization / SmoothRectangleResidues, with the analytic
principal parts exposed and subsequently instantiated by genuine Dedekind data. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Complex Set Filter OAI.Ostmann
open scoped Topology BigOperators Classical Interval
noncomputable section

theorem finite_principal_parts_regularization (f C : ℂ → ℂ) (U : Set ℂ) (S : Finset ℂ)
    (hreg : ∀ z, ∃ R : ℂ → ℂ, AnalyticAt ℂ R z ∧
      (fun s => f s+C z/(s-z)) =ᶠ[𝓝[≠] z] R)
    (hf : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧
      ∀ z ∉ S, F z = f z+∑ w ∈ S,C w/(z-w) := by
  choose R hR heR using hreg
  let F : ℂ → ℂ := fun z => if z ∈ S then
    R z z+∑ w ∈ S.erase z,C w/(z-w) else f z+∑ w ∈ S,C w/(z-w)
  refine ⟨F,?_,fun z hz => by simp [F,hz]⟩
  intro z hzU
  by_cases hz : z ∈ S
  · have hsum : AnalyticAt ℂ (fun s => ∑ w ∈ S.erase z,C w/(s-w)) z := by
      apply (S.erase z).analyticAt_fun_sum
      intro w hw
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm)
    apply ((hR z).add hsum).congr
    have hav : ∀ᶠ s in 𝓝 z,s ∉ S.erase z :=
      (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    have he : ∀ᶠ s in 𝓝 z,s ≠ z → f s+C z/(s-z)=R z s := by
      simpa only [mem_compl_iff,mem_singleton_iff] using
        eventually_nhdsWithin_iff.mp (heR z)
    filter_upwards [hav,he] with s hs hres
    by_cases hsz : s=z
    · subst s
      simp [F,hz]
    · have hsS : s ∉ S := fun hsS => hs (Finset.mem_erase.mpr ⟨hsz,hsS⟩)
      simp only [F,ite_eq_right hsS]
      rw [← Finset.sum_erase_add _ _ hz]
      simp only [Pi.add_apply]
      rw [← hres hsz]
      ring
  · have hsum : AnalyticAt ℂ (fun s => ∑ w ∈ S,C w/(s-w)) z := by
      apply S.analyticAt_fun_sum
      intro w hw
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (fun he => hz (he ▸ hw)))
    apply ((hf z hzU hz).add hsum).congr
    have hav : ∀ᶠ s in 𝓝 z,s ∉ S := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hz
    filter_upwards [hav] with s hs
    simp [F,hs]

/-- The exact rectangle identity obtained from actual local principal parts. -/
theorem rectangle_principal_parts (f C : ℂ → ℂ) (a b c d : ℝ) (S : Finset ℂ)
    (hinside : ∀ z ∈ S,a<z.re ∧ z.re<b ∧ c<z.im ∧ z.im<d)
    (hreg : ∀ z,∃ R : ℂ → ℂ,AnalyticAt ℂ R z ∧
      (fun s => f s+C z/(s-z)) =ᶠ[𝓝[≠] z] R)
    (hf : ∀ z ∈ uIcc a b ×ℂ uIcc c d,z ∉ S → AnalyticAt ℂ f z) :
    rectangleBoundaryIntegral f a b c d =
      -(2*(Real.pi : ℂ)*I)*∑ z ∈ S,C z := by
  let g : ℂ → ℂ := fun s => ∑ z ∈ S,C z*(s-z)⁻¹
  obtain ⟨F,hF,heF⟩ := finite_principal_parts_regularization f C
    (uIcc a b ×ℂ uIcc c d) S hreg hf
  have hnot (w : ℂ) (hw : w ∈ contourRectangleBoundary a b c d) : w ∉ S := by
    intro hmem
    exact contourBoundary_ne_interior (hinside w hmem) hw rfl
  have hfi : RectangleIntegrable f a b c d :=
    rectangleIntegrable_of_continuousOn (fun w hw =>
      (hf w ⟨hw.1,hw.2.1⟩ (hnot w hw)).continuousAt.continuousWithinAt)
  have hterm (z : ℂ) (hz : z ∈ S) :
      RectangleIntegrable (fun s => C z*(s-z)⁻¹) a b c d :=
    (rectangleIntegrable_sub_inv (hinside z hz)).const_mul (C z)
  have hgi : RectangleIntegrable g a b c d := RectangleIntegrable.sum S hterm
  have hfg : rectangleBoundaryIntegral F a b c d =
      rectangleBoundaryIntegral (fun z => f z+g z) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro z hz
    simpa only [g,div_eq_mul_inv] using heF z (hnot z hz)
  have hgvalue : rectangleBoundaryIntegral g a b c d =
      (2*(Real.pi : ℂ)*I)*∑ z ∈ S,C z := by
    rw [show g=(fun s => ∑ z ∈ S,C z*(s-z)⁻¹) from rfl,
      rectangleBoundaryIntegral_sum S hterm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [rectangleBoundaryIntegral_const_mul,
      rectangleBoundaryIntegral_sub_inv z a b c d (hinside z hz).1
        (hinside z hz).2.1 (hinside z hz).2.2.1 (hinside z hz).2.2.2]
    ring
  have hzero := rectangleBoundaryIntegral_eq_zero hF
  rw [hfg,rectangleBoundaryIntegral_add hfi hgi,hgvalue] at hzero
  linear_combination hzero

end
end ArtinMatthews.VaryingKummerAnalytic
