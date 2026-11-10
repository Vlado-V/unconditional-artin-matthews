module

public import ArtinMatthews.SourceHyperbolicH1LocalTests
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Filter Set SourceHyperbolicGreen
open scoped Topology ContDiff Classical
noncomputable section

/-- A genuine smooth local plateau with compact support inside a chosen open chart. -/
theorem h1LocalPlateauCutoff_exists {ι : Type*} [Fintype ι]
    (U : Set (ProductSpace ι)) (hU : IsOpen U) (hUupper : U ⊆ productUpper ι)
    (x : ProductSpace ι) (hx : x ∈ U) :
    ∃ η : h1LocalTests U,
      ContDiff ℝ ∞ η.val.val ∧ (∀ y, ‖η.val.val y‖ ≤ 1) ∧
      ∃ V : Set (ProductSpace ι), IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, η.val.val y = 1 := by
  obtain ⟨g,hgs,hgc,hgd,hgr,hgx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds hx)
  have hgd' : ContDiff ℝ ∞ g := hgd
  let φ : ProductSpace ι → ℝ := fun y => Real.smoothTransition (4 * g y - 2)
  have hφd : ContDiff ℝ ∞ φ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul hgd').sub contDiff_const)
  have hφs : tsupport φ ⊆ tsupport g := by
    apply closure_mono
    intro y hy
    by_contra hgy
    have hzero : g y = 0 := by simpa only [Function.mem_support, not_not] using hgy
    apply hy
    exact Real.smoothTransition.zero_of_nonpos (by rw [hzero]; norm_num)
  have hφc : HasCompactSupport φ := hgc.of_isClosed_subset isClosed_closure hφs
  let η : h1LocalTests U := ⟨h1RealTest φ (hφd.of_le (by simp)) hφc
      (hφs.trans (hgs.trans hUupper)), by
    exact (tsupport_comp_subset (g := Complex.ofReal) rfl φ).trans (hφs.trans hgs)⟩
  refine ⟨η, ?_, ?_, {y | 3 / 4 < g y}, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp hφd
  · intro y
    change ‖(φ y : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · exact isOpen_Ioi.preimage hgd'.continuous
  · change 3 / 4 < g x
    rw [hgx]
    norm_num
  · intro y hy
    change (φ y : ℂ) = 1
    have he : φ y = 1 := Real.smoothTransition.one_of_one_le (by
      change 3 / 4 < g y at hy
      linarith)
    rw [he]
    norm_num

end
end ArtinMatthews
