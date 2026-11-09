module

public import ArtinMatthews.UnitTorusFourierTail
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Compactness of bounded weak-H1 energy on the actual normalized torus. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus Set
open scoped BigOperators Topology ENNReal
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (ι : Type*) [Fintype ι]

def unitTorusFourierHull (S : Finset (ι → ℤ)) (R : ℝ) : Set (UnitTorusL2 ι) :=
  (fun a : S → ℂ => ∑ n : S, a n • mFourierBasis (n : ι → ℤ)) ''
    {a | ∀ n, ‖a n‖ ≤ R}

theorem unitTorusFourierHull_isCompact (S : Finset (ι → ℤ)) (R : ℝ) :
    IsCompact (unitTorusFourierHull ι S R) := by
  have hc : IsCompact {a : S → ℂ | ∀ n, ‖a n‖ ≤ R} := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      isCompact_pi_infinite (fun _ : S => isCompact_closedBall (0 : ℂ) R)
  exact hc.image (continuous_finsetSum _ (fun n _ =>
    (continuous_apply n).smul continuous_const))

theorem unitTorusFourierTruncation_mem_hull (S : Finset (ι → ℤ)) (R : ℝ)
    (f : UnitTorusL2 ι) (hf : ‖f‖ ≤ R) :
    unitTorusFourierTruncation ι S f ∈ unitTorusFourierHull ι S R := by
  refine ⟨fun n => mFourierCoeff f n, ?_, ?_⟩
  · exact fun n => (unitTorus_fourier_coefficient_norm ι f n).trans hf
  · exact Finset.sum_coe_sort S (fun n => mFourierCoeff f n • mFourierBasis n)

def unitTorusH1EnergySublevel (R : ℝ) : Set (UnitTorusL2 ι) :=
  {f | ∃ g : ι → UnitTorusL2 ι, UnitTorusWeakGradient ι f g ∧
    ‖f‖ ^ 2 + ∑ j, ‖g j‖ ^ 2 ≤ R}

variable [DecidableEq ι]

theorem unitTorusH1EnergySublevel_totallyBounded (R : ℝ) :
    TotallyBounded (unitTorusH1EnergySublevel ι R) := by
  by_cases hR : 0 ≤ R
  · apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * Real.sqrt R / ε))
    have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_left _ _) hN)
    have hNε : Real.sqrt R < (N : ℝ) * (ε / 2) := by
      have := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hN)
      nlinarith
    let S := unitTorusFrequencyBox ι N
    let K := unitTorusFourierHull ι S (Real.sqrt R)
    have hK : IsCompact K := unitTorusFourierHull_isCompact ι S (Real.sqrt R)
    obtain ⟨T, hTfinite, hTcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
      (ε / 2) (by positivity)
    refine ⟨T, hTfinite, ?_⟩
    rintro f ⟨g, hgrad, henergy⟩
    have hgs : 0 ≤ ∑ j, ‖g j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hf : ‖f‖ ≤ Real.sqrt R := by
      have hs := Real.sq_sqrt hR
      nlinarith [norm_nonneg f, Real.sqrt_nonneg R]
    have hg : (∑ j, ‖g j‖ ^ 2) ≤ R := by nlinarith [sq_nonneg ‖f‖]
    have htail := unitTorus_weakGradient_fourier_tail ι N f g hgrad
    have htailR : (N : ℝ) * ‖f - unitTorusFourierTruncation ι S f‖ ≤ Real.sqrt R :=
      htail.trans (Real.sqrt_le_sqrt hg)
    have hdist : dist f (unitTorusFourierTruncation ι S f) < ε / 2 := by
      rw [dist_eq_norm]
      nlinarith
    have hp : unitTorusFourierTruncation ι S f ∈ K :=
      unitTorusFourierTruncation_mem_hull ι S (Real.sqrt R) f hf
    have hcovered := hTcover hp
    simp only [Set.mem_iUnion, Metric.mem_ball] at hcovered ⊢
    obtain ⟨y, hyT, hy⟩ := hcovered
    refine ⟨y, hyT, ?_⟩
    exact (dist_triangle f (unitTorusFourierTruncation ι S f) y).trans_lt (by linarith)
  · have hempty : unitTorusH1EnergySublevel ι R = ∅ := by
      ext f
      constructor
      · rintro ⟨g, _, henergy⟩
        have hsum : 0 ≤ ∑ j, ‖g j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        exact False.elim (hR (le_trans (add_nonneg (sq_nonneg _) hsum) henergy))
      · simp
    rw [hempty]
    exact totallyBounded_empty

theorem unitTorusH1EnergySublevel_isCompact_closure (R : ℝ) :
    IsCompact (closure (unitTorusH1EnergySublevel ι R)) :=
  (unitTorusH1EnergySublevel_totallyBounded ι R).closure.isCompact_of_isClosed isClosed_closure

theorem unitTorusWeakGradient_bounded_image_isCompact_closure
    (S : Set (UnitTorusL2 ι × (ι → UnitTorusL2 ι))) (hS : Bornology.IsBounded S)
    (hgrad : ∀ fg ∈ S, UnitTorusWeakGradient ι fg.1 fg.2) :
    IsCompact (closure (Prod.fst '' S)) := by
  obtain ⟨C, hC⟩ := hS.exists_norm_le
  have hsubset : Prod.fst '' S ⊆ unitTorusH1EnergySublevel ι
      ((1 + Fintype.card ι : ℝ) * C ^ 2) := by
    rintro f ⟨fg, hfg, rfl⟩
    refine ⟨fg.2, hgrad fg hfg, ?_⟩
    have hCf : ‖fg.1‖ ≤ C := (norm_fst_le fg).trans (hC fg hfg)
    have hCg (j : ι) : ‖fg.2 j‖ ≤ C :=
      (norm_le_pi_norm fg.2 j).trans ((norm_snd_le fg).trans (hC fg hfg))
    have hf2 : ‖fg.1‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hCf 2
    have hg2 : (∑ j, ‖fg.2 j‖ ^ 2) ≤ (Fintype.card ι : ℝ) * C ^ 2 := by
      calc
        _ ≤ ∑ _j : ι, C ^ 2 := Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hCg j) 2
        _ = _ := by simp
    nlinarith
  exact ((unitTorusH1EnergySublevel_totallyBounded ι _).subset hsubset).closure.isCompact_of_isClosed
    isClosed_closure

theorem unitTorusH1_bounded_image_isCompact_closure
    (S : Set (UnitTorusH1 ι)) (hS : Bornology.IsBounded S) :
    IsCompact (closure ((fun fg : UnitTorusH1 ι => fg.val.1) '' S)) := by
  have hb : Bornology.IsBounded (Subtype.val '' S) :=
    isometry_subtype_coe.lipschitzWith.isBounded_image hS
  have hg : ∀ fg ∈ Subtype.val '' S, UnitTorusWeakGradient ι fg.1 fg.2 := by
    rintro fg ⟨x, _, rfl⟩
    exact x.property
  simpa only [Set.image_image, Function.comp_def] using
    unitTorusWeakGradient_bounded_image_isCompact_closure ι (Subtype.val '' S) hb hg

theorem unitTorusH1_closedBall_image_isCompact_closure (f : UnitTorusH1 ι) (R : ℝ) :
    IsCompact (closure ((fun fg : UnitTorusH1 ι => fg.val.1) '' Metric.closedBall f R)) :=
  unitTorusH1_bounded_image_isCompact_closure ι _ Metric.isBounded_closedBall

end
end ArtinMatthews
