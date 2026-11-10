module

public import ArtinMatthews.VaryingKummerAnalyticHeckeGaussianDetectorWindow
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A finite height cover for the actual maximal Hecke detector.  The loss
is exactly the number of unit windows, independent of their locations. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def detectorHeightCenters (Y : ℝ) : Finset ℝ :=
  ((Finset.range (Nat.ceil Y + 1)).image (fun n : ℕ => (n : ℝ))) ∪
    ((Finset.range (Nat.ceil Y + 1)).image (fun n : ℕ => -(n : ℝ)))

theorem detectorHeightCenters_card_le {Y : ℝ} (hY : 0 ≤ Y) :
    ((detectorHeightCenters Y).card : ℝ) ≤ 2*Y+4 := by
  have hn : (detectorHeightCenters Y).card ≤ 2*(Nat.ceil Y+1) := by
    unfold detectorHeightCenters
    apply (Finset.card_union_le _ _).trans
    have hp := Finset.card_image_le (s := Finset.range (Nat.ceil Y+1)) (f := fun n : ℕ => (n : ℝ))
    have hm := Finset.card_image_le (s := Finset.range (Nat.ceil Y+1)) (f := fun n : ℕ => -(n : ℝ))
    simpa only [Finset.card_range,two_mul] using add_le_add hp hm
  have hn' : ((detectorHeightCenters Y).card : ℝ) ≤ 2*((Nat.ceil Y : ℝ)+1) := by
    exact_mod_cast hn
  have hc := Nat.ceil_lt_add_one hY
  linarith

theorem detectorHeightCenters_cover {Y t : ℝ} (ht : |t| ≤ Y) :
    ∃ t₀ ∈ detectorHeightCenters Y, |t-t₀| ≤ 1 := by
  by_cases hpos : 0 ≤ t
  · have hn : Nat.floor t < Nat.ceil Y+1 := Nat.lt_succ_iff.mpr
      ((Nat.floor_mono ((le_abs_self t).trans ht)).trans (Nat.floor_le_ceil Y))
    refine ⟨(Nat.floor t : ℝ),Finset.mem_union_left _ ?_,Nat.abs_sub_floor_le hpos⟩
    exact Finset.mem_image.mpr ⟨Nat.floor t,Finset.mem_range.mpr hn,rfl⟩
  · have hn : Nat.floor (-t) < Nat.ceil Y+1 := Nat.lt_succ_iff.mpr
      ((Nat.floor_mono ((neg_le_abs t).trans ht)).trans (Nat.floor_le_ceil Y))
    refine ⟨-(Nat.floor (-t) : ℝ),Finset.mem_union_right _ ?_,?_⟩
    · exact Finset.mem_image.mpr ⟨Nat.floor (-t),Finset.mem_range.mpr hn,rfl⟩
    · rw [show t - -(Nat.floor (-t) : ℝ) = -((-t)-(Nat.floor (-t) : ℝ)) by ring,abs_neg]
      exact Nat.abs_sub_floor_le (by linarith)

def coefficientFamilyLargeHeightWindows
    (A : Finset (integralFractionalIdeals K → ℂ))
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ δ : ℝ) (H : Finset ℝ) : Finset (integralFractionalIdeals K → ℂ) :=
  H.biUnion (fun t₀ => A.filter (fun a => ∃ t : ℝ, |t-t₀| ≤ 1 ∧
    δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖))

theorem mem_coefficientFamilyLargeHeightWindows
    (A : Finset (integralFractionalIdeals K → ℂ))
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ δ : ℝ) (H : Finset ℝ) (a : integralFractionalIdeals K → ℂ) :
    a ∈ coefficientFamilyLargeHeightWindows K A B v σ δ H ↔
      a ∈ A ∧ ∃ t₀ ∈ H, ∃ t : ℝ, |t-t₀| ≤ 1 ∧
        δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖ := by
  simp only [coefficientFamilyLargeHeightWindows,Finset.mem_biUnion,Finset.mem_filter]
  constructor
  · rintro ⟨t₀,ht₀,ha,ht⟩
    exact ⟨ha,t₀,ht₀,ht⟩
  · rintro ⟨ha,t₀,ht₀,ht⟩
    exact ⟨t₀,ht₀,ha,ht⟩

theorem actualHecke_coefficientFamily_height_windows_count
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ δ : ℝ) (hδ : 0 < δ) (H : Finset ℝ) :
    (∑ M ∈ T, (coefficientFamilyLargeHeightWindows K
      ((A M).image (fun ψ => ψ.coefficient)) B v σ δ H).card : ℝ) ≤
      (H.card : ℝ) *
        ((heckeGaussianWindowConstant K * (X+U^2) * (1+(Real.log X)^2) *
          coefficientClassDirichletMass K B v σ) / δ^2) := by
  calc
    _ ≤ ∑ M ∈ T, ∑ t₀ ∈ H, ((((A M).image (fun ψ => ψ.coefficient)).filter
        (fun a => ∃ t : ℝ, |t-t₀| ≤ 1 ∧
          δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro M _
      unfold coefficientFamilyLargeHeightWindows
      exact_mod_cast Finset.card_biUnion_le
    _ = ∑ t₀ ∈ H, ∑ M ∈ T, ((((A M).image (fun ψ => ψ.coefficient)).filter
        (fun a => ∃ t : ℝ, |t-t₀| ≤ 1 ∧
          δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖)).card : ℝ) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _t₀ ∈ H,
        (heckeGaussianWindowConstant K * (X+U^2) * (1+(Real.log X)^2) *
          coefficientClassDirichletMass K B v σ) / δ^2 := by
      exact Finset.sum_le_sum fun t₀ _ =>
        actualHecke_coefficientFamily_unit_window_count K hU hX T hT A hA B hB v σ t₀ δ hδ
    _ = _ := by simp

/-- The entire real height interval is covered with a linear, explicit
`2Y+4` loss. This is the actual maximal polynomial estimate used before
the remaining mollifier zero-detection argument. -/
theorem actualHecke_coefficientFamily_bounded_height_count
    {U X Y : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X) (hY : 0 ≤ Y)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ δ : ℝ) (hδ : 0 < δ) :
    (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
      (fun a => ∃ t : ℝ, |t| ≤ Y ∧
        δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖)).card : ℝ) ≤
      (2*Y+4) *
        ((heckeGaussianWindowConstant K * (X+U^2) * (1+(Real.log X)^2) *
          coefficientClassDirichletMass K B v σ) / δ^2) := by
  have hC := (heckeGaussianWindowConstant_pos K).le
  have hm := coefficientClassDirichletMass_nonneg K B v σ
  have hR : 0 ≤ (heckeGaussianWindowConstant K * (X+U^2) * (1+(Real.log X)^2) *
      coefficientClassDirichletMass K B v σ) / δ^2 := by positivity
  calc
    _ ≤ ∑ M ∈ T, ((coefficientFamilyLargeHeightWindows K
        ((A M).image (fun ψ => ψ.coefficient)) B v σ δ (detectorHeightCenters Y)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro M _
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro a ha
      obtain ⟨ha, t,ht,hval⟩ := Finset.mem_filter.mp ha
      obtain ⟨t₀,ht₀,hnear⟩ := detectorHeightCenters_cover ht
      exact (mem_coefficientFamilyLargeHeightWindows K _ B v σ δ _ a).mpr
        ⟨ha,t₀,ht₀,t,hnear,hval⟩
    _ ≤ ((detectorHeightCenters Y).card : ℝ) *
        ((heckeGaussianWindowConstant K * (X+U^2) * (1+(Real.log X)^2) *
          coefficientClassDirichletMass K B v σ) / δ^2) :=
      actualHecke_coefficientFamily_height_windows_count K hU hX T hT A hA B hB v σ δ hδ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (detectorHeightCenters_card_le hY) hR

end
end ArtinMatthews.VaryingKummerAnalytic
