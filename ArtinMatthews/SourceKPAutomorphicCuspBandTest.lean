module

public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicCompactCutoff
public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceKPAdelicCuspBand
public import ArtinMatthews.SourceKPAdelicCutoffSupport
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPAutomorphicCompactMeasure
public import ArtinMatthews.SourceKPAutomorphicCompactTopology
public import ArtinMatthews.SourceKPAutomorphicMeasureRegularity
public import ArtinMatthews.SourceKPCompactCutoffContinuity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

/-! A genuine test supported on a full height band of the actual compact quotient. -/

namespace ArtinMatthews
open NumberField Matrix MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "H" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

/-- A fixed inducing parameter and two actual cutoffs give a test over the entire cusp band. -/
def sourceKPAutomorphicCuspBandTest (A B : ℝ) (s : ℂ) (x : Y) : ℂ :=
  sourceKPAutomorphicCompactCutoffEisenstein K hζ A s x -
    sourceKPAutomorphicCompactCutoffEisenstein K hζ B s x

theorem sourceKPAutomorphicCuspBandTest_adelic {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) (q : SourceKPAdelicProjective K hζ) (hq : 1 < sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAutomorphicCuspBandTest K hζ A B s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) =
      ((sourceKPAdelicHeightCutoff A (sourceKPAdelicCoverHeight K hζ q) -
        sourceKPAdelicHeightCutoff B (sourceKPAdelicCoverHeight K hζ q) : ℝ) : ℂ) *
          sourceKPAdelicCompactScalar K hζ s q := by
  unfold sourceKPAutomorphicCuspBandTest
  rw [sourceKPAutomorphicCompactCutoffEisenstein_adelic,
    sourceKPAutomorphicCompactCutoffEisenstein_adelic,
    sourceKPAdelicCutoffEisenstein_eq_cutoffSeed_of_high K hζ hA s q hq,
    sourceKPAdelicCutoffEisenstein_eq_cutoffSeed_of_high K hζ (hA.trans hAB) s q hq,
    Complex.ofReal_sub, sub_mul]

theorem sourceKPAutomorphicCuspBandTest_adelic_upper {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) (y : 𝔸[K]) (q : SourceKPAdelicProjective K hζ)
    (hq : 1 < sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAutomorphicCuspBandTest K hζ A B s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
        (sourceKPAdelicUpperLift K hζ y * q))) =
    sourceKPAutomorphicCuspBandTest K hζ A B s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) := by
  simp only [sourceKPAutomorphicCuspBandTest, sourceKPAutomorphicCompactCutoffEisenstein_adelic,
    sourceKPAdelicCutoffEisenstein_left_upper_of_high K hζ hA s y q hq,
    sourceKPAdelicCutoffEisenstein_left_upper_of_high K hζ (hA.trans hAB) s y q hq]

theorem sourceKPAutomorphicCuspBandTest_center (A B : ℝ) (s : ℂ)
    (z : rootsOfUnity 3 K) (x : Y) :
    sourceKPAutomorphicCuspBandTest K hζ A B s (z • x) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) * sourceKPAutomorphicCuspBandTest K hζ A B s x := by
  unfold sourceKPAutomorphicCuspBandTest
  rw [sourceKPAutomorphicCompactCutoffEisenstein_center,
    sourceKPAutomorphicCompactCutoffEisenstein_center, mul_sub]

theorem sourceKPAutomorphicCuspBandTest_continuous {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (s : ℂ) : Continuous (sourceKPAutomorphicCuspBandTest K hζ A B s) := by
  have hin : Continuous (fun x : Y => (s, x)) := continuous_const.prodMk continuous_id
  have hc (L : ℝ) (hL : 0 < L) : Continuous (sourceKPAutomorphicCompactCutoffEisenstein K hζ L s) := by
    simpa only [Function.comp_def] using
      (sourceKPAutomorphicCompactCutoffEisenstein_joint_continuous K hζ hL).comp hin
  change Continuous (fun x : Y => sourceKPAutomorphicCompactCutoffEisenstein K hζ A s x -
    sourceKPAutomorphicCompactCutoffEisenstein K hζ B s x)
  exact (hc A hA).sub (hc B hB)

theorem sourceKPAutomorphicCuspBandTest_zero_of_height_le {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (s : ℂ) (x : Y) (hx : H x ≤ A) : sourceKPAutomorphicCuspBandTest K hζ A B s x = 0 := by
  induction x using Quotient.inductionOn with
  | _ x =>
    obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
    change sourceKPAdelicOrbitHeight K hζ q ≤ A at hx
    change sourceKPAdelicCutoffEisenstein K hζ A s q - sourceKPAdelicCutoffEisenstein K hζ B s q = 0
    rw [sourceKPAdelicCutoffEisenstein_zero_of_orbit_le K hζ hA s q hx,
      sourceKPAdelicCutoffEisenstein_zero_of_orbit_le K hζ (hA.trans_le hAB) s q (hx.trans hAB),
      sub_self]

theorem sourceKPAutomorphicCuspBandTest_zero_of_le_height {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) (x : Y) (hx : 2*B ≤ H x) : sourceKPAutomorphicCuspBandTest K hζ A B s x = 0 := by
  induction x using Quotient.inductionOn with
  | _ x =>
    obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
    change 2*B ≤ sourceKPAdelicOrbitHeight K hζ q at hx
    have hB := hA.trans hAB
    have hhigh : 1 < sourceKPAdelicOrbitHeight K hζ q := by linarith
    obtain ⟨a,⟨γ,rfl⟩,hγ⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hhigh
    let q' := sourceKPAdelicProjectiveRationalLift K hζ γ * q
    have he : sourceKPAdelicCoverHeight K hζ q' = sourceKPAdelicOrbitHeight K hζ q :=
      (sourceKPAdelicOrbitHeight_eq_cover_of_high K hζ q' hγ).symm.trans
        (sourceKPAdelicOrbitHeight_rational K hζ q γ)
    have hq' : 2*B ≤ sourceKPAdelicCoverHeight K hζ q' := he.symm ▸ hx
    change sourceKPAdelicCutoffEisenstein K hζ A s q - sourceKPAdelicCutoffEisenstein K hζ B s q = 0
    rw [← sourceKPAdelicCutoffEisenstein_rational K hζ A s γ q,
      ← sourceKPAdelicCutoffEisenstein_rational K hζ B s γ q]
    change sourceKPAdelicCutoffEisenstein K hζ A s q' - sourceKPAdelicCutoffEisenstein K hζ B s q' = 0
    rw [sourceKPAdelicCutoffEisenstein_eq_of_high K hζ hA s q' (by linarith),
      sourceKPAdelicCutoffEisenstein_eq_of_high K hζ hB s q' hq', sub_self]

theorem sourceKPAutomorphicCuspBandTest_support {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) : Function.support (sourceKPAutomorphicCuspBandTest K hζ A B s) ⊆
      {x : Y | A < H x ∧ H x < 2*B} := by
  intro x hx
  exact ⟨lt_of_not_ge (fun h => hx (sourceKPAutomorphicCuspBandTest_zero_of_height_le K hζ
      (zero_lt_one.trans_le hA) hAB s x h)),
    lt_of_not_ge (fun h => hx (sourceKPAutomorphicCuspBandTest_zero_of_le_height K hζ hA hAB s x h))⟩

theorem sourceKPAutomorphicCuspBandTest_hasCompactSupport {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (s : ℂ) : HasCompactSupport (sourceKPAutomorphicCuspBandTest K hζ A B s) :=
  HasCompactSupport.of_support_subset_isCompact
    (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ (2*B))
    (fun _ hx => (sourceKPAutomorphicCuspBandTest_support K hζ hA hAB s hx).2.le)

theorem sourceKPAutomorphicCuspBandTest_bounded {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (s : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Y, ‖sourceKPAutomorphicCuspBandTest K hζ A B s x‖ ≤ C := by
  have hAc := zero_lt_one.trans_le hA
  have hc := sourceKPAutomorphicCuspBandTest_continuous K hζ hAc (hAc.trans_le hAB) s
  have hS := sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ (2*B)
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : H x ≤ 2*B
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [sourceKPAutomorphicCuspBandTest_zero_of_le_height K hζ hA hAB s x (le_of_not_ge hx), norm_zero]
    exact le_max_right _ _

theorem sourceKPAutomorphicCuspBandTest_memLp {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (s : ℂ) :
    MemLp (sourceKPAutomorphicCuspBandTest K hζ A B s) 2 μY :=
  (sourceKPAutomorphicCuspBandTest_continuous K hζ (zero_lt_one.trans_le hA)
    (zero_lt_one.trans_le (hA.trans hAB)) s).memLp_of_hasCompactSupport
      (sourceKPAutomorphicCuspBandTest_hasCompactSupport K hζ hA hAB s)

end
end ArtinMatthews
