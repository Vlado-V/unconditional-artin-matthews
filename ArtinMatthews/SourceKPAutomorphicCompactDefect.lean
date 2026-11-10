module

public import ArtinMatthews.SourceKPAutomorphicCutoff
public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceKPAdelicCutoffDefectParameter
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

/-! The literal compact cutoff defect on the actual scalar-unitary
quotient used for the global energy space. -/

namespace ArtinMatthews
open NumberField Matrix Topology MulOpposite
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicCutoffDefect_rightCompact {T : ℝ} (hT : 0 < T) (s : ℂ)
    (k : SourceKPArchCompactRightGroup K hζ) (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicCutoffDefect K hζ T s (k • x) =
      sourceKPAutomorphicCutoffDefect K hζ T s x := by
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  calc
    sourceKPAutomorphicCutoffDefect K hζ T s (k • sourceKPAutomorphicLevelMk K hζ q) =
        sourceKPAutomorphicCutoffDefect K hζ T s
          (sourceKPAutomorphicLevelMk K hζ (q.1*unop k.val,q.2)) :=
      congrArg (sourceKPAutomorphicCutoffDefect K hζ T s)
        (sourceKPAutomorphicLevelMk_archRight K hζ k.val q)
    _ = sourceKPAutomorphicCutoffDefect K hζ T s (sourceKPAutomorphicLevelMk K hζ q) := by
      rw [sourceKPAutomorphicCutoffDefect_mk,sourceKPAutomorphicCutoffDefect_mk]
      have hp : (q.1*unop k.val,q.2) = q*((unop k.val,1) : SourceKPAdelicProjective K hζ) :=
        Prod.ext rfl (mul_one q.2).symm
      rw [hp]
      exact sourceKPAdelicCutoffCasimirDefect_right K hζ hT s q
        ⟨(unop k.val,1),sourceKPArchCompactRight_deep K hζ k⟩

def sourceKPAutomorphicCompactCutoffDefect {T : ℝ} (hT : 0 < T) (s : ℂ) :
    SourceKPAutomorphicCompactLevel K hζ → ℂ :=
  Quotient.lift (sourceKPAutomorphicCutoffDefect K hζ T s) (by
    intro x y hxy
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp hxy
    rw [← hk]
    exact sourceKPAutomorphicCutoffDefect_rightCompact K hζ hT s k y)

theorem sourceKPAutomorphicCompactCutoffDefect_mk {T : ℝ} (hT : 0 < T) (s : ℂ)
    (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicCompactCutoffDefect K hζ hT s (sourceKPAutomorphicCompactMk K hζ x) =
      sourceKPAutomorphicCutoffDefect K hζ T s x := rfl

theorem sourceKPAutomorphicCompactCutoffDefect_adelic {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicCompactCutoffDefect K hζ hT s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) =
        sourceKPAdelicCutoffCasimirDefect K hζ T s q := rfl

theorem sourceKPAutomorphicCompactCutoffDefect_entire {T : ℝ} (hT : 0 < T)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    Differentiable ℂ (fun s => sourceKPAutomorphicCompactCutoffDefect K hζ hT s x) := by
  induction x using Quotient.inductionOn with
  | _ x =>
    obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
    exact sourceKPAdelicCutoffCasimirDefect_entire K hζ hT q

theorem sourceKPAutomorphicCompactCutoffDefect_support {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    Function.support (sourceKPAutomorphicCompactCutoffDefect K hζ
      (lt_of_lt_of_le zero_lt_one hT) s) ⊆
        {x | sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ 2*T} := by
  intro x hx
  induction x using Quotient.inductionOn with
  | _ x => exact sourceKPAutomorphicCutoffDefect_support K hζ hT s hx

theorem sourceKPAutomorphicCompactCutoffDefect_tsupport {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    tsupport (sourceKPAutomorphicCompactCutoffDefect K hζ
      (lt_of_lt_of_le zero_lt_one hT) s) ⊆
        {x | sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ 2*T} :=
  closure_minimal (sourceKPAutomorphicCompactCutoffDefect_support K hζ hT s)
    ((lowerSemicontinuous_iff_isClosed_preimage.mp
      (sourceKPAutomorphicCompactOrbitHeight_lowerSemicontinuous K hζ)) (2*T))

theorem sourceKPAutomorphicCompactCutoffDefect_hasCompactSupport {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    HasCompactSupport (sourceKPAutomorphicCompactCutoffDefect K hζ
      (lt_of_lt_of_le zero_lt_one hT) s) :=
  (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ (2*T)).of_isClosed_subset
    (isClosed_tsupport _) (sourceKPAutomorphicCompactCutoffDefect_tsupport K hζ hT s)

end
end ArtinMatthews
