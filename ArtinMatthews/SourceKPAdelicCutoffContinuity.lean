module

public import ArtinMatthews.SourceKPAdelicCuspCutoff
public import ArtinMatthews.SourceKPFiniteLevelTopology
public import ArtinMatthews.SourceKPAdelicCutoffLocalFinite
public import ArtinMatthews.SourceKPAdelicDefectTermContinuity
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

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Filter
open scoped NumberField AdeleRing MatrixGroups BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCutoffSummand_joint_arch_continuous (T : ℝ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T p.1) (p.2,qf) c) := by
  simp_rw [sourceKPAdelicCutoffSummand_eq]
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp
      ((sourceKPAdelicHeightCutoff_contDiff T).continuous.comp
        ((sourceKPAdelicRationalHeight_arch_continuous K hζ qf c).comp continuous_snd))
  · exact sourceKPAdelicRationalScalar_joint_arch_continuous K hζ qf c

private theorem cutoffSummand_matrix_continuous (T : ℝ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T p.1) (ProjGenLinGroup.mk p.2,qf) c) := by
  have hm : Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      (p.1,ProjGenLinGroup.mk p.2)) :=
    continuous_fst.prodMk (continuous_quot_mk.comp continuous_snd)
  simpa only [Function.comp_def] using
    (sourceKPAdelicCutoffSummand_joint_arch_continuous K hζ T qf c).comp hm

theorem sourceKPAdelicCutoffEisenstein_joint_matrix_continuous {T : ℝ} (hT : 0 < T)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicCutoffEisenstein K hζ T p.1 (ProjGenLinGroup.mk p.2,qf)) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨I,hI,hzero⟩ := sourceKPAdelicCutoffSummand_locally_finite K hζ hT qf p₀.2
  have hc : Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      ∑ c ∈ hI.toFinset,
        sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T p.1) (ProjGenLinGroup.mk p.2,qf) c) := by
    apply continuous_finsetSum
    intro c _
    exact cutoffSummand_matrix_continuous K hζ T qf c
  apply hc.continuousAt.congr_of_eventuallyEq
  have hn := (continuous_snd.tendsto p₀).eventually hzero
  filter_upwards [hn] with p hp
  unfold sourceKPAdelicCutoffEisenstein sourceKPAdelicRationalSum
  apply tsum_eq_sum
  intro c hci
  exact hp p.1 c (by simpa only [Set.Finite.mem_toFinset] using hci)

end
end ArtinMatthews
