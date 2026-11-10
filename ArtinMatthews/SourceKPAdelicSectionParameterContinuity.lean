module

public import ArtinMatthews.SourceKPAdelicProjectiveHeight
public import ArtinMatthews.SourceKPFiniteLevelTopology
public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceArchSectionContinuity
public import ArtinMatthews.SourceKPAdelicFlatSection
public import ArtinMatthews.SourceKPAdelicParameterDerivative
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

/-! Joint spectral and archimedean continuity of the actual flat
section and its literal parameter derivative. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactScalar_flat_cover (s : ℂ) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s q =
      Complex.exp (s*(Real.log (sourceKPAdelicCoverHeight K hζ q) : ℂ))*
        sourceKPAdelicCompactScalar K hζ 0 q := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  have hh : sourceKPAdelicCoverHeight K hζ q = sourceKPAdelicHeight K hζ g := by
    unfold sourceKPAdelicCoverHeight
    rw [← hg,sourceKPAdelicHeightOnProjective_mk]
  rw [hh]
  exact sourceKPAdelicCompactScalar_flat K hζ s q g hg.symm

theorem sourceKPAdelicCompactScalar_arch_continuous (s : ℂ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun a : PGL(2,InfiniteAdeleRing K) => sourceKPAdelicCompactScalar K hζ s (a,qf)) := by
  apply (QuotientGroup.isQuotientMap_mk
    (Subgroup.center (GL (Fin 2) (InfiniteAdeleRing K)))).continuous_iff.mpr
  exact sourceArchCompactScalar_continuous K hζ s qf

theorem sourceKPAdelicCompactScalar_joint_arch_continuous
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalar K hζ p.1 (p.2,qf)) := by
  have hl : Continuous (fun a : PGL(2,InfiniteAdeleRing K) =>
      Real.log (sourceKPAdelicCoverHeight K hζ (a,qf))) :=
    (sourceKPAdelicCoverHeight_arch_continuous K hζ qf).log
      (fun a => (sourceKPAdelicCoverHeight_pos K hζ (a,qf)).ne')
  have he : (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalar K hζ p.1 (p.2,qf)) = fun p =>
        Complex.exp (p.1*(Real.log (sourceKPAdelicCoverHeight K hζ (p.2,qf)) : ℂ))*
          sourceKPAdelicCompactScalar K hζ 0 (p.2,qf) :=
    funext (fun p => sourceKPAdelicCompactScalar_flat_cover K hζ p.1 (p.2,qf))
  rw [he]
  exact (Complex.continuous_exp.comp (continuous_fst.mul
    (Complex.continuous_ofReal.comp (hl.comp continuous_snd)))).mul
      ((sourceKPAdelicCompactScalar_arch_continuous K hζ 0 qf).comp continuous_snd)

def sourceKPAdelicCompactScalarParameterDerivative (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) : ℂ :=
  (Real.log (sourceKPAdelicCoverHeight K hζ q) : ℂ)*sourceKPAdelicCompactScalar K hζ s q

theorem sourceKPAdelicCompactScalarParameterDerivative_hasDerivAt (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    HasDerivAt (fun z => sourceKPAdelicCompactScalar K hζ z q)
      (sourceKPAdelicCompactScalarParameterDerivative K hζ s q) s := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  have hh : sourceKPAdelicCoverHeight K hζ q = sourceKPAdelicHeight K hζ g := by
    unfold sourceKPAdelicCoverHeight
    rw [← hg,sourceKPAdelicHeightOnProjective_mk]
  simpa only [sourceKPAdelicCompactScalarParameterDerivative,hh] using
    sourceKPAdelicCompactScalar_hasDerivAt K hζ s q g hg.symm

theorem sourceKPAdelicCompactScalarParameterDerivative_joint_arch_continuous
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalarParameterDerivative K hζ p.1 (p.2,qf)) := by
  have hl := (sourceKPAdelicCoverHeight_arch_continuous K hζ qf).log
    (fun a => (sourceKPAdelicCoverHeight_pos K hζ (a,qf)).ne')
  exact (Complex.continuous_ofReal.comp (hl.comp continuous_snd)).mul
    (sourceKPAdelicCompactScalar_joint_arch_continuous K hζ qf)

end
end ArtinMatthews
