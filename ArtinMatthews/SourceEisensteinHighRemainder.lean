module

public import ArtinMatthews.SourceEisensteinHighOutgoing
public import ArtinMatthews.SourceKPAutomorphicCutoff
public import ArtinMatthews.SourceKPAutomorphicEisenstein
public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceEisensteinInitialDifference
public import ArtinMatthews.SourceEisensteinNonconstantInvariance
public import ArtinMatthews.SourceKPTraceIntertwinerRational
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

/-! Genuine rational-Borel descent of the nonconstant term and the exact
high-cusp split of the original automorphic Eisenstein-minus-cutoff function. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicNonconstantEisenstein_rationalBorel (s : ℂ) (b : PGL(2,K))
    (hb : b ∈ sourceKPRationalBorel K) (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicProjectiveRationalLift K hζ b*g) =
      sourceKPAdelicNonconstantEisenstein K hζ s g := by
  have hA : sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveRationalLift K hζ b*g) =
      sourceKPAdelicCompactScalar K hζ s g :=
    (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s)).property b hb g
  simp only [sourceKPAdelicNonconstantEisenstein,sourceKPAdelicCompactEisenstein_rational_invariant,
    hA,sourceKPAdelicTraceIntertwiner_rationalBorel K hζ s b hb]

theorem sourceKPAdelicNonconstantEisenstein_finite_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicNonconstantEisenstein K hζ s (g*sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicNonconstantEisenstein K hζ s g :=
  sourceKPAdelicNonconstantEisenstein_deepCompact_right K hζ s g
    ⟨sourceKPFiniteDeepCoverLift K hζ k,⟨sourceKPFiniteDeepIntoAdelic K hζ k,rfl⟩⟩

def sourceKPFiniteLevelNonconstantEisenstein (s : ℂ) : SourceKPFiniteLevelSpace K hζ → ℂ :=
  sourceKPFiniteLevelDescend K hζ (sourceKPAdelicNonconstantEisenstein K hζ s)
    (sourceKPAdelicNonconstantEisenstein_finite_right K hζ s)

theorem sourceKPFiniteLevelNonconstantEisenstein_mk (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelNonconstantEisenstein K hζ s (sourceKPFiniteLevelMk K hζ g) =
      sourceKPAdelicNonconstantEisenstein K hζ s g := rfl

theorem sourceKPFiniteLevelNonconstantEisenstein_rationalBorel (s : ℂ) (b : PGL(2,K))
    (hb : b ∈ sourceKPRationalBorel K) (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelNonconstantEisenstein K hζ s (b • x) =
      sourceKPFiniteLevelNonconstantEisenstein K hζ s x := by
  obtain ⟨g,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  rw [← sourceKPFiniteLevelMk_rational,sourceKPFiniteLevelNonconstantEisenstein_mk,
    sourceKPFiniteLevelNonconstantEisenstein_mk,sourceKPAdelicNonconstantEisenstein_rationalBorel K hζ s b hb]

def sourceKPHighCuspNonconstantEisenstein (s : ℂ) (T : ℝ) (hT : 1 < T) :
    SourceKPHighCuspAutomorphic K hζ T → ℂ :=
  let R : SourceKPHighCuspBorelQuotient K hζ T → ℂ :=
    Quotient.lift (fun x : SourceKPHighCuspFinite K hζ T => sourceKPFiniteLevelNonconstantEisenstein K hζ s x.val)
      (by
        intro x y hxy
        obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp hxy
        rw [← hb]
        exact sourceKPFiniteLevelNonconstantEisenstein_rationalBorel K hζ s b.val b.property y.val)
  R ∘ (sourceKPHighCuspHomeomorph K hζ T hT).symm

theorem sourceKPHighCuspNonconstantEisenstein_rep (s : ℂ) (T : ℝ) (hT : 1 < T)
    (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspNonconstantEisenstein K hζ s T hT (sourceKPHighCuspProjection K hζ T x) =
      sourceKPFiniteLevelNonconstantEisenstein K hζ s x.val := by
  simp only [sourceKPHighCuspNonconstantEisenstein,Function.comp_apply,
    ← sourceKPHighCuspHomeomorph_mk K hζ T hT x,Homeomorph.symm_apply_apply]
  rfl

theorem sourceKPAutomorphicInitialDifference_high_split (s : ℂ) (T₀ T : ℝ)
    (hT₀ : 1 ≤ T₀) (hT : 1 < T) (hcut : 2*T₀ ≤ T)
    (x : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPAutomorphicEisenstein K hζ s x.val - sourceKPAutomorphicCutoffEisenstein K hζ T₀ s x.val =
      sourceKPHighCuspNonconstantEisenstein K hζ s T hT x +
        sourceKPHighCuspOutgoingEisenstein K hζ s T hT x := by
  obtain ⟨a,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T x
  induction a using Quotient.inductionOn with
  | _ y =>
    rw [sourceKPHighCuspQuotientMap_mk,sourceKPHighCuspNonconstantEisenstein_rep,
      sourceKPHighCuspOutgoingEisenstein_rep]
    obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ y.val
    have he : (sourceKPHighCuspProjection K hζ T y).val = sourceKPAutomorphicLevelMk K hζ q := by
      change (Quotient.mk _ y.val : SourceKPAutomorphicLevel K hζ) =
        Quotient.mk _ (sourceKPFiniteLevelMk K hζ q)
      exact congrArg (Quotient.mk _) hq.symm
    rw [he,sourceKPAutomorphicEisenstein_mk,sourceKPAutomorphicCutoffEisenstein_mk,
      ← hq,sourceKPFiniteLevelNonconstantEisenstein_mk,sourceKPFiniteLevelOutgoingEisenstein_mk]
    have hy := y.property
    rw [← hq,sourceKPFiniteLevelHeight_mk] at hy
    exact sourceKPAdelicInitialDifference_high K hζ hT₀ s q (hcut.trans hy.le)

end
end ArtinMatthews
