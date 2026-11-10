module

public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceKPArchComponentConjugacyMeasure
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
public import Mathlib.NumberTheory.Height.NumberField
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
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchComponentSubgroup_rational (γ : PGL(2, K))
    (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPArchComponentSubgroup K hζ (γ • b) =
      sourceConjugateSubgroup (sourceKPArchComponentSubgroup K hζ b)
        (sourceKPRationalArchMap K hζ γ) := by
  unfold sourceKPArchComponentSubgroup sourceKPRationalFiniteStabilizer
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  simp only [sourceConjugateSubgroup, Subgroup.map_map]
  congr 1
  ext x
  simp [MonoidHom.comp_apply, MulAut.conj_apply]

def sourceKPArchComponentPushMeasure (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) : Measure (SourceKPAutomorphicLevel K hζ) :=
  Measure.map (sourceKPArchComponentEmbedding K hζ b)
    (sourceKPArchComponentQuotientMeasure K hζ b μ)

theorem sourceKPArchComponent_rational_embedding (γ : PGL(2, K))
    (b : SourceKPFiniteLevelFiber K hζ) (q : SourceKPArchComponentQuotient K hζ b) :
    sourceKPArchComponentEmbedding K hζ (γ • b)
      (sourceKPArchComponentConjugacy K hζ b (γ • b) (sourceKPRationalArchMap K hζ γ)
        (sourceKPArchComponentSubgroup_rational K hζ γ b) q) =
      sourceKPArchComponentEmbedding K hζ b q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change sourceKPArchComponentEmbedding K hζ (γ • b)
      (sourceKPArchComponentConjugacy K hζ b (γ • b) (sourceKPRationalArchMap K hζ γ)
        (sourceKPArchComponentSubgroup_rational K hζ γ b)
        (sourceKPArchComponentQuotientMap K hζ b a)) = _
    rw [sourceKPArchComponentConjugacy_mk]
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨γ,rfl⟩

theorem sourceKPArchComponentPushMeasure_rational (γ : PGL(2, K))
    (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    sourceKPArchComponentPushMeasure K hζ (γ • b) μ =
      sourceKPArchComponentPushMeasure K hζ b μ := by
  have he := sourceKPArchComponentConjugacy_measurePreserving K hζ b (γ • b)
    (sourceKPRationalArchMap K hζ γ) (sourceKPArchComponentSubgroup_rational K hζ γ b) μ
  unfold sourceKPArchComponentPushMeasure
  rw [← he.map_eq, Measure.map_map (sourceKPArchComponentEmbedding_measurable K hζ _) he.measurable]
  congr 1
  funext q
  exact sourceKPArchComponent_rational_embedding K hζ γ b q

theorem sourceKPArchComponentPushMeasure_orbit (b c : SourceKPFiniteLevelFiber K hζ)
    (h : sourceKPFiniteOrbitMk K hζ b = sourceKPFiniteOrbitMk K hζ c)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    sourceKPArchComponentPushMeasure K hζ b μ = sourceKPArchComponentPushMeasure K hζ c μ := by
  obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
  rw [← hγ]
  exact sourceKPArchComponentPushMeasure_rational K hζ γ c μ

theorem sourceKPArchComponentPushMeasure_eq_component (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    sourceKPArchComponentPushMeasure K hζ b μ =
      sourceKPAutomorphicComponentMeasure K hζ μ (sourceKPFiniteOrbitMk K hζ b) := by
  apply sourceKPArchComponentPushMeasure_orbit K hζ
  exact (sourceKPFiniteOrbitRepresentative_spec K hζ _).symm

end
end ArtinMatthews
