module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedResidualSlice
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedFiniteEval
public import ArtinMatthews.SourceRetainedTensorExpansion
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

/-! The literal unit-frequency residue on a fixed retained tuple is a
finite tensor of its actual local Jacquet coordinates. Coefficients
are the same residue at the actual chosen basis lifts. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (places : Finset (HeightOneSpectrum (𝓞 K))) (hs : 0 < (1 / 6 : ℂ).re)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ places
local notation "Rest" => SourceKPAdelicOutgoingRetainedFiniteRest K hζ places
local notation "ev" => sourceKPAdelicOutgoingRetainedFiniteEval K hζ places
local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)
local notation "A" => sourceKPAdelicOutgoingRetainedResidualCoefficient K hζ places
local notation "v" => (fun P : ↥places =>
  sourceKPAdelicOutgoingRetainedJacquetVector K hζ (Subtype.val P) hs)
local notation "W" => (fun P : ↥places =>
  sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ
    (Singleton.singleton (Subtype.val P) : Finset (HeightOneSpectrum (𝓞 K))) (1 / 6 : ℂ) hs)
local notation "Label" => SourceKPAdelicOutgoingRetainedJacquetLabel K hζ hs places
local notation "lift" => sourceKPAdelicOutgoingRetainedJacquetBasisLift K hζ
local notation "coord" => sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate K hζ

local instance sourceKPAdelicOutgoingRetainedResidualTensorAddCommGroup (P : ↥places) :
    AddCommGroup (W P) := Submodule.addCommGroup _

theorem sourceKPAdelicOutgoingRetainedResidualCoefficient_tensor {T : ℝ} (hT : 2 < T)
    (qf : Gf) (hqf : ∀ P : ↥places, sourceKPAdelicLocalBase K hζ P.val (1,qf) = 1)
    (g : Gₛ) :
    A hT qf g = ∑ k : Label, A hT qf (fun P => lift P.val hs (k P)) *
      ∏ P : ↥places, coord P.val hs (k P) (v P (g P)) := by
  letI : ∀ P : ↥places, FiniteDimensional ℂ (W P) := fun P =>
    sourceKPAdelicOutgoingRegularizedLocalCarrier_finiteDimensional K hζ P.val (1 / 6 : ℂ) hs
  exact sourceRetainedTensorExpansion v (A hT qf)
    (fun g P d hd => sourceKPAdelicOutgoingRetainedResidualCoefficient_slice_relation K hζ places hs hT
      qf g P (hqf P) d hd) g

theorem sourceKPAdelicOutgoingResidualFourierValue_retained_tensor {T : ℝ} (hT : 2 < T) (qf : Gf) :
    ∃ q : Gₛ × Rest, ev q = qf ∧
      C₁ (one_le_two.trans hT.le) qf =
        ∑ k : Label, A hT q.2.val (fun P => lift P.val hs (k P)) *
          ∏ P : ↥places, coord P.val hs (k P) (v P (q.1 P)) := by
  obtain ⟨q,hq⟩ := sourceKPAdelicOutgoingRetainedFiniteEval_surjective K hζ places qf
  refine ⟨q,hq,?_⟩
  exact (congrArg (C₁ (one_le_two.trans hT.le)) hq.symm).trans
    (sourceKPAdelicOutgoingRetainedResidualCoefficient_tensor K hζ places hs hT q.2.val q.2.property q.1)

theorem sourceKPAdelicOutgoingResidualFourierValue_retained_basis_ne_zero
    {T : ℝ} (hT : 2 < T) (qf : Gf) (h : C₁ (one_le_two.trans hT.le) qf ≠ 0) :
    ∃ q : Gₛ × Rest, ev q = qf ∧
      ∃ k : Label, A hT q.2.val (fun P => lift P.val hs (k P)) ≠ 0 := by
  obtain ⟨q,hq,he⟩ := sourceKPAdelicOutgoingResidualFourierValue_retained_tensor K hζ places hs hT qf
  refine ⟨q,hq,?_⟩
  by_contra hn
  apply h
  refine he.trans (Finset.sum_eq_zero fun k _ => ?_)
  have hk : A hT q.2.val (fun P => lift P.val hs (k P)) = 0 := by
    by_contra hk
    exact hn ⟨k,hk⟩
  rw [hk,zero_mul]

end
end ArtinMatthews
