module

public import ArtinMatthews.SourceKPRetainedSeedExterior
public import ArtinMatthews.SourceKPRetainedSeedVector
public import ArtinMatthews.SourceKPRetainedDepthCutoff
public import ArtinMatthews.SourceKPRetainedSeedPrincipal
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

/-! The canonical phase-free seed can meet every prescribed depth on the
original retained set and has literal local sixth-power support. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceReflection
open scoped NumberField MatrixGroups AdeleRing SourcePhysical Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ
local notation "rUnit" => FiniteAdeleRing.unitEmbedding (𝓞 K) K
local notation "unitAt" => sourceKPRetainedUnitAt K
local notation "S[" S₀ "]" => sourceHilbertSet K S₀

theorem sourceKPRetainedPositiveSeed_principal_squarefree_cube_at_depth
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    (depth : S[S₀] → ℕ) {T : ℝ} (hT : 2 < T) :
    ∃ (a : A) (R M : S[S₀] → ℕ) (U : ∀ P : S[S₀], SourceThetaFiniteCutoff K P.val),
      let q₀ := (tuple 1 a S[S₀]).2
      let C₀ := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) q₀
      C₀ ≠ 0 ∧ sourceKPRetainedSeedVector K hζ S[S₀] R M hT q₀ ≠ 0 ∧
      (∀ (P : S[S₀]) (t : (P.val.adicCompletion K)ˣ), t ∈ (U P).region →
        ((t : P.val.adicCompletion K)-1) ∈ sourceLocalBall K P.val (-(depth P:ℤ)) ∧
          ∃ w, w^6 = t) ∧
      ∀ (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀)
        (z : ∀ P : S[S₀], (P.val.adicCompletion K)ˣ),
        let m := sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)
        sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
            sourceKPRetainedSeedFourierAt K hζ S[S₀] R M (one_le_two.trans hT.le) m q₀
              (D (sourceKPRetainedDiagonalUnit K S[S₀] z)) =
          C₀ * (∏ P : S[S₀], (U P).factor (unitAt P.val (rUnit m) * z P)) *
            (reflectionGammaTwo K hζ S₀ c.val /
              ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) *
                (sourcePrimeExponentNorm K S₀ n : ℂ))) := by
  obtain ⟨a,R,M,U,hne,hv,hdeep,hcut⟩ :=
    sourceKPRetainedPositiveSeed_exists_at_depth K hζ S₀ hS depth hT
  have hCube (P : S[S₀]) (t : (P.val.adicCompletion K)ˣ) (ht : t ∈ (U P).region) :
      ∃ w, w^3 = t := by
    obtain ⟨w,hw⟩ := (hdeep P t ht).2
    refine ⟨w^2,?_⟩
    rw [← pow_mul, show (2:ℕ)*3 = 6 from rfl, hw]
  exact ⟨a,R,M,U,hne,hv,hdeep,
    sourceKPRetainedSeedFourierAt_principal_squarefree_cube_of_cubeCutoffs
      K hζ S₀ hS R M hT a U hCube hcut⟩

end
end ArtinMatthews
