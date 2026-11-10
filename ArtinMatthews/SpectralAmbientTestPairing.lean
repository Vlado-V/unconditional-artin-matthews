module

public import ArtinMatthews.SpectralEisensteinTestMultiplier
public import ArtinMatthews.SpectralCuspidalTestMultiplier
public import ArtinMatthews.SpectralResidualTestMultiplier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The bounded native spectral action and its full weighted pairing.
Every actual cusp and residual coefficient is retained, and the continuum
has the literal positive-frequency measure dt/(2*pi). -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

local instance ambientTest_cuspInner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜:=ℂ) (E:=Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

def gamma0AmbientTestOperator (N : ℕ) [NeZero N] (h : SpectralEnergyTest) :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  gamma0CuspidalTestOperator N h+(gamma0ContinuousTestOperator N h+gamma0ResidualTestOperator N h)

theorem gamma0AmbientTestOperator_pair (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u v : Gamma0RegionL2 N) :
    inner ℂ u (gamma0AmbientTestOperator N h v)=
      (∑' i : Gamma0AllHeightSpectralIndex N,gamma0CuspidalTestSymbol N h i*
        (inner ℂ u (gamma0FullCuspidalSpectralBasis N i).val*
          inner ℂ (gamma0FullCuspidalSpectralBasis N i).val v))+
      ((∫ t,spectralContinuousTestSymbol h t*
        gamma0EisensteinChannelPair N (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N v) t
          ∂gamma0EisensteinSpectralMeasure)+
        ∑ l∈gamma0ResidualEnergyWindow N,h l*
          ∑ j,inner ℂ u (gamma0ResidualEigenbasis N l j).val*
            inner ℂ (gamma0ResidualEigenbasis N l j).val v) := by
  rw [gamma0AmbientTestOperator,add_apply,add_apply,inner_add_right,inner_add_right,
    gamma0CuspidalTestOperator_pair,gamma0ContinuousTestOperator_pair,gamma0ResidualTestOperator_pair]

theorem spectral_inner_pair_diagonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v : H) : inner ℂ u v*inner ℂ v u=((‖inner ℂ u v‖^2:ℝ):ℂ) := by
  rw [← inner_conj_symm (𝕜:=ℂ) v u,mul_comm,← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]

theorem gamma0EisensteinChannelPair_diagonal (N : ℕ) [NeZero N]
    (f : Gamma0EisensteinSpectralSpace N) (t : ℝ) :
    gamma0EisensteinChannelPair N f f t=
      ∑ i : Gamma0EisensteinCuspClasses N,((‖f i t‖^2:ℝ):ℂ) := by
  unfold gamma0EisensteinChannelPair
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ),Complex.ofReal_pow]
  rfl

theorem gamma0AmbientTestOperator_parseval (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u : Gamma0RegionL2 N) :
    inner ℂ u (gamma0AmbientTestOperator N h u)=
      (∑' i : Gamma0AllHeightSpectralIndex N,gamma0CuspidalTestSymbol N h i*
        ((‖inner ℂ u (gamma0FullCuspidalSpectralBasis N i).val‖^2:ℝ):ℂ))+
      ((∫ t,spectralContinuousTestSymbol h t*
        ∑ i : Gamma0EisensteinCuspClasses N,((‖(gamma0EisensteinAnalysis N u) i t‖^2:ℝ):ℂ)
          ∂gamma0EisensteinSpectralMeasure)+
        ∑ l∈gamma0ResidualEnergyWindow N,h l*
          ∑ j,((‖inner ℂ u (gamma0ResidualEigenbasis N l j).val‖^2:ℝ):ℂ)) := by
  rw [gamma0AmbientTestOperator_pair]
  simp_rw [spectral_inner_pair_diagonal,gamma0EisensteinChannelPair_diagonal]

theorem gamma0CuspidalTestCore_one (N : ℕ) [NeZero N] (u : gamma0AllHeightCuspidalMassSpace N) :
    gamma0CuspidalTestCore N 1 u=u := by
  apply (gamma0FullCuspidalSpectralBasis N).repr.injective
  apply Subtype.ext
  funext i
  rw [gamma0CuspidalTestCore,spectralHilbertMultiplier_repr]
  change (1:ℂ)*_= _
  exact one_mul _

theorem gamma0CuspidalTestOperator_one (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0CuspidalTestOperator N 1 u=(gamma0CuspidalProjection N u).val := by
  change (gamma0CuspidalTestCore N 1 (gamma0CuspidalProjection N u)).val=_
  rw [gamma0CuspidalTestCore_one]

theorem gamma0ResidualTestOperator_one (N : ℕ) [NeZero N] :
    gamma0ResidualTestOperator N 1=gamma0ResidualProjection N := by
  rw [gamma0ResidualTestOperator,gamma0ResidualProjection]
  apply Finset.sum_congr rfl
  intro l _
  exact one_smul ℂ _

theorem gamma0AmbientTestOperator_one (N : ℕ) [NeZero N] :
    gamma0AmbientTestOperator N 1=ContinuousLinearMap.id ℂ (Gamma0RegionL2 N) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [gamma0AmbientTestOperator,add_apply,add_apply,gamma0CuspidalTestOperator_one,
    gamma0ContinuousTestOperator_one,gamma0ResidualTestOperator_one]
  change (gamma0CuspidalProjection N u).val+
    ((gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinAnalysis N u)+gamma0ResidualProjection N u)=u
  calc
    _ = (gamma0CuspidalProjection N u).val+gamma0ResidualProjection N u+
      (gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinAnalysis N u) := by abel
    _ = u := (gamma0AmbientEisenstein_resolution N u).symm

theorem gamma0AmbientTestOperator_green (N : ℕ) [NeZero N] :
    gamma0AmbientTestOperator N spectralGreenEnergyTest=gamma0Green N := by
  apply ContinuousLinearMap.ext
  intro u
  rw [gamma0AmbientTestOperator,add_apply,add_apply,gamma0CuspidalTestOperator_green,
    gamma0ContinuousTestOperator_green,gamma0ResidualTestOperator_green]
  calc
    _ = gamma0Green N ((gamma0CuspidalProjection N u).val+gamma0ResidualProjection N u+
      (gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinAnalysis N u)) := by
        simp only [map_add]
        abel
    _ = gamma0Green N u := congrArg (gamma0Green N) (gamma0AmbientEisenstein_resolution N u).symm

end ArtinMatthews
